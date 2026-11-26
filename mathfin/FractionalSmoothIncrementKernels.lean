import FractionalApproximationResolvent
import FractionalKernelIncrements

/-! Reflected old and recent kernel weights in the smooth variance
increment, with uniform fractional L¹ and L² bounds. -/

open MeasureTheory Set
open scoped Interval

namespace RoughHeston

theorem intervalIntegral_reflect_recent_kernel (K φ : ℝ → ℝ) (s t : ℝ) :
    (∫ r in s..t, φ (K (t-r))) = ∫ r in (0:ℝ)..(t-s), φ (K r) := by
  have h := intervalIntegral.integral_comp_sub_left (f := fun r => φ (K r)) (a := s) (b := t) t
  simpa only [sub_self] using h

theorem intervalIntegral_reflect_old_kernel_difference (K φ : ℝ → ℝ) (s t : ℝ) :
    (∫ r in (0:ℝ)..s, φ (K (t-r)-K (s-r))) =
      ∫ r in (0:ℝ)..s, φ (K (r+(t-s))-K r) := by
  have h := intervalIntegral.integral_comp_sub_left (f := fun r => φ (K (t-r)-K (s-r)))
    (a := 0) (b := s) s
  simp only [sub_self, sub_zero, sub_sub_cancel] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro r _
  congr 3
  ring

/-- The deterministic squared stochastic increment weights have the
same fractional rate uniformly in the smooth approximation index. -/
theorem fractionalSmooth_increment_energy_le {α s t : ℝ}
    (hα : 1/2 < α) (hα' : α < 1) (hs : 0 ≤ s) (hst : s ≤ t) (n : ℕ) :
    let K := fractionalExponentialApproximation α n
    (∫ r in (0:ℝ)..s, (K (t-r)-K (s-r))^2) + (∫ r in s..t, (K (t-r))^2) ≤
      (2/(Real.Gamma α^2*(2*α-1)))*(t-s)^(2*α-1) := by
  dsimp only
  have hα₀ : 0 < α := by linarith
  obtain ⟨hc,h₀,hanti⟩ := fractionalExponentialApproximation_properties hα₀ hα' n
  rw [intervalIntegral_reflect_old_kernel_difference _ (fun x : ℝ => x^2),
    intervalIntegral_reflect_recent_kernel _ (fun x : ℝ => x^2), add_comm]
  exact heston_dominated_kernel_increment_L2 hα hs (sub_nonneg.mpr hst) hc.measurable
    (fun x _ => h₀ x) (hanti.antitoneOn _)
    (fun _ hx => fractionalExponentialApproximation_le_hestonKernel hα₀ hα' hx n)

theorem fractionalSmooth_increment_mass_le {α s t : ℝ}
    (hα : 0 < α) (hα' : α < 1) (hs : 0 ≤ s) (hst : s ≤ t) (n : ℕ) :
    let K := fractionalExponentialApproximation α n
    (∫ r in (0:ℝ)..s, |K (t-r)-K (s-r)|) + (∫ r in s..t, |K (t-r)|) ≤
      (2/(Real.Gamma α*α))*(t-s)^α := by
  dsimp only
  obtain ⟨hc,h₀,hanti⟩ := fractionalExponentialApproximation_properties hα hα' n
  simp_rw [abs_of_nonneg (h₀ _)]
  have hR : (∫ r in s..t, fractionalExponentialApproximation α n (t-r)) =
      ∫ r in (0:ℝ)..(t-s), fractionalExponentialApproximation α n r :=
    intervalIntegral_reflect_recent_kernel (fractionalExponentialApproximation α n) id s t
  rw [intervalIntegral_reflect_old_kernel_difference _ abs, hR, add_comm]
  exact heston_dominated_kernel_increment_L1 hα hs (sub_nonneg.mpr hst) hc.measurable
    (fun x _ => h₀ x) (hanti.antitoneOn _)
    (fun _ hx => fractionalExponentialApproximation_le_hestonKernel hα hα' hx n)

#print axioms RoughHeston.fractionalSmooth_increment_energy_le
#print axioms RoughHeston.fractionalSmooth_increment_mass_le

end RoughHeston
