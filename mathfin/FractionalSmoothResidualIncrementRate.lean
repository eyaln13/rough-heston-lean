import FractionalSmoothVarianceIncrementRate

/-! The normalized residual increment has at least the same fractional
rate as its physical variance coordinate. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {T : ℝ≥0} {α κ σ : ℝ} {n : ℕ} {v : Option ι → ℝ} {β : Option ι → ℝ≥0 → ℝ}

namespace FractionalCoupledSmoothLaw

theorem residual_increment_even_moment_le
    (L : FractionalCoupledSmoothLaw T α n κ σ v β)
    (hα : 1/2 < α) (hα' : α < 1) (i : Option ι)
    {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B)
    {s t : ℝ≥0} (hst : s ≤ t) (ht : t ≤ T) (m : ℕ) (hm : 2 ≤ m)
    {Cₘ : ℝ≥0∞}
    (hVm : ∀ u ≤ T, (∫⁻ p, ENNReal.ofReal (max (L.variance i u p) 0)^m
        ∂(L.law : Measure _)) ≤ Cₘ) :
    (∫⁻ q, ‖L.residual i t q-L.residual i s q‖ₑ^(2*m : ℕ) ∂(L.law : Measure _)) ≤
      boundedMartingaleEvenPowerConstant m * ENNReal.ofReal (σ^2)^m *
        ENNReal.ofReal ((T:ℝ)^((2-2*α)*(m:ℝ))) * Cₘ *
      ENNReal.ofReal ((((t:ℝ)-(s:ℝ)))^((2*α-1)*(m:ℝ))) := by
  let Ω := CanonicalPath T (FractionalCoupledSmoothState ι n)
  let Δ := (t:ℝ)-(s:ℝ)
  let e := (2*α-1)*(m:ℝ)
  have hK : fractionalExponentialApproximation α n 0 ≠ 0 :=
    (fractionalExponentialApproximation_pos_at_zero (by linarith : 0 < α) hα' n).ne'
  have h := L.rawWeightedRow_increment_even_moment_le hK i hB hβ hβB
    (H := T) le_rfl (g := fun _ => 1) (d := fun _ => 0)
    contDiff_const continuous_const (fun _ => hasDerivAt_const _ _) hst ht m hm hVm
  have he (q : Ω) :
      (L.residual i t q-L.residual i 0 q) - (L.residual i s q-L.residual i 0 q) =
      L.residual i t q-L.residual i s q := by ring
  simp only [min_eq_left ht, min_eq_left (hst.trans ht), one_pow, one_mul, zero_mul,
    intervalIntegral.integral_zero, sub_zero, he, intervalIntegral.integral_const, smul_eq_mul] at h
  have hΔ : 0 ≤ Δ := sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst)
  have hΔT : Δ ≤ (T:ℝ) := (sub_le_self _ s.coe_nonneg).trans (NNReal.coe_le_coe.mpr ht)
  have hm₀ : 0 < (m:ℝ) := by positivity
  have hAlpha : 0 < 2*α-1 := by linarith
  have hAlpha' : 2*α-1 ≤ 1 := by linarith
  have hM : e ≤ (m:ℝ) := by
    simpa only [e, one_mul] using mul_le_mul_of_nonneg_right hAlpha' hm₀.le
  have he₀ : 0 < e := mul_pos hAlpha hm₀
  have hR := ofReal_rpow_le_horizon_mul_ofReal_rpow hΔ hΔT he₀ hM
  have hE : (m:ℝ)-e = (2-2*α)*(m:ℝ) := by dsimp [e]; ring
  rw [hE] at hR
  refine h.trans ?_
  change boundedMartingaleEvenPowerConstant m * ENNReal.ofReal (Δ*σ^2)^m * Cₘ ≤ _
  rw [mul_comm Δ, ENNReal.ofReal_mul (sq_nonneg _), mul_pow, ← ENNReal.ofReal_pow hΔ]
  have hUpper :
      boundedMartingaleEvenPowerConstant m * (ENNReal.ofReal (σ^2)^m * ENNReal.ofReal (Δ^(m:ℝ))) * Cₘ ≤
      boundedMartingaleEvenPowerConstant m * (ENNReal.ofReal (σ^2)^m *
        (ENNReal.ofReal ((T:ℝ)^((2-2*α)*(m:ℝ))) * ENNReal.ofReal (Δ^e))) * Cₘ := by
    gcongr
  convert hUpper using 1
  · simp only [Real.rpow_natCast]
  · change boundedMartingaleEvenPowerConstant m * ENNReal.ofReal (σ^2)^m *
        ENNReal.ofReal ((T:ℝ)^((2-2*α)*(m:ℝ))) * Cₘ * ENNReal.ofReal (Δ^e) = _
    ac_rfl

end FractionalCoupledSmoothLaw

#print axioms RoughHeston.FractionalCoupledSmoothLaw.residual_increment_even_moment_le

end RoughHeston
