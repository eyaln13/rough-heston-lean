import FractionalSmoothIncrementKernels
import ExplicitPulsedKernelProfile
import EulerLinearGrowthEnergy

/-! Reflect the true singular kernel on the entire fixed horizon. The
same deterministic L¹ and L² rates control the aggregate increments. -/

open MeasureTheory Set Filter
open scoped NNReal ENNReal Interval Topology

namespace RoughHeston

set_option maxHeartbeats 1500000

theorem intervalIntegrable_causal_hestonKernel_translate {α t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T)
    {f : ℝ → ℝ} (h0 : f 0 = 0) (hf : IntervalIntegrable (fun s => f (hestonKernel α s)) volume 0 t) :
    IntervalIntegrable (fun r => f (hestonKernel α (t-r))) volume 0 T := by
  have hR := hf.comp_sub_left t
  have hL : IntervalIntegrable (fun r => f (hestonKernel α (t-r))) volume 0 t := by
    simpa only [sub_self, sub_zero] using hR.symm
  apply hL.trans
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le htT).2
  refine (integrable_zero _ _ _).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  rw [hestonKernel, if_neg (not_lt_of_ge (sub_nonpos.mpr hr.1.le)), h0]
  rfl

theorem intervalIntegrable_hestonKernelDifference {α s t T : ℝ} (hα : 1/2 < α)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hsT : s ≤ T) (htT : t ≤ T) :
    let D := fun r => hestonKernel α (t-r)-hestonKernel α (s-r)
    IntervalIntegrable (fun r => (D r)^2) volume 0 T ∧ IntervalIntegrable (fun r => |D r|) volume 0 T := by
  intro D
  have hT := ht.trans htT
  have hi (u : ℝ) (hu : 0 ≤ u) (huT : u ≤ T) :
      MemLp (fun r => hestonKernel α (u-r)) 2 (volume.restrict (Ioc 0 T)) := by
    apply (memLp_two_iff_integrable_sq ((hestonKernel_measurable α).comp
      (measurable_const.sub measurable_id)).aestronglyMeasurable).2
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1
    apply intervalIntegrable_causal_hestonKernel_translate hu huT (f := fun x => x^2) (by norm_num)
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hu).2
    have h := (hestonKernel_memLp_two hα (Real.toNNReal u)).integrable_sq
    unfold IntegrableOn
    simpa only [Real.coe_toNNReal u hu] using h
  have hD : MemLp D 2 (volume.restrict (Ioc 0 T)) := (hi t ht htT).sub (hi s hs hsT)
  exact ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 hD.integrable_sq,
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 ((hD.integrable one_le_two).norm)⟩

private theorem intervalIntegral_hestonKernelDifference_split {α s t T : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T)
    {f : ℝ → ℝ} (hf₀ : f 0 = 0)
    (hD : IntervalIntegrable (fun r => f (hestonKernel α (t-r)-hestonKernel α (s-r))) volume 0 T) :
    (∫ r in (0:ℝ)..T, f (hestonKernel α (t-r)-hestonKernel α (s-r))) =
      (∫ r in (0:ℝ)..s, f (hestonKernel α (t-r)-hestonKernel α (s-r))) +
        (∫ r in s..t, f (hestonKernel α (t-r))) := by
  let D (r : ℝ) := f (hestonKernel α (t-r)-hestonKernel α (s-r))
  have h₁ (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) : IntervalIntegrable D volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
      (((intervalIntegrable_iff_integrableOn_Ioc_of_le (hs.trans (hst.trans htT))).1 hD).mono_set (Ioc_subset_Ioc ha hb))
  change (∫ r in (0:ℝ)..T, D r) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals (h₁ 0 t le_rfl (hs.trans hst) htT)
    (h₁ t T (hs.trans hst) htT le_rfl),
    ← intervalIntegral.integral_add_adjacent_intervals (h₁ 0 s le_rfl hs (hst.trans htT))
      (h₁ s t hs hst htT)]
  have hLast : (∫ r in t..T, D r) = 0 := by
    rw [intervalIntegral.integral_of_le htT]
    calc
      _ = ∫ _ in Ioc t T, (0:ℝ) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro r hr
        have hK₀ (x : ℝ) (hx : x ≤ 0) : hestonKernel α x = 0 := if_neg (not_lt_of_ge hx)
        dsimp [D]
        rw [hK₀ _ (sub_nonpos.mpr hr.1.le), hK₀ _ (sub_nonpos.mpr (hst.trans hr.1.le)), sub_self, hf₀]
      _ = 0 := integral_zero _ _
  rw [hLast, add_zero]
  congr 1
  rw [intervalIntegral.integral_of_le hst, intervalIntegral.integral_of_le hst]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r hr
  dsimp [D]
  have hK₀ : hestonKernel α (s-r) = 0 := if_neg (not_lt_of_ge (sub_nonpos.mpr hr.1.le))
  rw [hK₀, sub_zero]

theorem hestonKernel_lower_shift_energy_mass {α s t T : ℝ} (hα : 1/2 < α) (hα' : α ≤ 1)
    (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    let D := fun r => hestonKernel α (t-r)-hestonKernel α (s-r)
    (∫ r in (0:ℝ)..T, (D r)^2) ≤ (2/(Real.Gamma α^2*(2*α-1)))*(t-s)^(2*α-1) ∧
    (∫ r in (0:ℝ)..T, |D r|) ≤ (2/(Real.Gamma α*α))*(t-s)^α := by
  intro D
  obtain ⟨h₂,h₁⟩ := intervalIntegrable_hestonKernelDifference hα hs (hs.trans hst) (hst.trans htT) htT
  constructor
  · change (∫ r in (0:ℝ)..T, (hestonKernel α (t-r)-hestonKernel α (s-r))^2) ≤ _
    rw [intervalIntegral_hestonKernelDifference_split hs hst htT (f := fun x => x^2) (by norm_num) h₂,
      intervalIntegral_reflect_old_kernel_difference _ (fun x : ℝ => x^2),
      intervalIntegral_reflect_recent_kernel _ (fun x : ℝ => x^2), add_comm]
    exact hestonKernel_increment_L2 hα hα' hs (sub_nonneg.mpr hst)
  · change (∫ r in (0:ℝ)..T, |hestonKernel α (t-r)-hestonKernel α (s-r)|) ≤ _
    rw [intervalIntegral_hestonKernelDifference_split hs hst htT (f := abs) abs_zero h₁,
      intervalIntegral_reflect_old_kernel_difference _ abs, intervalIntegral_reflect_recent_kernel _ abs]
    simp_rw [abs_of_nonneg (hestonKernel_nonneg_explicit (by linarith : 0 < α) _)]
    rw [add_comm]
    exact hestonKernel_increment_L1 (by linarith) hα' hs (sub_nonneg.mpr hst)

#print axioms RoughHeston.hestonKernel_lower_shift_energy_mass

end RoughHeston
