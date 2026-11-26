import FractionalKernelL1
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open MeasureTheory Filter Set
open scoped MeasureTheory Topology

namespace RoughHeston

/-- The time derivative kernel for the positive history contribution. -/
noncomputable def fractionalHistoryDensity (α u : ℝ) : ℝ :=
  α / Real.Gamma (1 - α) * u ^ (-(1 + α))

theorem fractionalHistoryDensity_nonneg {α u : ℝ}
    (hα : 0 ≤ α) (hα' : α < 1) (hu : 0 ≤ u) :
    0 ≤ fractionalHistoryDensity α u :=
  mul_nonneg (div_nonneg hα (Real.Gamma_pos_of_pos (sub_pos.mpr hα')).le)
    (Real.rpow_nonneg hu _)

theorem hasDerivAt_fractionalL {α u : ℝ} (hu : 0 < u) :
    HasDerivAt (fractionalL α) (-fractionalHistoryDensity α u) u := by
  have h := (Real.hasDerivAt_rpow_const (p := -α) (Or.inl hu.ne')).div_const (Real.Gamma (1 - α))
  have hfun : (fun x : ℝ => x ^ (-α) / Real.Gamma (1 - α)) =ᶠ[𝓝 u] fractionalL α := by
    filter_upwards [Ioi_mem_nhds hu] with x hx
    rw [fractionalL, ite_eq_right (not_le_of_gt hx)]
  convert h.congr_of_eventuallyEq hfun.symm using 1
  unfold fractionalHistoryDensity
  rw [show -α - 1 = -(1 + α) by ring]
  ring

theorem integral_fractionalHistoryDensity_shift {α u r : ℝ} (hu : 0 < u) (hr : 0 ≤ r) :
    IntervalIntegrable (fun s => fractionalHistoryDensity α (u + s)) volume 0 r ∧
      (∫ s in (0 : ℝ)..r, fractionalHistoryDensity α (u + s)) =
        fractionalL α u - fractionalL α (u + r) := by
  have hd (s : ℝ) (hs : s ∈ uIcc (0 : ℝ) r) :
      HasDerivAt (fun x => -fractionalL α (u + x)) (fractionalHistoryDensity α (u + s)) s := by
    rw [uIcc_of_le hr] at hs
    have ha := (hasDerivAt_const s u).add (hasDerivAt_id s)
    have h := (hasDerivAt_fractionalL (α := α) (add_pos_of_pos_of_nonneg hu hs.1)).comp s ha
    simpa only [Function.comp_def, zero_add, mul_one, neg_neg, Pi.neg_def] using h.neg
  have hc : ContinuousOn (fun s => fractionalHistoryDensity α (u + s)) (Icc 0 r) := by
    intro s hs
    have hx : u + s ≠ 0 := (add_pos_of_pos_of_nonneg hu hs.1).ne'
    exact (continuousAt_const.mul ((continuousAt_const.add continuousAt_id).rpow_const
      (Or.inl hx))).continuousWithinAt
  have hi := hc.intervalIntegrable_of_Icc (μ := volume) hr
  refine ⟨hi, ?_⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi, add_zero]
  ring

/-- Translation of the past term in the inverse equation gives the
integral of the positive history input. The identity is a Lebesgue
integral statement, so it includes the singular endpoint. -/
theorem fractional_history_input_splitting {α t r C : ℝ} {V : ℝ → ℝ}
    (hα : 0 < α) (hα' : α < 1) (hr : 0 ≤ r) (_hC : 0 ≤ C)
    (hV : Measurable V) (hV₀ : ∀ u ∈ Ioc (0 : ℝ) t, 0 ≤ V u)
    (hVb : ∀ u ∈ Ioc (0 : ℝ) t, V u ≤ C) :
    let ν := volume.restrict (Ioc (0 : ℝ) t)
    let η := volume.restrict (Ioc (0 : ℝ) r)
    let q (u s : ℝ) := fractionalHistoryDensity α (u + s) * V u
    Integrable (Function.uncurry q) (ν.prod η) ∧
      (∫ s in Ioc (0 : ℝ) r, ∫ u in Ioc (0 : ℝ) t, q u s) =
        ∫ u in Ioc (0 : ℝ) t, (fractionalL α u - fractionalL α (u + r)) * V u := by
  dsimp only
  let ν := volume.restrict (Ioc (0 : ℝ) t)
  let η := volume.restrict (Ioc (0 : ℝ) r)
  let q (u s : ℝ) := fractionalHistoryDensity α (u + s) * V u
  have hq : Measurable (Function.uncurry q) := by
    unfold q fractionalHistoryDensity Function.uncurry
    exact (measurable_const.mul ((measurable_fst.add measurable_snd).pow_const _)).mul
      (hV.comp measurable_fst)
  have hLpos (x : ℝ) (hx : 0 < x) : 0 ≤ fractionalL α x := by
    rw [fractionalL, ite_eq_right (not_le_of_gt hx)]
    exact div_nonneg (Real.rpow_nonneg hx.le _) (Real.Gamma_pos_of_pos (sub_pos.mpr hα')).le
  have hInt (u : ℝ) (hu : u ∈ Ioc (0 : ℝ) t) :
      Integrable (q u) η ∧ (∫ s, q u s ∂η) =
        (fractionalL α u - fractionalL α (u + r)) * V u := by
    obtain ⟨hi, he⟩ := integral_fractionalHistoryDensity_shift (α := α) hu.1 hr
    have hi' := (intervalIntegrable_iff_integrableOn_Ioc_of_le hr).1 hi
    refine ⟨hi'.mul_const (V u), ?_⟩
    change (∫ s, fractionalHistoryDensity α (u + s) * V u ∂η) = _
    rw [integral_mul_const]
    exact congrArg (fun a : ℝ => a * V u) ((intervalIntegral.integral_of_le hr).symm.trans he)
  have hNorm (u : ℝ) (hu : u ∈ Ioc (0 : ℝ) t) :
      (∫ s, ‖q u s‖ ∂η) = ∫ s, q u s ∂η := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact Real.norm_of_nonneg (mul_nonneg
      (fractionalHistoryDensity_nonneg hα.le hα' (add_nonneg hu.1.le hs.1.le)) (hV₀ u hu))
  have ho : Integrable (fun u => ∫ s, ‖q u s‖ ∂η) ν := by
    refine ((fractionalL_integrableOn_Ioc hα' t).mul_const C).mono_nonneg
      hq.aestronglyMeasurable.norm.integral_prod_right'
      (ae_of_all ν fun _ => integral_nonneg fun _ => norm_nonneg _) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [hNorm u hu, (hInt u hu).2]
    exact (mul_le_mul_of_nonneg_right (sub_le_self _ (hLpos _ (add_pos_of_pos_of_nonneg hu.1 hr)))
      (hV₀ u hu)).trans (mul_le_mul_of_nonneg_left (hVb u hu) (hLpos _ hu.1))
  have hp : Integrable (Function.uncurry q) (ν.prod η) := by
    refine (integrable_prod_iff hq.aestronglyMeasurable).2 ⟨?_, ho⟩
    exact (ae_restrict_mem measurableSet_Ioc).mono fun u hu => (hInt u hu).1
  refine ⟨hp, ?_⟩
  change (∫ s, ∫ u, q u s ∂ν ∂η) =
    ∫ u, (fractionalL α u - fractionalL α (u + r)) * V u ∂ν
  rw [← integral_integral_swap hp]
  exact integral_congr_ae ((ae_restrict_mem measurableSet_Ioc).mono fun u hu => (hInt u hu).2)

end RoughHeston

#print axioms RoughHeston.hasDerivAt_fractionalL
#print axioms RoughHeston.integral_fractionalHistoryDensity_shift
#print axioms RoughHeston.fractional_history_input_splitting
