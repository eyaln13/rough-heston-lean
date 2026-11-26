import HistoryInputSplitting
import Mathlib.MeasureTheory.Measure.OpenPos

open MeasureTheory Filter Set
open scoped MeasureTheory Topology

namespace RoughHeston

private theorem fractionalL_nonnegative {α x : ℝ} (hα : α < 1) :
    0 ≤ fractionalL α x := by
  unfold fractionalL
  split
  · exact le_rfl
  · exact div_nonneg (Real.rpow_nonneg (le_of_lt (lt_of_not_ge ‹¬x ≤ 0›)) _)
      (Real.Gamma_pos_of_pos (sub_pos.mpr hα)).le

private theorem fractionalL_positive {α x : ℝ} (hα : α < 1) (hx : 0 < x) :
    0 < fractionalL α x := by
  rw [fractionalL, ite_eq_right (not_le_of_gt hx)]
  exact div_pos (Real.rpow_pos_of_pos hx _) (Real.Gamma_pos_of_pos (sub_pos.mpr hα))

/-- A nonnegative continuous cluster that has been positive at some
earlier interior time has a strictly positive inverse-kernel history. -/
theorem fractional_cluster_history_pos {α t s₀ : ℝ} {U : ℝ → ℝ}
    (hα : α < 1) (hs₀ : s₀ ∈ Ioo (0 : ℝ) t) (hU : Continuous U)
    (hU₀ : ∀ s ∈ Icc (0 : ℝ) t, 0 ≤ U s) (hpositive : 0 < U s₀) :
    0 < volterraConvolution (fractionalL α) U t := by
  let g (s : ℝ) := fractionalL α (t - s) * U s
  let ν := volume.restrict (Ioc (0 : ℝ) t)
  have hg : Measurable g :=
    ((fractionalL_measurable α).comp (measurable_const.sub measurable_id)).mul hU.measurable
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn hU.continuousOn
  have hi : IntegrableOn (fun s => fractionalL α (t - s)) (Ioc 0 t) :=
    fractionalL_reflected_integrableOn_Ioc hα (hs₀.1.trans hs₀.2).le
  have hgi : Integrable g ν := by
    refine (hi.mul_const C).mono' hg.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have h0 := fractionalL_nonnegative (x := t - s) hα
    change ‖fractionalL α (t - s) * U s‖ ≤ fractionalL α (t - s) * C
    rw [norm_mul, Real.norm_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left (hC _ ⟨hs.1.le, hs.2⟩) h0
  have hgn : 0 ≤ᵐ[ν] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact mul_nonneg (fractionalL_nonnegative hα) (hU₀ s ⟨hs.1.le, hs.2⟩)
  have hgpos : 0 < g s₀ :=
    mul_pos (fractionalL_positive hα (sub_pos.mpr hs₀.2)) hpositive
  have hgc : ContinuousAt g s₀ :=
    ((hasDerivAt_fractionalL (α := α) (sub_pos.mpr hs₀.2)).continuousAt.comp
      (continuous_const.sub continuous_id).continuousAt).mul hU.continuousAt
  have hset : {s : ℝ | 0 < g s} ∩ Ioo (0 : ℝ) t ∈ 𝓝 s₀ :=
    inter_mem (hgc.tendsto (Ioi_mem_nhds hgpos)) (Ioo_mem_nhds hs₀.1 hs₀.2)
  have hmeas : MeasurableSet (Function.support g) := hg.stronglyMeasurable.measurableSet_support
  have hmass : 0 < ν (Function.support g) := by
    rw [Measure.restrict_apply hmeas]
    refine (volume.measure_pos_of_mem_nhds hset).trans_le (measure_mono ?_)
    intro s hs
    exact ⟨ne_of_gt hs.1, Ioo_subset_Ioc_self hs.2⟩
  exact (integral_pos_iff_support_of_nonneg_ae hgn hgi).2 hmass

/-- The biased mass cannot vanish during the pulse or at a later time
once the cluster has a positive pre-pulse-end contribution. -/
theorem pulsed_cluster_mass_pos {α κ ε d r : ℝ} {U A : ℝ → ℝ}
    (hα : α < 1) (hκ : 0 ≤ κ)
    (hU : Continuous U) (hU₀ : ∀ s ∈ Icc (0 : ℝ) r, 0 ≤ U s)
    (hA : ∀ s ∈ Icc (0 : ℝ) r, A s ≤ ε) (hAearly : ∀ s ∈ Ico (0 : ℝ) d, A s < ε)
    (hpos : ∃ s ∈ Ioo (0 : ℝ) d, 0 < U s) :
    ∀ t ∈ Icc (0 : ℝ) r,
      0 < ε - A t + volterraConvolution (fractionalL α) U t +
        κ * ∫ s in Ioc (0 : ℝ) t, U s := by
  intro t ht
  have hD : 0 ≤ ∫ s in Ioc (0 : ℝ) t, U s :=
    setIntegral_nonneg measurableSet_Ioc fun s hs => hU₀ s ⟨hs.1.le, hs.2.trans ht.2⟩
  by_cases ht' : t < d
  · have hL : 0 ≤ volterraConvolution (fractionalL α) U t := by
      apply setIntegral_nonneg measurableSet_Ioc
      intro s hs
      exact mul_nonneg (fractionalL_nonnegative hα) (hU₀ s ⟨hs.1.le, hs.2.trans ht.2⟩)
    exact add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg (sub_pos.mpr (hAearly t ⟨ht.1, ht'⟩)) hL)
      (mul_nonneg hκ hD)
  · obtain ⟨s₀, hs₀, hs⟩ := hpos
    have hL : 0 < volterraConvolution (fractionalL α) U t :=
      fractional_cluster_history_pos hα ⟨hs₀.1, hs₀.2.trans_le (le_of_not_gt ht')⟩ hU
        (fun s hs' => hU₀ s ⟨hs'.1, hs'.2.trans ht.2⟩) hs
    exact add_pos_of_pos_of_nonneg
      (add_pos_of_nonneg_of_pos (sub_nonneg.mpr (hA t ht)) hL) (mul_nonneg hκ hD)

end RoughHeston

#print axioms RoughHeston.fractional_cluster_history_pos
#print axioms RoughHeston.pulsed_cluster_mass_pos
