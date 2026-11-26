/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from MathFin/Probability/Brownian/Ito/ItoIntegralCLM.lean
at commit cbe842dda1e71fd7173f3325971796686dbf7feb.
-/
import JointItoAssembly
import CommonDriverLimit
import MathFin.Probability.Brownian.Ito.ItoIntegralCLM

open MeasureTheory ProbabilityTheory Filter Set
open scoped MeasureTheory ProbabilityTheory NNReal ENNReal

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω}
variable (𝒢 : Filtration ℝ≥0 m) (μ : Measure Ω) [IsFiniteMeasure μ]
variable {t T : ℝ≥0}

/-- The band supporting the smaller predictable measure is predictably measurable. -/
lemma measurableSet_joint_timeBand (t : ℝ≥0) :
    MeasurableSet[𝒢.predictable] (Ioc (0 : ℝ≥0) t ×ˢ (univ : Set Ω)) :=
  measurableSet_predictable_Ioc_prod (𝓕 := 𝒢) 0 t MeasurableSet.univ

/-- Writing the horizon as a restriction of the locally finite predictable measure. -/
lemma jointPredictableMeasure_eq_restrict_full (t : ℝ≥0) :
    jointPredictableMeasure 𝒢 μ t =
      ((MathFin.ItoIntegralL2.timeMeasure.prod μ).trim 𝒢.predictable_le_prod).restrict
        (Ioc (0 : ℝ≥0) t ×ˢ (univ : Set Ω)) := by
  unfold jointPredictableMeasure MathFin.ItoIntegralCLM.timeMeasureHorizon
  rw [Measure.restrict_prod_eq_prod_univ,
    ← restrict_trim 𝒢.predictable_le_prod _ (measurableSet_joint_timeBand 𝒢 t)]

/-- The smaller joint predictable measure is the restriction of the larger one. -/
theorem jointPredictableMeasure_eq_restrict (ht : t ≤ T) :
    jointPredictableMeasure 𝒢 μ t =
      (jointPredictableMeasure 𝒢 μ T).restrict (Ioc (0 : ℝ≥0) t ×ˢ (univ : Set Ω)) := by
  rw [jointPredictableMeasure_eq_restrict_full, jointPredictableMeasure_eq_restrict_full,
    Measure.restrict_restrict (measurableSet_joint_timeBand 𝒢 t),
    inter_eq_left.mpr (prod_mono (Ioc_subset_Ioc_right ht) (Subset.refl _))]

/-- Extension by zero preserves a.e. equality on the smaller horizon. -/
lemma joint_timeBand_indicator_ae_eq (ht : t ≤ T) {f g : ℝ≥0 × Ω → ℝ}
    (h : f =ᵐ[jointPredictableMeasure 𝒢 μ t] g) :
    (Ioc (0 : ℝ≥0) t ×ˢ (univ : Set Ω)).indicator f
      =ᵐ[jointPredictableMeasure 𝒢 μ T]
    (Ioc (0 : ℝ≥0) t ×ˢ (univ : Set Ω)).indicator g := by
  rw [jointPredictableMeasure_eq_restrict 𝒢 μ ht] at h
  filter_upwards [(ae_restrict_iff' (measurableSet_joint_timeBand 𝒢 t)).1 h] with z hz
  by_cases hzBand : z ∈ Ioc (0 : ℝ≥0) t ×ˢ (univ : Set Ω)
  · rw [indicator_of_mem hzBand, indicator_of_mem hzBand, hz hzBand]
  · rw [indicator_of_notMem hzBand, indicator_of_notMem hzBand]

/-- Extension by zero takes the smaller predictable L² space into the larger one. -/
lemma joint_timeBand_indicator_memLp (ht : t ≤ T) {f : ℝ≥0 × Ω → ℝ}
    (hf : MemLp f 2 (jointPredictableMeasure 𝒢 μ t)) :
    MemLp ((Ioc (0 : ℝ≥0) t ×ˢ (univ : Set Ω)).indicator f) 2
      (jointPredictableMeasure 𝒢 μ T) :=
  (memLp_indicator_iff_restrict (measurableSet_joint_timeBand 𝒢 t).nullMeasurableSet).2
    (by rw [← jointPredictableMeasure_eq_restrict 𝒢 μ ht]; exact hf)

/-- Linear isometric extension by zero for the joint predictable L² spaces. -/
noncomputable def jointBandExtend (ht : t ≤ T) :
    Lp ℝ 2 (jointPredictableMeasure 𝒢 μ t) →ₗᵢ[ℝ]
      Lp ℝ 2 (jointPredictableMeasure 𝒢 μ T) where
  toFun φ := (joint_timeBand_indicator_memLp 𝒢 μ ht (Lp.memLp φ)).toLp _
  map_add' φ ψ := by
    let hφ := joint_timeBand_indicator_memLp 𝒢 μ ht (Lp.memLp φ)
    let hψ := joint_timeBand_indicator_memLp 𝒢 μ ht (Lp.memLp ψ)
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp (joint_timeBand_indicator_memLp 𝒢 μ ht (Lp.memLp (φ + ψ))),
      Lp.coeFn_add (hφ.toLp _) (hψ.toLp _), MemLp.coeFn_toLp hφ, MemLp.coeFn_toLp hψ,
      joint_timeBand_indicator_ae_eq 𝒢 μ ht (Lp.coeFn_add φ ψ)] with z h1 h2 h3 h4 h5
    simp only [h1, h2, h3, h4, h5, Pi.add_apply, Set.indicator_add']
  map_smul' c φ := by
    let hφ := joint_timeBand_indicator_memLp 𝒢 μ ht (Lp.memLp φ)
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp (joint_timeBand_indicator_memLp 𝒢 μ ht (Lp.memLp (c • φ))),
      Lp.coeFn_smul c (hφ.toLp _), MemLp.coeFn_toLp hφ,
      joint_timeBand_indicator_ae_eq 𝒢 μ ht (Lp.coeFn_smul c φ)] with z h1 h2 h3 h4
    simp only [h1, h2, h3, h4, Pi.smul_apply, RingHom.id_apply]
    by_cases hz : z ∈ Ioc (0 : ℝ≥0) t ×ˢ (univ : Set Ω)
    · rw [indicator_of_mem hz, indicator_of_mem hz, Pi.smul_apply]
    · rw [indicator_of_notMem hz, indicator_of_notMem hz, smul_zero]
  norm_map' φ := by
    rw [LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp, Lp.norm_def,
      eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_joint_timeBand 𝒢 t).nullMeasurableSet,
      ← jointPredictableMeasure_eq_restrict 𝒢 μ ht]

lemma jointBandExtend_coeFn (ht : t ≤ T)
    (φ : Lp ℝ 2 (jointPredictableMeasure 𝒢 μ t)) :
    ⇑(jointBandExtend 𝒢 μ ht φ) =ᵐ[jointPredictableMeasure 𝒢 μ T]
      (Ioc (0 : ℝ≥0) t ×ˢ (univ : Set Ω)).indicator ⇑φ :=
  MemLp.coeFn_toLp (joint_timeBand_indicator_memLp 𝒢 μ ht (Lp.memLp φ))

/-- The horizon measure charges only positive times up to the horizon. -/
lemma ae_mem_joint_timeBand (T : ℝ≥0) :
    ∀ᵐ z ∂jointPredictableMeasure 𝒢 μ T, z ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) := by
  rw [jointPredictableMeasure_eq_restrict_full]
  exact ae_restrict_mem (measurableSet_joint_timeBand 𝒢 T)

/-- If `g` vanishes past the smaller horizon, extension retains the same representative. -/
lemma jointBandExtend_toLp_ae_eq (ht : t ≤ T) {g : ℝ≥0 × Ω → ℝ}
    (hg0 : ∀ z : ℝ≥0 × Ω, t < z.1 → g z = 0)
    (hg : MemLp g 2 (jointPredictableMeasure 𝒢 μ t)) :
    ⇑(jointBandExtend 𝒢 μ ht (hg.toLp g)) =ᵐ[jointPredictableMeasure 𝒢 μ T] g := by
  filter_upwards [jointBandExtend_coeFn 𝒢 μ ht (hg.toLp g),
    joint_timeBand_indicator_ae_eq 𝒢 μ ht hg.coeFn_toLp,
    ae_mem_joint_timeBand 𝒢 μ T] with z h1 h2 hz
  rw [h1, h2]
  by_cases hzt : z.1 ≤ t
  · have hband : z ∈ Ioc (0 : ℝ≥0) t ×ˢ (univ : Set Ω) := ⟨⟨hz.1.1, hzt⟩, mem_univ _⟩
    exact indicator_of_mem hband _
  · have hband : z ∉ Ioc (0 : ℝ≥0) t ×ˢ (univ : Set Ω) := fun h => hzt h.1.2
    rw [indicator_of_notMem hband, hg0 z (lt_of_not_ge hzt)]

/-- Promote a simple process whose support ends by `t` to the larger horizon. -/
def jointTBoundedSP_inclusion (ht : t ≤ T) (V : JointTBoundedSP t 𝒢) :
    JointTBoundedSP T 𝒢 :=
  ⟨V.val, fun p hp => (V.property p hp).trans ht⟩

/-- A bounded simple process vanishes after the endpoint of its support. -/
lemma jointSimpleProcess_uncurry_zero_of_lt (V : JointTBoundedSP t 𝒢) (z : ℝ≥0 × Ω)
    (hz : t < z.1) : Function.uncurry ⇑V.val z = 0 := by
  rcases z with ⟨s, ω⟩
  change V.val s ω = 0
  rw [SimpleProcess.apply_eq]
  have hs0 : s ≠ (⊥ : ℝ≥0) := by
    intro h
    rw [h, NNReal.bot_eq_zero] at hz
    exact (not_lt_of_ge (show 0 ≤ t from zero_le)) hz
  have hbot : ({(⊥ : ℝ≥0)} : Set ℝ≥0).indicator
      (fun _ => V.val.valueBot ω) s = 0 := indicator_of_notMem (by simpa using hs0) _
  rw [hbot, zero_add, Finsupp.sum]
  refine Finset.sum_eq_zero fun p hp => indicator_of_notMem (fun hs => ?_) _
  exact (not_le_of_gt ((V.property p hp).trans_lt hz)) hs.2

/-- Extension commutes with the predictable `L²` classes of simple processes. -/
theorem jointBandExtend_simpleAssembly (ht : t ≤ T) (V : JointTBoundedSP t 𝒢) :
    jointBandExtend 𝒢 μ ht (jointSimpleAssembly (μ := μ) t 𝒢 V) =
      jointSimpleAssembly (μ := μ) T 𝒢 (jointTBoundedSP_inclusion 𝒢 ht V) := by
  let g := Function.uncurry ⇑V.val
  have hg : MemLp g 2 (jointPredictableMeasure 𝒢 μ t) := simpleProcessUncurry_memLp_joint t V.val
  have heq : jointSimpleAssembly (μ := μ) t 𝒢 V = hg.toLp g :=
    Lp.ext ((jointSimpleAssembly_ae V).trans hg.coeFn_toLp.symm)
  rw [heq]
  exact Lp.ext ((jointBandExtend_toLp_ae_eq 𝒢 μ ht
    (jointSimpleProcess_uncurry_zero_of_lt 𝒢 V) hg).trans
      (jointSimpleAssembly_ae (jointTBoundedSP_inclusion 𝒢 ht V)).symm)

/-- Terminal integration over the smaller horizon agrees with integration of the
zero extension over the larger horizon. The shorter driver is the stopped martingale. -/
theorem jointItoIntegralCLM_cross_horizon {M : ℝ≥0 → Ω → ℝ} (ht : t ≤ T)
    (hM₂ : ∀ s, MemLp (M s) 2 μ) (hM : Martingale M 𝒢 μ)
    (hclock : Martingale (fun s ω => M s ω ^ 2 - ((min s T : ℝ≥0) : ℝ)) 𝒢 μ)
    (φ : Lp ℝ 2 (jointPredictableMeasure 𝒢 μ t)) :
    jointItoIntegralCLM (M := fun s => M (min s t)) t (fun s => hM₂ (min s t)) φ =
      jointItoIntegralCLM T hM₂ (jointBandExtend 𝒢 μ ht φ) := by
  let hM₂t (s : ℝ≥0) := hM₂ (min s t)
  have hMt : Martingale (fun s => M (min s t)) 𝒢 μ := martingale_freeze_at hM t
  have hclock_t : Martingale (fun s ω => M (min s t) ω ^ 2 - ((min s t : ℝ≥0) : ℝ)) 𝒢 μ := by
    simpa only [min_assoc, min_eq_left ht] using martingale_freeze_at hclock t
  let F := jointItoIntegralCLM (𝒢 := 𝒢) t hM₂t
  let G := (jointItoIntegralCLM (𝒢 := 𝒢) T hM₂).comp (jointBandExtend 𝒢 μ ht).toContinuousLinearMap
  change F φ = G φ
  refine congrFun ((jointSimpleAssembly_denseRange (μ := μ) t 𝒢).equalizer
    F.continuous G.continuous ?_) φ
  funext V
  change jointItoIntegralCLM t hM₂t (jointSimpleAssembly t 𝒢 V) =
    jointItoIntegralCLM T hM₂ (jointBandExtend 𝒢 μ ht (jointSimpleAssembly t 𝒢 V))
  rw [jointBandExtend_simpleAssembly, jointItoIntegralCLM_agrees t hM₂t hMt hclock_t,
    jointItoIntegralCLM_agrees T hM₂ hM hclock]
  apply Lp.ext
  filter_upwards [(memLp_jointItoSimple hM₂t V.val).coeFn_toLp,
    (memLp_jointItoSimple hM₂ V.val).coeFn_toLp] with ω h₁ h₂
  change ((memLp_jointItoSimple hM₂t V.val).toLp (jointItoSimple _ V.val)) ω =
    ((memLp_jointItoSimple hM₂ V.val).toLp (jointItoSimple M V.val)) ω
  rw [h₁, h₂]
  simp only [jointItoSimple, Finsupp.sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp₂ := V.property p hp
  have hp₁ := (V.val.le_of_mem_support_value p hp).trans hp₂
  simp only [min_eq_left hp₁, min_eq_left hp₂]

end RoughHeston

#print axioms RoughHeston.jointPredictableMeasure_eq_restrict
#print axioms RoughHeston.jointBandExtend
#print axioms RoughHeston.jointBandExtend_coeFn

#print axioms RoughHeston.jointBandExtend_toLp_ae_eq
#print axioms RoughHeston.jointBandExtend_simpleAssembly
#print axioms RoughHeston.jointItoIntegralCLM_cross_horizon
