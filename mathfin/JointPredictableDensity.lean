/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from MathFin/Probability/Brownian/Ito/ItoIntegralHorizonDense.lean
at commit cbe842dda1e71fd7173f3325971796686dbf7feb.
The rectangle generator proof is generalized to an arbitrary filtration.
The density proof uses indicatorConstLp and an abstract support condition.
-/
import MathFin.Probability.Brownian.Ito.ItoIntegralHorizonDense

open MeasureTheory Filter Set
open scoped MeasureTheory ProbabilityTheory NNReal ENNReal InnerProductSpace

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω}

private theorem generateFrom_predictableRectangles (𝒢 : Filtration ℝ≥0 m) :
    MeasurableSpace.generateFrom 𝒢.predictableRectangles = 𝒢.predictable := by
  apply le_antisymm
  · -- ≤: every basic rectangle is predictable-measurable
    apply MeasurableSpace.generateFrom_le
    rintro S (⟨F₀, hF₀, rfl⟩ | ⟨a, b, _hab, F, hF, rfl⟩)
    · -- `{0} ×ˢ F₀ = {⊥} ×ˢ F₀` (`(⊥ : ℝ≥0) = 0` by `rfl`)
      exact MeasureTheory.measurableSet_predictable_singleton_bot_prod (𝓕 := 𝒢) hF₀
    · exact MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := 𝒢) a b hF
  · -- ≥: the predictable σ-algebra is contained in `generateFrom predictableRect`
    apply MeasureTheory.measurableSpace_le_predictable_of_measurableSet
    -- Bot generator `{⊥} ×ˢ A`: directly a basic rectangle (`⊥ = 0`)
    · intro A hA
      exact MeasurableSpace.measurableSet_generateFrom
        (MeasureTheory.Filtration.singletonBot_prod_mem_predictableRectangles _ hA)
    -- Ioi generator `Ioi i ×ˢ A`: write as countable union of `Ioc i (seq n) ×ˢ A`
    · intro i A hA
      obtain ⟨seq, _hmono, htends⟩ :=
        Filter.exists_seq_monotone_tendsto_atTop_atTop ℝ≥0
      have h_Ioi : (Set.Ioi i : Set ℝ≥0) = ⋃ n : ℕ, Set.Ioc i (seq n) := by
        ext s
        simp only [Set.mem_Ioi, Set.mem_iUnion, Set.mem_Ioc]
        refine ⟨fun his ↦ ?_, fun ⟨_, h, _⟩ ↦ h⟩
        rw [Filter.tendsto_atTop_atTop] at htends
        obtain ⟨n, hn⟩ := htends s
        exact ⟨n, his, hn n le_rfl⟩
      rw [h_Ioi, Set.iUnion_prod_const]
      exact MeasurableSet.iUnion fun n ↦ MeasurableSpace.measurableSet_generateFrom
        (MeasureTheory.Filtration.Ioc_prod_mem_predictableRectangles _ i (seq n) hA)


/-- The (L²) indicator of an adapted rectangle. -/
noncomputable def jointRectangleLp {𝒢 : Filtration ℝ≥0 m}
    (ν : @Measure (ℝ≥0 × Ω) 𝒢.predictable) [IsFiniteMeasure ν]
    {a : ℝ≥0} (b : ℝ≥0) {A : Set Ω} (hA : MeasurableSet[𝒢 a] A) : Lp ℝ 2 ν :=
  indicatorConstLp 2 (measurableSet_predictable_Ioc_prod (𝓕 := 𝒢) a b hA)
    (measure_ne_top ν _) (1 : ℝ)

/-- Indicators with right endpoint at most the horizon. -/
def jointRectangleIndicators {𝒢 : Filtration ℝ≥0 m}
    (ν : @Measure (ℝ≥0 × Ω) 𝒢.predictable) [IsFiniteMeasure ν] (T : ℝ≥0) :
    Set (Lp ℝ 2 ν) :=
  {f | ∃ (a b : ℝ≥0), a ≤ b ∧ b ≤ T ∧
      ∃ (A : Set Ω) (hA : MeasurableSet[𝒢 a] A), f = jointRectangleLp ν b hA}

/-- Adapted rectangles up to the horizon span a dense subspace in
predictable (L²) for any finite measure supported on ((0,T]). -/
theorem dense_span_jointRectangleIndicators {𝒢 : Filtration ℝ≥0 m}
    (ν : @Measure (ℝ≥0 × Ω) 𝒢.predictable) [IsFiniteMeasure ν] (T : ℝ≥0)
    (hsupp : ∀ᵐ z ∂ν, z.1 ∈ Ioc (0 : ℝ≥0) T) :
    Dense (Submodule.span ℝ (jointRectangleIndicators ν T) : Set (Lp ℝ 2 ν)) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := 𝒢.predictable
  suffices horth : (Submodule.span ℝ (jointRectangleIndicators ν T))ᗮ = ⊥ from
    Submodule.dense_iff_topologicalClosure_eq_top.2
      (Submodule.topologicalClosure_eq_top_iff.2 horth)
  rw [Submodule.eq_bot_iff]
  intro g hg
  rw [Submodule.mem_orthogonal] at hg
  let S := Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)
  have hclip (R : Set (ℝ≥0 × Ω)) : ∫ z in R, g z ∂ν = ∫ z in R ∩ S, g z ∂ν := by
    apply setIntegral_congr_set
    filter_upwards [hsupp] with z hz
    simp [S, hz]
  have hrect {a b : ℝ≥0} (hab : a ≤ b) (hbT : b ≤ T) {A : Set Ω}
      (hA : MeasurableSet[𝒢 a] A) : ∫ z in Ioc a b ×ˢ A, g z ∂ν = 0 := by
    rw [← L2.inner_indicatorConstLp_one
      (measurableSet_predictable_Ioc_prod (𝓕 := 𝒢) a b hA) (measure_ne_top ν _) g]
    exact hg (jointRectangleLp ν b hA)
      (Submodule.subset_span ⟨a, b, hab, hbT, A, hA, rfl⟩)
  have hgen : ∀ R ∈ 𝒢.predictableRectangles, ∫ z in R, g z ∂ν = 0 := by
    rintro R (⟨A, hA, rfl⟩ | ⟨a, b, _, A, hA, rfl⟩)
    · rw [hclip]
      have he : ({(⊥ : ℝ≥0)} ×ˢ A) ∩ S = ∅ := by
        unfold S
        rw [prod_inter_prod,
          show ({(⊥ : ℝ≥0)} ∩ Ioc 0 T : Set ℝ≥0) = ∅ by ext z; simp, empty_prod]
      rw [he, setIntegral_empty]
    · rw [hclip]
      have he : (Ioc a b ×ˢ A) ∩ S = Ioc a (min b T) ×ˢ A := by
        unfold S
        rw [prod_inter_prod, Ioc_inter_Ioc, inter_univ, max_eq_left (show 0 ≤ a from zero_le)]
      rw [he]
      by_cases hab : a ≤ min b T
      · exact hrect hab (min_le_right _ _) hA
      · rw [Ioc_eq_empty (by exact fun h => hab h.le), empty_prod, setIntegral_empty]
  have htotal : ∫ z, g z ∂ν = 0 := by
    rw [← setIntegral_univ, hclip, univ_inter]
    exact hrect (show 0 ≤ T from zero_le) le_rfl MeasurableSet.univ
  have hgint : Integrable (fun z => g z) ν := (Lp.memLp g).integrable one_le_two
  have hall (R : Set (ℝ≥0 × Ω)) (hR : MeasurableSet R) : ∫ z in R, g z ∂ν = 0 := by
    refine MeasurableSpace.induction_on_inter
      (C := fun R _ => ∫ z in R, g z ∂ν = 0)
      (h_eq := (generateFrom_predictableRectangles 𝒢).symm)
      (h_inter := (Filtration.isSetSemiring_predictableRectangles 𝒢).isPiSystem)
      (empty := setIntegral_empty)
      (basic := hgen) (compl := ?_) (iUnion := ?_) R hR
    · intro R hR hz
      have he := integral_add_compl (μ := ν) (f := fun z => g z) hR hgint
      linarith
    · intro f hf hfm hf_zero
      rw [integral_iUnion hfm hf hgint.integrableOn]
      simp [hf_zero]
  refine (Lp.eq_zero_iff_ae_eq_zero (f := g)).mpr ?_
  exact Lp.ae_eq_zero_of_forall_setIntegral_eq_zero g
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    (fun _ _ _ => hgint.integrableOn) (fun s hs _ => hall s hs)

/-- The horizon product measure on the predictable σ-algebra of the
supplied filtration. -/
noncomputable def jointPredictableMeasure (𝒢 : Filtration ℝ≥0 m)
    (μ : Measure Ω) (T : ℝ≥0) : @Measure (ℝ≥0 × Ω) 𝒢.predictable :=
  ((MathFin.ItoIntegralCLM.timeMeasureHorizon T).prod μ).trim 𝒢.predictable_le_prod

instance (𝒢 : Filtration ℝ≥0 m) (μ : Measure Ω) [IsFiniteMeasure μ] (T : ℝ≥0) :
    IsFiniteMeasure (jointPredictableMeasure 𝒢 μ T) := by
  unfold jointPredictableMeasure
  infer_instance

/-- Density for the predictable (L²) space of a finite time horizon
with respect to the joint product measure. -/
theorem dense_span_jointPredictableMeasure (𝒢 : Filtration ℝ≥0 m)
    (μ : Measure Ω) [IsFiniteMeasure μ] (T : ℝ≥0) :
    Dense (Submodule.span ℝ (jointRectangleIndicators (jointPredictableMeasure 𝒢 μ T) T) :
      Set (Lp ℝ 2 (jointPredictableMeasure 𝒢 μ T))) := by
  apply dense_span_jointRectangleIndicators
  let I := Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)
  have hI : MeasurableSet[𝒢.predictable] I :=
    measurableSet_predictable_Ioc_prod 0 T MeasurableSet.univ
  have hm : jointPredictableMeasure 𝒢 μ T Iᶜ = 0 := by
    unfold jointPredictableMeasure MathFin.ItoIntegralCLM.timeMeasureHorizon
    rw [trim_measurableSet_eq 𝒢.predictable_le_prod hI.compl,
      Measure.restrict_prod_eq_prod_univ,
      Measure.restrict_apply (𝒢.predictable_le_prod _ hI.compl)]
    change (MathFin.ItoIntegralL2.timeMeasure.prod μ) (Iᶜ ∩ I) = 0
    rw [compl_inter_self, measure_empty]
  filter_upwards [ae_iff.mpr hm] with z hz
  exact hz.1

end RoughHeston

#print axioms RoughHeston.dense_span_jointRectangleIndicators
#print axioms RoughHeston.dense_span_jointPredictableMeasure
