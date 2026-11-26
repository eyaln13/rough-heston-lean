/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from MathFin/Probability/Brownian/Ito/ItoIntegralHorizonDense.lean
at commit cbe842dda1e71fd7173f3325971796686dbf7feb.
The submodule and linear embedding use an arbitrary filtration.
-/
import JointPredictableDensity

open MeasureTheory ProbabilityTheory Filter Set
open scoped MeasureTheory ProbabilityTheory NNReal ENNReal

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℝ≥0 m}

/-- Simple processes whose interval endpoints stay within the horizon. -/
def JointTBoundedSP (T : ℝ≥0) (𝒢 : Filtration ℝ≥0 m) :
    Submodule ℝ (SimpleProcess ℝ 𝒢) where
  carrier := { V | ∀ p ∈ V.value.support, p.2 ≤ T }
  add_mem' {V W} hV hW p hp := by
    rcases Finset.mem_union.mp (Finsupp.support_add hp) with h | h
    · exact hV p h
    · exact hW p h
  zero_mem' p hp := absurd hp (by simp)
  smul_mem' c V hV p hp := hV p (Finsupp.support_smul hp)

/-- Bounded simple processes are square-integrable on the finite horizon. -/
theorem simpleProcessUncurry_memLp_joint [IsFiniteMeasure μ] (T : ℝ≥0)
    (V : SimpleProcess ℝ 𝒢) :
    MemLp (Function.uncurry ⇑V) 2 (jointPredictableMeasure 𝒢 μ T) := by
  obtain ⟨C, hC⟩ := V.coe_bounded
  exact MemLp.of_bound V.isStronglyPredictable.aestronglyMeasurable C
    (Eventually.of_forall fun z ↦ hC z.1 z.2)

private noncomputable def jointSimpleProcessLp [IsFiniteMeasure μ] (T : ℝ≥0)
    (V : SimpleProcess ℝ 𝒢) : Lp ℝ 2 (jointPredictableMeasure 𝒢 μ T) :=
  (simpleProcessUncurry_memLp_joint T V).toLp (Function.uncurry ⇑V)

/-- The linear map assigning each simple process its predictable L² class. -/
noncomputable def jointSimpleAssembly [IsFiniteMeasure μ] (T : ℝ≥0)
    (𝒢 : Filtration ℝ≥0 m) : JointTBoundedSP T 𝒢 →ₗ[ℝ] Lp ℝ 2 (jointPredictableMeasure 𝒢 μ T) where
  toFun V := jointSimpleProcessLp T V.val
  map_add' V W := by
    change jointSimpleProcessLp T ((V + W).val) = _
    rw [Submodule.coe_add, jointSimpleProcessLp, jointSimpleProcessLp, jointSimpleProcessLp,
      ← MemLp.toLp_add (simpleProcessUncurry_memLp_joint T V.val)
        (simpleProcessUncurry_memLp_joint T W.val)]
    congr 1
    funext ⟨t, ω⟩
    simp [Function.uncurry]
  map_smul' c V := by
    change jointSimpleProcessLp T ((c • V).val) = _
    rw [Submodule.coe_smul, jointSimpleProcessLp, jointSimpleProcessLp, RingHom.id_apply,
      ← MemLp.toLp_const_smul c (simpleProcessUncurry_memLp_joint T V.val)]
    congr 1
    funext ⟨t, ω⟩
    simp [Function.uncurry]

/-- The assembled integrand and the original simple process agree almost everywhere. -/
theorem jointSimpleAssembly_ae [IsFiniteMeasure μ] {T : ℝ≥0}
    (V : JointTBoundedSP T 𝒢) :
    (jointSimpleAssembly (μ := μ) T 𝒢 V : ℝ≥0 × Ω → ℝ)
      =ᵐ[jointPredictableMeasure 𝒢 μ T] Function.uncurry ⇑V.val :=
  MemLp.coeFn_toLp (simpleProcessUncurry_memLp_joint T V.val)

/-- The rectangle indicator as an adapted simple process bounded by the horizon. -/
noncomputable def jointRectangleSP {T a b : ℝ≥0} (hab : a ≤ b) (hbT : b ≤ T)
    {A : Set Ω} (hA : MeasurableSet[𝒢 a] A) : JointTBoundedSP T 𝒢 :=
  ⟨(ElementaryPredictableSet.IocProd a b hA).indicator (1 : ℝ), fun p hp ↦ by
    have h_I_eq : (ElementaryPredictableSet.IocProd a b hA).I = {(a, b)} := by
      change (if a ≤ b then ({(a, b)} : Finset _) else ∅) = _
      rw [ite_eq_left hab]
    have h_in_I : p ∈ (ElementaryPredictableSet.IocProd a b hA).I := by
      by_contra hp_not
      apply Finsupp.mem_support_iff.mp hp
      change ((ElementaryPredictableSet.IocProd a b hA).indicator 1).value p = 0
      simp [ElementaryPredictableSet.indicator, Finsupp.onFinset_apply, hp_not]
    rw [h_I_eq, Finset.mem_singleton] at h_in_I
    rcases h_in_I with rfl
    exact hbT⟩

/-- The assembled rectangle is the same L² indicator used in the density theorem. -/
theorem jointSimpleAssembly_rectangle [IsFiniteMeasure μ] {T a b : ℝ≥0}
    (hab : a ≤ b) (hbT : b ≤ T) {A : Set Ω} (hA : MeasurableSet[𝒢 a] A) :
    jointSimpleAssembly (μ := μ) T 𝒢 (jointRectangleSP hab hbT hA)
      = jointRectangleLp (jointPredictableMeasure 𝒢 μ T) b hA := by
  apply Lp.ext
  have hInd : ⇑(jointRectangleLp (jointPredictableMeasure 𝒢 μ T) b hA)
      =ᵐ[jointPredictableMeasure 𝒢 μ T] (Ioc a b ×ˢ A).indicator (fun _ ↦ (1 : ℝ)) :=
    indicatorConstLp_coeFn
  refine (jointSimpleAssembly_ae (jointRectangleSP hab hbT hA)).trans ?_
  refine (EventuallyEq.of_eq ?_).trans hInd.symm
  funext ⟨t, ω⟩
  change ⇑((ElementaryPredictableSet.IocProd a b hA).indicator (1 : ℝ)) t ω
      = (Ioc a b ×ˢ A).indicator (fun _ ↦ (1 : ℝ)) (t, ω)
  rw [ElementaryPredictableSet.coe_indicator, ElementaryPredictableSet.coe_IocProd a b hA]
  rfl

/-- Horizon-bounded adapted simple processes are dense in the joint predictable L² space. -/
theorem jointSimpleAssembly_denseRange [IsFiniteMeasure μ] (T : ℝ≥0)
    (𝒢 : Filtration ℝ≥0 m) : DenseRange (jointSimpleAssembly (μ := μ) T 𝒢) :=
  (dense_span_jointPredictableMeasure 𝒢 μ T).mono fun _ hf ↦ LinearMap.mem_range.1 <|
    Submodule.span_le.2 (by
      rintro _ ⟨_, _, hab, hbT, _, hA, rfl⟩
      exact ⟨jointRectangleSP hab hbT hA, jointSimpleAssembly_rectangle hab hbT hA⟩) hf

end RoughHeston

#print axioms RoughHeston.jointSimpleAssembly
#print axioms RoughHeston.jointSimpleAssembly_rectangle
#print axioms RoughHeston.jointSimpleAssembly_denseRange
