/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from MathFin/Probability/Brownian/Ito/ItoIntegralL2.lean
at commit cbe842dda1e71fd7173f3325971796686dbf7feb.
The norm calculation uses the supplied filtration and restricted time measure.
-/
import JointSimpleAssembly

open MeasureTheory ProbabilityTheory Filter Set
open MathFin.ItoIntegralL2 MathFin.ItoIntegralCLM
open scoped MeasureTheory ProbabilityTheory NNReal ENNReal

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℝ≥0 m}

private noncomputable def jointRectTerm (V : SimpleProcess ℝ 𝒢) (p : ℝ≥0 × ℝ≥0) :
    ℝ≥0 × Ω → ℝ :=
  elemIntegrand p.1 p.2 (V.value p)

private theorem jointRectTerm_memLp [IsFiniteMeasure μ] (T : ℝ≥0)
    (V : SimpleProcess ℝ 𝒢) (p : ℝ≥0 × ℝ≥0) :
    MemLp (jointRectTerm V p) 2 ((timeMeasureHorizon T).prod μ) := by
  have heq : jointRectTerm V p =
      (Ioc p.1 p.2 ×ˢ (univ : Set Ω)).indicator (fun z ↦ V.value p z.2) := by
    funext z
    rw [jointRectTerm, elemIntegrand, indicator_apply, indicator_apply]
    simp only [mem_prod, mem_univ, and_true]
    split_ifs <;> simp
  rw [heq]
  have hm : Measurable (fun z : ℝ≥0 × Ω ↦ V.value p z.2) :=
    ((V.measurable_value p).mono (𝒢.le p.1) le_rfl).comp measurable_snd
  have hbase : MemLp (fun z : ℝ≥0 × Ω ↦ V.value p z.2) 2 ((timeMeasureHorizon T).prod μ) :=
    MemLp.of_bound hm.aestronglyMeasurable V.valueBound
      (Eventually.of_forall fun z ↦ by rw [Real.norm_eq_abs]; exact V.value_le_valueBound p z.2)
  exact hbase.indicator (measurableSet_Ioc.prod MeasurableSet.univ).nullMeasurableSet

private theorem uncurry_ae_eq_sum_jointRectTerm [IsFiniteMeasure μ] (T : ℝ≥0)
    (V : SimpleProcess ℝ 𝒢) :
    Function.uncurry ⇑V =ᵐ[(timeMeasureHorizon T).prod μ]
      fun z ↦ ∑ p ∈ V.value.support, jointRectTerm V p z := by
  have hν : ∀ᵐ z ∂(timeMeasureHorizon T).prod μ, z.1 ≠ 0 :=
    (ae_fst_ne_zero_prod μ).filter_mono
      (ae_mono (Measure.prod_mono Measure.restrict_le_self le_rfl))
  filter_upwards [hν] with z hz
  change ⇑V z.1 z.2 = _
  rw [SimpleProcess.apply_eq, indicator_of_notMem (by simpa using hz), zero_add, Finsupp.sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [jointRectTerm, elemIntegrand, indicator_apply, indicator_apply]
  split_ifs <;> simp

private theorem integral_jointRectTerm_mul [IsFiniteMeasure μ] {T : ℝ≥0}
    (V : SimpleProcess ℝ 𝒢) {p q : ℝ≥0 × ℝ≥0} (hpT : p.2 ≤ T) :
    ∫ z, jointRectTerm V p z * jointRectTerm V q z ∂((timeMeasureHorizon T).prod μ)
      = (∫ ω, V.value p ω * V.value q ω ∂μ)
          * max 0 ((min (p.2 : ℝ) q.2) - (max (p.1 : ℝ) q.1)) := by
  have hfun : (fun z : ℝ≥0 × Ω ↦ jointRectTerm V p z * jointRectTerm V q z)
      = fun z ↦ ((Ioc p.1 p.2).indicator (fun _ ↦ (1 : ℝ)) z.1
                    * (Ioc q.1 q.2).indicator (fun _ ↦ (1 : ℝ)) z.1)
                  * (V.value p z.2 * V.value q z.2) := by
    funext z
    simp only [jointRectTerm, elemIntegrand]
    ring
  rw [hfun, integral_prod_mul
        (fun i ↦ (Ioc p.1 p.2).indicator (fun _ ↦ (1 : ℝ)) i
          * (Ioc q.1 q.2).indicator (fun _ ↦ (1 : ℝ)) i)
        (fun ω ↦ V.value p ω * V.value q ω), mul_comm]
  congr 1
  have hpt : ∀ i : ℝ≥0, (Ioc p.1 p.2).indicator (fun _ ↦ (1 : ℝ)) i
        * (Ioc q.1 q.2).indicator (fun _ ↦ (1 : ℝ)) i
        = (Ioc p.1 p.2 ∩ Ioc q.1 q.2).indicator (1 : ℝ≥0 → ℝ) i := by
    intro i
    rw [inter_indicator_one]
    rfl
  have hs : Ioc p.1 p.2 ∩ Ioc q.1 q.2 ⊆ Ioc (0 : ℝ≥0) T :=
    fun _ hi ↦ ⟨zero_le.trans_lt hi.1.1, hi.1.2.trans hpT⟩
  simp_rw [hpt]
  rw [integral_indicator_one (measurableSet_Ioc.inter measurableSet_Ioc),
    Measure.real_def, timeMeasureHorizon, Measure.restrict_apply
      (measurableSet_Ioc.inter measurableSet_Ioc), inter_eq_left.mpr hs,
    timeMeasure_Ioc_inter, ENNReal.toReal_ofReal', max_comm]

/-- The squared predictable L² norm is the double sum of the interval
overlap lengths times the expected products of the adapted coefficients. -/
theorem jointSimpleAssembly_norm_sq [IsFiniteMeasure μ] {T : ℝ≥0}
    (V : JointTBoundedSP T 𝒢) :
    ‖jointSimpleAssembly (μ := μ) T 𝒢 V‖ ^ 2
      = ∑ p ∈ V.val.value.support, ∑ q ∈ V.val.value.support,
          (∫ ω, V.val.value p ω * V.val.value q ω ∂μ)
            * max 0 ((min (p.2 : ℝ) q.2) - (max (p.1 : ℝ) q.1)) := by
  have hStepA : ‖jointSimpleAssembly (μ := μ) T 𝒢 V‖ ^ 2
      = ∫ z, (Function.uncurry ⇑V.val z) ^ 2 ∂((timeMeasureHorizon T).prod μ) := by
    rw [MathFin.lp_two_norm_sq]
    have hco : (fun z ↦ (jointSimpleAssembly (μ := μ) T 𝒢 V z) ^ 2)
        =ᵐ[jointPredictableMeasure 𝒢 μ T] fun z ↦ (Function.uncurry ⇑V.val z) ^ 2 :=
      (jointSimpleAssembly_ae V).mono (fun _ hz ↦ congrArg (fun x : ℝ ↦ x ^ 2) hz)
    rw [integral_congr_ae hco]
    simp only [pow_two]
    have hsm : StronglyMeasurable[𝒢.predictable]
        (fun z ↦ Function.uncurry ⇑V.val z * Function.uncurry ⇑V.val z) :=
      V.val.isStronglyPredictable.mul V.val.isStronglyPredictable
    exact (integral_trim 𝒢.predictable_le_prod hsm).symm
  rw [hStepA]
  have hint (p q : ℝ≥0 × ℝ≥0) :
      Integrable (fun z ↦ jointRectTerm V.val p z * jointRectTerm V.val q z)
        ((timeMeasureHorizon T).prod μ) :=
    (jointRectTerm_memLp T V.val p).integrable_mul (jointRectTerm_memLp T V.val q)
  have hsq : ∀ᵐ z ∂(timeMeasureHorizon T).prod μ, (Function.uncurry ⇑V.val z) ^ 2
      = ∑ p ∈ V.val.value.support, ∑ q ∈ V.val.value.support,
          jointRectTerm V.val p z * jointRectTerm V.val q z := by
    filter_upwards [uncurry_ae_eq_sum_jointRectTerm T V.val] with z hz
    rw [hz, sq, Finset.sum_mul_sum]
  rw [integral_congr_ae hsq,
    integral_finsetSum _ (fun p _ ↦ integrable_finsetSum _ fun q _ ↦ hint p q)]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [integral_finsetSum _ fun q _ ↦ hint p q]
  exact Finset.sum_congr rfl fun q _ ↦ integral_jointRectTerm_mul V.val (V.property p hp)

end RoughHeston

#print axioms RoughHeston.jointSimpleAssembly_norm_sq
