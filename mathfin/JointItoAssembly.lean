/-
The elementary assembly and dense extension follow MathFin's
ItoIntegralL2 and ItoIntegralL2Dense (commit cbe842dda1e71fd7173f3325971796686dbf7feb).
Upstream copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under the Apache License, Version 2.0, in the accompanying LICENSE file.
-/
import JointPredictableNorm
import JointRectanglePairing
import StochasticCompletion
import Mathlib.Analysis.Normed.Operator.Extend
import MathFin.Probability.Brownian.Ito.StochasticFubini

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory NNReal ENNReal

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}

/-- The terminal elementary stochastic integral in the supplied filtration. -/
noncomputable def jointItoSimple (M : ℝ≥0 → Ω → ℝ) (V : SimpleProcess ℝ 𝒢) : Ω → ℝ :=
  fun ω => V.value.sum fun p v => v ω * (M p.2 ω - M p.1 ω)

private theorem jointSimpleValue_memLp_top (V : SimpleProcess ℝ 𝒢) (p : ℝ≥0 × ℝ≥0) :
    MemLp (V.value p) ⊤ μ :=
  memLp_top_of_bound ((V.measurable_value p).mono (𝒢.le p.1) le_rfl).aestronglyMeasurable
    V.valueBound (Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs] using V.value_le_valueBound p ω)

/-- Each elementary integral against a timewise square integrable process
is square integrable. -/
theorem memLp_jointItoSimple [IsFiniteMeasure μ] (hM₂ : ∀ t, MemLp (M t) 2 μ)
    (V : SimpleProcess ℝ 𝒢) : MemLp (jointItoSimple M V) 2 μ := by
  rw [show jointItoSimple M V =
    fun ω => ∑ p ∈ V.value.support, V.value p ω * (M p.2 ω - M p.1 ω) from rfl]
  exact memLp_finsetSum _ fun p _ =>
    (jointSimpleValue_memLp_top V p).mul ((hM₂ p.2).sub (hM₂ p.1))

private theorem jointItoSimple_add (V W : SimpleProcess ℝ 𝒢) :
    jointItoSimple M (V + W) = jointItoSimple M V + jointItoSimple M W := by
  funext ω
  simp only [jointItoSimple, Pi.add_apply, show (V + W).value = V.value + W.value from rfl]
  exact Finsupp.sum_add_index' (fun p => by simp) (fun p v w => by simp [add_mul])

private theorem jointItoSimple_smul (c : ℝ) (V : SimpleProcess ℝ 𝒢) :
    jointItoSimple M (c • V) = c • jointItoSimple M V := by
  funext ω
  simp only [jointItoSimple, Pi.smul_apply, smul_eq_mul,
    show (c • V).value = c • V.value from rfl]
  rw [Finsupp.sum_smul_index' (fun p => by simp), Finsupp.mul_sum]
  exact Finsupp.sum_congr fun p _ => by simp [mul_assoc]

/-- Elementary stochastic integration as a linear map into the terminal
random-variable L² space. The integrands use the supplied joint filtration. -/
noncomputable def jointItoAssembly [IsFiniteMeasure μ] (T : ℝ≥0)
    (hM₂ : ∀ t, MemLp (M t) 2 μ) : JointTBoundedSP T 𝒢 →ₗ[ℝ] Lp ℝ 2 μ where
  toFun V := (memLp_jointItoSimple hM₂ V.val).toLp (jointItoSimple M V.val)
  map_add' V W := by
    rw [← MemLp.toLp_add (memLp_jointItoSimple hM₂ V.val)
      (memLp_jointItoSimple hM₂ W.val)]
    congr 1
    exact jointItoSimple_add V.val W.val
  map_smul' c V := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul c (memLp_jointItoSimple hM₂ V.val)]
    congr 1
    exact jointItoSimple_smul c V.val

/-- The elementary Itô isometry on the joint filtration. -/
theorem jointItoAssembly_isometry [IsFiniteMeasure μ] {T : ℝ≥0}
    (hM : Martingale M 𝒢 μ) (hM₂ : ∀ t, MemLp (M t) 2 μ)
    (hclock : Martingale (fun t ω => M t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) 𝒢 μ)
    (V : JointTBoundedSP T 𝒢) :
    ‖jointItoAssembly T hM₂ V‖ = ‖jointSimpleAssembly (μ := μ) T 𝒢 V‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hBsq : ‖jointItoAssembly T hM₂ V‖ ^ 2 =
      ∫ ω, (jointItoSimple M V.val ω) ^ 2 ∂μ :=
    norm_toLp_two_sq (memLp_jointItoSimple hM₂ V.val)
  rw [hBsq, jointSimpleAssembly_norm_sq]
  let d (p : ℝ≥0 × ℝ≥0) (ω : Ω) := V.val.value p ω * (M p.2 ω - M p.1 ω)
  have h₂ (p : ℝ≥0 × ℝ≥0) : MemLp (d p) 2 μ :=
    (jointSimpleValue_memLp_top V.val p).mul ((hM₂ p.2).sub (hM₂ p.1))
  have hprod (p q : ℝ≥0 × ℝ≥0) : Integrable (fun ω => d p ω * d q ω) μ :=
    (h₂ p).integrable_mul (h₂ q)
  simp only [jointItoSimple, Finsupp.sum, sq, Finset.sum_mul_sum]
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ fun q _ => hprod p q)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [integral_finsetSum _ (fun q _ => hprod p q)]
  apply Finset.sum_congr rfl
  intro q hq
  exact joint_rect_increment_pairing hM hM₂ hclock
    (V.val.le_of_mem_support_value p hp) (V.val.le_of_mem_support_value q hq)
    (V.property p hp) (V.property q hq)
    (V.val.measurable_value p).stronglyMeasurable (V.val.measurable_value q).stronglyMeasurable
    (jointSimpleValue_memLp_top V.val p) (jointSimpleValue_memLp_top V.val q)

/-- Extend the elementary integral along the dense joint predictable
assembly. For martingales with unit clock this is an isometry. -/
noncomputable def jointItoIntegralCLM [IsFiniteMeasure μ] (T : ℝ≥0)
    (hM₂ : ∀ t, MemLp (M t) 2 μ) :
    Lp ℝ 2 (jointPredictableMeasure 𝒢 μ T) →L[ℝ] Lp ℝ 2 μ :=
  (jointItoAssembly (𝒢 := 𝒢) T hM₂).extendOfNorm (jointSimpleAssembly T 𝒢)

theorem jointItoIntegralCLM_agrees [IsFiniteMeasure μ] (T : ℝ≥0)
    (hM₂ : ∀ t, MemLp (M t) 2 μ)
    (hM : Martingale M 𝒢 μ)
    (hclock : Martingale (fun t ω => M t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) 𝒢 μ)
    (V : JointTBoundedSP T 𝒢) :
    jointItoIntegralCLM T hM₂ (jointSimpleAssembly T 𝒢 V) = jointItoAssembly T hM₂ V := by
  unfold jointItoIntegralCLM
  exact LinearMap.extendOfNorm_eq (jointSimpleAssembly_denseRange T 𝒢)
    ⟨1, fun W => by rw [one_mul]; exact (jointItoAssembly_isometry hM hM₂ hclock W).le⟩ V

theorem jointItoIntegralCLM_norm [IsFiniteMeasure μ] (T : ℝ≥0)
    (hM₂ : ∀ t, MemLp (M t) 2 μ)
    (hM : Martingale M 𝒢 μ)
    (hclock : Martingale (fun t ω => M t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) 𝒢 μ)
    (f : Lp ℝ 2 (jointPredictableMeasure 𝒢 μ T)) :
    ‖jointItoIntegralCLM T hM₂ f‖ = ‖f‖ := by
  unfold jointItoIntegralCLM
  exact LinearMap.norm_extendOfNorm_eq_of_isometry (jointSimpleAssembly_denseRange T 𝒢)
    (jointItoAssembly_isometry hM hM₂ hclock) f

/-- Stochastic Fubini for the integral built on the supplied joint
filtration. The parameter family and its representatives satisfy the
Bochner-integrability hypotheses of MathFin's interchange theorem. -/
theorem jointItoIntegralCLM_fubini [IsFiniteMeasure μ]
    {A : Type*} {mA : MeasurableSpace A} {ν : Measure A} [SFinite ν]
    (T : ℝ≥0) (hM₂ : ∀ t, MemLp (M t) 2 μ)
    (φ : A → Lp ℝ 2 (jointPredictableMeasure 𝒢 μ T))
    (hφ : Integrable φ ν) (ψ : A → (ℝ≥0 × Ω) → ℝ)
    (hψ : MathFin.StochasticFubini.JointIntegrable ψ ν (jointPredictableMeasure 𝒢 μ T))
    (hφψ : ∀ u, ⇑(φ u) =ᵐ[jointPredictableMeasure 𝒢 μ T] ψ u)
    (g : Lp ℝ 2 (jointPredictableMeasure 𝒢 μ T))
    (hg : ⇑g =ᵐ[jointPredictableMeasure 𝒢 μ T] fun x => ∫ u, ψ u x ∂ν) :
    (∫ u, jointItoIntegralCLM T hM₂ (φ u) ∂ν) = jointItoIntegralCLM T hM₂ g :=
  MathFin.StochasticFubini.stochFubini_ofCLM (jointItoIntegralCLM T hM₂) φ hφ ψ hψ hφψ g hg

end RoughHeston

#print axioms RoughHeston.memLp_jointItoSimple
#print axioms RoughHeston.jointItoAssembly
#print axioms RoughHeston.jointItoAssembly_isometry
#print axioms RoughHeston.jointItoIntegralCLM_agrees
#print axioms RoughHeston.jointItoIntegralCLM_norm

#print axioms RoughHeston.jointItoIntegralCLM_fubini
