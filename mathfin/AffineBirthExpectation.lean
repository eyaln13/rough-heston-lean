import LaplaceBoundary

open MeasureTheory Set Filter
open scoped ENNReal

namespace RoughHeston

/-- At birth, the conditional Laplace complement has the original
zero-conditioned expectation of the terminal payoff complement. -/
theorem affine_birth_laplace_complement_expectation
    {Ω : Type*} {m m₀ : MeasurableSpace Ω} {μ : @Measure Ω m} [IsFiniteMeasure μ]
    (hm : m₀≤m) {Z : Set Ω} (hZm : MeasurableSet[m₀] Z) (hZ : 0<μ Z)
    {X Ψ : Ω → ℝ} (hXm : Measurable[m] X) (hX₀ : ∀ ω,0≤X ω) (n : ℕ)
    (hce : μ[laplaceBoundaryWeight X n | m₀] =ᵐ[μ] fun ω => Real.exp (-Ψ ω)) :
    let Q := @boundaryConditionedMeasure Ω m μ Z
    (∫ ω,1-Real.exp (-Ψ ω) ∂Q)=(∫ ω,1-laplaceBoundaryWeight X n ω ∂Q) ∧
    (∫ ω,1-Real.exp (-Ψ ω) ∂Q)≤Q.real {ω | 0<X ω} := by
  let _ : MeasurableSpace Ω := m
  let Q := boundaryConditionedMeasure μ Z
  let : IsProbabilityMeasure Q := boundaryConditionedMeasure_isProbability hZ
  let L := laplaceBoundaryWeight X n
  let F (ω : Ω) := Real.exp (-Ψ ω)
  have hL₀ (ω : Ω) : 0≤L ω := (Real.exp_pos _).le
  have hL₁ (ω : Ω) : L ω≤1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (hX₀ ω))
  have hLm : Measurable L := ((hXm.const_mul (-(n:ℝ))).exp)
  have hLi : Integrable L μ := (integrable_const (1:ℝ)).mono' hLm.aestronglyMeasurable
    (ae_of_all _ fun ω => by simpa only [Real.norm_of_nonneg (hL₀ ω)] using hL₁ ω)
  have hZr : μ[L | m₀] =ᵐ[μ.restrict Z] F :=
    hce.filter_mono (ae_mono Measure.restrict_le_self)
  have hFi : Integrable F (μ.restrict Z) := integrable_condExp.restrict.congr hZr
  have hEq : (∫ ω in Z,F ω ∂μ)=(∫ ω in Z,L ω ∂μ) :=
    (integral_congr_ae hZr.symm).trans (setIntegral_condExp hm hLi hZm)
  have hEq' : (∫ ω,1-F ω ∂Q)=(∫ ω,1-L ω ∂Q) := by
    change (∫ ω,1-F ω ∂boundaryConditionedMeasure μ Z) =
      (∫ ω,1-L ω ∂boundaryConditionedMeasure μ Z)
    rw [integral_boundaryConditionedMeasure,integral_boundaryConditionedMeasure,
      integral_sub (integrable_const _) hFi,integral_sub (integrable_const _) hLi.restrict,hEq]
  refine ⟨hEq',hEq'.trans_le ?_⟩
  have hLi' : Integrable L Q :=
    (hLi.restrict (s := Z)).smul_measure (ENNReal.inv_ne_top.mpr hZ.ne')
  let A := {ω | 0<X ω}
  have hA : MeasurableSet A := measurableSet_lt measurable_const hXm
  have hh : Integrable (A.indicator (fun _ => (1:ℝ))) Q := (integrable_const _).indicator hA
  have hB : ∀ ω, 1-L ω≤A.indicator (fun _ => (1:ℝ)) ω := by
    intro ω
    by_cases hω : ω∈A
    · rw [indicator_of_mem hω]
      exact sub_le_self _ (hL₀ ω)
    · rw [indicator_of_notMem hω]
      have he : X ω=0 := le_antisymm (le_of_not_gt (show ¬(0<X ω) from hω)) (hX₀ ω)
      simp [L,laplaceBoundaryWeight,he]
  have hmono := integral_mono ((integrable_const _).sub hLi') hh hB
  rw [integral_indicator hA,setIntegral_const,smul_eq_mul,mul_one] at hmono
  exact hmono

#print axioms affine_birth_laplace_complement_expectation

end RoughHeston
