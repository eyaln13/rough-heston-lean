import SizeBiasBirthTestExpectation
import AffineBirthExpectation

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace RoughHeston.GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 m} {A : Set Ω} {b H : ℝ≥0} {Z : ℝ≥0 → Ω → ℝ} {ε : ℝ}

/-- The physical old-law conditional Laplace complement has the
original birth-restricted payoff expectation even after terminal focal
size bias. -/
theorem point_test_conditioned_birth_sizeBias_le
    (hA : MeasurableSet[F b] A) (hPA : 0<P A) (hb : b≤H)
    (hZ : Martingale Z F (boundaryConditionedMeasure P A))
    (hZ₀ : ∀ t, ∀ᵐ ω ∂boundaryConditionedMeasure P A, 0≤Z t ω)
    (hε : 0<ε) (hZb : Z b =ᵐ[boundaryConditionedMeasure P A] fun _ => ε)
    {Y : Ω → ℝ} (hY : Measurable Y) (hY₀ : ∀ ω, 0≤Y ω) {q : ℝ} (hq : 0≤q) :
    let μ := boundaryConditionedMeasure P A
    let Q := sizeBiasedLaw μ (Z H) ε
    (∫ ω,1-P[(fun ω => Real.exp (-q*Y ω))|F b] ω ∂Q) ≤ μ.real {ω | 0<Y ω} := by
  let μ := boundaryConditionedMeasure P A
  let Q := sizeBiasedLaw μ (Z H) ε
  let : IsProbabilityMeasure μ := boundaryConditionedMeasure_isProbability hPA
  let f (ω : Ω) := Real.exp (-q*Y ω)
  let c := P[f|F b]
  let V := {ω | 0<Y ω}
  have hV : MeasurableSet V := measurableSet_lt measurable_const hY
  have hp (ω : Ω) : 0≤f ω := (Real.exp_pos _).le
  have hunit (ω : Ω) : f ω≤1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq) (hY₀ ω))
  have hfm : Measurable f := (measurable_const.mul hY).exp
  have hfi : Integrable f P := Integrable.of_bound hfm.aestronglyMeasurable 1
    (ae_of_all _ fun ω => by rw [Real.norm_of_nonneg (hp ω)]; exact hunit ω)
  have hfe : Integrable f μ :=
    (hfi.restrict (s:=A)).smul_measure (ENNReal.inv_ne_top.mpr hPA.ne')
  have hce : Integrable c P := integrable_condExp
  have hm : StronglyMeasurable[F b] (fun ω => 1-c ω) :=
    stronglyMeasurable_const.sub stronglyMeasurable_condExp
  have hEqual : (∫ ω,1-c ω ∂μ) = ∫ ω,1-f ω ∂μ := by
    change (∫ ω,1-c ω ∂boundaryConditionedMeasure P A) =
      ∫ ω,1-f ω ∂boundaryConditionedMeasure P A
    rw [integral_boundaryConditionedMeasure,integral_boundaryConditionedMeasure,
      integral_sub (integrable_const _) hce.restrict,integral_sub (integrable_const _) hfi.restrict]
    rw [setIntegral_condExp (F.le b) hfi hA]
  have hInt : Integrable (V.indicator fun _ => (1:ℝ)) μ := (integrable_const 1).indicator hV
  have he : ∫ ω,V.indicator (fun _ => (1:ℝ)) ω ∂μ = μ.real V := by
    rw [integral_indicator hV,setIntegral_const,smul_eq_mul,mul_one]
  change (∫ ω,1-c ω ∂Q) ≤ μ.real V
  rw [integral_sizeBiasedLaw_eq_at_birth hZ hε hZ₀ hb hZb hm,hEqual,←he]
  refine integral_mono ((integrable_const 1).sub hfe) hInt fun ω => ?_
  by_cases hn : ω∈V
  · rw [indicator_of_mem hn]
    exact sub_le_self _ (hp ω)
  · have h : Y ω=0 := le_antisymm (le_of_not_gt hn) (hY₀ ω)
    simp [f,h,indicator_of_notMem hn]

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.point_test_conditioned_birth_sizeBias_le
