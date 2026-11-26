import ClusterPulseHorizonConsistency

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston.GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 m} {T : ℝ≥0} {B U : ℝ≥0 → Ω → ℝ}

theorem fractionalSecondKindResolvent_zero_of_nonpos (α κ : ℝ) {t : ℝ} (ht : t≤0) :
    fractionalSecondKindResolvent α κ t=0 := by
  simp [fractionalSecondKindResolvent,fractionalK,ht]

/-- Extension by zero identifies a terminal resolvent row at an earlier
age with the same reflected kernel on the common time horizon. -/
theorem cluster_resolvent_row_extend {t : ℝ≥0} (ht : t≤T)
    {R : ℝ → ℝ} (hz : ∀ x≤0, R x=0) {σ : ℝ}
    (f : Lp ℝ 2 (jointPredictableMeasure F P t))
    (hf : f =ᵐ[jointPredictableMeasure F P t]
      fun z => σ*R ((t:ℝ)-(z.1:ℝ))*Real.sqrt (U z.1 z.2)) :
    ⇑(jointBandExtend F P ht f) =ᵐ[jointPredictableMeasure F P T]
      fun z => σ*R ((t:ℝ)-(z.1:ℝ))*Real.sqrt (U z.1 z.2) := by
  refine ((jointBandExtend_coeFn F P ht f).trans (joint_timeBand_indicator_ae_eq F P ht hf)).trans ?_
  filter_upwards [ae_mem_joint_timeBand F P T] with z hmem
  by_cases h : z.1 ≤ t
  · exact indicator_of_mem (show z∈Ioc (0:ℝ≥0) t ×ˢ(univ:Set Ω) from ⟨⟨hmem.1.1,h⟩,mem_univ _⟩) _
  · have hnot : z∉Ioc (0:ℝ≥0) t ×ˢ(univ:Set Ω) := fun hh => h hh.1.2
    rw [indicator_of_notMem hnot]
    simp only [hz _ (sub_nonpos.mpr (show (t:ℝ)≤(z.1:ℝ) from (le_of_not_ge h))),mul_zero,zero_mul]

/-- Both observation times share an Itô map, including the new
interval between them. This gives the signed kernel row for increments. -/
theorem cluster_increment_of_resolvent_rows
    (hB₂ : ∀ t, MemLp (B t) 2 P) (hB : Martingale B F P)
    (hclock : Martingale (fun s ω => B s ω^2-((min s T:ℝ≥0):ℝ)) F P)
    {a b : ℝ≥0} (ha : a≤T) (hb : b≤T) {R : ℝ → ℝ} (hz : ∀ x≤0, R x=0)
    {σ Ia Ib : ℝ} (fa : Lp ℝ 2 (jointPredictableMeasure F P a))
    (fb : Lp ℝ 2 (jointPredictableMeasure F P b))
    (hfa : fa =ᵐ[jointPredictableMeasure F P a] fun z => σ*R ((a:ℝ)-(z.1:ℝ))*Real.sqrt (U z.1 z.2))
    (hfb : fb =ᵐ[jointPredictableMeasure F P b] fun z => σ*R ((b:ℝ)-(z.1:ℝ))*Real.sqrt (U z.1 z.2))
    (hae : U a =ᵐ[P] fun ω => Ia+jointItoIntegralCLM a (fun r => hB₂ (min r a)) fa ω)
    (hbe : U b =ᵐ[P] fun ω => Ib+jointItoIntegralCLM b (fun r => hB₂ (min r b)) fb ω) :
    ∃ f : Lp ℝ 2 (jointPredictableMeasure F P T),
      (⇑f =ᵐ[jointPredictableMeasure F P T] fun z =>
        σ*(R ((b:ℝ)-(z.1:ℝ))-R ((a:ℝ)-(z.1:ℝ)))*Real.sqrt (U z.1 z.2)) ∧
      (∀ᵐ ω ∂P, U b ω-U a ω=Ib-Ia+jointItoIntegralCLM T hB₂ f ω) := by
  let A := jointBandExtend F P ha fa
  let D := jointBandExtend F P hb fb
  refine ⟨D-A,?_,?_⟩
  · filter_upwards [Lp.coeFn_sub D A,cluster_resolvent_row_extend ha hz fa hfa,
      cluster_resolvent_row_extend hb hz fb hfb] with z h hA hD
    change (D-A) z = D z-A z at h
    change D z = _ at hD
    change A z = _ at hA
    rw [h,hD,hA]; ring
  · rw [jointItoIntegralCLM_cross_horizon F P ha hB₂ hB hclock] at hae
    rw [jointItoIntegralCLM_cross_horizon F P hb hB₂ hB hclock] at hbe
    rw [map_sub]
    filter_upwards [hae,hbe,Lp.coeFn_sub (jointItoIntegralCLM T hB₂ D) (jointItoIntegralCLM T hB₂ A)]
      with ω hA hD hsub
    change _ = Ib-Ia+(jointItoIntegralCLM T hB₂ D-jointItoIntegralCLM T hB₂ A) ω
    change _ = jointItoIntegralCLM T hB₂ D ω-jointItoIntegralCLM T hB₂ A ω at hsub
    rw [hsub,hD,hA]; dsimp only [A,D]; ring

#print axioms cluster_resolvent_row_extend
#print axioms cluster_increment_of_resolvent_rows

end RoughHeston.GirsanovPort
