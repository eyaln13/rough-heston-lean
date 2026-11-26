import AffinePointTimeEnergy
import StoppedAffineRowEnergy
import JointAffineStopAfterBirth

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston.GirsanovPort

open SHEStochastic SHE SHE.PredictableL2

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} [Approximable F μ] {T : ℝ≥0}
  {B D Y : ℝ≥0 → Ω → ℝ}

local notation "ν" => jointPredictableMeasure F μ T

omit [Approximable F μ] in
/-- A common null set in sample space stays null after restricting time
and trimming to the predictable sigma algebra of a complete filtration. -/
theorem ae_joint_of_ae_sample (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    {P : Ω → Prop} (hP : ∀ᵐ ω ∂μ, P ω) :
    ∀ᵐ p ∂ν, P p.2 := by
  let N : Set Ω := {ω | ¬P ω}
  have hN : μ N=0 := ae_iff.mp hP
  have hS : MeasurableSet[F.predictable] (Ioi (0:ℝ≥0) ×ˢ N) :=
    measurableSet_predictable_Ioi_prod (hnull 0 N hN)
  have hn : ν (Ioi (0:ℝ≥0) ×ˢ N) = 0 := by
    rw [jointPredictableMeasure, trim_measurableSet_eq F.predictable_le_prod hS,
      Measure.prod_prod,hN,mul_zero]
  have hn' : ∀ᵐ p ∂ν, p ∉ Ioi (0:ℝ≥0) ×ˢ N := by
    apply ae_iff.mpr
    rwa [show {p | ¬p ∉ Ioi (0:ℝ≥0) ×ˢ N} = Ioi (0:ℝ≥0) ×ˢ N by ext p; simp]
  filter_upwards [ae_mem_joint_timeBand F μ T, hn'] with p hp hn
  by_contra h
  exact hn ⟨hp.1.1,h⟩

set_option maxHeartbeats 900000 in
/-- Normalize the continuous conditional density into a bounded
predictable Laplace process, and stop its actual Brownian integral
after the deterministic birth time. -/
theorem normalized_affine_test_at_stop
    (P : FiniteScalarIto.Family F μ T Unit)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hB₂ : ∀ t, MemLp (B t) 2 μ) (hB : Martingale B F μ)
    (hBclock : Martingale (fun t ω => B t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) F μ)
    (hAgree : ∀ t ≤ T, P.W () t =ᵐ[μ] B t)
    {K : ℝ} (hK : 0<K) (hD : StronglyAdapted F D)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => D t ω))
    (hBd : ∀ t, ∀ᵐ ω ∂μ, ‖D t ω‖ ≤ K)
    (hD₀ : ∀ t ω, 0 ≤ D t ω)
    {k : ℝ≥0 → ℝ} (hk : Measurable k) (hk₂ : MemLp k 2 (hestonTimeMeasure T))
    (hY : IsStronglyPredictable F Y) (hY₀ : ∀ t ω, 0 ≤ Y t ω)
    (hYi : ∀ t, Integrable (Y t) μ) {A : ℝ} (hMean : ∀ t, (∫ ω,Y t ω ∂μ) ≤ A)
    (hRep : ∀ u : Lp ℝ 2 ν,
      ⇑u =ᵐ[ν] (fun p => min K (D p.1 p.2) * (-(k p.1 * Real.sqrt (Y p.1 p.2)))) →
      ∀ t, (fun ω => D t ω - 1) =ᵐ[μ] jointItoIntegralCLM T hB₂ (NativeTimeCut.prior t u))
    {b : ℝ≥0} {τ : Ω → ℝ≥0} (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτb : ∀ ω, b ≤ τ ω) (hτT : ∀ ω, τ ω ≤ T) :
    ∃ L : ℝ≥0 → Ω → ℝ, IsStronglyPredictable F L ∧
      (∀ t ω, L t ω ∈ Icc (0:ℝ) 1) ∧
      (∀ᵐ ω ∂μ, ∀ t, L t ω = K⁻¹ * D t ω) ∧
      ∃ f : Lp ℝ 2 ν, ⇑f =ᵐ[ν] Function.uncurry (stoppedAffineTestRow k L Y b τ) ∧
        (fun ω => 1-L (τ ω) ω) =ᵐ[μ]
          (fun ω => 1-L b ω + jointItoIntegralCLM T hB₂ f ω) := by
  classical
  let L (t : ℝ≥0) (ω : Ω) : ℝ :=
    if Continuous (fun t => D t ω) then min 1 (max 0 (K⁻¹ * D t ω)) else 0
  have hLrange (t : ℝ≥0) (ω : Ω) : L t ω ∈ Icc (0:ℝ) 1 := by
    by_cases h : Continuous (fun t => D t ω)
    · simpa only [L,ite_eq_left h,mem_Icc] using
        And.intro (le_min zero_le_one (le_max_left 0 (K⁻¹*D t ω))) (min_le_left (1:ℝ) _)
    · simp [L,h]
  have hLc (ω : Ω) : Continuous (fun t => L t ω) := by
    by_cases h : Continuous (fun t => D t ω)
    · simpa only [L,ite_eq_left h,Pi.mul_apply] using
        continuous_const.min (continuous_const.max (continuous_const.mul h))
    · simpa only [L,ite_eq_right h] using (@continuous_const ℝ≥0 ℝ _ _ 0)
  have hLa (t : ℝ≥0) : StronglyMeasurable[F t] (L t) := by
    apply NullCompleteFiltration.stronglyMeasurable_congr F μ hnull t
      ((measurable_const.min (measurable_const.max (measurable_const.mul (hD t).measurable))).stronglyMeasurable :
        StronglyMeasurable[F t] (fun ω => min 1 (max 0 (K⁻¹*D t ω))))
    filter_upwards [hc] with ω hω
    simp [L,hω]
  have hL : IsStronglyPredictable F L := ContinuousPredictable.stronglyMeasurable F L hLa hLc
  have hLg : ∀ᵐ ω ∂μ, ∀ t, L t ω = K⁻¹ * D t ω := by
    filter_upwards [hc,ae_uniform_bound_of_timewise_bound hc hBd] with ω hcω hb t
    have hd : D t ω ≤ K := by simpa only [Real.norm_of_nonneg (hD₀ t ω)] using hb t
    have h₀ := mul_nonneg (inv_nonneg.mpr hK.le) (hD₀ t ω)
    have h₁ : K⁻¹ * D t ω ≤ 1 := by
      simpa only [inv_mul_cancel₀ hK.ne'] using mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hK.le)
    change (if Continuous (fun t => D t ω) then min 1 (max 0 (K⁻¹ * D t ω)) else 0) = _
    rw [ite_eq_left hcω,max_eq_right h₀,min_eq_right h₁]
  have huL := stoppedAffineTestRow_memLp (F := F) (b := 0) hk hk₂
    (isStoppingTime_const F T) hL hY hY₀ hYi hMean
  let u := (-K) • huL.toLp _
  have hu : ⇑u =ᵐ[ν] fun p => min K (D p.1 p.2) * (-(k p.1 * Real.sqrt (Y p.1 p.2))) := by
    filter_upwards [Lp.coeFn_smul (-K) (huL.toLp _), huL.coeFn_toLp,
      ae_mem_joint_timeBand F μ T,ae_joint_of_ae_sample hnull hLg,
      ae_joint_of_ae_sample hnull (ae_uniform_bound_of_timewise_bound hc hBd)] with p hu hf ht hg hb
    have hd : D p.1 p.2 ≤ K := by simpa only [Real.norm_of_nonneg (hD₀ p.1 p.2)] using hb p.1
    have hr := hLrange p.1 p.2
    change u p = (-K) * _ at hu
    change (huL.toLp _) p = stoppedAffineTestRow k L Y 0 (fun _ => T) p.1 p.2 at hf
    rw [hu,hf,stoppedAffineTestRow,
      ite_eq_left ⟨ht.1.1,ht.1.2⟩,max_eq_right hr.1,min_eq_right hr.2,hg,min_eq_right hd]
    field_simp
  let g (p : ℝ≥0 × Ω) : ℝ := controlThrough (fun t ω => u (t,ω)) τ p.1 p.2
  have hgu : MemLp g 2 ν := by
    let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    have hp : IsStronglyPredictable F (fun t ω => u (t,ω)) := Lp.stronglyMeasurable u
    have hs := controlThrough_predictable hτ hp
    refine (Lp.memLp u).mono hs.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    by_cases ht : p.1 ≤ τ p.2 <;> simp [g,controlThrough,ht]
  let v := hgu.toLp g
  have hv : ⇑v =ᵐ[ν] fun p => if p.1 ≤ τ p.2 then u p else 0 := by
    simpa only [v,g,controlThrough] using hgu.coeFn_toLp
  have hfL := stoppedAffineTestRow_memLp (F := F) (b := b) hk hk₂ hτ hL hY hY₀ hYi hMean
  let f := hfL.toLp _
  let w := (-K) • f
  have hw : ⇑w =ᵐ[ν] fun p => if b<p.1 ∧ p.1≤τ p.2 then u p else 0 := by
    filter_upwards [Lp.coeFn_smul (-K) f,hfL.coeFn_toLp,hu,ae_joint_of_ae_sample hnull hLg,
      ae_joint_of_ae_sample hnull (ae_uniform_bound_of_timewise_bound hc hBd)] with p hw hf hu hg hb
    have hd : D p.1 p.2 ≤ K := by simpa only [Real.norm_of_nonneg (hD₀ p.1 p.2)] using hb p.1
    have hr := hLrange p.1 p.2
    have hf' : f p = stoppedAffineTestRow k L Y b τ p.1 p.2 := hf
    change w p = (-K) * _ at hw
    rw [hw,hf',stoppedAffineTestRow]
    by_cases ht : b<p.1 ∧ p.1≤τ p.2
    · rw [ite_eq_left ht,ite_eq_left ht,max_eq_right hr.1,min_eq_right hr.2,hg,hu,min_eq_right hd]
      field_simp
    · rw [ite_eq_right ht,ite_eq_right ht,mul_zero]
  have hDC : ∀ᵐ ω ∂μ, Continuous (fun t => D t ω-1) := hc.mono fun _ hω => hω.sub continuous_const
  have hStop := jointIto_random_stop_after_birth P hnull hB₂ hB hBclock hAgree
    (M := fun t ω => D t ω-1) (fun t => (hD t).sub stronglyMeasurable_const) hDC
    u v w (hRep u hu) hτ hτb hτT hv hw
  let J := jointItoIntegralCLM (𝒢 := F) T hB₂
  have hJ : J w = (-K) • J f := map_smul J (-K) f
  refine ⟨L,hL,hLrange,hLg,f,hfL.coeFn_toLp,?_⟩
  filter_upwards [hStop,hLg,Lp.coeFn_smul (-K) (J f)] with ω hStop hg hf
  change D (τ ω) ω-1 = D b ω-1+J w ω at hStop
  change ((-K) • J f) ω = (-K)*J f ω at hf
  rw [hJ,hf] at hStop
  change 1-L (τ ω) ω = 1-L b ω+J f ω
  rw [hg (τ ω),hg b]
  field_simp [hK.ne']
  linarith

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.ae_joint_of_ae_sample
#print axioms RoughHeston.GirsanovPort.normalized_affine_test_at_stop
