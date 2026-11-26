import AffineNormalizedStop
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Sequences

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston.GirsanovPort

open SHEStochastic SHE SHE.PredictableL2

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} [Approximable F μ] {T : ℝ≥0}
  {B M Y C : ℝ≥0 → Ω → ℝ}

local notation "ν" => jointPredictableMeasure F μ T

set_option maxHeartbeats 1600000 in
/-- The original competitor point test, stopped at its observation clock
after birth, has the exact predictable row that vanishes at zero
variance. The original conditional terminal test supplies its birth
value. -/
theorem actual_original_stopped_point_affine_of_joint_prefix
    (P : FiniteScalarIto.Family F μ T Unit)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hB₂ : ∀ t, MemLp (B t) 2 μ) (hB : Martingale B F μ)
    (hBclock : Martingale (fun t ω => B t ω^2 - ((min t T : ℝ≥0):ℝ)) F μ)
    (hAgree : ∀ t ≤ T, P.W () t =ᵐ[μ] B t)
    {α κ σ q : ℝ} (hα : 0 < α) (hα' : α < 1) (hT : 0 < T) (hq : 0 ≤ q)
    (hσ : 0 ≤ σ) {w j : ℝ → ℝ}
    (hw : AffineRiccatiTestOn α κ (σ^2/2) q (T:ℝ) w (fun _ => 0))
    (hj : AffineInputOn (T:ℝ) j)
    (hM : Martingale M F μ) (hM₂ : ∀ t, MemLp (M t) 2 μ)
    (hMc : ∀ ω, Continuous (fun t => M t ω)) (hM₀ : M 0 =ᵐ[μ] 0)
    (hY : IsStronglyPredictable F Y) (hYc : ∀ ω, Continuous (fun t => Y t ω))
    (hY₀ : ∀ t ω, 0 ≤ Y t ω) {Y₀ : ℝ} (hstart : ∀ ω, Y 0 ω ≤ Y₀)
    (hYi : ∀ t, Integrable (Y t) μ) {A : ℝ} (hMean : ∀ t, (∫ ω,Y t ω ∂μ) ≤ A)
    (hMC : Martingale (fun t => M t*M t-C t) F μ)
    (hCi : ∀ t, Integrable (C t) μ)
    (hCmon : ∀ s t, s ≤ t → C s ≤ᵐ[μ] C t)
    (hClock : ∀ t ≤ T, C t =ᵐ[μ] fun ω => ∫ r in (0:ℝ)..(t:ℝ), σ^2*Y r.toNNReal ω)
    (hInv : ∀ᵐ ω ∂μ, ∀ r ∈ Ioc (0:ℝ) (T:ℝ),
      M r.toNNReal ω = volterraConvolution (fractionalL α) (fun u => Y u.toNNReal ω) r +
        ∫ u in Ioc (0:ℝ) r, κ*Y u.toNNReal ω-j u)
    (hMPrefix : let ha₂ := (sqrt_variance_memLp_joint T hY hY₀ hYi hMean).const_mul σ
      ∀ r ≤ T, M r =ᵐ[μ] jointItoIntegralCLM T hB₂ (jointAmplitudeSectionLp (𝒢:=F) (a:=fun t ω => σ*Real.sqrt (Y t ω)) r ha₂))
    {b : ℝ≥0} (hb : b < T)
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτb : ∀ ω, b ≤ τ ω) (hτT : ∀ ω, τ ω ≤ T) :
    ∃ L : ℝ≥0 → Ω → ℝ, IsStronglyPredictable F L ∧
      (∀ t ω, L t ω ∈ Icc (0:ℝ) 1) ∧
      L b =ᵐ[μ] μ[(fun ω => Real.exp (-q*Y T ω)) | F b] ∧
      (∀ᵐ ω ∂μ, τ ω = T → 1-L (τ ω) ω = 1-Real.exp (-q*Y T ω)) ∧
      ∃ f : Lp ℝ 2 ν, ⇑f =ᵐ[ν] Function.uncurry
          (stoppedAffineTestRow (fun t => σ*w ((T:ℝ)-(t:ℝ))) L Y b τ) ∧
        (fun ω => 1-L (τ ω) ω) =ᵐ[μ]
          (fun ω => 1-L b ω + jointItoIntegralCLM T hB₂ f ω) := by
  let c := volterraConvolution w j T
  let K := Real.exp c
  let a (t : ℝ≥0) (ω : Ω) := σ*Real.sqrt (Y t ω)
  let D := affinePointDensityPath T w c q M a Y
  let k (t : ℝ≥0) := σ*w ((T:ℝ)-(t:ℝ))
  have hk : Measurable k :=
    measurable_const.mul (hw.solution_measurable.comp (measurable_const.sub measurable_subtype_coe))
  have hK : 0<K := Real.exp_pos _
  have ha : IsStronglyPredictable F a := by
    let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    exact (measurable_const.mul hY.measurable.sqrt).stronglyMeasurable
  have hac (ω : Ω) : Continuous (fun t => a t ω) :=
    continuous_const.mul ((Real.continuous_sqrt).comp (hYc ω))
  have ha₀ (t : ℝ≥0) (ω : Ω) : 0 ≤ a t ω := mul_nonneg hσ (Real.sqrt_nonneg _)
  have ha₂ : MemLp (Function.uncurry a) 2 ν :=
    (sqrt_variance_memLp_joint T hY hY₀ hYi hMean).const_mul σ
  have hD₀ (t : ℝ≥0) (ω : Ω) : 0 ≤ D t ω := by
    dsimp only [D,affinePointDensityPath]
    split
    · exact (Real.exp_pos _).le
    · exact (Real.exp_pos _).le
  obtain ⟨hDa,hDc,hDbd,hDpre,hDlaw⟩ :=
    affine_point_density_path_of_inverse hα hα' hT hq hw hj hM hM₂ hMc hM₀
      hY.stronglyAdapted hYc hY₀ hstart hMC hCi hCmon hClock hInv
  have hTclosure : T ∈ closure (Iio T) := by
    rw [closure_Iio' (a:=T) ⟨0,hT⟩]
    exact mem_Iic.mpr (show T ≤ T from le_rfl)
  obtain ⟨s,hs,hslim⟩ := mem_closure_iff_seq_limit.mp hTclosure
  have hRep (u : Lp ℝ 2 ν)
      (hu : ⇑u =ᵐ[ν] fun p => min K (D p.1 p.2) * (-(k p.1 * Real.sqrt (Y p.1 p.2)))) :
      ∀ t, (fun ω => D t ω - 1) =ᵐ[μ] jointItoIntegralCLM T hB₂ (NativeTimeCut.prior t u) := by
    have hu' : ⇑u =ᵐ[ν] fun p => min K (D p.1 p.2) *
        (-(w ((T:ℝ)-(p.1:ℝ))*a p.1 p.2)) := by
      filter_upwards [hu] with p hp
      rw [hp]
      simp only [k,a]
      ring
    have hPre := affine_point_compatible_prefix_of_joint_prefix P hB₂ hB hBclock hAgree ha
      hac ha₀ ha₂ hMPrefix hM hM₂ hMc hw.solution_smooth hK.le hDpre u hu'
    have hTerminal := affine_point_prefices_include_terminal hB₂ hDa hDc u hPre hs hslim
    intro t
    by_cases ht : t < T
    · exact hPre t ht
    · have hprior : NativeTimeCut.prior t u = u := by
        apply Lp.ext
        filter_upwards [NativeTimeCut.prior_ae t u,
          ae_fst_mem_Ioo_jointPredictableMeasure (𝒢:=F) (μ:=μ) T] with p hp hmem
        rw [hp,ite_eq_right (not_lt_of_ge (hmem.2.le.trans (le_of_not_gt ht)))]
      rw [hprior]
      filter_upwards [hTerminal] with ω hω
      simpa only [D,affinePointDensityPath,ite_eq_right ht,ite_eq_right (lt_irrefl T)] using hω
  obtain ⟨L,hL,hRange,hLgood,f,hf,hStop⟩ := normalized_affine_test_at_stop
    P hnull hB₂ hB hBclock hAgree hK hDa hDc hDbd hD₀ hk
    (reflected_riccati_memLp_two T hw.solution_measurable hw.solution_sq_integrable σ)
    hY hY₀ hYi hMean (D := D) hRep hτ hτb hτT
  refine ⟨L,hL,hRange,?_,?_,f,hf,hStop⟩
  · let y (ω : Ω) := Real.exp (-q*Y T ω)
    let z (ω : Ω) := Real.exp (c-q*Y T ω)
    have hy : y = K⁻¹ • z := by
      funext ω
      change Real.exp (-q*Y T ω) = (Real.exp c)⁻¹ * Real.exp (c-q*Y T ω)
      rw [← Real.exp_neg,← Real.exp_add]
      congr 1
      ring
    change L b =ᵐ[μ] μ[y|F b]
    rw [hy]
    filter_upwards [condExp_smul (μ:=μ) K⁻¹ z (F b),hDlaw b hb,hLgood] with ω h₁ h₂ h₃
    change μ[K⁻¹ • z|F b] ω = K⁻¹ * μ[z|F b] ω at h₁
    change μ[z|F b] ω = D b ω at h₂
    rw [h₁,h₂,h₃ b]
  · filter_upwards [hLgood] with ω hω h
    rw [h,hω T]
    change 1-(Real.exp c)⁻¹ * affinePointDensityPath T w c q M a Y T ω = _
    rw [affinePointDensityPath,ite_eq_right (lt_irrefl T),←Real.exp_neg,←Real.exp_add]
    congr 2
    ring

set_option maxHeartbeats 900000 in
theorem actual_original_stopped_point_affine
    (P : FiniteScalarIto.Family F μ T Unit)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hB₂ : ∀ t, MemLp (B t) 2 μ) (hB : Martingale B F μ)
    (hBclock : Martingale (fun t ω => B t ω^2 - ((min t T : ℝ≥0):ℝ)) F μ)
    (hAgree : ∀ t ≤ T, P.W () t =ᵐ[μ] B t)
    {α κ σ q : ℝ} (hα : 0 < α) (hα' : α < 1) (hT : 0 < T) (hq : 0 ≤ q)
    (hσ : 0 ≤ σ) {w j : ℝ → ℝ}
    (hw : AffineRiccatiTestOn α κ (σ^2/2) q (T:ℝ) w (fun _ => 0))
    (hj : AffineInputOn (T:ℝ) j)
    (hM : Martingale M F μ) (hM₂ : ∀ t, MemLp (M t) 2 μ)
    (hMc : ∀ ω, Continuous (fun t => M t ω)) (hM₀ : M 0 =ᵐ[μ] 0)
    (hY : IsStronglyPredictable F Y) (hYc : ∀ ω, Continuous (fun t => Y t ω))
    (hY₀ : ∀ t ω, 0 ≤ Y t ω) {Y₀ : ℝ} (hstart : ∀ ω, Y 0 ω ≤ Y₀)
    (hYi : ∀ t, Integrable (Y t) μ) {A : ℝ} (hMean : ∀ t, (∫ ω,Y t ω ∂μ) ≤ A)
    (hMC : Martingale (fun t => M t*M t-C t) F μ)
    (hCi : ∀ t, Integrable (C t) μ)
    (hCmon : ∀ s t, s ≤ t → C s ≤ᵐ[μ] C t)
    (hClock : ∀ t ≤ T, C t =ᵐ[μ] fun ω => ∫ r in (0:ℝ)..(t:ℝ), σ^2*Y r.toNNReal ω)
    (hInv : ∀ᵐ ω ∂μ, ∀ r ∈ Ioc (0:ℝ) (T:ℝ),
      M r.toNNReal ω = volterraConvolution (fractionalL α) (fun u => Y u.toNNReal ω) r +
        ∫ u in Ioc (0:ℝ) r, κ*Y u.toNNReal ω-j u)
    (hCut : HasAmplitudeCutoffIntegral F μ T B M (fun t ω => σ*Real.sqrt (Y t ω)))
    {b : ℝ≥0} (hb : b < T)
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτb : ∀ ω, b ≤ τ ω) (hτT : ∀ ω, τ ω ≤ T) :
    ∃ L : ℝ≥0 → Ω → ℝ, IsStronglyPredictable F L ∧
      (∀ t ω, L t ω ∈ Icc (0:ℝ) 1) ∧
      L b =ᵐ[μ] μ[(fun ω => Real.exp (-q*Y T ω)) | F b] ∧
      (∀ᵐ ω ∂μ, τ ω = T → 1-L (τ ω) ω = 1-Real.exp (-q*Y T ω)) ∧
      ∃ f : Lp ℝ 2 ν, ⇑f =ᵐ[ν] Function.uncurry
          (stoppedAffineTestRow (fun t => σ*w ((T:ℝ)-(t:ℝ))) L Y b τ) ∧
        (fun ω => 1-L (τ ω) ω) =ᵐ[μ]
          (fun ω => 1-L b ω + jointItoIntegralCLM T hB₂ f ω) := by
  apply actual_original_stopped_point_affine_of_joint_prefix P hnull hB₂ hB hBclock hAgree
    hα hα' hT hq hσ hw hj hM hM₂ hMc hM₀ hY hYc hY₀ hstart hYi hMean hMC hCi hCmon hClock
    hInv ?_ hb hτ hτb hτT
  intro ha₂ r hr
  have ha : IsStronglyPredictable F (fun t ω => σ*Real.sqrt (Y t ω)) := by
    let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    exact (measurable_const.mul hY.measurable.sqrt).stronglyMeasurable
  have hac (ω : Ω) : Continuous (fun t => σ*Real.sqrt (Y t ω)) :=
    continuous_const.mul ((Real.continuous_sqrt).comp (hYc ω))
  exact hCut.ae_eq_jointIto_fixed_horizon hr hB hB₂ hBclock ha.stronglyAdapted ha
    (ae_of_all _ fun ω => (hac ω).continuousOn) (fun t ω => mul_nonneg hσ (Real.sqrt_nonneg _))
    ha₂

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.actual_original_stopped_point_affine
#print axioms RoughHeston.GirsanovPort.actual_original_stopped_point_affine_of_joint_prefix
