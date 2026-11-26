import ActualBirthTraceStoppedOccupation
import AffineTestInstantiation

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston.GirsanovPort

open SHEStochastic

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 m} {A : Set Ω} {b s r : ℝ≥0} {α κ σ : ℝ}
  {B M Y C : ℝ≥0 → Ω → ℝ} {j : ℝ → ℝ}

private theorem affine_point_test_nat (hα : 1/2<α) (hα' : α<1) (hκ : 0≤κ)
    {T : ℝ} (hT : 0<T) (n : ℕ) :
    ∃ w, AffineRiccatiTestOn α κ (σ^2/2) (n:ℝ) T w (fun _ => 0) := by
  cases n with
  | zero =>
    refine ⟨fun _ => 0, ?_⟩
    refine ⟨measurable_const,?_,?_,?_,?_,measurable_const,?_,?_,?_,?_⟩
    · exact fun _ _ => le_rfl
    · exact fun _ _ => contDiffAt_const
    · simp
    · simp
    · exact fun _ _ => le_rfl
    · exact continuousOn_const
    · simp
    · intro t ht
      simp [volterraConvolution]
  | succ n =>
    obtain ⟨w,hw,_⟩ := exists_affine_point_test hα hα'
      (by positivity : 0<((n+1:ℕ):ℝ)) hκ (by positivity : 0≤σ^2/2) hT
    exact ⟨w,hw⟩

set_option maxHeartbeats 2200000 in
/-- The fixed-mesh old competitor inverse and common Brownian integral
produce all old physical Laplace tests needed at a trace observation.
The Riccati equation runs over the original physical horizon, retaining
the competitor's entire history at birth. -/
theorem raw_original_point_tests_at_birth_trace
    (P₀ : FiniteScalarIto.Family F P (b+r) Unit) (hs₀ : 0<s) (hs : s≤r)
    (hnull : SHE.NullCompleteFiltration.ContainsNullSets F P)
    (hB₂ : ∀ t, MemLp (B t) 2 P) (hB : Martingale B F P)
    (hBc : Martingale (fun t ω => B t ω^2-((min t (b+r):ℝ≥0):ℝ)) F P)
    (hAgree : ∀ t≤b+r, P₀.W () t =ᵐ[P] B t)
    (hα : 1/2<α) (hα' : α<1) (hκ : 0≤κ) (hσ : 0≤σ)
    (hj : AffineInputOn ((b+s:ℝ≥0):ℝ) j)
    (hM : Martingale M F P) (hM₂ : ∀ t, MemLp (M t) 2 P)
    (hMc : ∀ ω, Continuous (fun t => M t ω)) (hM₀ : M 0 =ᵐ[P] 0)
    (hY : IsStronglyPredictable F Y) (hYc : ∀ ω, Continuous (fun t => Y t ω))
    (hY₀ : ∀ t ω, 0≤Y t ω) {Y₀ : ℝ} (hstart : ∀ ω, Y 0 ω≤Y₀)
    (hYi : ∀ t, Integrable (Y t) P) {HMean : ℝ} (hMean : ∀ t, (∫ ω,Y t ω ∂P)≤HMean)
    (hMC : Martingale (fun t => M t*M t-C t) F P)
    (hCi : ∀ t, Integrable (C t) P)
    (hCmon : ∀ u t, u≤t → C u≤ᵐ[P] C t)
    (hClock : ∀ t≤b+r, C t =ᵐ[P] fun ω => ∫ u in (0:ℝ)..(t:ℝ), σ^2*Y u.toNNReal ω)
    (hInv : ∀ᵐ ω ∂P, ∀ t ∈ Ioc (0:ℝ) ((b+r:ℝ≥0):ℝ),
      M t.toNNReal ω = volterraConvolution (fractionalL α) (fun u => Y u.toNNReal ω) t +
        ∫ u in Ioc (0:ℝ) t, κ*Y u.toNNReal ω-j u)
    (hCut : HasAmplitudeCutoffIntegral F P (b+r) B M (fun t ω => σ*Real.sqrt (Y t ω)))
    (hA : MeasurableSet[F b] A) {τ : A → ℝ≥0}
    (hτ : IsStoppingTime (birthTraceFiltration F b A) (fun ω => (τ ω:WithTop ℝ≥0))) :
    let hB₂' (t : ℝ≥0) := hB₂ (min t (b+s))
    let ν := jointPredictableMeasure F P (b+s)
    ∃ w : ℕ → ℝ → ℝ, (∀ n, Measurable (w n)) ∧
      (∀ n, IntegrableOn (fun t => (w n t)^2) (Ioc (0:ℝ) (s:ℝ))) ∧
      ∀ n : ℕ, ∃ L : ℝ≥0 → Ω → ℝ, IsStronglyPredictable F L ∧
        (∀ t ω, L t ω ∈ Icc (0:ℝ) 1) ∧
        L b =ᵐ[P] P[(fun ω => Real.exp (-(n:ℝ)*Y (b+s) ω)) | F b] ∧
        (∀ᵐ ω ∂P, physicalObservationOfTrace τ b s ω = b+s →
          1-L (physicalObservationOfTrace τ b s ω) ω = 1-Real.exp (-(n:ℝ)*Y (b+s) ω)) ∧
        ∃ u : Lp ℝ 2 ν, ⇑u =ᵐ[ν] Function.uncurry
            (stoppedAffineTestRow (fun t => σ*w n (((b+s:ℝ≥0):ℝ)-(t:ℝ))) L Y b
              (physicalObservationOfTrace τ b s)) ∧
          (fun ω => 1-L (physicalObservationOfTrace τ b s ω) ω) =ᵐ[P]
            (fun ω => 1-L b ω + jointItoIntegralCLM (b+s) hB₂' u ω) := by
  let T := b+s
  let T₀ := b+r
  let B' (t : ℝ≥0) := B (min t T)
  change ∃ w : ℕ → ℝ → ℝ, _ ∧ _ ∧ _
  have hT : T≤T₀ := add_le_add_right hs b
  have hbT : b<T := lt_add_of_pos_right b hs₀
  have hT₀ : 0<T := zero_le.trans_lt hbT
  have hTreal : 0<(T:ℝ) := hT₀
  choose w hw using fun n : ℕ => affine_point_test_nat (σ:=σ) hα hα' hκ hTreal n
  refine ⟨w,fun n => (hw n).solution_measurable,?_,?_⟩
  · intro n
    exact (hw n).solution_sq_integrable.mono_set (Ioc_subset_Ioc_right (by exact_mod_cast show s≤T from le_add_of_nonneg_left zero_le))
  have hB' : Martingale B' F P := martingale_freeze_at hB T
  have hBc' : Martingale (fun t ω => B' t ω^2-((min t T:ℝ≥0):ℝ)) F P := by
    have hTT : min T (b+r)=T := min_eq_left hT
    simpa only [B',min_assoc,hTT] using martingale_freeze_at hBc T
  let P₁ := truncateScalarNativeFamily P₀ hT
  have hAgr (t : ℝ≥0) (ht : t≤T) : P₁.W () t =ᵐ[P] B' t := by
    change P₀.W () t =ᵐ[P] B (min t T)
    rw [min_eq_left ht]
    exact hAgree t (ht.trans hT)
  let a (t : ℝ≥0) (ω : Ω) := σ*Real.sqrt (Y t ω)
  have ha : IsStronglyPredictable F a := by
    let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    exact (measurable_const.mul hY.measurable.sqrt).stronglyMeasurable
  have hac (ω : Ω) : Continuous (fun t => a t ω) :=
    continuous_const.mul (Real.continuous_sqrt.comp (hYc ω))
  let haL := (sqrt_variance_memLp_joint T₀ hY hY₀ hYi hMean).const_mul σ
  have hPrefix (t : ℝ≥0) (ht : t≤T) :
      M t =ᵐ[P] jointItoIntegralCLM T (fun u => hB₂ (min u T))
        (jointAmplitudeSectionLp (𝒢:=F) (a:=a) t ((sqrt_variance_memLp_joint T hY hY₀ hYi hMean).const_mul σ)) := by
    let haS := (sqrt_variance_memLp_joint T hY hY₀ hYi hMean).const_mul σ
    let f := (Ioc (0:ℝ≥0) t ×ˢ (univ : Set Ω)).indicator (Function.uncurry a)
    have hzero (p : ℝ≥0 × Ω) (hp : T<p.1) : f p=0 := by
      have hn : p∉Ioc (0:ℝ≥0) t ×ˢ (univ : Set Ω) := fun h => hp.not_ge (h.1.2.trans ht)
      exact indicator_of_notMem hn _
    rw [jointIto_short_horizon_eq_of_supported_row hT hB₂ hB hBc hzero
      (jointAmplitudeSectionLp_ae (𝒢:=F) (a:=a) t haS) (jointAmplitudeSectionLp_ae (𝒢:=F) (a:=a) t haL)]
    exact hCut.ae_eq_jointIto_fixed_horizon (ht.trans hT) hB hB₂ hBc ha.stronglyAdapted ha
      (ae_of_all _ fun ω => (hac ω).continuousOn) (fun _ _ => mul_nonneg hσ (Real.sqrt_nonneg _)) haL
  intro n
  exact actual_original_stopped_point_affine_of_joint_prefix P₁ hnull
    (fun u => hB₂ (min u T)) hB' hBc' hAgr (by linarith) hα' hT₀ (Nat.cast_nonneg _)
    hσ (hw n) hj hM hM₂ hMc hM₀ hY hYc hY₀ hstart hYi hMean hMC hCi hCmon
    (fun t ht => hClock t (ht.trans hT))
    (hInv.mono fun ω hω t ht => hω t ⟨ht.1,ht.2.trans (by exact_mod_cast hT)⟩)
    hPrefix hbT (isStoppingTime_physicalObservationOfTrace hA hτ)
    (fun ω => (physicalObservationOfTrace_range τ b s ω).1)
    (fun ω => (physicalObservationOfTrace_range τ b s ω).2)

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.raw_original_point_tests_at_birth_trace
