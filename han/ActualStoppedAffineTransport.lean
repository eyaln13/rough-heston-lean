import ActualStoppedPointAffine
import AffineObservationClock
import StoppedAffineTestTransport

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston.GirsanovPort

open SHEStochastic SHE SHE.PredictableL2

variable {Ω : Type*} [m : MeasurableSpace Ω] {P Q R : Measure Ω}
  [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {F : Filtration ℝ≥0 m} [Approximable F P] {H b s : ℝ≥0}
  {B W N U Z X Y M C : ℝ≥0 → Ω → ℝ}
  {hB₂ : ∀ t, MemLp (B t) 2 P} {hW₂ : ∀ t, MemLp (W t) 2 Q}

set_option maxHeartbeats 2250000 in
/-- The stopped positivity estimate for an actual fractional competitor
follows from both Brownian drift changes and the original birth-law
conditional Laplace bound. The observation time can be shorter than the
common Brownian horizon. -/
theorem actual_stopped_competitor_positive_le
    (A : FiniteScalarIto.Family F P H Unit)
    (hnull : NullCompleteFiltration.ContainsNullSets F P)
    (hB : Martingale B F P) (hW : Martingale W F Q)
    (hBclock : Martingale (fun t ω => B t ω^2 - ((min t H : ℝ≥0):ℝ)) F P)
    (hWclock : Martingale (fun t ω => W t ω^2 - ((min t H : ℝ≥0):ℝ)) F Q)
    (hAgree : ∀ t ≤ H, A.W () t =ᵐ[P] B t)
    (hQP : Q ≪ P) {α κ σ δ d : ℝ} {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime F (fun ω => (τ ω:WithTop ℝ≥0))) (hτm : Measurable τ)
    (hτb : ∀ ω, b ≤ τ ω) (hbs : b<s) (hs : s≤H)
    (hQshift : ∀ᵐ ω ∂Q, ∀ t ≤ H, W t ω = B t ω -
      ∫ r, σ*U r ω/(Z r ω*Real.sqrt (X r ω)) ∂hestonTimeMeasure t)
    (hDrift : MemLp (fun p : ℝ≥0 × Ω => σ*U p.1 p.2/(Z p.1 p.2*Real.sqrt (X p.1 p.2)))
      2 ((hestonTimeMeasure H).prod Q))
    (hc : IsStoppedDriftChange (F:=F) (H:=H) b δ
      (controlThrough (competitorAfterBirth b σ U Z X Y) τ) hW₂ R N)
    (hα : 0<α) (hα' : α<1) (hσ : 0≤σ) {w : ℕ → ℝ → ℝ} {j : ℝ → ℝ}
    (hw : ∀ n : ℕ, AffineRiccatiTestOn α κ (σ^2/2) (n:ℝ) (s:ℝ) (w n) (fun _ => 0))
    (hj : AffineInputOn (s:ℝ) j)
    (hM : Martingale M F P) (hM₂ : ∀ t, MemLp (M t) 2 P)
    (hMc : ∀ ω, Continuous (fun t => M t ω)) (hM₀ : M 0 =ᵐ[P] 0)
    (hY : IsStronglyPredictable F Y) (hYc : ∀ ω, Continuous (fun t => Y t ω))
    (hY₀ : ∀ t ω, 0≤Y t ω) {Y₀ : ℝ} (hstart : ∀ ω, Y 0 ω≤Y₀)
    (hYi : ∀ t, Integrable (Y t) P) {A₀ : ℝ} (hMean : ∀ t, (∫ ω,Y t ω ∂P)≤A₀)
    (hYiQ : ∀ t, Integrable (Y t) Q) {A₁ : ℝ} (hMeanQ : ∀ t, (∫ ω,Y t ω ∂Q)≤A₁)
    (hYiR : ∀ t, Integrable (Y t) R) {A₂ : ℝ} (hMeanR : ∀ t, (∫ ω,Y t ω ∂R)≤A₂)
    (hMC : Martingale (fun t => M t*M t-C t) F P)
    (hCi : ∀ t, Integrable (C t) P)
    (hCmon : ∀ r t, r≤t → C r≤ᵐ[P] C t)
    (hClock : ∀ t≤s, C t =ᵐ[P] fun ω => ∫ r in (0:ℝ)..(t:ℝ), σ^2*Y r.toNNReal ω)
    (hInv : ∀ᵐ ω ∂P, ∀ r ∈ Ioc (0:ℝ) (s:ℝ),
      M r.toNNReal ω = volterraConvolution (fractionalL α) (fun u => Y u.toNNReal ω) r +
        ∫ u in Ioc (0:ℝ) r, κ*Y u.toNNReal ω-j u)
    (hMPrefix : let ha₂ := (sqrt_variance_memLp_joint H hY hY₀ hYi hMean).const_mul σ
      ∀ r≤s, M r =ᵐ[P] jointItoIntegralCLM H hB₂ (jointAmplitudeSectionLp (𝒢:=F) (a:=fun t ω => σ*Real.sqrt (Y t ω)) r ha₂))
    (hBirth : ∀ n : ℕ, (∫ ω,1-P[(fun ω => Real.exp (-(n:ℝ)*Y s ω))|F b] ω ∂Q)≤d) :
    R.real {ω | s≤τ ω ∧ 0<Y s ω} ≤ d := by
  let : IsProbabilityMeasure R := hc.1
  let A' := truncateScalarNativeFamily A hs
  let B' (t : ℝ≥0) := B (min t s)
  let hB₂' (t : ℝ≥0) := hB₂ (min t s)
  have hB' : Martingale B' F P := martingale_freeze_at hB s
  have hBclock' : Martingale (fun t ω => B' t ω^2 - ((min t s : ℝ≥0):ℝ)) F P := by
    simpa only [B',min_assoc,min_eq_left hs] using martingale_freeze_at hBclock s
  have hAgree' (t : ℝ≥0) (ht : t≤s) : A'.W () t =ᵐ[P] B' t := by
    change A.W () t =ᵐ[P] B (min t s)
    rw [min_eq_left ht]
    exact hAgree t (ht.trans hs)
  have hMPrefix' : let ha₂ := (sqrt_variance_memLp_joint s hY hY₀ hYi hMean).const_mul σ
      ∀ r≤s, M r =ᵐ[P] jointItoIntegralCLM s hB₂' (jointAmplitudeSectionLp (𝒢:=F) (a:=fun t ω => σ*Real.sqrt (Y t ω)) r ha₂) := by
    intro ha₂ r hr
    let ha₂H := (sqrt_variance_memLp_joint H hY hY₀ hYi hMean).const_mul σ
    let g := (Ioc (0:ℝ≥0) r ×ˢ (univ : Set Ω)).indicator
      (Function.uncurry (fun t ω => σ*Real.sqrt (Y t ω)))
    have hz (p : ℝ≥0 × Ω) (hp : s<p.1) : g p=0 := by
      have hn : p ∉ Ioc (0:ℝ≥0) r ×ˢ (univ : Set Ω) := fun h => hp.not_ge (h.1.2.trans hr)
      exact indicator_of_notMem hn _
    rw [jointIto_short_horizon_eq_of_supported_row hs hB₂ hB hBclock hz
      (jointAmplitudeSectionLp_ae (𝒢:=F) (a:=fun t ω => σ*Real.sqrt (Y t ω)) r ha₂) (jointAmplitudeSectionLp_ae (𝒢:=F) (a:=fun t ω => σ*Real.sqrt (Y t ω)) r ha₂H)]
    exact hMPrefix r hr
  let τ' (ω : Ω) := min s (τ ω)
  have hτ' : IsStoppingTime F (fun ω => (τ' ω:WithTop ℝ≥0)) := affine_observation_stop hτ
  have hb' (ω : Ω) : b≤τ' ω := le_min hbs.le (hτb ω)
  have hs' (ω : Ω) : τ' ω≤s := min_le_left _ _
  let k (n : ℕ) (t : ℝ≥0) := σ*w n ((s:ℝ)-(t:ℝ))
  let kH (n : ℕ) := (Ioc (0:ℝ≥0) s).indicator (k n)
  have hk (n : ℕ) : Measurable (k n) :=
    measurable_const.mul ((hw n).solution_measurable.comp (measurable_const.sub measurable_subtype_coe))
  have hkH (n : ℕ) : Measurable (kH n) := (hk n).indicator measurableSet_Ioc
  have hk₂ (n : ℕ) : MemLp (kH n) 2 (hestonTimeMeasure H) :=
    reflected_riccati_zero_extension_memLp_two hs (hw n).solution_measurable (hw n).solution_sq_integrable σ
  have hTests (n : ℕ) := actual_original_stopped_point_affine_of_joint_prefix A'
    hnull hB₂' hB' hBclock' hAgree' hα hα' (zero_le.trans_lt hbs) (Nat.cast_nonneg n)
    hσ (hw n) hj hM hM₂ hMc hM₀ hY hYc hY₀ hstart hYi hMean hMC hCi hCmon hClock hInv hMPrefix'
    hbs hτ' hb' hs'
  choose L hL hRange hLbirth hLterminal fS hfS hS using hTests
  let test (n : ℕ) (ω : Ω) := 1-L n (τ' ω) ω
  let a (n : ℕ) (ω : Ω) := 1-L n b ω
  let f (n : ℕ) := Function.uncurry (stoppedAffineTestRow (kH n) (L n) Y b τ')
  have hfp (n : ℕ) : StronglyMeasurable[F.predictable] (f n) :=
    stoppedAffineTestRow_predictable (hkH n) hτ' (hL n) hY
  have hfP (n : ℕ) : MemLp (f n) 2 (jointPredictableMeasure F P H) :=
    stoppedAffineTestRow_memLp (hkH n) (hk₂ n) hτ' (hL n) hY hY₀ hYi hMean
  have hfQ (n : ℕ) : MemLp (f n) 2 (jointPredictableMeasure F Q H) :=
    stoppedAffineTestRow_memLp (hkH n) (hk₂ n) hτ' (hL n) hY hY₀ hYiQ hMeanQ
  have hfR (n : ℕ) : MemLp (f n) 2 (jointPredictableMeasure F R H) :=
    stoppedAffineTestRow_memLp (hkH n) (hk₂ n) hτ' (hL n) hY hY₀ hYiR hMeanR
  have hactive (n : ℕ) (t : ℝ≥0) (ω : Ω) (hn : f n (t,ω)≠0) :
      b<t ∧ t≤τ ω ∧ 0<Y t ω := by
    have h := stoppedAffineTestRow_active t ω hn
    exact ⟨h.1,h.2.1.trans (min_le_right _ _),h.2.2⟩
  have ha (n : ℕ) : StronglyMeasurable[F b] (a n) :=
    stronglyMeasurable_const.sub ((hL n).stronglyAdapted b)
  have hai (n : ℕ) : Integrable (a n) R := by
    refine Integrable.of_bound ((ha n).mono (F.le b)).aestronglyMeasurable 1 (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (sub_nonneg.mpr (hRange n b ω).2)]
    exact sub_le_self _ (hRange n b ω).1
  have hrep (n : ℕ) : test n =ᵐ[P] fun ω =>
      a n ω + jointItoIntegralCLM H hB₂ ((hfP n).toLp (f n)) ω := by
    have hfsmall : ⇑(fS n) =ᵐ[jointPredictableMeasure F P s] f n := by
      simpa only [f, kH, stoppedAffineTestRow_zero_extension hs'] using hfS n
    have hZero (p : ℝ≥0 × Ω) (hp : s<p.1) : f n p=0 := by
      change stoppedAffineTestRow (kH n) (L n) Y b τ' p.1 p.2=0
      rw [stoppedAffineTestRow,ite_eq_right (fun h => hp.not_ge (h.2.trans (hs' _)))]
    have he := jointIto_short_horizon_eq_of_supported_row hs hB₂ hB hBclock hZero
      hfsmall (hfP n).coeFn_toLp
    change jointItoIntegralCLM s hB₂' (fS n) = _ at he
    simpa only [he] using hS n
  have hNonneg (n : ℕ) : ∀ᵐ ω ∂P, 0≤test n ω :=
    ae_of_all _ fun ω => sub_nonneg.mpr (hRange n (τ' ω) ω).2
  have hTerminal (n : ℕ) : ∀ᵐ ω ∂P, s≤τ ω →
      test n ω=1-Real.exp (-(n:ℝ)*Y s ω) := by
    filter_upwards [hLterminal n] with ω hω h
    exact hω (min_eq_left h)
  have hborn (n : ℕ) : (∫ ω,a n ω ∂Q)≤d := by
    refine (le_of_eq (integral_congr_ae ?_)).trans (hBirth n)
    filter_upwards [hQP.ae_eq (hLbirth n)] with ω hω
    change 1-L n b ω = _
    rw [hω]
  exact stopped_occupation_of_original_affine_representation hB hW hBclock hWclock hQP hτm
    hQshift hDrift hc (((hY.stronglyAdapted s).mono (F.le s)).measurable) (hY₀ s)
    hfp hfP hfQ hfR hactive ha hai hrep hNonneg hTerminal hborn

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.actual_stopped_competitor_positive_le
