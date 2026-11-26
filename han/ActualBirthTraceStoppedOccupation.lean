import BirthTraceAffineRow
import ActualStoppedAffineTransport

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston.GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 m} {A : Set Ω} {b s H : ℝ≥0}

local notation "G" => birthTraceFiltration F b A
local notation "μ" => birthTraceLaw P A
local notation "ν" => jointPredictableMeasure F P (b+s)

set_option maxHeartbeats 2400000 in
/-- The original physical affine point tests produce the actual stopped
competitor occupation estimate on the birth trace after both drift
changes. The Riccati length is the physical observation time b+s. -/
theorem actual_birthTrace_stopped_competitor_positive_le
    (hA : MeasurableSet[F b] A) (hPA : 0<P A)
    [IsProbabilityMeasure μ] {Q R : Measure A} [IsProbabilityMeasure Q]
    {B : ℝ≥0 → Ω → ℝ} {D W N U Z X : ℝ≥0 → A → ℝ} {Y : ℝ≥0 → Ω → ℝ}
    (hB₂ : ∀ t, MemLp (B t) 2 P) (hB : Martingale B F P)
    (hBc : Martingale (fun t ω => B t ω ^ 2-((min t (b+s):ℝ≥0):ℝ)) F P)
    (hD₂ : ∀ t, MemLp (D t) 2 μ) (hD : Martingale D G μ)
    (hDc : Martingale (fun t ω => D t ω ^ 2-((min t H:ℝ≥0):ℝ)) G μ)
    (hClock : ∀ t≤s, D t =ᵐ[μ] (fun ω : A => B (b+t) ω-B b ω))
    (hW₂ : ∀ t, MemLp (W t) 2 Q) (hW : Martingale W G Q)
    (hWc : Martingale (fun t ω => W t ω ^ 2-((min t H:ℝ≥0):ℝ)) G Q)
    (hs : s≤H) (hQP : Q ≪ μ) {σ δ d : ℝ} {τ : A → ℝ≥0}
    (hτ : IsStoppingTime G (fun ω => (τ ω:WithTop ℝ≥0)))
    (hQshift : ∀ᵐ ω ∂Q, ∀ t ≤ H, W t ω = D t ω -
      ∫ r, σ*U r ω/(Z r ω*Real.sqrt (X r ω)) ∂hestonTimeMeasure t)
    (hDrift : MemLp (fun p : ℝ≥0 × A => σ*U p.1 p.2/(Z p.1 p.2*Real.sqrt (X p.1 p.2)))
      2 ((hestonTimeMeasure H).prod Q))
    (hc : IsStoppedDriftChange (F:=G) (H:=H) 0 δ
      (controlThrough (competitorAfterBirth 0 σ U Z X (fun t (ω : A) => Y (b+t) ω)) τ) hW₂ R N)
    (hY : IsStronglyPredictable F Y) (hY₀ : ∀ t ω, 0≤Y t ω)
    (hYi : ∀ t, Integrable (fun ω : A => Y (b+t) ω) μ) {K₀ : ℝ}
    (hYmean : ∀ t, (∫ ω : A,Y (b+t) ω ∂μ)≤K₀)
    (hYiQ : ∀ t, Integrable (fun ω : A => Y (b+t) ω) Q) {K₁ : ℝ}
    (hYmeanQ : ∀ t, (∫ ω : A,Y (b+t) ω ∂Q)≤K₁)
    (hYiR : ∀ t, Integrable (fun ω : A => Y (b+t) ω) R) {K₂ : ℝ}
    (hYmeanR : ∀ t, (∫ ω : A,Y (b+t) ω ∂R)≤K₂)
    {w : ℕ → ℝ → ℝ} (hwm : ∀ n, Measurable (w n))
    (hw₂ : ∀ n, IntegrableOn (fun t => (w n t)^2) (Ioc (0:ℝ) (s:ℝ)))
    (hOld : ∀ n : ℕ, ∃ L : ℝ≥0 → Ω → ℝ, IsStronglyPredictable F L ∧
      (∀ t ω, L t ω ∈ Icc (0:ℝ) 1) ∧
      L b =ᵐ[P] P[(fun ω => Real.exp (-(n:ℝ)*Y (b+s) ω)) | F b] ∧
      (∀ᵐ ω ∂P, physicalObservationOfTrace τ b s ω = b+s →
        1-L (physicalObservationOfTrace τ b s ω) ω = 1-Real.exp (-(n:ℝ)*Y (b+s) ω)) ∧
      ∃ u : Lp ℝ 2 ν, ⇑u =ᵐ[ν] Function.uncurry
          (stoppedAffineTestRow (fun t => σ*w n (((b+s:ℝ≥0):ℝ)-(t:ℝ))) L Y b
            (physicalObservationOfTrace τ b s)) ∧
        (fun ω => 1-L (physicalObservationOfTrace τ b s ω) ω) =ᵐ[P]
          (fun ω => 1-L b ω + jointItoIntegralCLM (b+s) hB₂ u ω))
    (hBorn : ∀ n : ℕ, (∫ ω : A,1-P[(fun x => Real.exp (-(n:ℝ)*Y (b+s) x))|F b] ω ∂Q)≤d) :
    R.real {ω : A | s≤τ ω ∧ 0<Y (b+s) ω} ≤ d := by
  let : IsProbabilityMeasure R := hc.1
  choose L hL hRange hBornL hTerm u hu hRep using hOld
  let τ' (ω : A) := min s (τ ω)
  have hτ' : IsStoppingTime G (fun ω => (τ' ω:WithTop ℝ≥0)) := affine_observation_stop hτ
  have hτ's (ω : A) : τ' ω≤s := min_le_left _ _
  let k (n : ℕ) (t : ℝ≥0) := σ*w n ((s:ℝ)-(t:ℝ))
  let kH (n : ℕ) := (Ioc (0:ℝ≥0) s).indicator (k n)
  have hk (n : ℕ) : Measurable (k n) :=
    measurable_const.mul ((hwm n).comp (measurable_const.sub measurable_subtype_coe))
  have hkH (n : ℕ) : Measurable (kH n) := (hk n).indicator measurableSet_Ioc
  have hk₂ (n : ℕ) : MemLp (kH n) 2 (hestonTimeMeasure H) :=
    reflected_riccati_zero_extension_memLp_two hs (hwm n) (hw₂ n) σ
  let Y' (t : ℝ≥0) (ω : A) := Y (b+t) ω
  let L' (n : ℕ) (t : ℝ≥0) (ω : A) := L n (b+t) ω
  have hLa (n : ℕ) : IsStronglyPredictable G (L' n) := stronglyPredictable_birthTrace (hL n)
  have hYa : IsStronglyPredictable G Y' := stronglyPredictable_birthTrace hY
  let a (n : ℕ) (ω : A) := 1-L n b ω
  let test (n : ℕ) (ω : A) := 1-L n (b+τ' ω) ω
  let f (n : ℕ) := Function.uncurry (stoppedAffineTestRow (kH n) (L' n) Y' 0 τ')
  let f' (n : ℕ) := Function.uncurry (stoppedAffineTestRow (k n) (L' n) Y' 0 τ')
  have hfp (n : ℕ) : StronglyMeasurable[(G).predictable] (f n) :=
    stoppedAffineTestRow_predictable (hkH n) hτ' (hLa n) hYa
  have hfP (n : ℕ) : MemLp (f n) 2 (jointPredictableMeasure G μ H) :=
    stoppedAffineTestRow_memLp (hkH n) (hk₂ n) hτ' (hLa n) hYa (fun _ _ => hY₀ _ _) hYi hYmean
  have hfQ (n : ℕ) : MemLp (f n) 2 (jointPredictableMeasure G Q H) :=
    stoppedAffineTestRow_memLp (hkH n) (hk₂ n) hτ' (hLa n) hYa (fun _ _ => hY₀ _ _) hYiQ hYmeanQ
  have hfR (n : ℕ) : MemLp (f n) 2 (jointPredictableMeasure G R H) :=
    stoppedAffineTestRow_memLp (hkH n) (hk₂ n) hτ' (hLa n) hYa (fun _ _ => hY₀ _ _) hYiR hYmeanR
  have hfS (n : ℕ) : MemLp (f' n) 2 (jointPredictableMeasure G μ s) :=
    stoppedAffineTestRow_memLp (hk n) (reflected_riccati_memLp_two s (hwm n) (hw₂ n) σ) hτ'
      (hLa n) hYa (fun _ _ => hY₀ _ _) hYi hYmean
  have hfEq (n : ℕ) : f n=f' n := congrArg Function.uncurry (stoppedAffineTestRow_zero_extension hτ's)
  have hactive (n : ℕ) (t : ℝ≥0) (ω : A) (hn : f n (t,ω)≠0) :
      0<t ∧ t≤τ ω ∧ 0<Y' t ω := by
    have h := stoppedAffineTestRow_active t ω hn
    exact ⟨h.1,h.2.1.trans (min_le_right _ _),h.2.2⟩
  have ha (n : ℕ) : StronglyMeasurable[G 0] (a n) := by
    have he (ω : A) : a n ω = 1-L' n 0 ω := by simp [a,L']
    exact (funext he).symm ▸ (stronglyMeasurable_const.sub ((hLa n).stronglyAdapted 0))
  have hai (n : ℕ) : Integrable (a n) R := by
    refine Integrable.of_bound ((ha n).mono ((G).le 0)).aestronglyMeasurable 1 (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (sub_nonneg.mpr (hRange n b ω).2)]
    exact sub_le_self _ (hRange n b ω).1
  have hrep (n : ℕ) : test n =ᵐ[μ] fun ω =>
      a n ω + jointItoIntegralCLM H hD₂ ((hfP n).toLp (f n)) ω := by
    let D' (t : ℝ≥0) := D (min t s)
    let hD₂' (t : ℝ≥0) := hD₂ (min t s)
    have hD' : Martingale D' G μ := martingale_freeze_at hD s
    have hDc' : Martingale (fun t ω => D' t ω ^ 2-((min t s:ℝ≥0):ℝ)) G μ := by
      simpa only [D',min_assoc,min_eq_left hs] using martingale_freeze_at hDc s
    have hClock' (t : ℝ≥0) (ht : t≤s) : D' t =ᵐ[μ] (fun ω : A => B (b+t) ω-B b ω) := by
      simpa only [D',min_eq_left ht] using hClock t ht
    have h := birthTrace_stopped_affine_row hA hPA hB₂ hB hBc hD₂' hD' hDc' hClock'
      (u n) ((hfS n).toLp (f' n)) (hu n) (hfS n).coeFn_toLp (hRep n)
    have hZero (p : ℝ≥0 × A) (hp : s<p.1) : f n p=0 := by
      change stoppedAffineTestRow (kH n) (L' n) Y' 0 τ' p.1 p.2=0
      rw [stoppedAffineTestRow,ite_eq_right (fun hz => hp.not_ge (hz.2.trans (hτ's _)))]
    have hv : ⇑((hfS n).toLp (f' n)) =ᵐ[jointPredictableMeasure G μ s] f n := by
      rw [hfEq n]
      exact (hfS n).coeFn_toLp
    have he := jointIto_short_horizon_eq_of_supported_row hs hD₂ hD hDc hZero hv (hfP n).coeFn_toLp
    change jointItoIntegralCLM s hD₂' ((hfS n).toLp (f' n)) = _ at he
    simpa only [he] using h
  have hSub : QuasiMeasurePreserving (Subtype.val : A → Ω) μ P :=
    ⟨measurable_subtype_coe,Measure.absolutelyContinuous_of_le_smul (birthTrace_subtype_dom hA)⟩
  have hNonneg (n : ℕ) : ∀ᵐ ω ∂μ, 0≤test n ω :=
    ae_of_all _ fun ω => sub_nonneg.mpr (hRange n (b+τ' ω) ω).2
  have hTerminal (n : ℕ) : ∀ᵐ ω ∂μ, s≤τ ω → test n ω=1-Real.exp (-(n:ℝ)*Y' s ω) := by
    filter_upwards [hSub.ae (hTerm n)] with ω hω h
    have ht : physicalObservationOfTrace τ b s ω=b+s :=
      (physicalObservationOfTrace_eq τ b s ω).trans (by rw [min_eq_left h])
    simpa only [physicalObservationOfTrace_eq] using hω ht
  have hborn (n : ℕ) : (∫ ω,a n ω ∂Q)≤d := by
    refine (le_of_eq (integral_congr_ae ?_)).trans (hBorn n)
    filter_upwards [(hQP.ae_le) (hSub.ae (hBornL n))] with ω hω
    change 1-L n b ω = _
    rw [hω]
  exact stopped_occupation_of_original_affine_representation hD hW hDc hWc hQP
    (measurable_finite_stop hτ) hQshift hDrift hc
    (((hYa.stronglyAdapted s).mono ((G).le s)).measurable) (fun _ => hY₀ _ _)
    hfp hfP hfQ hfR hactive ha hai hrep hNonneg hTerminal hborn

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.actual_birthTrace_stopped_competitor_positive_le
