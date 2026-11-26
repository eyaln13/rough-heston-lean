import RawOriginalPointTests
import FiniteBrownianFreezing
import FocalDriftEnergy
import ActualAgePulseStoppedLaw
import ActualTwoTiltVarianceMoments
import BirthTraceAffineBirthExpectation

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston.GirsanovPort

open SHEStochastic

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 m} [F.IsComplete P] [F.IsRightContinuous]
  {A : Set Ω} {b r : ℝ≥0} {B M Y C : ℝ≥0 → Ω → ℝ} {j : ℝ → ℝ}

local notation "G" => birthTraceFiltration F b A
local notation "μ" => birthTraceLaw P A

set_option maxHeartbeats 3000000 in
/-- With the age Brownian identified by the actual focal size-bias
construction, the raw old variance inverse and its common Brownian
integral give the reverse law and all stopped energy budgets. -/
theorem actual_capped_law_on_birth_trace
    (hA : MeasurableSet[F b] A) (hPA : 0<P A) [IsProbabilityMeasure μ]
    (hB : MathFinBridge.BrownianOn P F (b+r) B)
    (hB₂ : ∀ t, MemLp (B t) 2 P) (hBm : Martingale B F P)
    (hBc : Martingale (fun t ω => B t ω ^ 2-((min t (b+r):ℝ≥0):ℝ)) F P)
    (hr : 0<r) {α κ σ ε Cenv Kocc γ η δ : ℝ}
    (hα : 1/2<α) (hα' : α<1) (hκ : 0≤κ) (hσ : 0≤σ) (hε : 0<ε)
    (hγ : 0≤γ) (hgap : 3*γ<η) (hδ : 0≤δ) (hCenv : 0≤Cenv) (hKocc : 0≤Kocc)
    (hj : ∀ s∈Ioc (0:ℝ≥0) r, AffineInputOn ((b+s:ℝ≥0):ℝ) j)
    (hM : Martingale M F P) (hM₂ : ∀ t, MemLp (M t) 2 P)
    (hMc : ∀ ω, Continuous (fun t => M t ω)) (hM₀ : M 0 =ᵐ[P] 0)
    (hY : IsStronglyPredictable F Y) (hYc : ∀ ω, Continuous (fun t => Y t ω))
    (hY₀ : ∀ t ω, 0≤Y t ω) {Y₀ : ℝ} (hstart : ∀ ω, Y 0 ω≤Y₀)
    (hY4 : ∀ t, Integrable (fun ω => Y t ω ^ 4) P) {K₄ : ℝ}
    (hY4mean : ∀ t, (∫ ω,Y t ω ^ 4 ∂P)≤K₄)
    (hMC : Martingale (fun t => M t*M t-C t) F P)
    (hCi : ∀ t, Integrable (C t) P)
    (hCmon : ∀ u t, u≤t → C u≤ᵐ[P] C t)
    (hClock : ∀ t≤b+r, C t =ᵐ[P] fun ω => ∫ u in (0:ℝ)..(t:ℝ), σ^2*Y u.toNNReal ω)
    (hInv : ∀ᵐ ω ∂P, ∀ t ∈ Ioc (0:ℝ) ((b+r:ℝ≥0):ℝ),
      M t.toNNReal ω = volterraConvolution (fractionalL α) (fun u => Y u.toNNReal ω) t +
        ∫ u in Ioc (0:ℝ) t, κ*Y u.toNNReal ω-j u)
    (hCut : HasAmplitudeCutoffIntegral F P (b+r) B M (fun t ω => σ*Real.sqrt (Y t ω)))
    {U Z X : ℝ≥0 → A → ℝ} (hZu : Martingale Z G μ) (hZb : Z 0 =ᵐ[μ] fun _ => ε)
    (hZ₂ : MemLp (Z r) 2 μ) (hZp : ∀ t ω, 0<Z t ω)
    (hu : IsStronglyPredictable G U) (hz : IsStronglyPredictable G Z)
    (hx : IsStronglyPredictable G X) (huc : ∀ ω, ContinuousOn (fun s => U s ω) (Icc 0 r))
    (hzc : ∀ ω, ContinuousOn (fun s => Z s ω) (Icc 0 r))
    (hun : ∀ t≤r, ∀ ω, 0≤U t ω) (hux : ∀ t≤r, ∀ ω, U t ω≤X t ω)
    [IsProbabilityMeasure (sizeBiasedLaw μ (Z r) ε)]
    {W : ℝ≥0 → A → ℝ} (hW : MathFinBridge.BrownianOn (sizeBiasedLaw μ (Z r) ε) G r W)
    (hWshift : ∀ᵐ ω ∂sizeBiasedLaw μ (Z r) ε, ∀ t≤r,
      W t ω = (B (b+min t r) ω-B b ω) -
        ∫ u, focalDriverDrift σ Z U X u ω ∂hestonTimeMeasure t)
    (hg₂ : Integrable (fun p : ℝ≥0 × A => (focalDriverDrift σ Z U X p.1 p.2)^2)
      ((hestonTimeMeasure r).prod (sizeBiasedLaw μ (Z r) ε)))
    (hBoundary : ∀ s∈Ioc (0:ℝ≥0) r,
      (boundaryConditionedMeasure P A).real {ω | 0<Y (b+s) ω} ≤ Kocc*(s:ℝ)^η) :
    let Q := sizeBiasedLaw μ (Z r) ε
    let env := envelopeStop r (Cenv*(r:ℝ)^(3*γ)) (clusterEnvelopeValue 0 σ (1+3*γ) U Z)
    ∃ R : Measure A, ∃ (_ : IsProbabilityMeasure R),
      R ≪ Q ∧ Nonempty (PulseStoppedLaw Q R r δ ((Cenv*Kocc/(η-3*γ))*(r:ℝ)^η)
        (Kocc*(r:ℝ)^η) env (fun ω : A => Y (b+r) ω)) := by
  let Q := sizeBiasedLaw μ (Z r) ε
  let D₀ (t : ℝ≥0) (ω : A) := B (b+t) ω-B b ω
  let D (t : ℝ≥0) := D₀ (min t r)
  let W' (t : ℝ≥0) := W (min t r)
  let Y' (t : ℝ≥0) (ω : A) := Y (b+t) ω
  let : (G).IsComplete μ := birthTraceFiltration_complete hA
  let : (G).IsRightContinuous := birthTraceFiltration_rightContinuous hA
  have hZm : Measurable (Z r) := ((hZu.stronglyAdapted r).mono ((G).le r)).measurable
  have hQP : Q≪μ := withDensity_absolutelyContinuous _ _
  have hPQ : μ≪Q := withDensity_absolutelyContinuous' (hZm.div_const ε).ennreal_ofReal.aemeasurable
    (ae_of_all _ fun ω => (ENNReal.ofReal_pos.mpr (div_pos (hZp r ω) hε)).ne')
  let : (G).IsComplete Q := ⟨fun E hE t =>
    Filtration.IsComplete.measurableSet_of_null (𝓕:=G) (hPQ hE) t⟩
  have hNull : SHE.NullCompleteFiltration.ContainsNullSets F P :=
    fun t _ h => Filtration.IsComplete.measurableSet_of_null (𝓕:=F) h t
  have hNullQ : SHE.NullCompleteFiltration.ContainsNullSets G Q :=
    fun t _ h => Filtration.IsComplete.measurableSet_of_null (𝓕:=G) h t
  have hD₀ : MathFinBridge.BrownianOn μ G r D₀ := brownianOn_birthTrace hB hA hPA
  obtain ⟨hD₂,hDm,hDc⟩ := finiteBrownianOn_frozen_martingales hD₀
  obtain ⟨hW₂,hWm,hWc⟩ := finiteBrownianOn_frozen_martingales hW
  have hW' : MathFinBridge.BrownianOn Q G r W' := finiteBrownianOn_freeze hW
  obtain ⟨PN,hPN⟩ := exists_scalarNativeFamily_of_brownianOn hB (fun E _ hE => hNull 0 E hE)
  have hYm (t : ℝ≥0) : Measurable (Y t) := ((hY.stronglyAdapted t).mono (F.le t)).measurable
  obtain ⟨Hmean,_,_,hOldMean,_,_⟩ := uniform_necessary_moments_under_two_tilts
    (P:=P) (Q:=P) (R:=P) (D₁:=fun _ => 1) (D₂:=fun _ => 1)
    measurable_const measurable_const (ae_of_all _ fun _ => zero_le_one)
    (memLp_const 1) (by simp) (by simp)
    (ae_of_all _ fun _ => zero_le_one) (memLp_const 1) hYm hY4 hY4mean
  have hYp : IsStronglyPredictable G Y' := stronglyPredictable_birthTrace hY
  have hYm' (t : ℝ≥0) : Measurable (Y' t) := ((hYp.stronglyAdapted t).mono ((G).le t)).measurable
  have hY4' := birthTrace_fourth_moment_bounded hA hPA hYm hY4 hY4mean
  have hGm := focalDriverDrift_predictable (σ:=σ) hz hu hx
  have hg : MemLp (fun p : ℝ≥0 × A => σ*U p.1 p.2/(Z p.1 p.2*Real.sqrt (X p.1 p.2))) 2
      ((hestonTimeMeasure r).prod Q) :=
    (memLp_two_iff_integrable_sq (hGm.mono (G).predictable_le_prod).aestronglyMeasurable).2 hg₂
  have hShift : ∀ᵐ ω ∂Q, ∀ t≤r, W' t ω = D t ω -
      ∫ u, σ*U u ω/(Z u ω*Real.sqrt (X u ω)) ∂hestonTimeMeasure t := by
    filter_upwards [hWshift] with ω hω t ht
    simpa only [W',D,D₀,focalDriverDrift,min_eq_left ht] using hω t ht
  apply actual_age_pulse_stopped_law_with_cap hW' hW₂ hWm hWc hr hγ hgap hδ hCenv hKocc
    hu hz hx hYp huc hzc (fun t _ => hZp t) hun hux
  intro R N τ hτ hc hcap s hs
  obtain ⟨A₀,A₁,A₂,h0,h1,h2⟩ := actual_two_tilt_variance_first_moments hε hZm
    (ae_of_all _ fun ω => (hZp r ω).le) hZ₂ hW' hNullQ hW₂ hWm hWc hδ hc hcap
    hYm' (fun t => (hY4' t).1) (fun t => (hY4' t).2)
  obtain ⟨w,hwm,hw₂,hOld⟩ := raw_original_point_tests_at_birth_trace PN hs.1 hs.2
    hNull hB₂ hBm hBc hPN hα hα' hκ hσ (hj s hs) hM hM₂ hMc hM₀ hY hYc hY₀ hstart
    (fun t => (hOldMean t).1) (fun t => (hOldMean t).2) hMC hCi hCmon hClock hInv hCut hA hτ
  let B' (t : ℝ≥0) := B (min t (b+s))
  let hB₂' (t : ℝ≥0) := hB₂ (min t (b+s))
  have hBc' : Martingale (fun t ω => B' t ω ^ 2-((min t (b+s):ℝ≥0):ℝ)) F P := by
    have ht : min (b+s) (b+r)=b+s := min_eq_left (add_le_add_right hs.2 b)
    simpa only [B',min_assoc,ht] using martingale_freeze_at hBc (b+s)
  have hD' (t : ℝ≥0) (ht : t≤s) : D t =ᵐ[μ] fun ω : A => B' (b+t) ω-B' b ω := by
    have hbt : b+t≤b+s := add_le_add_right ht b
    have hbb : b≤b+s := le_add_of_nonneg_right zero_le
    exact ae_of_all _ fun ω => by simp only [D,D₀,B',min_eq_left (ht.trans hs.2),min_eq_left hbt,min_eq_left hbb]
  have hBorn (n : ℕ) : (∫ ω : A,1-P[(fun x => Real.exp (-(n:ℝ)*Y (b+s) x))|F b] ω ∂Q)
      ≤ Kocc*(s:ℝ)^η :=
    (point_test_trace_birth_sizeBias_le hA hPA hZu
      (fun t => ae_of_all _ fun ω => (hZp t ω).le)
      hε hZb (hYm (b+s)) (hY₀ (b+s)) (Nat.cast_nonneg n)).trans (hBoundary s hs)
  exact actual_birthTrace_stopped_competitor_positive_le hA hPA hB₂' (martingale_freeze_at hBm (b+s))
    hBc' hD₂ hDm hDc hD' hW₂ hWm hWc hs.2 hQP hτ hShift hg hc hY hY₀
    (fun t => (h0 t).1) (fun t => (h0 t).2) (fun t => (h1 t).1) (fun t => (h1 t).2)
    (fun t => (h2 t).1) (fun t => (h2 t).2) hwm hw₂ hOld hBorn

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.actual_capped_law_on_birth_trace
