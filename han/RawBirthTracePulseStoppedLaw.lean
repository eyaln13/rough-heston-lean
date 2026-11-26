import ActualCappedLawOnBirthTrace
import PositiveFocalMassVersion
import RawFocalFirstTilt

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston.GirsanovPort

open SHEStochastic

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 m} [F.IsComplete P] [F.IsRightContinuous]
  {A : Set Ω} {b r : ℝ≥0} {B M Y C : ℝ≥0 → Ω → ℝ} {j : ℝ → ℝ}

local notation "G" => birthTraceFiltration F b A
local notation "μ" => birthTraceLaw P A

omit [IsProbabilityMeasure P] [F.IsComplete P] [F.IsRightContinuous] in
private theorem envelope_path_eq {S : Type*} {E E' : ℝ≥0 → S → ℝ}
    (r : ℝ≥0) (c : ℝ) (ω : S) (h : ∀ t, E t ω=E' t ω) :
    envelopeStop r c E ω=envelopeStop r c E' ω := by
  have hS : {t : ℝ≥0 | ⊥≤t ∧ E t ω∈Ioi c}={t : ℝ≥0 | ⊥≤t ∧ E' t ω∈Ioi c} := by
    ext t
    simp only [mem_ofPred_eq,h]
  have hE : (∃ t : ℝ≥0, ⊥≤t ∧ E t ω∈Ioi c) ↔ (∃ t : ℝ≥0, ⊥≤t ∧ E' t ω∈Ioi c) := by
    constructor
    · rintro ⟨t,ht,he⟩
      exact ⟨t,ht,(h t) ▸ he⟩
    · rintro ⟨t,ht,he⟩
      exact ⟨t,ht,(h t).symm ▸ he⟩
  unfold envelopeStop leastGT hittingAfter
  by_cases he : ∃ t : ℝ≥0, ⊥≤t ∧ E t ω∈Ioi c
  · rw [ite_eq_left he,ite_eq_left (hE.mp he),hS]
  · rw [ite_eq_right he,ite_eq_right (he ∘ hE.mpr)]

set_option maxHeartbeats 3700000 in
/-- The fixed-mesh physical Brownian and bracket data give the whole
capped law on the genuine birth trace. The only supplied occupation
input is the original zero-conditioned boundary estimate. -/
theorem raw_birth_trace_pulse_stopped_law
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
    {d : ℝ} (hd : 0<d) (hdr : d≤(r:ℝ))
    {J U Ccl : ℝ≥0 → A → ℝ} {Uphysical Xphysical Mphysical FocalClock : ℝ≥0 → Ω → ℝ}
    (hPulse : FractionalPulseProcess μ G r α κ (σ^2/2) ε d J U Ccl)
    (hCc : ∀ ω, Continuous (fun t => Ccl t ω))
    (hCmonCl : ∀ᵐ ω ∂μ, Monotone (fun t => Ccl t ω))
    (hUJ : ∀ t (ω : A), U t ω=Uphysical (b+t) ω)
    (hJ : ∀ᵐ ω ∂μ, ∀ t≤r, J t ω=Mphysical (b+t) ω-Mphysical b ω)
    (hXp : IsStronglyPredictable F Xphysical)
    (hParts : ∀ t≤r, ∀ ω : A, U t ω≤Xphysical (b+t) ω)
    (hUint : Integrable (Function.uncurry U) ((hestonTimeMeasure r).prod μ))
    (hMold : Martingale Mphysical F P) (hMold₂ : ∀ t, MemLp (Mphysical t) 2 P)
    (hMixed : Martingale (fun t => B t*Mphysical t-FocalClock t) F P)
    (hDensity : IsStronglyPredictable F (focalBracketDensity σ Uphysical Xphysical))
    (hiDensity : ∀ᵐ ω ∂P, IntervalIntegrable
      (fun u : ℝ => focalBracketDensity σ Uphysical Xphysical u.toNNReal ω) volume 0 ((b+r:ℝ≥0):ℝ))
    (hFocalClock : ∀ t≤b+r, FocalClock t =ᵐ[P] fun ω => ∫ u in (0:ℝ)..(t:ℝ),
      focalBracketDensity σ Uphysical Xphysical u.toNNReal ω)
    (hBoundary : ∀ s∈Ioc (0:ℝ≥0) r,
      (boundaryConditionedMeasure P A).real {ω | 0<Y (b+s) ω} ≤ Kocc*(s:ℝ)^η) :
    let Z (t : ℝ≥0) := fractionalPulseMass ε J (min t r)
    let Q := sizeBiasedLaw μ (fractionalPulseMass ε J r) ε
    let env := envelopeStop r (Cenv*(r:ℝ)^(3*γ)) (clusterEnvelopeValue 0 σ (1+3*γ) U Z)
    ∃ R : Measure A, ∃ (_ : IsProbabilityMeasure R),
      Nonempty (PulseStoppedLaw Q R r δ ((Cenv*Kocc/(η-3*γ))*(r:ℝ)^η)
        (Kocc*(r:ℝ)^η) env (fun ω : A => Y (b+r) ω)) := by
  let Z (t : ℝ≥0) := fractionalPulseMass ε J (min t r)
  let X (t : ℝ≥0) (ω : A) := Xphysical (b+t) ω
  let Q := sizeBiasedLaw μ (Z r) ε
  let : (G).IsComplete μ := birthTraceFiltration_complete hA
  let : (G).IsRightContinuous := birthTraceFiltration_rightContinuous hA
  have hTilt := raw_focal_first_tilt_on_birth_trace hA hPA hB hBm hB₂
    (by linarith : 0<α) hα' hκ hε hd hdr hPulse hCc hCmonCl hUJ hJ hXp hParts
    hUint hMold hMold₂ hMixed hDensity hiDensity hFocalClock
  obtain ⟨hZm,hZb,hPos,hZ₂,hQ,hQP,hPQ,hg₂,W,hW,hShift⟩ := hTilt
  let : IsProbabilityMeasure Q := hQ
  let : (G).IsComplete Q := ⟨fun E hE t =>
    Filtration.IsComplete.measurableSet_of_null (𝓕:=G) (hPQ hE) t⟩
  have hZc (ω : A) : Continuous (fun t => Z t ω) := continuous_const.add
    ((hPulse.martingale_continuous ω).comp (continuous_id.min continuous_const))
  have hz : IsStronglyPredictable G Z :=
    SHE.ContinuousPredictable.stronglyMeasurable _ _ hZm.stronglyAdapted hZc
  have hu : IsStronglyPredictable G U :=
    SHE.ContinuousPredictable.stronglyMeasurable _ _ hPulse.variance_adapted hPulse.variance_continuous
  have hx : IsStronglyPredictable G X := stronglyPredictable_birthTrace hXp
  obtain ⟨Z',hZ'm,hZ'p,hZ'c,hZ'pos,hZ'eq⟩ := exists_everywhere_positive_focal_mass hZm hZc hPos
  have hZ'r : Z' r =ᵐ[μ] Z r := hZ'eq.mono fun _ h => h r
  let Q' := sizeBiasedLaw μ (Z' r) ε
  have hQ' : Q'=Q := by
    apply withDensity_congr_ae
    filter_upwards [hZ'r] with ω hω
    rw [hω]
  let : IsProbabilityMeasure Q' := hQ'.symm ▸ hQ
  have hW' : MathFinBridge.BrownianOn Q' G r W := hQ'.symm ▸ hW
  have hShift' : ∀ᵐ ω ∂Q', ∀ t≤r,
      W t ω = (B (b+min t r) ω-B b ω) -
        ∫ u, focalDriverDrift σ Z' U X u ω ∂hestonTimeMeasure t := by
    rw [hQ']
    filter_upwards [hShift,hQP.ae_le hZ'eq] with ω hω he t ht
    have he' (u : ℝ≥0) : focalDriverDrift σ Z' U X u ω=focalDriverDrift σ Z U X u ω := by
      simp only [focalDriverDrift,he,Z]
    simpa only [he',Z,X] using hω t ht
  have hg' : Integrable (fun p : ℝ≥0 × A => (focalDriverDrift σ Z' U X p.1 p.2)^2)
      ((hestonTimeMeasure r).prod Q') := by
    rw [hQ']
    apply hg₂.congr
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae (hQP.ae_le hZ'eq)] with p hp
    simp only [focalDriverDrift,hp,Z,X]
  have hZb' : Z' 0 =ᵐ[μ] fun _ => ε := by
    filter_upwards [hZ'eq,hZb] with ω he h₀
    exact (he 0).trans h₀
  obtain ⟨R,hR,hRQ,⟨law⟩⟩ := actual_capped_law_on_birth_trace hA hPA hB hB₂ hBm hBc
    hr hα hα' hκ hσ hε hγ hgap hδ hCenv hKocc hj hM hM₂ hMc hM₀ hY hYc hY₀ hstart hY4 hY4mean
    hMC hCi hCmon hClock hInv hCut hZ'm hZb'
    ((hZ₂ r).ae_eq hZ'r.symm) hZ'pos hu hZ'p hx (fun ω => (hPulse.variance_continuous ω).continuousOn)
    (fun ω => (hZ'c ω).continuousOn) (fun t _ => hPulse.variance_nonnegative t) hParts hW' hShift' hg' hBoundary
  let env := envelopeStop r (Cenv*(r:ℝ)^(3*γ)) (clusterEnvelopeValue 0 σ (1+3*γ) U Z)
  let env' := envelopeStop r (Cenv*(r:ℝ)^(3*γ)) (clusterEnvelopeValue 0 σ (1+3*γ) U Z')
  change R≪Q' at hRQ
  change PulseStoppedLaw Q' R r δ ((Cenv*Kocc/(η-3*γ))*(r:ℝ)^η)
    (Kocc*(r:ℝ)^η) env' (fun ω : A => Y (b+r) ω) at law
  rw [hQ'] at hRQ law
  have hm : Measurable env := measurable_finite_stop (envelopeStop_isStoppingTime Q r _
    (clusterEnvelopeValue_predictable 0 σ (1+3*γ) hu hz))
  have hm' : Measurable env' := measurable_finite_stop (envelopeStop_isStoppingTime Q r _
    (clusterEnvelopeValue_predictable 0 σ (1+3*γ) hu hZ'p))
  have he : env=ᵐ[Q] env' := by
    filter_upwards [hQP.ae_le hZ'eq] with ω hω
    apply envelope_path_eq
    intro t
    simp only [clusterEnvelopeValue,hω,Z]
  have hZfinal : Z r=fractionalPulseMass ε J r := by simp [Z]
  change ∃ R : Measure A, ∃ (_ : IsProbabilityMeasure R), Nonempty
    (PulseStoppedLaw (sizeBiasedLaw μ (fractionalPulseMass ε J r) ε) R r δ
      ((Cenv*Kocc/(η-3*γ))*(r:ℝ)^η) (Kocc*(r:ℝ)^η) env (fun ω : A=>Y (b+r) ω))
  rw [←hZfinal]
  exact ⟨R,hR,⟨PulseStoppedLaw_change_envelope law hm hm' he hRQ⟩⟩

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.raw_birth_trace_pulse_stopped_law
