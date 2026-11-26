import FocalAuxiliaryBirthTrace
import FocalPulseTraceClock

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

open GirsanovPort

/-- Assemble the age-recentered auxiliary unit clock, the orthogonal
physical pulse bracket, and the actual inverse pulse on their common
completed birth trace. All processes are frozen at the focal horizon. -/
theorem focalPulseDynamics_onBirthTrace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {A : Set Ω} {b H K T : ℝ≥0}
    {α κ σ ε d : ℝ} {M U C W J : ℝ≥0→Ω→ℝ}
    (hA : MeasurableSet[F b] A) (hp : 0<P A) (hH : H≤K) (hT : b+H≤T)
    (hPulse : FractionalPulseProcess P (pulseAgeFiltration F b) K α κ (σ^2/2) ε d M U C)
    (hC : ∀ᵐ ω ∂P,Continuous (fun t => C t ω))
    {D : ℝ≥0∞} (hD : D≠∞) (hFourth : ∀ t≤H,eLpNorm (U t) 4 P≤D)
    (hM : ∀ t≤H,M t=ᵐ[P] fun ω => J (b+t) ω-J b ω)
    (hW : Martingale W F P) (hJ : Martingale J F P)
    (hW₂ : ∀ t,MemLp (W t) 2 P) (hJ₂ : ∀ t,MemLp (J t) 2 P)
    (hWc : ∀ᵐ ω ∂P,Continuous (fun t => W t ω))
    (hWsq : Martingale (fun t ω => W t ω*W t ω-((min t T:ℝ≥0):ℝ)) F P)
    (hWJ : Martingale (fun t => W t*J t) F P) :
    let Q := birthTraceLaw P A
    let _ : IsProbabilityMeasure Q := birthTraceLaw_isProbability (F.le b A hA) hp
    FocalPulseDynamics Q (birthTraceFiltration F b A) H α κ σ ε d
      (fun t (ω : A) => M (min t H) ω) (fun t (ω : A) => U (min t H) ω)
      (fun t (ω : A) => C (min t H) ω) (birthTraceStoppedIncrement A b H W) := by
  let Q := birthTraceLaw P A
  let hQ := birthTraceLaw_isProbability (F.le b A hA) hp
  let G := birthTraceFiltration F b A
  let W' := birthTraceStoppedIncrement A b H W
  let J' := birthTraceStoppedIncrement A b H J
  let M' (t : ℝ≥0) (ω : A) := M (min t H) ω
  let P' := boundaryConditionedMeasure P A
  have hPres : MeasurePreserving (Subtype.val : A→Ω) Q P' :=
    ⟨measurable_subtype_coe,birthTraceLaw_map (F.le b A hA)⟩
  have hAC : P' ≪ P :=
    ((Measure.AbsolutelyContinuous.refl (P.restrict A)).smul_left _).trans
      Measure.restrict_le_self.absolutelyContinuous
  have hA0 : MeasurableSet[pulseAgeFiltration F b 0] A := by
    change MeasurableSet[F (b+0)] A
    rwa [add_zero]
  have hPulse' := (hPulse.freeze_horizon hH).birthTrace hA0 hp
  rw [birthTraceFiltration_pulseAge] at hPulse'
  have hC' : ∀ᵐ (ω : A) ∂Q,Continuous (fun t => C (min t H) ω) := by
    filter_upwards [hPres.quasiMeasurePreserving.ae (hAC.ae_le hC)] with ω h
    exact h.comp (continuous_id.min continuous_const)
  have hUm (t : ℝ≥0) (_ : t≤H) : Measurable (U t) :=
    ((hPulse.variance_adapted t).mono ((pulseAgeFiltration F b).le t)).measurable
  have hUR := FocalPulseRegularity.of_frozen_birthTrace_fourth hA hp hUm
    hPulse.variance_continuous hD hFourth
  obtain ⟨hW',hW'₂,hW'c,hW'cl,hW'J'⟩ := orthogonal_unit_clock_birthTrace
    hA hp hT hW hJ hW₂ hJ₂ hWc hWsq hWJ
  have he (t : ℝ≥0) : M' t =ᵐ[Q] J' t :=
    hPres.quasiMeasurePreserving.ae (hAC.ae_le (hM _ (min_le_right t H)))
  have hCross : Martingale (fun t => W' t*M' t) G Q := by
    exact hW'J'.congr (fun t => (hW'.stronglyAdapted t).mul (hPulse'.martingale.stronglyAdapted t))
      (fun t => EventuallyEq.rfl.mul (he t).symm)
  exact ⟨hPulse', hPulse'.clock_ae_all hC', hUR,hW',hW'₂,hW'c,hW'cl,hCross⟩

#print axioms focalPulseDynamics_onBirthTrace

end RoughHeston
