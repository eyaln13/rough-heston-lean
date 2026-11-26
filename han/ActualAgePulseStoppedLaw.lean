import ActualPulseStoppedSeparation
import StoppedCompetitorSeparation

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston.GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {F : Filtration ℝ≥0 m} [F.IsComplete Q] [F.IsRightContinuous]
  {r : ℝ≥0} {W U Z X Y : ℝ≥0 → Ω → ℝ} {σ C D γ η δ : ℝ}

/-- The capped Girsanov construction and the occupation estimate on
the genuine birth-age clock produce the stopped law required by the
uniform pulse separation theorem. -/
theorem actual_age_pulse_stopped_law_with_cap
    (hW : MathFinBridge.BrownianOn Q F r W)
    (hW₂ : ∀ t, MemLp (W t) 2 Q) (hWm : Martingale W F Q)
    (hWclock : Martingale (fun t ω => W t ω ^ 2-((min t r : ℝ≥0):ℝ)) F Q)
    (hr : 0<r) (hγ : 0≤γ) (hgap : 3*γ<η)
    (hδ : 0≤δ) (hC : 0≤C) (hD : 0≤D)
    (hu : IsStronglyPredictable F U) (hz : IsStronglyPredictable F Z)
    (hx : IsStronglyPredictable F X) (hy : IsStronglyPredictable F Y)
    (huc : ∀ ω, ContinuousOn (fun s => U s ω) (Icc 0 r))
    (hzc : ∀ ω, ContinuousOn (fun s => Z s ω) (Icc 0 r))
    (hzpos : ∀ s≤r, ∀ ω, 0<Z s ω)
    (hun : ∀ s≤r, ∀ ω, 0≤U s ω) (hux : ∀ s≤r, ∀ ω, U s ω≤X s ω)
    (hOcc : ∀ {R : Measure Ω} {N : ℝ≥0 → Ω → ℝ} {τ : Ω → ℝ≥0},
      IsStoppingTime F (fun ω => (τ ω:WithTop ℝ≥0)) →
      IsStoppedDriftChange (F:=F) (H:=r) 0 δ
        (controlThrough (competitorAfterBirth 0 σ U Z X Y) τ) hW₂ R N →
      (∀ᵐ ω ∂Q, (∫ s, controlThrough (competitorAfterBirth 0 σ U Z X Y) τ s ω ^ 2
        ∂hestonTimeMeasure r)≤δ) →
      ∀ s ∈ Ioc (0:ℝ≥0) r, R.real {ω | s≤τ ω ∧ 0<Y s ω} ≤ D*(s:ℝ)^η) :
    let env := envelopeStop r (C*(r:ℝ)^(3*γ)) (clusterEnvelopeValue 0 σ (1+3*γ) U Z)
    ∃ R : Measure Ω, ∃ (_ : IsProbabilityMeasure R),
      R ≪ Q ∧ Nonempty (PulseStoppedLaw Q R r δ ((C*D/(η-3*γ))*(r:ℝ)^η)
        (D*(r:ℝ)^η) env (Y r)) := by
  let env := envelopeStop r (C*(r:ℝ)^(3*γ)) (clusterEnvelopeValue 0 σ (1+3*γ) U Z)
  have hC' : 0≤C*(r:ℝ)^(3*γ) := mul_nonneg hC (Real.rpow_nonneg r.2 _)
  have hp : 0<1+3*γ := by linarith
  obtain ⟨τ,ht,_,hexit,hbudget,henv,R,N,hc⟩ := stopped_competitor_change_at_envelope
    (B:=W) (birth:=0) (σ:=σ) hW hW₂ hWm hWclock zero_le hδ hp hC'
    hu hz hx hy huc hzc hzpos hun hux
  have hR : IsProbabilityMeasure R := hc.1
  let : IsProbabilityMeasure R := hR
  have hTv : R≪Q ∧ (∀ A, MeasurableSet A → |R.real A-Q.real A|≤Real.sqrt δ/2) := by
    obtain ⟨_,_,hRQ,_,_,htv,_⟩ := hc
    exact ⟨hRQ,htv⟩
  let E (ω : Ω) := ∫ s, controlThrough (competitorAfterBirth 0 σ U Z X Y) τ s ω ^ 2 ∂hestonTimeMeasure r
  have hcap : ∀ᵐ ω ∂Q, E ω≤δ := ae_of_all _ fun ω => (hbudget ω).le.trans (min_le_left _ _)
  have he := competitor_stopped_energy_of_occupation (R:=R) hr hgap hC hD hu hz hx hy ht
    (fun ω s hs hsτ => by simpa only [NNReal.coe_zero,sub_zero] using henv ω s hs hsτ) (hOcc ht hc hcap)
  have hex (ω : Ω) (hs : τ ω<r) (hg : r≤env ω) : δ≤E ω := by
    change δ≤∫ s, controlThrough (competitorAfterBirth 0 σ U Z X Y) τ s ω ^ 2 ∂hestonTimeMeasure r
    rw [hbudget ω,min_eq_left (hexit ω hs hg)]
  refine ⟨R,hR,hTv.1,⟨⟨τ,E,measurable_finite_stop ht,he.1,?_,he.2.1,?_,hex,
    hOcc ht hc hcap r ⟨hr,le_rfl⟩,hTv.2⟩⟩⟩
  · exact ae_of_all _ fun ω => integral_nonneg fun s => sq_nonneg _
  · convert he.2.2 using 1
    ring

theorem actual_age_pulse_stopped_law
    (hW : MathFinBridge.BrownianOn Q F r W)
    (hW₂ : ∀ t, MemLp (W t) 2 Q) (hWm : Martingale W F Q)
    (hWclock : Martingale (fun t ω => W t ω ^ 2-((min t r : ℝ≥0):ℝ)) F Q)
    (hr : 0<r) (hγ : 0≤γ) (hgap : 3*γ<η)
    (hδ : 0≤δ) (hC : 0≤C) (hD : 0≤D)
    (hu : IsStronglyPredictable F U) (hz : IsStronglyPredictable F Z)
    (hx : IsStronglyPredictable F X) (hy : IsStronglyPredictable F Y)
    (huc : ∀ ω, ContinuousOn (fun s => U s ω) (Icc 0 r))
    (hzc : ∀ ω, ContinuousOn (fun s => Z s ω) (Icc 0 r))
    (hzpos : ∀ s≤r, ∀ ω, 0<Z s ω)
    (hun : ∀ s≤r, ∀ ω, 0≤U s ω) (hux : ∀ s≤r, ∀ ω, U s ω≤X s ω)
    (hOcc : ∀ {R : Measure Ω} {N : ℝ≥0 → Ω → ℝ} {τ : Ω → ℝ≥0},
      IsStoppingTime F (fun ω => (τ ω:WithTop ℝ≥0)) →
      IsStoppedDriftChange (F:=F) (H:=r) 0 δ
        (controlThrough (competitorAfterBirth 0 σ U Z X Y) τ) hW₂ R N →
      ∀ s ∈ Ioc (0:ℝ≥0) r, R.real {ω | s≤τ ω ∧ 0<Y s ω} ≤ D*(s:ℝ)^η) :
    let env := envelopeStop r (C*(r:ℝ)^(3*γ)) (clusterEnvelopeValue 0 σ (1+3*γ) U Z)
    ∃ R : Measure Ω, ∃ (_ : IsProbabilityMeasure R),
      Nonempty (PulseStoppedLaw Q R r δ ((C*D/(η-3*γ))*(r:ℝ)^η)
        (D*(r:ℝ)^η) env (Y r)) := by
  obtain ⟨R,hR,_,hData⟩ := actual_age_pulse_stopped_law_with_cap hW hW₂ hWm hWclock hr hγ hgap hδ hC hD
    hu hz hx hy huc hzc hzpos hun hux (fun ht hc _ => hOcc ht hc)
  exact ⟨R,hR,hData⟩

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.actual_age_pulse_stopped_law
#print axioms RoughHeston.GirsanovPort.actual_age_pulse_stopped_law_with_cap
