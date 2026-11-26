import StoppedClusterEnvelope
import ActualFractionalPulse

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace RoughHeston.GirsanovPort

variable {Ω : Type*} {r : ℝ≥0} {c : ℝ} {E E' : ℝ≥0 → Ω → ℝ}

private theorem envelopeStop_lt_of_le_horizon {t : ℝ≥0} (ht : t≤r) (ω : Ω) :
    envelopeStop r c E ω<t ↔ ∃ u<t, c<E u ω := by
  have hcoe : (envelopeStop r c E ω : WithTop ℝ≥0) =
      min (r:WithTop ℝ≥0) (leastGT E c ω) := by
    unfold envelopeStop
    cases h : leastGT E c ω with
    | top => rw [min_eq_left (le_top : (r:WithTop ℝ≥0)≤⊤)]; rfl
    | coe a => rw [← WithTop.coe_min]; rfl
  have hn : ¬(r:WithTop ℝ≥0) < (t:WithTop ℝ≥0) :=
    not_lt_of_ge (WithTop.coe_le_coe.mpr ht)
  rw [←WithTop.coe_lt_coe,hcoe,min_lt_iff,leastGT_lt_iff]
  simp only [hn,false_or]

/-- A horizon-capped envelope stop depends only on observations
strictly before its deterministic horizon. -/
theorem envelopeStop_eq_of_agree_before (h : ∀ t<r, ∀ ω, E t ω=E' t ω) :
    envelopeStop r c E=envelopeStop r c E' := by
  funext ω
  have hle {V W : ℝ≥0 → Ω → ℝ} (hVW : ∀ t<r, V t ω=W t ω) :
      envelopeStop r c V ω≤envelopeStop r c W ω := by
    by_contra! hlt
    let t := envelopeStop r c V ω
    have ht : t≤r := envelopeStop_le _ _ _ _
    obtain ⟨u,hu,hc⟩ := (envelopeStop_lt_of_le_horizon (E:=W) ht ω).1 hlt
    have hz := (envelopeStop_lt_of_le_horizon (E:=V) ht ω).2
      ⟨u,hu,by rwa [hVW u (hu.trans_le ht)]⟩
    exact lt_irrefl t hz
  exact le_antisymm (hle fun t ht => h t ht ω) (hle fun t ht => (h t ht ω).symm)

/-- Freezing the prospective focal mass at the observation time has
no effect on the stopped envelope used in the separation estimate. -/
theorem envelopeStop_frozen_focal_mass_eq (r : ℝ≥0) (c σ p ε : ℝ)
    (U M : ℝ≥0 → Ω → ℝ) :
    envelopeStop r c (clusterEnvelopeValue 0 σ p U
      (fun t => fractionalPulseMass ε M (min t r))) =
      envelopeStop r c (clusterEnvelopeValue 0 σ p U (fractionalPulseMass ε M)) := by
  apply envelopeStop_eq_of_agree_before
  intro t ht ω
  simp only [clusterEnvelopeValue,min_eq_left ht.le]

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.envelopeStop_frozen_focal_mass_eq
