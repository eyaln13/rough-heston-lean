import BirthTraceItoClock
import BirthTraceStoppedObservation
import AffineObservationClock

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace RoughHeston.GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 m} {A : Set Ω} {b s : ℝ≥0}

local notation "G" => birthTraceFiltration F b A
local notation "Q" => birthTraceLaw P A
local notation "ν" => jointPredictableMeasure F P (b+s)
local notation "ν'" => jointPredictableMeasure (birthTraceFiltration F b A) (birthTraceLaw P A) s

set_option maxHeartbeats 1600000 in
/-- An evaluated old physical affine test has the same stopped
representation on the genuine birth trace. All Brownian integrals
use their original joint filtrations, with the latter measured in age. -/
theorem birthTrace_stopped_affine_row
    (hA : MeasurableSet[F b] A) (hPA : 0<P A) [IsProbabilityMeasure Q]
    {B : ℝ≥0 → Ω → ℝ} {B' : ℝ≥0 → A → ℝ}
    (hB₂ : ∀ t, MemLp (B t) 2 P) (hB : Martingale B F P)
    (hBc : Martingale (fun t ω => B t ω ^ 2-((min t (b+s):ℝ≥0):ℝ)) F P)
    (hB'₂ : ∀ t, MemLp (B' t) 2 Q) (hB' : Martingale B' G Q)
    (hB'c : Martingale (fun t ω => B' t ω ^ 2-((min t s:ℝ≥0):ℝ)) G Q)
    (hAgree : ∀ t≤s, B' t =ᵐ[Q] (fun ω => B (b+t) ω-B b ω))
    {τ : A → ℝ≥0} {L Y : ℝ≥0 → Ω → ℝ} {w : ℝ → ℝ} {σ : ℝ}
    (u : Lp ℝ 2 ν) (v : Lp ℝ 2 ν')
    (hu : ⇑u =ᵐ[ν] Function.uncurry
      (stoppedAffineTestRow (fun t => σ*w (((b+s:ℝ≥0):ℝ)-(t:ℝ))) L Y b
        (physicalObservationOfTrace τ b s)))
    (hv : ⇑v =ᵐ[ν'] Function.uncurry
      (stoppedAffineTestRow (fun t => σ*w ((s:ℝ)-(t:ℝ)))
        (fun t (ω : A) => L (b+t) ω) (fun t (ω : A) => Y (b+t) ω) 0 (fun ω => min s (τ ω))))
    (hRep : (fun ω => 1-L (physicalObservationOfTrace τ b s ω) ω) =ᵐ[P]
      fun ω => 1-L b ω + jointItoIntegralCLM (b+s) hB₂ u ω) :
    (fun ω : A => 1-L (b+min s (τ ω)) ω) =ᵐ[Q]
      fun ω => 1-L b ω + jointItoIntegralCLM s hB'₂ v ω := by
  have hSub : QuasiMeasurePreserving (Subtype.val : A → Ω) Q P :=
    ⟨measurable_subtype_coe,Measure.absolutelyContinuous_of_le_smul (birthTrace_subtype_dom hA)⟩
  let φ (p : ℝ≥0 × A) : ℝ≥0 × Ω := (b+p.1,p.2.val)
  letI : MeasurableSpace (ℝ≥0 × A) := (G).predictable
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hφ : QuasiMeasurePreserving φ ν' ν :=
    ⟨measurable_birthTrace_predictableShift,
      Measure.absolutelyContinuous_of_le_smul (birthTrace_joint_dom hA hPA)⟩
  have hSupp : ∀ᵐ p ∂ν, p.1≤b → u p=0 := by
    filter_upwards [hu] with p hp hb
    have hn : ¬(b<p.1 ∧ p.1≤physicalObservationOfTrace τ b s p.2) :=
      fun h => (not_lt_of_ge hb) h.1
    simpa only [Function.uncurry,stoppedAffineTestRow,ite_eq_right hn] using hp
  have hRow : ⇑v =ᵐ[ν'] fun p => u (φ p) := by
    filter_upwards [hv,hφ.ae hu] with p hp hq
    rw [hp,hq]
    change stoppedAffineTestRow (fun t => σ*w ((s:ℝ)-(t:ℝ)))
        (fun t (ω : A) => L (b+t) ω) (fun t (ω : A) => Y (b+t) ω) 0
        (fun ω => min s (τ ω)) p.1 p.2 =
      stoppedAffineTestRow (fun t => σ*w (((b+s:ℝ≥0):ℝ)-(t:ℝ))) L Y b
        (physicalObservationOfTrace τ b s) (b+p.1) p.2.val
    have hObs := physicalObservationOfTrace_eq τ b s p.2
    have hlt : b<b+p.1 ↔ 0<p.1 := by
      exact ⟨fun h => pos_of_ne_zero (fun h0 => by simp [h0] at h), lt_add_of_pos_right b⟩
    have heT : (b<b+p.1 ∧ b+p.1≤physicalObservationOfTrace τ b s p.2) ↔
        (0<p.1 ∧ p.1≤min s (τ p.2)) := by
      rw [hObs,hlt,add_le_add_iff_left]
    have he : ((b+s:ℝ≥0):ℝ) - ((b+p.1:ℝ≥0):ℝ) = (s:ℝ)-(p.1:ℝ) := by push_cast; ring
    by_cases ht : 0<p.1 ∧ p.1≤min s (τ p.2)
    · rw [stoppedAffineTestRow,stoppedAffineTestRow,ite_eq_left ht,ite_eq_left (heT.mpr ht),he]
    · rw [stoppedAffineTestRow,stoppedAffineTestRow,ite_eq_right ht,ite_eq_right (ht ∘ heT.mp)]
  have hJ := birthTrace_jointIto_shift hA hPA hB₂ hB hBc hB'₂ hB' hB'c hAgree u v hSupp hRow
  filter_upwards [hSub.ae hRep,hJ] with ω hω hI
  rw [physicalObservationOfTrace_eq] at hω
  rw [hω,hI]

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.birthTrace_stopped_affine_row
