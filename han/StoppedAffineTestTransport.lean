import FirstTiltItoTransport
import StoppedCompetitorSeparation

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston.GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {P Q R : Measure Ω}
  [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {F : Filtration ℝ≥0 m} {H b s : ℝ≥0} {B W N U Z X Y : ℝ≥0 → Ω → ℝ}
  {hB₂ : ∀ t, MemLp (B t) 2 P} {hW₂ : ∀ t, MemLp (W t) 2 Q}

omit [IsProbabilityMeasure Q] in
private theorem jointMeasure_ac_of_ac [IsFiniteMeasure R] (hQR : Q ≪ R) :
    jointPredictableMeasure F Q H ≪ jointPredictableMeasure F R H := by
  let ν := MathFin.ItoIntegralCLM.timeMeasureHorizon H
  have hProd : ν.prod Q ≪ ν.prod R := (Measure.AbsolutelyContinuous.refl ν).prod hQR
  unfold jointPredictableMeasure
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hAR
  rw [trim_measurableSet_eq F.predictable_le_prod hA] at hAR ⊢
  exact hProd hAR

set_option maxHeartbeats 950000 in
/-- An original stopped affine test and the two actual drift changes
give the competitor occupation estimate under the capped measure.
The two drift pairings cancel on the predictable support of the test. -/
theorem stopped_occupation_of_original_affine_representation
    (hB : Martingale B F P) (hW : Martingale W F Q)
    (hBclock : Martingale (fun t ω => B t ω^2 - ((min t H : ℝ≥0) : ℝ)) F P)
    (hWclock : Martingale (fun t ω => W t ω^2 - ((min t H : ℝ≥0) : ℝ)) F Q)
    (hQP : Q ≪ P) {σ δ d : ℝ} {τ : Ω → ℝ≥0}
    (hτ : Measurable τ)
    (hQshift : ∀ᵐ ω ∂Q, ∀ t ≤ H, W t ω = B t ω -
      ∫ r, σ * U r ω / (Z r ω * Real.sqrt (X r ω)) ∂hestonTimeMeasure t)
    (hDrift : MemLp (fun p : ℝ≥0 × Ω => σ * U p.1 p.2 / (Z p.1 p.2 * Real.sqrt (X p.1 p.2)))
      2 ((hestonTimeMeasure H).prod Q))
    (hc : IsStoppedDriftChange (F := F) (H := H) b δ
      (controlThrough (competitorAfterBirth b σ U Z X Y) τ) hW₂ R N)
    (hY : Measurable (Y s)) (hY₀ : ∀ ω, 0 ≤ Y s ω)
    {test a : ℕ → Ω → ℝ} {f : ℕ → ℝ≥0 × Ω → ℝ}
    (hfp : ∀ n, StronglyMeasurable[F.predictable] (f n))
    (hfP : ∀ n, MemLp (f n) 2 (jointPredictableMeasure F P H))
    (hfQ : ∀ n, MemLp (f n) 2 (jointPredictableMeasure F Q H))
    (hfR : ∀ n, MemLp (f n) 2 (jointPredictableMeasure F R H))
    (hactive : ∀ n t ω, f n (t, ω) ≠ 0 → b < t ∧ t ≤ τ ω ∧ 0 < Y t ω)
    (ha : ∀ n, StronglyMeasurable[F b] (a n)) (hai : ∀ n, Integrable (a n) R)
    (hrep : ∀ n, test n =ᵐ[P] fun ω =>
      a n ω + jointItoIntegralCLM H hB₂ ((hfP n).toLp (f n)) ω)
    (hNonneg : ∀ n, ∀ᵐ ω ∂P, 0 ≤ test n ω)
    (hterminal : ∀ n, ∀ᵐ ω ∂P, s ≤ τ ω → test n ω = 1 - Real.exp (-(n:ℝ)*Y s ω))
    (hborn : ∀ n, (∫ ω, a n ω ∂Q) ≤ d) :
    R.real {ω | s ≤ τ ω ∧ 0 < Y s ω} ≤ d := by
  have hc' := hc
  obtain ⟨hR, hQR, hRQ, _⟩ := hc'
  have : IsProbabilityMeasure R := hR
  let D (p : ℝ≥0 × Ω) := σ * U p.1 p.2 / (Z p.1 p.2 * Real.sqrt (X p.1 p.2))
  let g := controlThrough (competitorAfterBirth b σ U Z X Y) τ
  let C (n : ℕ) (ω : Ω) := ∫ r, f n (r, ω) * g r ω ∂hestonTimeMeasure H
  let v (n : ℕ) := (hfQ n).toLp (f n)
  let w (n : ℕ) := (hfR n).toLp (f n)
  have hv : ∀ n, v n =ᵐ[jointPredictableMeasure F Q H] f n := fun n => (hfQ n).coeFn_toLp
  have hw : ∀ n, v n =ᵐ[jointPredictableMeasure F Q H] w n :=
    fun n => (hv n).trans ((jointMeasure_ac_of_ac (F := F) (H := H) hQR).ae_eq (hfR n).coeFn_toLp).symm
  have hRepQ (n : ℕ) :
      test n =ᵐ[Q] fun ω => a n ω + jointItoIntegralCLM H hW₂ (v n) ω + C n ω := by
    have hTransport := jointIto_transport_of_physicalShift hB hW hB₂ hW₂ hBclock hWclock hQP
      hQshift hDrift (hfp n) (hfP n) (hfQ n)
    filter_upwards [hQP.ae_eq (hrep n), hTransport] with ω hω hh
    rw [hω, hh]
    have he : (∫ r, f n (r, ω) * D (r, ω) ∂hestonTimeMeasure H) = C n ω :=
      drift_pairing_through_stop (H := H) (birth := b) (τ := τ) (σ := σ)
        (U := U) (Z := Z) (X := X) (Y := Y) (hactive n) ω
    change _ = a n ω +
      (jointItoIntegralCLM H hB₂ ((hfP n).toLp (f n)) ω -
        ∫ r, f n (r, ω) * D (r, ω) ∂hestonTimeMeasure H) + C n ω
    rw [he]
    ring
  exact stopped_occupation_from_affine_tests hc hτ hY hY₀ v w hv hw ha hai hRepQ
    (fun _ => EventuallyEq.rfl) (fun n => (hNonneg n).filter_mono
      (hRQ.ae_le.trans hQP.ae_le))
    (fun n => (hterminal n).filter_mono (hRQ.ae_le.trans hQP.ae_le)) hborn

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.stopped_occupation_of_original_affine_representation
