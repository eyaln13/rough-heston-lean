import BirthTraceMartingaleShift
import PulsedCommonBrownianFocal

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Interval Topology

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 m} {b H T : ℝ≥0} {A : Set Ω}
  {B J C U X : ℝ≥0 → Ω → ℝ} {σ ε : ℝ}

/-- The physical common-driver compensation gives the literal focal
size-bias product compensation on the conditioned age clock. -/
theorem pulsed_focal_compensatedProduct_birthTrace
    (hA : MeasurableSet[F b] A) (hp : 0 < P A) (hBH : b+H ≤ T)
    (hB : Martingale B F P) (hJ : Martingale J F P)
    (hB₂ : ∀ t, MemLp (B t) 2 P) (hJ₂ : ∀ t, MemLp (J t) 2 P)
    (hC : Martingale (fun t => B t * J (min t T) - C t) F P)
    (hCeq : ∀ t ≤ T, C t =ᵐ[P] fun ω => ∫ r in (0 : ℝ)..(t : ℝ),
      focalBracketDensity σ U X r.toNNReal ω)
    (hU : IsStronglyPredictable F U) (hX : IsStronglyPredictable F X)
    (hUc : ∀ᵐ ω ∂P, ContinuousOn (fun t => U t ω) (Icc 0 T))
    (hXc : ∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Icc 0 T))
    (hParts : ∀ᵐ ω ∂P, ∀ t ≤ T, 0 ≤ U t ω ∧ U t ω ≤ X t ω)
    (hσ : 0 ≤ σ) (ε : ℝ) :
    let Bage (t : ℝ≥0) (ω : A) := B (b+t) ω - B b ω
    let Zage (t : ℝ≥0) (ω : A) := J (b+t) ω - J b ω + ε
    Martingale (fun t (ω : A) => Zage (min t H) ω * Bage (min t H) ω -
      ∫ r, σ * U (b+r) ω / Real.sqrt (X (b+r) ω) ∂hestonTimeMeasure (min t H))
      (birthTraceFiltration F b A) (birthTraceLaw P A) := by
  let q := focalBracketDensity σ U X
  have hQpred : IsStronglyPredictable F q := focalBracketDensity_predictable hU hX
  have hInt : ∀ᵐ ω ∂P, IntervalIntegrable (fun r : ℝ => q r.toNNReal ω) volume 0 (T : ℝ) := by
    filter_upwards [hUc, hXc, hParts] with ω hu hx hPart
    have hq := continuousOn_focalBracketRatio hu hx hσ (fun t ht => hPart t ht.2)
    apply ContinuousOn.intervalIntegrable_of_Icc (NNReal.coe_nonneg T)
    apply hq.comp continuous_real_toNNReal.continuousOn
    intro r hr
    refine ⟨zero_le, ?_⟩
    have hrT : (r.toNNReal : ℝ) ≤ (T : ℝ) := (Real.coe_toNNReal _ hr.1).trans_le hr.2
    exact_mod_cast hrT
  have h := martingale_compensatedProduct_birthTrace_density hA hp hBH hB
    (martingale_freeze_at hJ T) hB₂ (fun t => hJ₂ _) hC hQpred hInt hCeq ε
  have hbT : b ≤ T := (show b ≤ b+H by simp).trans hBH
  have htT (t : ℝ≥0) : b+min t H ≤ T := (add_le_add_right (min_le_right t H) b).trans hBH
  simpa only [min_eq_left hbT, fun t => min_eq_left (htT t), mul_comm, q, focalBracketDensity] using h

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.pulsed_focal_compensatedProduct_birthTrace
