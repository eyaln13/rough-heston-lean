import SizeBiasedBurst
import Mathlib.Probability.Martingale.Basic

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {Z : ℝ≥0 → Ω → ℝ}

/-- Tilting at a later age gives the same probability to every earlier
observable event when the tilt density is a nonnegative martingale. -/
theorem sizeBiasedLaw_real_event_eq_of_martingale {s t : ℝ≥0} (hst : s ≤ t)
    (hZ : Martingale Z F P) {ε : ℝ} (hε : 0 < ε)
    (hZs : 0 ≤ᵐ[P] Z s) (hZt : 0 ≤ᵐ[P] Z t)
    {A : Set Ω} (hA : MeasurableSet[F s] A) :
    (sizeBiasedLaw P (Z t) ε).real A = (sizeBiasedLaw P (Z s) ε).real A := by
  have hAm := F.le s A hA
  have hEq (r : ℝ≥0) (hr : 0 ≤ᵐ[P] Z r) :
      (sizeBiasedLaw P (Z r) ε).real A = (∫ ω in A, Z r ω ∂P) / ε := by
    let Q := sizeBiasedLaw P (Z r) ε
    have hZm : Measurable (Z r) := (hZ.stronglyAdapted r).measurable.mono (F.le r) le_rfl
    have h1 : Q.real A = ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂Q := by
      rw [integral_indicator hAm, setIntegral_const, smul_eq_mul, mul_one]
    rw [h1, integral_sizeBiasedLaw_eq hε hZm hr, ← integral_indicator hAm]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun ω => by by_cases hω : ω ∈ A <;> simp [hω]
  rw [hEq t hZt, hEq s hZs, ← setIntegral_condExp (F.le s) (hZ.integrable t) hA]
  exact congrArg (fun x : ℝ => x / ε)
    (integral_congr_ae (ae_restrict_of_ae (hZ.condExp_ae_eq hst)))

/-- The height-and-mass cutoff event used for the focal burst is
measurable at the observation age. -/
theorem cluster_burst_event_measurable {t : ℝ≥0} {U : ℝ≥0 → Ω → ℝ}
    (hU : StronglyAdapted F U) (hZ : StronglyAdapted F Z) (a b : ℝ) :
    MeasurableSet[F t] {ω | a ≤ U t ω ∧ Z t ω ≤ b} := by
  exact (measurableSet_le measurable_const (hU t).measurable).inter
    (measurableSet_le (hZ t).measurable measurable_const)

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.sizeBiasedLaw_real_event_eq_of_martingale
#print axioms RoughHeston.GirsanovPort.cluster_burst_event_measurable
