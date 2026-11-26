import SizeBiasGirsanov
import Mathlib.MeasureTheory.Measure.WithDensity

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} {H : ℝ≥0} {Z g : ℝ≥0 → Ω → ℝ} {ε : ℝ}

local instance energyTimeMeasureFinite (t : ℝ≥0) : IsFiniteMeasure (hestonTimeMeasure t) := by
  rw [hestonTimeMeasure_eq_horizon]
  infer_instance

/-- Under the terminal tilt, its measure restricted to the observation
sigma algebra is exactly the measure tilted by the observed focal mass. -/
theorem sizeBiasedLaw_trim_eq (hZ : Martingale Z F μ) (hε : 0 < ε)
    (hZ₀ : ∀ t, ∀ᵐ ω ∂μ, 0 ≤ Z t ω) {t : ℝ≥0} (ht : t ≤ H) :
    (sizeBiasedLaw μ (Z H) ε).trim (F.le t) = (sizeBiasedLaw μ (Z t) ε).trim (F.le t) := by
  apply @Measure.ext Ω (F t)
  intro E hE
  have hEμ := F.le t E hE
  simp only [trim_measurableSet_eq _ hE, sizeBiasedLaw, withDensity_apply _ hEμ]
  have hint (r : ℝ≥0) : Integrable (fun ω => Z r ω / ε) (μ.restrict E) :=
    ((hZ.integrable r).div_const ε).integrableOn
  have hpos (r : ℝ≥0) : 0 ≤ᵐ[μ.restrict E] fun ω => Z r ω / ε :=
    ae_restrict_of_ae ((hZ₀ r).mono fun ω hw => div_nonneg hw hε.le)
  rw [← ofReal_integral_eq_lintegral_ofReal (hint H) (hpos H),
    ← ofReal_integral_eq_lintegral_ofReal (hint t) (hpos t),
    integral_div, integral_div, hZ.setIntegral_eq ht hE]

/-- Conditional mass-density transport applies to arbitrary nonnegative
adapted payoffs, including those whose expectations may be infinite. -/
theorem sizeBiasedLaw_lintegral_of_adapted (hZ : Martingale Z F μ) (hε : 0 < ε)
    (hZ₀ : ∀ t, ∀ᵐ ω ∂μ, 0 ≤ Z t ω) {t : ℝ≥0} (ht : t ≤ H)
    {f : Ω → ℝ≥0∞} (hf : Measurable[F t] f) :
    (∫⁻ ω, f ω ∂sizeBiasedLaw μ (Z H) ε) =
      ∫⁻ ω, ENNReal.ofReal (Z t ω / ε) * f ω ∂μ := by
  rw [← lintegral_trim (F.le t) hf, sizeBiasedLaw_trim_eq hZ hε hZ₀ ht, lintegral_trim (F.le t) hf]
  have hm : Measurable (Z t) := ((hZ.stronglyMeasurable t).mono (F.le t)).measurable
  exact lintegral_withDensity_eq_lintegral_mul μ (hm.div_const ε).ennreal_ofReal (hf.mono (F.le t) le_rfl)

/-- Fubini and the exact conditional mass density transfer square energy
from the old law weighted by the adapted mass to the actual terminal tilt. -/
theorem sizeBiasedLaw_integrable_square_of_weighted (hZ : Martingale Z F μ) (hε : 0 < ε)
    (hZ₀ : ∀ t, ∀ᵐ ω ∂μ, 0 ≤ Z t ω)
    (hJointZ : Measurable (Function.uncurry Z))
    (hg : IsStronglyPredictable F g)
    [IsProbabilityMeasure (sizeBiasedLaw μ (Z H) ε)]
    (hEnergy : Integrable (fun p : ℝ≥0 × Ω => Z p.1 p.2 * g p.1 p.2 ^ 2)
      ((hestonTimeMeasure H).prod μ)) :
    Integrable (fun p : ℝ≥0 × Ω => g p.1 p.2 ^ 2)
      ((hestonTimeMeasure H).prod (sizeBiasedLaw μ (Z H) ε)) := by
  let θ := hestonTimeMeasure H
  let Q := sizeBiasedLaw μ (Z H) ε
  let φ (p : ℝ≥0 × Ω) := g p.1 p.2 ^ 2
  let ψ (p : ℝ≥0 × Ω) := Z p.1 p.2 / ε * φ p
  have hφ : Measurable φ := (hg.mono F.predictable_le_prod).measurable.pow_const 2
  have hψ : Measurable ψ := (hJointZ.div_const ε).mul hφ
  have hψInt : Integrable ψ (θ.prod μ) := by
    apply (hEnergy.div_const ε).congr
    exact ae_of_all _ fun p => by dsimp [ψ, φ]; ring
  have hψnn : 0 ≤ᵐ[θ.prod μ] ψ := by
    apply (Measure.ae_prod_iff_ae_ae ?_).2
    · exact ae_of_all _ fun t => (hZ₀ t).mono fun ω hw => mul_nonneg (div_nonneg hw hε.le) (sq_nonneg _)
    · exact measurableSet_le measurable_const hψ
  refine ⟨hφ.aestronglyMeasurable, ?_⟩
  have hφEn (p : ℝ≥0 × Ω) : ‖φ p‖ₑ = ENNReal.ofReal (φ p) :=
    Real.enorm_eq_ofReal (sq_nonneg _)
  change (∫⁻ p, ‖φ p‖ₑ ∂θ.prod Q) < ∞
  simp only [hφEn]
  have hθ : ∀ᵐ t ∂θ, t ≤ H := by
    rw [show θ = (MathFin.ItoIntegralL2.timeMeasure).restrict (Ioc 0 H) from hestonTimeMeasure_eq_horizon H]
    exact (ae_restrict_mem measurableSet_Ioc).mono fun _ hw => hw.2
  have he : (∫⁻ p, ENNReal.ofReal (φ p) ∂θ.prod Q) =
      ∫⁻ p, ENNReal.ofReal (ψ p) ∂θ.prod μ := by
    rw [lintegral_prod _ hφ.ennreal_ofReal.aemeasurable, lintegral_prod _ hψ.ennreal_ofReal.aemeasurable]
    apply lintegral_congr_ae
    filter_upwards [hθ] with t ht
    have hm : Measurable[F t] (fun ω => ENNReal.ofReal (φ (t, ω))) :=
      ((hg.stronglyAdapted t).measurable.pow_const 2).ennreal_ofReal
    rw [sizeBiasedLaw_lintegral_of_adapted hZ hε hZ₀ ht hm]
    apply lintegral_congr
    intro ω
    exact (ENNReal.ofReal_mul' (sq_nonneg (g t ω))).symm
  rw [he, ← ofReal_integral_eq_lintegral_ofReal hψInt hψnn]
  exact ENNReal.ofReal_lt_top

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.sizeBiasedLaw_trim_eq
#print axioms RoughHeston.GirsanovPort.sizeBiasedLaw_integrable_square_of_weighted
