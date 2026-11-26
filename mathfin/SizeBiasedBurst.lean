import Verification
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory Filter Set
open scoped MeasureTheory Topology ENNReal

namespace RoughHeston

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

noncomputable def sizeBiasedLaw (μ : Measure Ω) (Z : Ω → ℝ) (ε : ℝ) : Measure Ω :=
  μ.withDensity fun ω => ENNReal.ofReal (Z ω / ε)

/-- Normalizing by the mean mass gives a probability law. -/
theorem sizeBiasedLaw_isProbabilityMeasure {Z : Ω → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hZ : Integrable Z μ) (hZ₀ : ∀ᵐ ω ∂μ, 0 ≤ Z ω)
    (hZmean : (∫ ω, Z ω ∂μ) = ε) :
    IsProbabilityMeasure (sizeBiasedLaw μ Z ε) := by
  refine ⟨?_⟩
  unfold sizeBiasedLaw
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hZ.div_const ε)
      (hZ₀.mono fun _ h => div_nonneg h hε.le), integral_div, hZmean, div_self hε.ne', ENNReal.ofReal_one]

/-- Expected payoffs under the size-biased law are terminal mixed
moments divided by the initial mass. -/
theorem integral_sizeBiasedLaw_eq {Z : Ω → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hZ : Measurable Z) (hZ₀ : ∀ᵐ ω ∂μ, 0 ≤ Z ω) (f : Ω → ℝ) :
    (∫ ω, f ω ∂sizeBiasedLaw μ Z ε) = (∫ ω, Z ω * f ω ∂μ) / ε := by
  unfold sizeBiasedLaw
  rw [integral_withDensity_eq_integral_toReal_smul
    (hZ.div_const ε).ennreal_ofReal (ae_of_all μ fun _ => ENNReal.ofReal_lt_top) f, ← integral_div]
  apply integral_congr_ae
  filter_upwards [hZ₀] with ω hω
  rw [ENNReal.toReal_ofReal (div_nonneg hω hε.le), smul_eq_mul]
  ring

/-- A first-moment lower bound and a second-moment upper bound yield a
positive probability of a fixed-size burst. An upper first moment for
the mass permits a simultaneous upper mass cutoff. -/
theorem burst_probability_of_moments [IsProbabilityMeasure μ]
    {U Z : Ω → ℝ} {a b z : ℝ} (ha : 0 < a) (hb : 0 < b) (hz : 0 ≤ z)
    (hU : Measurable U) (hU₀ : ∀ ω, 0 ≤ U ω) (hU₂ : MemLp U 2 μ)
    (hZ₀ : ∀ᵐ ω ∂μ, 0 ≤ Z ω) (hZi : Integrable Z μ)
    (hUlow : a ≤ ∫ ω, U ω ∂μ) (hUup : (∫ ω, U ω ^ 2 ∂μ) ≤ b)
    (hZup : (∫ ω, Z ω ∂μ) ≤ z) :
    a ^ 2 / (8 * b) ≤ μ.real {ω | a / 2 ≤ U ω ∧ Z ω ≤ 8 * b * (z + 1) / a ^ 2} := by
  let A := {ω | a / 2 ≤ U ω}
  let L := 8 * b * (z + 1) / a ^ 2
  let D := {ω | L < Z ω}
  let X := A.indicator U
  have hA : MeasurableSet A := measurableSet_le measurable_const hU
  have hX : Measurable X := hU.indicator hA
  have hX₀ (ω : Ω) : 0 ≤ X ω := by by_cases h : ω ∈ A <;> simp [X, h, hU₀]
  have hX₂ : MemLp X 2 μ := hU₂.indicator hA.nullMeasurableSet
  have hXlow : a / 2 ≤ ∫ ω, X ω ∂μ := by
    have hi := hX₂.integrable one_le_two
    have hle : (∫ ω, U ω ∂μ) ≤ ∫ ω, X ω + a / 2 ∂μ := by
      apply integral_mono (hU₂.integrable one_le_two) (hi.add (integrable_const _))
      intro ω
      change U ω ≤ A.indicator U ω + a / 2
      by_cases h : ω ∈ A
      · simp only [indicator_of_mem h, le_add_iff_nonneg_right]
        positivity
      · have hh : U ω < a / 2 := lt_of_not_ge h
        simpa only [X, indicator_of_notMem h, zero_add] using hh.le
    have hcalc : (∫ ω, X ω + a / 2 ∂μ) = (∫ ω, X ω ∂μ) + a / 2 := by
      calc
        _ = (∫ ω, X ω ∂μ) + (∫ _ : Ω, a / 2 ∂μ) := integral_add hi (integrable_const _)
        _ = _ := by simp
    rw [hcalc] at hle
    linarith [hUlow]
  have hXup : (∫ ω, X ω ^ 2 ∂μ) ≤ b := by
    refine (integral_mono hX₂.integrable_sq hU₂.integrable_sq ?_).trans hUup
    intro ω
    by_cases h : ω ∈ A <;> simp [X, h, sq_nonneg]
  have hsupport := second_moment_support hX hX₀ hX₂
  have hlower := (count_lower_bound (half_pos ha) hb hXlow hXup ENNReal.toReal_nonneg hsupport).2
  have hAlower : (a / 2) ^ 2 / b ≤ μ.real A := hlower.trans
    (measureReal_mono fun ω hω => by
      by_contra h
      simp [X, indicator_of_notMem h] at hω)
  have hL : 0 < L := by dsimp [L]; positivity
  have hDupper : μ.real D ≤ a ^ 2 / (8 * b) := by
    have hm := mul_meas_ge_le_integral_of_nonneg hZ₀ hZi L
    have hmon : μ.real D ≤ μ.real {ω | L ≤ Z ω} :=
      measureReal_mono (fun _ (h : L < Z _) => h.le)
    have hprod := (mul_le_mul_of_nonneg_left hmon hL.le).trans (hm.trans hZup)
    have hmul : L * (a ^ 2 / (8 * b)) = z + 1 := by
      dsimp [L]
      field_simp
    apply le_of_mul_le_mul_left _ hL
    exact hprod.trans (hmul.symm ▸ le_add_of_nonneg_right zero_le_one)
  have hdiff : μ.real A - μ.real D ≤ μ.real (A \ D) := le_measureReal_sdiff (measure_ne_top μ D)
  have hAarith : (a / 2) ^ 2 / b = a ^ 2 / (8 * b) + a ^ 2 / (8 * b) := by ring
  rw [hAarith] at hAlower
  have he : A \ D = {ω | a / 2 ≤ U ω ∧ Z ω ≤ L} := by
    ext ω
    simp [A, D]
  rw [he] at hdiff
  change a ^ 2 / (8 * b) ≤ μ.real {ω | a / 2 ≤ U ω ∧ Z ω ≤ L}
  linarith

end RoughHeston

#print axioms RoughHeston.sizeBiasedLaw_isProbabilityMeasure
#print axioms RoughHeston.integral_sizeBiasedLaw_eq
#print axioms RoughHeston.burst_probability_of_moments
