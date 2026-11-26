import SizeBiasedBurst
import LaplaceBoundary
import Mathlib.Probability.Martingale.Basic

/-! Transferring a capped-event probability back from terminal size bias. -/

open MeasureTheory Set Filter
open scoped ENNReal

namespace RoughHeston

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- On an event where terminal mass is bounded above, the size-bias
density is bounded by the cutoff divided by the initial mass. -/
theorem sizeBiasedLaw_apply_cap_le {Z : Ω → ℝ} {ε z : ℝ} (hε : 0 < ε)
    (hZ : Measurable Z) {E : Set Ω} (hE : MeasurableSet E) :
    sizeBiasedLaw μ Z ε (E ∩ {ω | Z ω ≤ z}) ≤ ENNReal.ofReal (z / ε) * μ E := by
  let D := E ∩ {ω | Z ω ≤ z}
  have hD : MeasurableSet D := hE.inter (measurableSet_le hZ measurable_const)
  change sizeBiasedLaw μ Z ε D ≤ _
  rw [sizeBiasedLaw, withDensity_apply _ hD]
  calc
    _ ≤ ∫⁻ _ in D, ENNReal.ofReal (z / ε) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hD] with ω hω
      exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hω.2 hε.le)
    _ = ENNReal.ofReal (z / ε) * μ D := by
      rw [lintegral_const, Measure.restrict_apply_univ]
    _ ≤ _ := mul_right_mono (measure_mono inter_subset_left)

/-- A lower probability bound for a capped event under the tilted law
gives an unconditioned lower bound for the original event. -/
theorem measureReal_lower_bound_of_sizeBiasedLaw_cap [IsFiniteMeasure μ]
    {Z : Ω → ℝ} {ε z p : ℝ} (hε : 0 < ε) (hz : 0 < z)
    (hZ : Measurable Z) {E : Set Ω} (hE : MeasurableSet E)
    (hp : p ≤ (sizeBiasedLaw μ Z ε).real (E ∩ {ω | Z ω ≤ z})) :
    ε * p / z ≤ μ.real E := by
  have hcap := sizeBiasedLaw_apply_cap_le (μ := μ) (z := z) hε hZ hE
  have hfin : ENNReal.ofReal (z / ε) * μ E ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ E)
  have hcapReal : (sizeBiasedLaw μ Z ε).real (E ∩ {ω | Z ω ≤ z}) ≤ (z / ε) * μ.real E := by
    simpa only [measureReal_def, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (div_nonneg hz.le hε.le)] using ENNReal.toReal_mono hfin hcap
  apply (div_le_iff₀ hz).2
  calc
    ε * p ≤ ε * ((z / ε) * μ.real E) := mul_le_mul_of_nonneg_left (hp.trans hcapReal) hε.le
    _ = μ.real E * z := by field_simp

/-- Size bias by terminal mass after conditioning on the birth event. -/
noncomputable def birthConditionedSizeBiasedLaw
    (μ : Measure Ω) (A : Set Ω) (Z : Ω → ℝ) (ε : ℝ) : Measure Ω :=
  sizeBiasedLaw (boundaryConditionedMeasure μ A) Z ε

/-- The normalized mass gives a probability law after conditioning. The
normalization is stated as the original set integral over the birth event. -/
theorem birthConditionedSizeBiasedLaw_isProbabilityMeasure [IsFiniteMeasure μ]
    {A : Set Ω} (hA : 0 < μ A) {Z : Ω → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hZ : IntegrableOn Z A μ) (hZ₀ : ∀ᵐ ω ∂μ.restrict A, 0 ≤ Z ω)
    (hmean : (∫ ω in A, Z ω ∂μ) = ε * μ.real A) :
    IsProbabilityMeasure (birthConditionedSizeBiasedLaw μ A Z ε) := by
  have hAre : 0 < μ.real A :=
    ENNReal.toReal_pos_iff.2 ⟨hA, lt_top_iff_ne_top.2 (measure_ne_top μ A)⟩
  apply sizeBiasedLaw_isProbabilityMeasure hε
  · exact hZ.smul_measure (ENNReal.inv_ne_top.2 hA.ne')
  · exact Measure.ae_smul_measure hZ₀ (μ A)⁻¹
  · rw [integral_boundaryConditionedMeasure, hmean, mul_div_cancel_right₀ _ hAre.ne']

/-- Undo the size bias and birth-time conditioning. The lower bound
holds already for the intersection with the birth event. -/
theorem measureReal_inter_birth_lower_bound_of_conditioned_size_bias [IsFiniteMeasure μ]
    {A : Set Ω} (hA : 0 < μ A) {Z : Ω → ℝ} {ε z p : ℝ}
    (hε : 0 < ε) (hz : 0 < z) (hZ : Measurable Z) {E : Set Ω} (hE : MeasurableSet E)
    (hp : p ≤ (birthConditionedSizeBiasedLaw μ A Z ε).real (E ∩ {ω | Z ω ≤ z})) :
    μ.real A * ε * p / z ≤ μ.real (E ∩ A) := by
  have hAre : 0 < μ.real A :=
    ENNReal.toReal_pos_iff.2 ⟨hA, lt_top_iff_ne_top.2 (measure_ne_top μ A)⟩
  let ν := boundaryConditionedMeasure μ A
  let : IsProbabilityMeasure ν := boundaryConditionedMeasure_isProbability hA
  have h := measureReal_lower_bound_of_sizeBiasedLaw_cap (μ := ν) hε hz hZ hE hp
  have hcond : ν.real E = μ.real (E ∩ A) / μ.real A := by
    unfold ν boundaryConditionedMeasure
    rw [measureReal_ennreal_smul_apply, ENNReal.toReal_inv, measureReal_restrict_apply hE,
      div_eq_mul_inv, mul_comm]
    rfl
  rw [hcond] at h
  calc
    μ.real A * ε * p / z = (ε * p / z) * μ.real A := by ring
    _ ≤ μ.real (E ∩ A) := (le_div_iff₀ hAre).1 h

/-- An event with positive capped probability under the law conditioned
at birth and then size-biased has the stated unconditional probability. -/
theorem measureReal_lower_bound_of_conditioned_size_bias [IsFiniteMeasure μ]
    {A : Set Ω} (hA : 0 < μ A) {Z : Ω → ℝ} {ε z p : ℝ}
    (hε : 0 < ε) (hz : 0 < z) (hZ : Measurable Z) {E : Set Ω} (hE : MeasurableSet E)
    (hp : p ≤ (birthConditionedSizeBiasedLaw μ A Z ε).real (E ∩ {ω | Z ω ≤ z})) :
    μ.real A * ε * p / z ≤ μ.real E :=
  (measureReal_inter_birth_lower_bound_of_conditioned_size_bias hA hε hz hZ hE hp).trans
    (measureReal_mono inter_subset_left)

/-- The conditional mean normalizes the tilt whenever the birth event
belongs to the initial σ-algebra of the terminal mass martingale. -/
theorem birthConditionedSizeBiasedLaw_isProbability_of_martingale
    {ι : Type*} [Preorder ι] [IsFiniteMeasure μ]
    {F : Filtration ι (inferInstance : MeasurableSpace Ω)} {Z : ι → Ω → ℝ}
    (hZ : Martingale Z F μ) {s t : ι} (hst : s ≤ t)
    {A : Set Ω} (hAmeas : MeasurableSet[F s] A) (hA : 0 < μ A)
    {ε : ℝ} (hε : 0 < ε) (hStart : Z s =ᵐ[μ] (fun _ => ε))
    (hPos : ∀ᵐ ω ∂μ, 0 ≤ Z t ω) :
    IsProbabilityMeasure (birthConditionedSizeBiasedLaw μ A (Z t) ε) := by
  apply birthConditionedSizeBiasedLaw_isProbabilityMeasure hA hε
    (hZ.integrable t).integrableOn (ae_restrict_of_ae hPos)
  calc
    (∫ ω in A, Z t ω ∂μ) = ∫ ω in A, Z s ω ∂μ := (hZ.setIntegral_eq hst hAmeas).symm
    _ = ∫ _ in A, ε ∂μ := integral_congr_ae (ae_restrict_of_ae hStart)
    _ = ε * μ.real A := by rw [setIntegral_const, smul_eq_mul, mul_comm]

#print axioms sizeBiasedLaw_apply_cap_le
#print axioms measureReal_lower_bound_of_sizeBiasedLaw_cap
#print axioms birthConditionedSizeBiasedLaw_isProbabilityMeasure
#print axioms birthConditionedSizeBiasedLaw_isProbability_of_martingale
#print axioms measureReal_inter_birth_lower_bound_of_conditioned_size_bias
#print axioms measureReal_lower_bound_of_conditioned_size_bias

end RoughHeston
