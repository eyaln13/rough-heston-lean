import SizeBiasedBurst
import MathFin.Probability.Analysis.FiniteMeasureCauchySchwarz
import Mathlib.MeasureTheory.Measure.WithDensity

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The actual mass tilt transfers a fourth moment of the cluster and
a second moment of the mass into a second moment of the cluster. -/
theorem sizeBiased_cluster_second_moment {Z U : Ω → ℝ} {ε : ℝ}
    (hε : 0 < ε) (hZ : Measurable Z) (hZ₀ : ∀ᵐ ω ∂P, 0 ≤ Z ω)
    (hZ₂ : MemLp Z 2 P) (hU₄ : MemLp U 4 P) :
    let Q := sizeBiasedLaw P Z ε
    MemLp U 2 Q ∧
      (∫ ω, U ω ^ 2 ∂Q) ≤ Real.sqrt (∫ ω, Z ω ^ 2 ∂P) * Real.sqrt (∫ ω, U ω ^ 4 ∂P) / ε := by
  let Q := sizeBiasedLaw P Z ε
  have : ENNReal.HolderTriple 4 4 2 := ⟨by
    have htwo : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have htop : (2 : ℝ≥0∞) ≠ ∞ := ENNReal.ofNat_ne_top
    rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num,
      ENNReal.mul_inv (Or.inl htwo) (Or.inl htop), ← two_mul, ← mul_assoc,
      ENNReal.mul_inv_cancel htwo htop, one_mul]⟩
  have hu2 : MemLp (fun ω => U ω * U ω) 2 P := hU₄.mul hU₄
  have hsq : MemLp (fun ω => U ω ^ 2) 2 P := by simpa only [pow_two] using hu2
  have hi : Integrable (fun ω => Z ω * U ω ^ 2) P := hZ₂.integrable_mul hsq
  have hQAC : Q ≪ P := withDensity_absolutelyContinuous P _
  have hQU₂ : MemLp U 2 Q := by
    apply (memLp_two_iff_integrable_sq (hU₄.aestronglyMeasurable.mono_ac hQAC)).2
    unfold Q sizeBiasedLaw
    apply (integrable_withDensity_iff_integrable_smul' (hZ.div_const ε).ennreal_ofReal
      (ae_of_all P fun _ => ENNReal.ofReal_lt_top)).2
    apply (hi.div_const ε).congr
    filter_upwards [hZ₀] with ω hw
    rw [ENNReal.toReal_ofReal (div_nonneg hw hε.le), smul_eq_mul]
    ring
  refine ⟨hQU₂, ?_⟩
  rw [integral_sizeBiasedLaw_eq hε hZ hZ₀]
  apply div_le_div_of_nonneg_right _ hε.le
  have he : (∫ ω, Z ω * U ω ^ 2 ∂P) = ∫ ω, |Z ω * U ω ^ 2| ∂P := by
    exact integral_congr_ae (hZ₀.mono fun ω hw => (abs_of_nonneg (mul_nonneg hw (sq_nonneg _))).symm)
  rw [he]
  have hCS := MathFin.integral_abs_mul_le_sqrt_mul_sqrt hZ₂ hsq
  simp_rw [← pow_mul, show 2 * 2 = 4 by norm_num] at hCS
  exact hCS

/-- Normalize both observables before applying the burst estimate. The
mass cutoff then has its original scale even when the scale is small. -/
theorem scaled_cluster_burst_of_moments {Q : Measure Ω} [IsProbabilityMeasure Q]
    {U Z : Ω → ℝ} {a b z scaleU scaleZ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hz : 0 ≤ z)
    (hSU : 0 < scaleU) (hSZ : 0 < scaleZ)
    (hU : Measurable U) (hU₀ : ∀ ω, 0 ≤ U ω) (hU₂ : MemLp U 2 Q)
    (hZ₀ : ∀ᵐ ω ∂Q, 0 ≤ Z ω) (hZi : Integrable Z Q)
    (hUlow : a * scaleU ≤ ∫ ω, U ω ∂Q)
    (hUup : (∫ ω, U ω ^ 2 ∂Q) ≤ b * scaleU ^ 2)
    (hZup : (∫ ω, Z ω ∂Q) ≤ z * scaleZ) :
    a ^ 2 / (8 * b) ≤ Q.real {ω | (a / 2) * scaleU ≤ U ω ∧ Z ω ≤ (8 * b * (z + 1) / a ^ 2) * scaleZ} := by
  let Us (ω : Ω) := U ω / scaleU
  let Zs (ω : Ω) := Z ω / scaleZ
  have hU' : Measurable Us := hU.div_const _
  have hU₀' (ω : Ω) : 0 ≤ Us ω := div_nonneg (hU₀ ω) hSU.le
  have hU₂' : MemLp Us 2 Q := by
    change MemLp (fun ω => U ω / scaleU) 2 Q
    simp_rw [div_eq_inv_mul]
    exact hU₂.const_mul _
  have hZ₀' : ∀ᵐ ω ∂Q, 0 ≤ Zs ω := hZ₀.mono fun ω hw => div_nonneg hw hSZ.le
  have hZi' : Integrable Zs Q := hZi.div_const _
  have hUlow' : a ≤ ∫ ω, Us ω ∂Q := by
    change a ≤ ∫ ω, U ω / scaleU ∂Q
    rw [integral_div]
    exact (le_div_iff₀ hSU).2 hUlow
  have hUup' : (∫ ω, Us ω ^ 2 ∂Q) ≤ b := by
    change (∫ ω, (U ω / scaleU) ^ 2 ∂Q) ≤ b
    simp_rw [div_pow]
    rw [integral_div]
    exact (div_le_iff₀ (sq_pos_of_pos hSU)).2 hUup
  have hZup' : (∫ ω, Zs ω ∂Q) ≤ z := by
    change (∫ ω, Z ω / scaleZ ∂Q) ≤ z
    rw [integral_div]
    exact (div_le_iff₀ hSZ).2 hZup
  have h := burst_probability_of_moments ha hb hz hU' hU₀' hU₂' hZ₀' hZi' hUlow' hUup' hZup'
  have he : {ω | a / 2 ≤ Us ω ∧ Zs ω ≤ 8 * b * (z + 1) / a ^ 2} =
      {ω | (a / 2) * scaleU ≤ U ω ∧ Z ω ≤ (8 * b * (z + 1) / a ^ 2) * scaleZ} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Us, Zs, le_div_iff₀ hSU, div_le_iff₀ hSZ]
  rwa [he] at h

/-- The scaled burst uses the old-law fourth moment, together with the
exact terminal size-bias law and the two first-moment bounds. -/
theorem scaled_sizeBiased_cluster_burst_of_old_moments
    {Z U : Ω → ℝ} {ε a b z scaleU scaleZ : ℝ}
    (hε : 0 < ε) (ha : 0 < a) (hb : 0 < b) (hz : 0 < z)
    (hSU : 0 < scaleU) (hSZ : 0 < scaleZ)
    (hU : Measurable U) (hU₀ : ∀ ω, 0 ≤ U ω) (hU₄ : MemLp U 4 P)
    (hZ : Measurable Z) (hZ₀ : ∀ᵐ ω ∂P, 0 ≤ Z ω) (hZ₂ : MemLp Z 2 P)
    [IsProbabilityMeasure (sizeBiasedLaw P Z ε)]
    (hUlow : a * scaleU ≤ ∫ ω, U ω ∂sizeBiasedLaw P Z ε)
    (hZup : (∫ ω, Z ω ∂sizeBiasedLaw P Z ε) ≤ z * scaleZ)
    (hZsq : (∫ ω, Z ω ^ 2 ∂P) ≤ ε * z * scaleZ)
    (hUfour : (∫ ω, U ω ^ 4 ∂P) ≤ ε * b * scaleU ^ 4 / scaleZ) :
    let Q := sizeBiasedLaw P Z ε
    let c := Real.sqrt (b * z)
    a ^ 2 / (8 * c) ≤ Q.real {ω | (a / 2) * scaleU ≤ U ω ∧ Z ω ≤ (8 * c * (z + 1) / a ^ 2) * scaleZ} := by
  let Q := sizeBiasedLaw P Z ε
  let c := Real.sqrt (b*z)
  have hc : 0 < c := Real.sqrt_pos.2 (mul_pos hb hz)
  obtain ⟨hU₂, hQU₂⟩ := sizeBiased_cluster_second_moment hε hZ hZ₀ hZ₂ hU₄
  have hZint : Integrable Z Q := by
    unfold Q sizeBiasedLaw
    apply (integrable_withDensity_iff_integrable_smul' (hZ.div_const ε).ennreal_ofReal
      (ae_of_all P fun _ => ENNReal.ofReal_lt_top)).2
    apply (hZ₂.integrable_sq.div_const ε).congr
    filter_upwards [hZ₀] with ω hw
    rw [ENNReal.toReal_ofReal (div_nonneg hw hε.le), smul_eq_mul]
    ring
  have hNew : (∫ ω, U ω ^ 2 ∂Q) ≤ c * scaleU ^ 2 := by
    refine hQU₂.trans ((div_le_div_of_nonneg_right (mul_le_mul (Real.sqrt_le_sqrt hZsq)
      (Real.sqrt_le_sqrt hUfour) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hε.le).trans_eq ?_)
    have he : (ε*z*scaleZ) * (ε*b*scaleU^4/scaleZ) = (b*z) * (ε * scaleU^2)^2 := by
      field_simp
    rw [← Real.sqrt_mul (by positivity : 0 ≤ ε*z*scaleZ), he, Real.sqrt_mul (by positivity : 0 ≤ b*z),
      Real.sqrt_sq (by positivity : 0 ≤ ε * scaleU^2)]
    dsimp [c]
    field_simp
  exact scaled_cluster_burst_of_moments ha hc hz.le hSU hSZ hU hU₀ hU₂
    ((withDensity_absolutelyContinuous P _).ae_le hZ₀) hZint hUlow hNew hZup

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.sizeBiased_cluster_second_moment
#print axioms RoughHeston.GirsanovPort.scaled_cluster_burst_of_moments
#print axioms RoughHeston.GirsanovPort.scaled_sizeBiased_cluster_burst_of_old_moments
