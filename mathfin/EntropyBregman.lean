import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Set
open scoped ENNReal

namespace RoughHeston
namespace GirsanovPort

theorem hasDerivAt_mul_log {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun z : ℝ => z * Real.log z) (Real.log x + 1) x := by
  have hd := (hasDerivAt_id x).mul (Real.hasDerivAt_log hx.ne')
  change HasDerivAt ((id : ℝ → ℝ) * Real.log) (Real.log x + 1) x
  simpa only [id_eq, one_mul, mul_inv_cancel₀ hx.ne'] using hd

/-- On a positive interval with upper endpoint `K`, the entropy
increment exceeds its tangent by at least the quadratic Bregman term. -/
theorem entropy_bregman_lower {a b K : ℝ} (ha : 0 < a) (hb : 0 < b)
    (haK : a ≤ K) (hbK : b ≤ K) :
    (b - a) ^ 2 / (2 * K) ≤
      b * Real.log b - a * Real.log a - (Real.log a + 1) * (b - a) := by
  let c : ℝ := K⁻¹
  let φ (z : ℝ) := z * Real.log z - (c / 2) * z ^ 2
  let ψ (z : ℝ) := Real.log z + 1 - c * z
  have hφ {z : ℝ} (hz : 0 < z) : HasDerivAt φ (ψ z) z := by
    have h := (hasDerivAt_mul_log hz).sub (((hasDerivAt_id z).pow 2).const_mul (c / 2))
    have hφeq : φ = (fun z => z * Real.log z) - fun y => c / 2 * (id ^ 2) y := rfl
    rw [hφeq]
    convert h using 1
    dsimp [ψ]
    ring
  have hψ {z : ℝ} (hz : 0 < z) : HasDerivAt ψ (z⁻¹ - c) z := by
    change HasDerivAt ((fun x => Real.log x + 1) - fun y => c * id y) (z⁻¹ - c) z
    simpa only [mul_one] using
      ((Real.hasDerivAt_log hz.ne').add_const 1).sub ((hasDerivAt_id z).const_mul c)
  have hConv : ConvexOn ℝ (Ioc (0 : ℝ) K) φ := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioc _ _)
      (fun z hz => (hφ hz.1).continuousAt.continuousWithinAt)
      (fun z hz => (hφ (interior_subset hz).1).hasDerivWithinAt)
      (fun z hz => (hψ (interior_subset hz).1).hasDerivWithinAt) ?_
    intro z hz
    exact sub_nonneg.mpr (inv_anti₀ (interior_subset hz).1 (interior_subset hz).2)
  have hSupport : φ a + ψ a * (b - a) ≤ φ b := by
    rcases lt_trichotomy a b with hab | rfl | hba
    · have h := hConv.le_slope_of_hasDerivAt ⟨ha, haK⟩ ⟨hb, hbK⟩ hab (hφ ha)
      rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hab)] at h
      linarith
    · simp
    · have h := hConv.slope_le_of_hasDerivAt ⟨hb, hbK⟩ ⟨ha, haK⟩ hba (hφ ha)
      rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hba)] at h
      nlinarith
  have he : (b - a) ^ 2 / (2 * K) = (c / 2) * (b - a) ^ 2 := by
    have hK : K ≠ 0 := (ha.trans_le haK).ne'
    dsimp [c]
    field_simp
  rw [he]
  dsimp [φ, ψ] at hSupport
  nlinarith

/-- The entropy density has at most quadratic absolute growth on the
nonnegative half-line. -/
theorem abs_mul_log_le_sq_add_one {x : ℝ} (hx : 0 ≤ x) :
    |x * Real.log x| ≤ x ^ 2 + 1 := by
  rcases eq_or_lt_of_le hx with rfl | hx'
  · simp
  have hm := mul_le_mul_of_nonneg_left (Real.log_le_self hx) hx
  have hi := mul_le_mul_of_nonneg_left (Real.log_le_self (inv_nonneg.mpr hx)) hx
  rw [Real.log_inv, mul_inv_cancel₀ hx'.ne'] at hi
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

theorem integrable_mulLog_of_nonnegative_L2 {Z : Ω → ℝ} (hZ : MemLp Z 2 μ)
    (hZ₀ : ∀ᵐ ω ∂μ, 0 ≤ Z ω) : Integrable (fun ω => Z ω * Real.log (Z ω)) μ := by
  have hm := hZ.aestronglyMeasurable.mul hZ.aemeasurable.log.aestronglyMeasurable
  have hi : Integrable (fun ω => Z ω ^ 2 + 1) μ := hZ.integrable_sq.add (integrable_const 1)
  refine hi.mono' hm ?_
  exact hZ₀.mono fun ω hω => by simpa only [Real.norm_eq_abs] using abs_mul_log_le_sq_add_one hω

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.entropy_bregman_lower
#print axioms RoughHeston.GirsanovPort.integrable_mulLog_of_nonnegative_L2
