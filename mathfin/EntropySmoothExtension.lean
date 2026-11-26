import EntropyMartingaleGrid
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.MetricSpace.Lipschitz

open MeasureTheory Set
open scoped NNReal Interval

namespace RoughHeston
namespace GirsanovPort

noncomputable def extendedEntropySecond (η x : ℝ) : ℝ := (max x 0 + η)⁻¹

noncomputable def extendedEntropyFirst (η x : ℝ) : ℝ :=
  Real.log η + 1 + ∫ r in 0..x, extendedEntropySecond η r

noncomputable def extendedEntropy (η x : ℝ) : ℝ :=
  η * Real.log η + ∫ r in 0..x, extendedEntropyFirst η r

private theorem extendedEntropySecond_pos {η : ℝ} (hη : 0 < η) (x : ℝ) :
    0 < max x 0 + η := add_pos_of_nonneg_of_pos (le_max_right _ _) hη

theorem extendedEntropySecond_continuous {η : ℝ} (hη : 0 < η) :
    Continuous (extendedEntropySecond η) :=
  ((continuous_id.max continuous_const).add continuous_const).inv₀
    (fun x => (extendedEntropySecond_pos hη x).ne')

theorem extendedEntropySecond_lipschitz {η : ℝ} (hη : 0 < η) :
    LipschitzWith ⟨(η * η)⁻¹, inv_nonneg.mpr (mul_nonneg hη.le hη.le)⟩ (extendedEntropySecond η) := by
  refine lipschitzWith_iff_dist_le_mul.mpr ?_
  intro x y
  let a := max x 0 + η
  let b := max y 0 + η
  have ha : 0 < a := extendedEntropySecond_pos hη x
  have hb : 0 < b := extendedEntropySecond_pos hη y
  have hea : η ≤ a := le_add_of_nonneg_left (le_max_right _ _)
  have heb : η ≤ b := le_add_of_nonneg_left (le_max_right _ _)
  have hdist := (lipschitzWith_iff_dist_le_mul.mp ((LipschitzWith.id).max_const (0 : ℝ))) y x
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hdist
  have hd : |b - a| ≤ |x - y| := by
    simpa only [a, b, id_eq, add_sub_add_right_eq_sub, abs_sub_comm y x] using hdist
  have hden : η * η ≤ a * b := mul_le_mul hea heb hη.le ha.le
  rw [Real.dist_eq, Real.dist_eq]
  change |a⁻¹ - b⁻¹| ≤ (η * η)⁻¹ * |x - y|
  rw [inv_sub_inv ha.ne' hb.ne', abs_div, abs_of_pos (mul_pos ha hb), ← div_eq_inv_mul]
  exact (div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hη hη) hden).trans
    (div_le_div_of_nonneg_right hd (mul_nonneg hη.le hη.le))

theorem extendedEntropyFirst_hasDerivAt {η : ℝ} (hη : 0 < η) (x : ℝ) :
    HasDerivAt (extendedEntropyFirst η) (extendedEntropySecond η x) x := by
  have hc := extendedEntropySecond_continuous hη
  have h := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  exact h.const_add _

theorem extendedEntropy_hasDerivAt {η : ℝ} (hη : 0 < η) (x : ℝ) :
    HasDerivAt (extendedEntropy η) (extendedEntropyFirst η x) x := by
  have hc : Continuous (extendedEntropyFirst η) :=
    (show Differentiable ℝ (extendedEntropyFirst η) from
      fun x => (extendedEntropyFirst_hasDerivAt hη x).differentiableAt).continuous
  have h := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  exact h.const_add _

private theorem extendedEntropyFirst_eq {η x : ℝ} (hη : 0 < η) (hx : 0 ≤ x) :
    extendedEntropyFirst η x = Real.log (x + η) + 1 := by
  let f (y : ℝ) := Real.log (y + η) + 1
  have hd {y : ℝ} (hy : 0 ≤ y) : HasDerivAt f (extendedEntropySecond η y) y := by
    have hp : 0 < y + η := by positivity
    have h := ((Real.hasDerivAt_log hp.ne').comp y ((hasDerivAt_id y).add_const η)).add_const 1
    simpa only [f, Function.comp_def, extendedEntropySecond, max_eq_left hy, id_eq, mul_one] using h
  refine eq_of_has_deriv_right_eq
    (fun y _ => (extendedEntropyFirst_hasDerivAt hη y).hasDerivWithinAt)
    (fun y hy => (hd hy.1).hasDerivWithinAt)
    (fun y _ => (extendedEntropyFirst_hasDerivAt hη y).continuousAt.continuousWithinAt)
    (fun y hy => (hd hy.1).continuousAt.continuousWithinAt)
    (by simp [extendedEntropyFirst, f]) x ⟨hx, le_rfl⟩

/-- The globally differentiable extension agrees with shifted entropy
on the nonnegative half-line and has a globally Lipschitz second derivative. -/
theorem extendedEntropy_eq {η x : ℝ} (hη : 0 < η) (hx : 0 ≤ x) :
    extendedEntropy η x = regularizedEntropy η x := by
  have hd {y : ℝ} (hy : 0 ≤ y) :
      HasDerivAt (regularizedEntropy η) (extendedEntropyFirst η y) y := by
    rw [extendedEntropyFirst_eq hη hy]
    change HasDerivAt (fun x => (x + η) * Real.log (x + η)) (Real.log (y + η) + 1) y
    have hp : 0 < y + η := by positivity
    have h := (hasDerivAt_mul_log hp).comp y ((hasDerivAt_id y).add_const η)
    simpa only [regularizedEntropy, Function.comp_def, id_eq, mul_one] using h
  refine eq_of_has_deriv_right_eq
    (fun y _ => (extendedEntropy_hasDerivAt hη y).hasDerivWithinAt)
    (fun y hy => (hd hy.1).hasDerivWithinAt)
    (fun y _ => (extendedEntropy_hasDerivAt hη y).continuousAt.continuousWithinAt)
    (fun y hy => (hd hy.1).continuousAt.continuousWithinAt)
    (by simp [extendedEntropy, regularizedEntropy]) x ⟨hx, le_rfl⟩

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.extendedEntropy_eq
#print axioms RoughHeston.GirsanovPort.extendedEntropySecond_lipschitz
