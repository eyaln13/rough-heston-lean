import FractionalBoundaryHistory
import FractionalPowerRiccati
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

open MeasureTheory Set Filter
open scoped MeasureTheory Topology

namespace RoughHeston

noncomputable def backwardPowerCoefficient (α p : ℝ) : ℝ :=
  p * Real.Gamma (α - p) / Real.Gamma (1 - p)

/-- At the critical exponent, the backward power coefficient is half
the coefficient available from the singular Riccati limit. -/
theorem backwardPowerCoefficient_critical {α a : ℝ}
    (hα' : α < 1) (ha : 0 < a) :
    backwardPowerCoefficient α (2 * α - 1) = a * singularRiccatiCoefficient α a := by
  unfold backwardPowerCoefficient singularRiccatiCoefficient
  rw [show α - (2 * α - 1) = 1 - α by ring,
    show 1 - (2 * α - 1) = 2 - 2 * α by ring]
  have hΓ : Real.Gamma (2 - 2 * α) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  field_simp [ha.ne', hΓ]

/-- A power strictly above the critical one still has coefficient
strictly below twice the critical coefficient. -/
theorem exists_backwardPowerCoefficient_gap {α a : ℝ}
    (hα : 1 / 2 < α) (hα' : α < 1) (ha : 0 < a) :
    ∃ p ∈ Ioo (2 * α - 1) α,
      backwardPowerCoefficient α p < 2 * a * singularRiccatiCoefficient α a := by
  let β := 2 * α - 1
  have hc : 0 < singularRiccatiCoefficient α a := singularRiccatiCoefficient_pos hα hα' ha
  have hΓ : Real.Gamma (1 - β) ≠ 0 := (Real.Gamma_pos_of_pos (by dsimp [β]; linarith)).ne'
  have hcont : ContinuousAt (backwardPowerCoefficient α) β := by
    unfold backwardPowerCoefficient
    refine (continuousAt_id.mul ?_).div ?_ hΓ
    · have hG : ContinuousAt Real.Gamma (α - β) :=
        (Real.differentiableAt_Gamma fun n h => by
          dsimp [β] at h
          linarith [Nat.cast_nonneg (α := ℝ) n]).continuousAt
      exact hG.comp (continuousAt_const.sub continuousAt_id)
    · have hG : ContinuousAt Real.Gamma (1 - β) :=
        (Real.differentiableAt_Gamma fun n h => by
          dsimp [β] at h
          linarith [Nat.cast_nonneg (α := ℝ) n]).continuousAt
      exact hG.comp (continuousAt_const.sub continuousAt_id)
  have hstrict : backwardPowerCoefficient α β < 2 * a * singularRiccatiCoefficient α a := by
    rw [backwardPowerCoefficient_critical hα' ha]
    nlinarith [mul_pos ha hc]
  obtain ⟨r, hr, hn⟩ := Metric.eventually_nhds_iff.mp
    (hcont.eventually (Iio_mem_nhds hstrict))
  let δ := min (r / 2) ((α - β) / 2)
  have hβ : β < α := by dsimp [β]; linarith
  have hδ : 0 < δ := lt_min (half_pos hr) (half_pos (sub_pos.mpr hβ))
  refine ⟨β + δ, ⟨by linarith, ?_⟩, hn ?_⟩
  · linarith [min_le_right (r / 2) ((α - β) / 2)]
  · rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hδ]
    exact (min_le_left _ _).trans_lt (by linarith)

end RoughHeston

#print axioms RoughHeston.backwardPowerCoefficient_critical
#print axioms RoughHeston.exists_backwardPowerCoefficient_gap
