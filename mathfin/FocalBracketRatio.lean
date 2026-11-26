import FocalDriftEnergy
import RankOneCompensators

open MeasureTheory Set Filter
open scoped NNReal Topology Interval

namespace RoughHeston
namespace GirsanovPort

theorem focalBracketRatio_nonneg {u x σ : ℝ} (hσ : 0 ≤ σ) (hu : 0 ≤ u) :
    0 ≤ σ * u / Real.sqrt x :=
  div_nonneg (mul_nonneg hσ hu) (Real.sqrt_nonneg _)

theorem focalBracketRatio_le_sqrt {u x σ : ℝ}
    (hσ : 0 ≤ σ) (hu : 0 ≤ u) (hux : u ≤ x) :
    σ * u / Real.sqrt x ≤ σ * Real.sqrt x := by
  rcases eq_or_lt_of_le (hu.trans hux) with h0 | hx
  · simp [← h0]
  have hs := Real.sqrt_pos.2 hx
  rw [div_le_iff₀ hs]
  calc
    _ ≤ σ * x := mul_le_mul_of_nonneg_left hux hσ
    _ = _ := by rw [mul_assoc, ← sq, Real.sq_sqrt hx.le]

/-- The normalized cluster coefficient is continuous at a zero of the
aggregate because the nonnegative focal cluster is bounded by the aggregate. -/
theorem continuousOn_focalBracketRatio {ι : Type*} [TopologicalSpace ι] {s : Set ι}
    {U X : ι → ℝ} (hU : ContinuousOn U s) (hX : ContinuousOn X s)
    {σ : ℝ} (hσ : 0 ≤ σ) (hParts : ∀ t ∈ s, 0 ≤ U t ∧ U t ≤ X t) :
    ContinuousOn (fun t => σ * U t / Real.sqrt (X t)) s := by
  intro t ht
  have h0 := (hParts t ht).1.trans (hParts t ht).2
  rcases eq_or_lt_of_le h0 with hzero | hpos
  · have hUpper : Tendsto (fun r => σ * Real.sqrt (X r)) (𝓝[s] t) (𝓝 0) := by
      have h := (Real.continuous_sqrt.continuousAt.tendsto.comp (hX t ht)).const_mul σ
      simpa only [Function.comp_def, ← hzero, Real.sqrt_zero, mul_zero] using h
    have hL : Tendsto (fun r => σ * U r / Real.sqrt (X r)) (𝓝[s] t) (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpper ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact focalBracketRatio_nonneg hσ (hParts r hr).1
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact focalBracketRatio_le_sqrt hσ (hParts r hr).1 (hParts r hr).2
    simpa only [ContinuousWithinAt, ← hzero, Real.sqrt_zero, div_zero] using hL
  · exact (continuousWithinAt_const.mul (hU t ht)).div
      (Real.continuous_sqrt.continuousAt.comp_continuousWithinAt (hX t ht)) (Real.sqrt_pos.2 hpos).ne'

/-- The product of total normalization amplitude and focal coefficient
equals the sum of the aggregate and competitor focal bracket densities. -/
theorem focalBracketSum_eq {u x y σ : ℝ} (hu : 0 ≤ u) (hux : u ≤ x) :
    σ * (Real.sqrt x + Real.sqrt y) * (σ * u / Real.sqrt x) =
      σ ^ 2 * u + σ ^ 2 * u * Real.sqrt y / Real.sqrt x := by
  rcases eq_or_lt_of_le (hu.trans hux) with hx | hx
  · have hu0 : u = 0 := hu.antisymm' (hux.trans hx.ge)
    simp [hu0]
  have h := (Real.sqrt_pos.2 hx).ne'
  field_simp

theorem focalBracketRatio_eq_zero_of_totalAmplitude_zero {u x y σ : ℝ} (hσ : 0 < σ)
    (hz : σ * (Real.sqrt x + Real.sqrt y) = 0) :
    σ * u / Real.sqrt x = 0 := by
  have hz' := (mul_eq_zero.mp hz).resolve_left hσ.ne'
  have hs : Real.sqrt x = 0 := by
    linarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y]
  simp [hs]

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.continuousOn_focalBracketRatio
#print axioms RoughHeston.GirsanovPort.focalBracketSum_eq
