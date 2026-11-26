import SmoothCoupledDiffusion

/-! Continuity and linear growth for the finite exponential coupling, including zero aggregate mass. -/

open Filter
open scoped NNReal Topology

namespace RoughHeston

variable {ι η : Type*} [Fintype ι] [DecidableEq ι] [Fintype η]

theorem continuous_smoothVariancePositive (i : Option ι) :
    Continuous (fun z : SmoothCoupledState ι η => smoothVariancePositive z i) :=
  (continuous_apply (i, none)).max continuous_const

theorem continuous_smoothClusterTotal :
    Continuous (smoothClusterTotal : SmoothCoupledState ι η → ℝ) :=
  continuous_finsetSum _ fun i _ => continuous_smoothVariancePositive (some i)

theorem continuousAt_smoothClusterUnit {z : SmoothCoupledState ι η}
    (hz : smoothClusterTotal z ≠ 0) (i : ι) :
    ContinuousAt (fun y => smoothClusterUnit y i) z :=
  ((continuous_smoothVariancePositive (η := η) (some i)).continuousAt.div
    continuous_smoothClusterTotal.continuousAt hz).sqrt

private theorem continuousAt_mul_of_zero_and_bounded {E : Type*} [TopologicalSpace E]
    {x : E} {f g : E → ℝ} {B : ℝ} (hf : ContinuousAt f x) (hzero : f x = 0)
    (hg : ∀ y, ‖g y‖ ≤ B) : ContinuousAt (fun y => f y * g y) x := by
  change Tendsto (fun y => f y * g y) (𝓝 x) (𝓝 (f x * g x))
  rw [hzero, zero_mul]
  apply squeeze_zero_norm (a := fun y => ‖f y‖ * B)
  · intro y
    simpa only [norm_mul] using mul_le_mul_of_nonneg_left (hg y) (norm_nonneg (f y))
  · have h := hf.norm.mul (show ContinuousAt (fun _ : E => B) x from continuousAt_const)
    change Tendsto (fun y => ‖f y‖ * B) (𝓝 x) (𝓝 (‖f x‖ * B)) at h
    rwa [hzero, norm_zero, zero_mul] at h

private theorem clusterProjection_norm_le (z : SmoothCoupledState ι η) (i j : ι) :
    ‖(if i=j then 1 else 0) - smoothClusterUnit z i * smoothClusterUnit z j‖ ≤ 2 := by
  calc
    _ ≤ ‖(if i=j then (1 : ℝ) else 0)‖ + ‖smoothClusterUnit z i * smoothClusterUnit z j‖ :=
      norm_sub_le _ _
    _ ≤ 1 + 1 := by
      apply add_le_add
      · split_ifs <;> norm_num
      · rw [norm_mul, ← one_mul (1 : ℝ)]
        exact mul_le_mul (smoothClusterUnit_abs_le_one z i) (smoothClusterUnit_abs_le_one z j)
          (norm_nonneg _) zero_le_one
    _ = _ := by norm_num

/-- Even though the normalized cluster column can be discontinuous at total
zero, multiplication by the variance square root gives a continuous row. -/
theorem continuous_smoothCoupledDiffusion (K₀ σ : ℝ) (i : Option ι × Option η) (j : Option ι) :
    Continuous (fun w : ℝ≥0 × SmoothCoupledState ι η => smoothCoupledDiffusion K₀ σ w.1 w.2 i j) := by
  obtain ⟨i, _ | k⟩ := i
  swap
  · exact continuous_const
  cases i with
  | none =>
    cases j with
    | none =>
      exact continuous_const.mul ((continuous_smoothVariancePositive none).sqrt.comp continuous_snd)
    | some j => exact continuous_const
  | some i =>
    let f (z : SmoothCoupledState ι η) := K₀*σ*Real.sqrt (smoothVariancePositive z (some i))
    have hf : Continuous f := continuous_const.mul (continuous_smoothVariancePositive (some i)).sqrt
    have h0 (z : SmoothCoupledState ι η) (hz : smoothClusterTotal z = 0) : f z = 0 := by
      have hi := le_antisymm ((smoothVariancePositive_le_total z i).trans_eq hz)
        (smoothVariancePositive_nonneg z (some i))
      simp [f, hi]
    cases j with
    | none =>
      have hc : Continuous (fun z => f z * smoothClusterUnit z i) := by
        rw [continuous_iff_continuousAt]
        intro z
        by_cases hz : smoothClusterTotal z = 0
        · exact continuousAt_mul_of_zero_and_bounded hf.continuousAt (h0 z hz)
            (fun y => smoothClusterUnit_abs_le_one y i)
        · exact hf.continuousAt.mul (continuousAt_smoothClusterUnit hz i)
      exact hc.comp continuous_snd
    | some j =>
      have hc : Continuous (fun z => f z * ((if i=j then 1 else 0) -
          smoothClusterUnit z i * smoothClusterUnit z j)) := by
        rw [continuous_iff_continuousAt]
        intro z
        by_cases hz : smoothClusterTotal z = 0
        · exact continuousAt_mul_of_zero_and_bounded hf.continuousAt (h0 z hz)
            (fun y => clusterProjection_norm_le y i j)
        · exact hf.continuousAt.mul (continuousAt_const.sub
            ((continuousAt_smoothClusterUnit hz i).mul (continuousAt_smoothClusterUnit hz j)))
      exact hc.comp continuous_snd

private theorem norm_sqrt_variance_le (z : SmoothCoupledState ι η) (i : Option ι) :
    ‖Real.sqrt (smoothVariancePositive z i)‖ ≤ 1 + ‖z‖ := by
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 : smoothVariancePositive z i ≤ ‖z‖ := max_le
    ((le_abs_self _).trans (norm_le_pi_norm z (i, none))) (norm_nonneg _)
  nlinarith [norm_nonneg z, sq_nonneg ‖z‖]

/-- Common coordinatewise linear-growth estimate for the diffusion rows. -/
theorem smoothCoupledDiffusion_linear_growth (K₀ σ : ℝ) (t : ℝ≥0)
    (z : SmoothCoupledState ι η) (i : Option ι × Option η) (j : Option ι) :
    ‖smoothCoupledDiffusion K₀ σ t z i j‖ ≤ (2*‖K₀*σ‖)*(1+‖z‖) := by
  have hNonneg : 0 ≤ (2*‖K₀*σ‖)*(1+‖z‖) := by positivity
  have hbase (i : Option ι) : ‖K₀*σ*Real.sqrt (smoothVariancePositive z i)‖ ≤ ‖K₀*σ‖*(1+‖z‖) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_sqrt_variance_le z i) (norm_nonneg _)
  have htwo (i : Option ι) : ‖K₀*σ*Real.sqrt (smoothVariancePositive z i)‖ * 2 ≤
      (2*‖K₀*σ‖)*(1+‖z‖) := by
    linarith [mul_le_mul_of_nonneg_right (hbase i) (show 0 ≤ (2 : ℝ) by norm_num)]
  obtain ⟨i, _ | k⟩ := i
  swap
  · simpa only [smoothCoupledDiffusion, norm_zero] using hNonneg
  cases i with
  | none =>
    cases j with
    | none =>
      exact (le_mul_of_one_le_right (norm_nonneg _) (show 1 ≤ (2 : ℝ) by norm_num)).trans (htwo none)
    | some j => simpa only [smoothCoupledDiffusion, norm_zero] using hNonneg
  | some i =>
    cases j with
    | none =>
      rw [smoothCoupledDiffusion, norm_mul]
      exact (mul_le_mul_of_nonneg_left ((smoothClusterUnit_abs_le_one z i).trans (by norm_num))
        (norm_nonneg _)).trans (htwo (some i))
    | some j =>
      rw [smoothCoupledDiffusion, norm_mul]
      exact (mul_le_mul_of_nonneg_left (clusterProjection_norm_le z i j)
        (norm_nonneg _)).trans (htwo (some i))

#print axioms RoughHeston.continuous_smoothCoupledDiffusion
#print axioms RoughHeston.smoothCoupledDiffusion_linear_growth

end RoughHeston
