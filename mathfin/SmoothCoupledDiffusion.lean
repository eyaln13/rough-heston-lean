import EulerStoppedCovarianceTests
import Mathlib.Data.Fintype.Option

/-! Diffusion rows and covariances of the finite exponential cluster coupling. -/

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace RoughHeston

/-- The first option indexes Y and the clusters. The second indexes the
variance coordinate and the auxiliary exponential memories. -/
abbrev SmoothCoupledState (ι η : Type*) := (Option ι × Option η) → ℝ

noncomputable def smoothVariancePositive {ι η : Type*} (z : SmoothCoupledState ι η) (i : Option ι) : ℝ :=
  max (z (i, none)) 0

noncomputable def smoothClusterTotal {ι η : Type*} [Fintype ι] (z : SmoothCoupledState ι η) : ℝ :=
  ∑ i : ι, smoothVariancePositive z (some i)

noncomputable def smoothClusterUnit {ι η : Type*} [Fintype ι] (z : SmoothCoupledState ι η) (i : ι) : ℝ :=
  Real.sqrt (smoothVariancePositive z (some i) / smoothClusterTotal z)

theorem smoothVariancePositive_nonneg {ι η : Type*} (z : SmoothCoupledState ι η) (i : Option ι) :
    0 ≤ smoothVariancePositive z i := le_max_right _ _

theorem smoothClusterTotal_nonneg {ι η : Type*} [Fintype ι] (z : SmoothCoupledState ι η) :
    0 ≤ smoothClusterTotal z := Finset.sum_nonneg fun _ _ => smoothVariancePositive_nonneg _ _

theorem smoothVariancePositive_le_total {ι η : Type*} [Fintype ι] (z : SmoothCoupledState ι η) (i : ι) :
    smoothVariancePositive z (some i) ≤ smoothClusterTotal z :=
  Finset.single_le_sum (fun _ _ => smoothVariancePositive_nonneg _ _) (Finset.mem_univ i)

theorem smoothClusterUnit_abs_le_one {ι η : Type*} [Fintype ι] (z : SmoothCoupledState ι η) (i : ι) :
    |smoothClusterUnit z i| ≤ 1 := by
  rw [abs_of_nonneg (show 0 ≤ smoothClusterUnit z i from Real.sqrt_nonneg _)]
  by_cases h : smoothClusterTotal z = 0
  · simp [smoothClusterUnit, h]
  · have hpos : 0 < smoothClusterTotal z := lt_of_le_of_ne (smoothClusterTotal_nonneg z) (Ne.symm h)
    change Real.sqrt (smoothVariancePositive z (some i) / smoothClusterTotal z) ≤ 1
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt ((div_le_one₀ hpos).2 (smoothVariancePositive_le_total z i))

theorem smoothClusterUnit_sq_sum {ι η : Type*} [Fintype ι] (z : SmoothCoupledState ι η)
    (hz : smoothClusterTotal z ≠ 0) : ∑ i : ι, (smoothClusterUnit z i)^2 = 1 := by
  have hi (i : ι) :
      (smoothClusterUnit z i)^2 = smoothVariancePositive z (some i) / smoothClusterTotal z :=
    Real.sq_sqrt (div_nonneg (smoothVariancePositive_nonneg _ _) (smoothClusterTotal_nonneg _))
  simp_rw [hi]
  rw [← Finset.sum_div]
  exact div_self hz

variable {ι η : Type*} [Fintype ι] [DecidableEq ι]

/-- The driver columns are the common column and one column per cluster.
The auxiliary memory rows vanish. -/
noncomputable def smoothCoupledDiffusion (K₀ σ : ℝ) (_ : ℝ≥0)
    (z : SmoothCoupledState ι η) : Option ι × Option η → Option ι → ℝ
  | (_, some _), _ => 0
  | (none, none), none => K₀*σ * Real.sqrt (smoothVariancePositive z none)
  | (none, none), some _ => 0
  | (some i, none), none => K₀*σ * Real.sqrt (smoothVariancePositive z (some i)) * smoothClusterUnit z i
  | (some i, none), some j => K₀*σ * Real.sqrt (smoothVariancePositive z (some i)) *
      ((if i=j then 1 else 0) - smoothClusterUnit z i * smoothClusterUnit z j)

private theorem clusterProjection_dot_identity {u : ι → ℝ}
    (hu : ∑ j : ι, (u j)^2 = 1) (i l : ι) :
    u i*u l + (∑ j : ι, ((if i=j then 1 else 0) - u i*u j) *
      ((if l=j then 1 else 0) - u l*u j)) = if i=l then 1 else 0 := by
  let d (i j : ι) : ℝ := if i=j then 1 else 0
  have hD (i l : ι) : (∑ j, d i j * d l j) = d i l := by
    rw [Finset.sum_eq_single i]
    · simp [d, eq_comm]
    · intro j _ hj
      simp [d, Ne.symm hj]
    · simp
  have hU (i : ι) : (∑ j, d i j * u j) = u i := by
    rw [Finset.sum_eq_single i]
    · simp [d]
    · intro j _ hj
      simp [d, Ne.symm hj]
    · simp
  have hExpand :
      (∑ j : ι, (d i j-u i*u j)*(d l j-u l*u j)) =
        (∑ j, d i j*d l j) - u l*(∑ j, d i j*u j) - u i*(∑ j, d l j*u j) +
          (u i*u l)*(∑ j, (u j)^2) := by
    calc
      _ = ∑ j : ι, (d i j*d l j-u l*(d i j*u j)-u i*(d l j*u j)+(u i*u l)*(u j)^2) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  change u i*u l + (∑ j : ι, (d i j-u i*u j)*(d l j-u l*u j)) = d i l
  rw [hExpand, hD, hU, hU, hu]
  ring

variable [Fintype η]

/-- The cluster rows have zero cross covariance and the specified
square-root variance. -/
theorem smoothCoupledCovariance_cluster_cluster (K₀ σ : ℝ) (t : ℝ≥0)
    (z : SmoothCoupledState ι η) (i l : ι) :
    eulerCovarianceCoefficient (smoothCoupledDiffusion K₀ σ)
        (some i, none) (some l, none) t z =
      if i=l then (K₀*σ)^2 * smoothVariancePositive z (some i) else 0 := by
  let A (i : ι) := K₀*σ * Real.sqrt (smoothVariancePositive z (some i))
  let u := smoothClusterUnit z
  unfold eulerCovarianceCoefficient
  rw [Fintype.sum_option]
  change A i*u i*(A l*u l) +
      (∑ j : ι, (A i*((if i=j then 1 else 0)-u i*u j)) *
        (A l*((if l=j then 1 else 0)-u l*u j))) = _
  have hFact :
      A i*u i*(A l*u l) +
      (∑ j : ι, (A i*((if i=j then 1 else 0)-u i*u j)) *
        (A l*((if l=j then 1 else 0)-u l*u j))) =
      (A i*A l)*(u i*u l + ∑ j : ι, ((if i=j then 1 else 0)-u i*u j) *
        ((if l=j then 1 else 0)-u l*u j)) := by
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro j _
      ring
  rw [hFact]
  by_cases hz : smoothClusterTotal z = 0
  · have hi : smoothVariancePositive z (some i) = 0 :=
      le_antisymm ((smoothVariancePositive_le_total z i).trans_eq hz) (smoothVariancePositive_nonneg _ _)
    simp [A, hi]
  · have hU : ∑ j : ι, (u j)^2 = 1 := smoothClusterUnit_sq_sum z hz
    rw [clusterProjection_dot_identity hU]
    by_cases h : i=l
    · subst l
      simp only [ite_true, mul_one]
      rw [← pow_two]
      dsimp [A]
      rw [mul_pow, Real.sq_sqrt (smoothVariancePositive_nonneg _ _)]
    · simp [h]

/-- The common Y row has the prescribed diagonal variance. -/
theorem smoothCoupledCovariance_Y_Y (K₀ σ : ℝ) (t : ℝ≥0)
    (z : SmoothCoupledState ι η) :
    eulerCovarianceCoefficient (smoothCoupledDiffusion K₀ σ)
        (none, none) (none, none) t z =
      (K₀*σ)^2 * smoothVariancePositive z none := by
  classical
  unfold eulerCovarianceCoefficient
  rw [Fintype.sum_option]
  simp only [smoothCoupledDiffusion, zero_mul, Finset.sum_const_zero, add_zero]
  rw [← pow_two, mul_pow, Real.sq_sqrt (smoothVariancePositive_nonneg _ _)]

/-- The cluster/Y cross covariance implements shared aggregate Brownian
noise. The real division convention makes it zero at a zero total. -/
theorem smoothCoupledCovariance_cluster_Y (K₀ σ : ℝ) (t : ℝ≥0)
    (z : SmoothCoupledState ι η) (i : ι) :
    eulerCovarianceCoefficient (smoothCoupledDiffusion K₀ σ)
        (some i, none) (none, none) t z =
      (K₀*σ)^2 * (smoothVariancePositive z (some i) *
        Real.sqrt (smoothVariancePositive z none) / Real.sqrt (smoothClusterTotal z)) := by
  unfold eulerCovarianceCoefficient
  rw [Fintype.sum_option]
  simp only [smoothCoupledDiffusion, mul_zero, Finset.sum_const_zero, add_zero]
  rw [smoothClusterUnit, Real.sqrt_div (smoothVariancePositive_nonneg z (some i))]
  calc
    _ = (K₀*σ)^2 * (Real.sqrt (smoothVariancePositive z (some i))^2 *
        Real.sqrt (smoothVariancePositive z none) / Real.sqrt (smoothClusterTotal z)) := by ring
    _ = _ := by rw [Real.sq_sqrt (smoothVariancePositive_nonneg z (some i))]

/-- Any auxiliary memory row has zero covariance with every coordinate. -/
theorem smoothCoupledCovariance_memory_zero (K₀ σ : ℝ) (t : ℝ≥0)
    (z : SmoothCoupledState ι η) (i : Option ι) (j : η) (k : Option ι × Option η) :
    eulerCovarianceCoefficient (smoothCoupledDiffusion K₀ σ) (i, some j) k t z = 0 := by
  simp [eulerCovarianceCoefficient, smoothCoupledDiffusion]

#print axioms RoughHeston.smoothCoupledCovariance_cluster_cluster
#print axioms RoughHeston.smoothCoupledCovariance_Y_Y
#print axioms RoughHeston.smoothCoupledCovariance_cluster_Y
#print axioms RoughHeston.smoothCoupledCovariance_memory_zero

end RoughHeston
