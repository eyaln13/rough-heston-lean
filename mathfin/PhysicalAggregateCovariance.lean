import SmoothCoupledScaling
import CanonicalSeparatedVariance

/-! Exact covariance densities after summing the focal cluster rows. -/

open MeasureTheory Filter Set
open scoped NNReal

namespace RoughHeston

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem physicalCouplingDensity_clusters (σ : ℝ) (i j : ι) (v : Option ι → ℝ) :
    physicalCouplingDensity σ (some i) (some j) v =
      if i=j then σ^2*max (v (some i)) 0 else 0 := by
  unfold physicalCouplingDensity
  rw [smoothCoupledCovariance_cluster_cluster]
  simp only [one_mul, smoothVariancePositive]

theorem physicalCouplingDensity_cluster_companion (σ : ℝ) (i : ι) (v : Option ι → ℝ) :
    physicalCouplingDensity σ (some i) none v =
      σ^2*(max (v (some i)) 0 * Real.sqrt (max (v none) 0) /
        Real.sqrt (∑ j : ι, max (v (some j)) 0)) := by
  unfold physicalCouplingDensity
  rw [smoothCoupledCovariance_cluster_Y]
  simp only [one_mul, smoothVariancePositive, smoothClusterTotal]

theorem physicalCouplingDensity_symm (σ : ℝ) (i j : Option ι) (v : Option ι → ℝ) :
    physicalCouplingDensity σ i j v = physicalCouplingDensity σ j i v := by
  unfold physicalCouplingDensity eulerCovarianceCoefficient
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

/-- The aggregate covariance remains valid at zero total cluster variance. -/
theorem physicalCouplingDensity_sum_cluster_companion (σ : ℝ) (v : Option ι → ℝ) :
    (∑ i : ι, physicalCouplingDensity σ (some i) none v) =
      (σ*Real.sqrt (∑ i : ι, max (v (some i)) 0)) * (σ*Real.sqrt (max (v none) 0)) := by
  let X := ∑ i : ι, max (v (some i)) 0
  let Y := max (v none) 0
  have hX : 0 ≤ X := Finset.sum_nonneg fun i _ => le_max_right _ _
  have hXsq := Real.sq_sqrt hX
  simp_rw [physicalCouplingDensity_cluster_companion, ← Finset.mul_sum, ← Finset.sum_div,
    ← Finset.sum_mul]
  change σ^2*(X*Real.sqrt Y/Real.sqrt X) = _
  by_cases hx : Real.sqrt X = 0
  · rw [hx, div_zero, mul_zero, mul_zero, zero_mul]
  · have he : X*Real.sqrt Y/Real.sqrt X = Real.sqrt X*Real.sqrt Y := by
      rw [div_eq_iff hx]
      calc
        _ = (Real.sqrt X)^2*Real.sqrt Y := congrArg (fun x => x*Real.sqrt Y) hXsq.symm
        _ = _ := by ring
    rw [he]
    ring

theorem physicalCouplingDensity_sum_clusters (σ : ℝ) (v : Option ι → ℝ) :
    (∑ i : ι, ∑ j : ι, physicalCouplingDensity σ (some i) (some j) v) =
      σ^2*(∑ i : ι, max (v (some i)) 0) := by
  have h (i : ι) : (∑ j : ι, physicalCouplingDensity σ (some i) (some j) v) =
      σ^2*max (v (some i)) 0 := by
    rw [Finset.sum_eq_single i]
    · exact physicalCouplingDensity_diagonal _ _ _
    · intro j _ hj
      rw [physicalCouplingDensity_clusters, if_neg (Ne.symm hj)]
    · simp
  simp_rw [h, Finset.mul_sum]

/-- Summing cluster covariances gives exactly the covariance of the
aggregate and companion variances recorded by the pair-path limit. -/
theorem physicalCouplingDensity_aggregate_eq_canonical (σ : ℝ) (v : Option ι → ℝ)
    (hv : ∀ i, 0 ≤ v i) :
    let z : ℝ × ℝ := (∑ i : ι, v (some i), v none)
    (∑ i : ι, ∑ j : ι, physicalCouplingDensity σ (some i) (some j) v) =
      canonicalVarianceCovariance σ canonicalFirstVariance canonicalFirstVariance z ∧
    (∑ i : ι, physicalCouplingDensity σ (some i) none v) =
      canonicalVarianceCovariance σ canonicalFirstVariance canonicalSecondVariance z ∧
    physicalCouplingDensity σ none none v =
      canonicalVarianceCovariance σ canonicalSecondVariance canonicalSecondVariance z := by
  let x := ∑ i : ι, v (some i)
  have hx : 0 ≤ x := Finset.sum_nonneg fun i _ => hv (some i)
  intro z
  have h1 : canonicalFirstVariance z = x := max_eq_right hx
  have h2 : canonicalSecondVariance z = v none := max_eq_right (hv none)
  simp only [canonicalVarianceCovariance, ContinuousMap.coe_mk, h1, h2,
    physicalCouplingDensity_sum_clusters, physicalCouplingDensity_sum_cluster_companion,
    physicalCouplingDensity_diagonal, max_eq_left (hv _)]
  constructor
  · rw [← pow_two, mul_pow, Real.sq_sqrt hx]
  · exact ⟨rfl, by rw [← pow_two, mul_pow, Real.sq_sqrt (hv none)]⟩

#print axioms RoughHeston.physicalCouplingDensity_sum_cluster_companion
#print axioms RoughHeston.physicalCouplingDensity_aggregate_eq_canonical

end RoughHeston
