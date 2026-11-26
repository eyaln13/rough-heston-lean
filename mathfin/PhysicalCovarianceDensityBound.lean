import SmoothCoupledScaling

/-! A covariance envelope for uniform moments of the canonical
compensated products. -/

open MeasureTheory Set

namespace RoughHeston

theorem norm_physicalCouplingDensity_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : ℝ) (i j : Option ι) (v : Option ι → ℝ) :
    ‖physicalCouplingDensity σ i j v‖ ≤
      (σ^2/2)*(max (v i) 0 + max (v j) 0) := by
  let z : SmoothCoupledState ι Empty := fun a => v a.1
  let f (i a : Option ι) := smoothCoupledDiffusion (η := Empty) 1 σ 0 z (i, none) a
  have hDiag (k : Option ι) : (∑ a : Option ι, (f k a)^2) = σ^2 * max (v k) 0 := by
    calc
      _ = physicalCouplingDensity σ k k v := by
        unfold physicalCouplingDensity eulerCovarianceCoefficient
        simp only [f, z, pow_two]
      _ = _ := physicalCouplingDensity_diagonal _ _ _
  change ‖∑ a : Option ι, f i a*f j a‖ ≤ _
  calc
    _ ≤ ∑ a : Option ι, ‖f i a*f j a‖ := norm_sum_le _ _
    _ ≤ ∑ a : Option ι, ((f i a)^2+(f j a)^2)/2 := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      nlinarith [sq_nonneg (|f i a|-|f j a|), sq_abs (f i a), sq_abs (f j a)]
    _ = _ := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, hDiag, hDiag]
      ring

#print axioms RoughHeston.norm_physicalCouplingDensity_le

end RoughHeston
