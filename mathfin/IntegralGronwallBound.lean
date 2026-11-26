import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Integral Grönwall estimate for continuous nonnegative moment functions. -/

open Set MeasureTheory

namespace RoughHeston

/-- The standard integral Grönwall inequality for a continuous
nonnegative function on a real time horizon. -/
theorem le_exp_of_le_const_add_mul_intervalIntegral {f : ℝ → ℝ}
    (hf : Continuous f) (hfn : ∀ u, 0 ≤ f u)
    {A K T : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hbound : ∀ t ∈ Icc 0 T, f t ≤ A + K * (∫ u in 0..t, f u))
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    f t ≤ A * Real.exp (K * t) := by
  let F (v : ℝ) := A + K * (∫ u in 0..v, f u)
  have hFn (v : ℝ) (hv : 0 ≤ v) : 0 ≤ F v :=
    add_nonneg hA (mul_nonneg hK (intervalIntegral.integral_nonneg_of_forall hv hfn))
  have hv (v : ℝ) : HasDerivAt F (K * f v) v :=
    ((intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 v)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt).const_mul K).const_add A
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun v => (hv v).continuousAt
  have hF0 : F 0 = A := by simp [F]
  have H := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := F) (f' := fun v => K * f v) (δ := A) (K := K) (ε := 0)
    (a := 0) (b := T) hFc.continuousOn
    (fun v _ => (hv v).hasDerivWithinAt)
    (by rw [hF0, Real.norm_of_nonneg hA])
    (fun v hv => by
      rw [Real.norm_of_nonneg (mul_nonneg hK (hfn v)), Real.norm_of_nonneg (hFn v hv.1), add_zero]
      exact mul_le_mul_of_nonneg_left (hbound v ⟨hv.1, hv.2.le⟩) hK) t ht
  rw [Real.norm_of_nonneg (hFn t ht.1), sub_zero, gronwallBound_ε0] at H
  exact (hbound t ht).trans H

#print axioms RoughHeston.le_exp_of_le_const_add_mul_intervalIntegral

end RoughHeston
