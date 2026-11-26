import SmoothVarianceLift
import Verification

/-! Differentiating a smooth exponential convolution by integrating factors. -/

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RoughHeston

variable {ξ : Type*} [Fintype ξ]

noncomputable def smoothExponentialKernel (c rate : ξ → ℝ) (t : ℝ) : ℝ :=
  ∑ j, c j*Real.exp (-(rate j*t))

noncomputable def smoothExponentialKernelDerivative (c rate : ξ → ℝ) (t : ℝ) : ℝ :=
  ∑ j, (-(c j*rate j))*Real.exp (-(rate j*t))

theorem continuous_smoothExponentialKernel (c rate : ξ → ℝ) :
    Continuous (smoothExponentialKernel c rate) :=
  continuous_finsetSum _ fun j _ => by fun_prop

theorem continuous_smoothExponentialKernelDerivative (c rate : ξ → ℝ) :
    Continuous (smoothExponentialKernelDerivative c rate) :=
  continuous_finsetSum _ fun j _ => by fun_prop

private theorem hasDerivAt_exp_neg_rate (rate t : ℝ) :
    HasDerivAt (fun r : ℝ => Real.exp (-(rate*r))) (Real.exp (-(rate*t))*(-rate)) t := by
  have h : HasDerivAt (fun r : ℝ => -(rate*r)) (-rate) t := by
    simpa only [id_eq, neg_mul, mul_one] using (hasDerivAt_id t).const_mul (-rate)
  exact h.exp

theorem smoothExponentialKernel_hasDerivAt (c rate : ξ → ℝ) (t : ℝ) :
    HasDerivAt (smoothExponentialKernel c rate) (smoothExponentialKernelDerivative c rate t) t := by
  unfold smoothExponentialKernel smoothExponentialKernelDerivative
  apply HasDerivAt.fun_sum
  intro j _
  convert (hasDerivAt_exp_neg_rate (rate j) t).const_mul (c j) using 1
  ring

private noncomputable def signedExponentialHistory (rate : ℝ) (J : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..t, Real.exp (-(rate*(t-r))) * J r

private theorem signedExponentialHistory_eq_integrating_factor (rate : ℝ) (J : ℝ → ℝ) (t : ℝ) :
    signedExponentialHistory rate J t =
      Real.exp (-(rate*t))*(∫ r in (0 : ℝ)..t, Real.exp (rate*r)*J r) := by
  rw [signedExponentialHistory, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro r _
  change Real.exp (-(rate*(t-r)))*J r = Real.exp (-(rate*t))*(Real.exp (rate*r)*J r)
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

private theorem signedExponentialHistory_hasDerivAt {J : ℝ → ℝ} (hJ : Continuous J)
    (rate t : ℝ) :
    HasDerivAt (signedExponentialHistory rate J) (J t-rate*signedExponentialHistory rate J t) t := by
  let f (r : ℝ) := Real.exp (rate*r)*J r
  have hf : Continuous f := (continuous_const.mul continuous_id).rexp.mul hJ
  have hI : HasDerivAt (fun u => ∫ r in (0 : ℝ)..u, f r) (f t) t :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have h := (hasDerivAt_exp_neg_rate rate t).fun_mul hI
  rw [show signedExponentialHistory rate J =
    (fun u => Real.exp (-(rate*u))*(∫ r in (0 : ℝ)..u, Real.exp (rate*r)*J r)) from
    funext (signedExponentialHistory_eq_integrating_factor rate J)]
  convert h using 1
  simp only [f]
  have he : Real.exp (-(rate*t))*Real.exp (rate*t) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [← mul_assoc (Real.exp (-(rate*t))) (Real.exp (rate*t)), he, one_mul]
  ring

private theorem smoothKernel_intervalConvolution_eq_sum (c rate : ξ → ℝ) {J : ℝ → ℝ}
    (hJ : Continuous J) (t : ℝ) :
    (∫ r in (0 : ℝ)..t, smoothExponentialKernel c rate (t-r)*J r) =
      ∑ j, c j*signedExponentialHistory (rate j) J t := by
  unfold smoothExponentialKernel signedExponentialHistory
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [intervalIntegral.integral_finsetSum]
  · exact Finset.sum_congr rfl fun j _ => by
      exact intervalIntegral.integral_const_mul _ _
  · intro j _
    have hj : Continuous (fun r : ℝ => c j*(Real.exp (-(rate j*(t-r)))*J r)) := by fun_prop
    exact hj.intervalIntegrable _ _

/-- The derivative is the kernel's initial value times the present path
plus the ordinary convolution with the derivative of the kernel. -/
theorem hasDerivAt_smoothKernel_intervalConvolution (c rate : ξ → ℝ) {J : ℝ → ℝ}
    (hJ : Continuous J) (t : ℝ) :
    HasDerivAt (fun s => ∫ r in (0 : ℝ)..s, smoothExponentialKernel c rate (s-r)*J r)
      (smoothExponentialKernel c rate 0 * J t +
        ∫ r in (0 : ℝ)..t, smoothExponentialKernelDerivative c rate (t-r)*J r) t := by
  simp_rw [smoothKernel_intervalConvolution_eq_sum c rate hJ]
  have h : HasDerivAt (fun s => ∑ j, c j*signedExponentialHistory (rate j) J s)
      (∑ j, c j*(J t-rate j*signedExponentialHistory (rate j) J t)) t := by
    apply HasDerivAt.fun_sum
    intro j _
    exact (signedExponentialHistory_hasDerivAt hJ (rate j) t).const_mul (c j)
  convert h using 1
  rw [show smoothExponentialKernelDerivative c rate =
      smoothExponentialKernel (fun j => -(c j*rate j)) rate from rfl,
    smoothKernel_intervalConvolution_eq_sum _ _ hJ]
  simp only [smoothExponentialKernel, mul_zero, neg_zero, Real.exp_zero, mul_one, Finset.sum_mul]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

#print axioms RoughHeston.smoothExponentialKernel_hasDerivAt
#print axioms RoughHeston.hasDerivAt_smoothKernel_intervalConvolution

end RoughHeston
