import SmoothForwardKernel
import SmoothExponentialConvolutionDerivative

/-! Pointwise deterministic and martingale-convolution forms for the
smooth exponential approximants. -/

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RoughHeston

set_option maxHeartbeats 800000

variable {ξ : Type*} [Fintype ξ]

/-- The integrated equation differentiates to a pointwise equation on
the entire closed horizon. The input path need only be continuous. -/
theorem smooth_firstKind_inverse_pointwise_forward
    (c rate : ξ → ℝ) {L U J : ℝ → ℝ} {a T : ℝ} (hT : 0 < T)
    (hL : Continuous L) (hU : Continuous U) (hJc : Continuous J)
    (hKL : ∀ s ∈ Icc (0 : ℝ) T, a*smoothExponentialKernel c rate s +
      volterraConvolution L (smoothExponentialKernel c rate) s = 1)
    (hJ : ∀ s ∈ Icc (0 : ℝ) T, J s = a*U s + volterraConvolution L U s) :
    ∀ t ∈ Icc (0 : ℝ) T,
      U t = smoothExponentialKernel c rate 0 * J t +
        ∫ r in (0 : ℝ)..t, smoothExponentialKernelDerivative c rate (t-r)*J r := by
  let K := smoothExponentialKernel c rate
  have hEq (t : ℝ) (ht : t ∈ Icc 0 T) :
      (∫ r in (0 : ℝ)..t, K (t-r)*J r) = ∫ r in (0 : ℝ)..t, U r := by
    rw [intervalIntegral.integral_of_le ht.1]
    exact smooth_firstKind_inverse_integrated_forward ht.1 (continuous_smoothExponentialKernel c rate)
      hL hU (fun s hs => hKL s ⟨hs.1, hs.2.trans ht.2⟩)
      (fun s hs => hJ s ⟨hs.1, hs.2.trans ht.2⟩)
  intro t ht
  have hF : HasDerivAt (fun s => ∫ r in (0 : ℝ)..s, U r) (U t) t :=
    intervalIntegral.integral_hasDerivAt_right (hU.intervalIntegrable _ _)
      hU.aestronglyMeasurable.stronglyMeasurableAtFilter hU.continuousAt
  have h₂ := hasDerivAt_smoothKernel_intervalConvolution c rate hJc t
  have h₂' := h₂.hasDerivWithinAt.congr_of_mem (fun s hs => (hEq s hs).symm) ht
  have hu := (uniqueDiffOn_Icc hT) t ht
  rw [← hF.hasDerivWithinAt.derivWithin hu, h₂'.derivWithin hu]

private theorem integral_smoothKernelDerivative_reflected
    (c rate : ξ → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    (∫ r in (0 : ℝ)..s, smoothExponentialKernelDerivative c rate (s-r)) =
      smoothExponentialKernel c rate s - smoothExponentialKernel c rate 0 := by
  have h := intervalIntegral.integral_comp_sub_left (f := smoothExponentialKernelDerivative c rate)
    (a := 0) (b := s) s
  rw [sub_self, sub_zero] at h
  rw [h]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => smoothExponentialKernel_hasDerivAt c rate r)
  exact (continuous_smoothExponentialKernelDerivative c rate).intervalIntegrable _ _

/-- Associativity moves a Lebesgue primitive through the differentiated
smooth kernel. This accommodates immigration rates with jump times. -/
theorem smoothKernelDerivative_convolution_primitive
    (c rate : ξ → ℝ) {f : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hf : Measurable f) (hfi : IntegrableOn f (Ioc 0 t)) :
    smoothExponentialKernel c rate 0 * (∫ r in (0 : ℝ)..t, f r) +
        (∫ r in (0 : ℝ)..t, smoothExponentialKernelDerivative c rate (t-r)*
          (∫ u in (0 : ℝ)..r, f u)) =
      ∫ r in (0 : ℝ)..t, smoothExponentialKernel c rate (t-r)*f r := by
  let K := smoothExponentialKernel c rate
  let k := smoothExponentialKernelDerivative c rate
  let u := (Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ))
  have hu₀ (s : ℝ) (hs : s ≤ 0) : u s = 0 := by simp [u, hs]
  have hui : IntegrableOn u (Ioc 0 t) := by
    have hI : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 t) :=
      integrableOn_const measure_Ioc_lt_top.ne
    refine hI.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    simp [u, hs.1]
  have hk := continuous_smoothExponentialKernelDerivative c rate
  obtain ⟨B, hB⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := t)).image hk).isBounded.exists_norm_le
  have hTri := affine_volterra_triangle_integrable (l := k) (k := u) (f := f) ht
    (le_max_left (0 : ℝ) B) hk.measurable (measurable_const.indicator measurableSet_Ioi)
    hf hu₀ hui hfi (fun s hs => (hB _ ⟨s, hs, rfl⟩).trans (le_max_right _ _))
  have hA (r : ℝ) (hr : 0 ≤ r) : volterraConvolution u f r = ∫ x in (0 : ℝ)..r, f x := by
    rw [intervalIntegral.integral_of_le hr]
    apply setIntegral_congr_ae measurableSet_Ioc
    filter_upwards [volume.ae_ne r] with s hn hs
    have hrs : 0 < r-s := sub_pos.mpr (lt_of_le_of_ne hs.2 hn)
    simp [u, hrs]
  have hKu (s : ℝ) (hs : 0 ≤ s) : volterraConvolution k u s = K s-K 0 := by
    have he : volterraConvolution k u s = ∫ r in (0 : ℝ)..s, k (s-r) := by
      rw [intervalIntegral.integral_of_le hs]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro r hr
      simp [u, hr.1]
    rw [he]
    exact integral_smoothKernelDerivative_reflected c rate hs
  simp_rw [intervalIntegral.integral_of_le ht]
  have hde :
      (∫ r in Ioc (0 : ℝ) t, k (t-r)*(∫ x in (0 : ℝ)..r, f x)) =
        ∫ r in Ioc (0 : ℝ) t, (K (t-r)-K 0)*f r := by
    calc
      _ = volterraConvolution k (volterraConvolution u f) t := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro r hr
        simp only [hA r hr.1.le]
      _ = volterraConvolution (volterraConvolution k u) f t :=
        volterra_convolution_assoc hu₀ hTri
      _ = _ := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro r hr
        simp only [hKu (t-r) (sub_nonneg.mpr hr.2)]
  change K 0*(∫ r in Ioc (0 : ℝ) t, f r) +
    (∫ r in Ioc (0 : ℝ) t, k (t-r)*(∫ x in (0 : ℝ)..r, f x)) =
      ∫ r in Ioc (0 : ℝ) t, K (t-r)*f r
  have hC (s : ℝ) : Continuous (fun r => K (s-r)-K 0) :=
    ((continuous_smoothExponentialKernel c rate).comp (continuous_const.sub continuous_id)).sub continuous_const
  have hi : IntegrableOn (fun r => (K (t-r)-K 0)*f r) (Ioc 0 t) := by
    obtain ⟨D, hD⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := t)).image (hC t)).isBounded.exists_norm_le
    refine (hfi.norm.const_mul (max D 0)).mono'
      ((hC t).measurable.mul hf).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right ((hD _ ⟨r, ⟨hr.1.le, hr.2⟩, rfl⟩).trans (le_max_left _ _))
      (norm_nonneg _)
  rw [hde, ← integral_const_mul, ← integral_add (hfi.const_mul (K 0)) hi]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r _
  change K 0*f r + (K (t-r)-K 0)*f r = K (t-r)*f r
  ring

#print axioms RoughHeston.smooth_firstKind_inverse_pointwise_forward
#print axioms RoughHeston.smoothKernelDerivative_convolution_primitive

end RoughHeston
