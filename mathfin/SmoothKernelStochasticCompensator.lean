import SmoothCoupledForward
import AffineDyadicIntegrationByParts

/-! Square compensators for the smooth kernel stochastic convolutions,
obtained by sampling the original continuous martingale. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

variable {ξ Ω : Type*} [Fintype ξ] {m : MeasurableSpace Ω} {μ : Measure Ω}
  {F : Filtration ℝ≥0 m}

private theorem contDiff_smoothKernel_shift (c x : ξ → ℝ) :
    ContDiff ℝ 1 (fun r : ℝ => smoothExponentialKernel c x (r-1)) := by
  unfold smoothExponentialKernel
  exact ContDiff.sum fun j _ => by fun_prop

/-- The hand-computable terminal integration-by-parts expression is
the value of a continuous weighted martingale with its exact bracket. -/
theorem exists_smooth_kernel_weighted_martingale [IsProbabilityMeasure μ]
    (c x : ξ → ℝ) (H : ℝ≥0) {M C : ℝ≥0 → Ω → ℝ} {D : ℝ → Ω → ℝ}
    (hM : Martingale M F μ) (hM₂ : ∀ t, MemLp (M t) 2 μ) (hM₀ : M 0 =ᵐ[μ] 0)
    (hMc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hMC : Martingale (fun t => M t * M t - C t) F μ)
    (hCi : ∀ t, Integrable (C t) μ) (hCmon : ∀ s t, s ≤ t → C s ≤ᵐ[μ] C t)
    (hC : ∀ t ≤ H, C t =ᵐ[μ] fun ω => ∫ r in (0 : ℝ)..(t : ℝ), D r ω)
    (hD : ∀ᵐ ω ∂μ, IntervalIntegrable (fun r => D r ω) volume 0 H)
    (hWD : ∀ᵐ ω ∂μ, IntervalIntegrable (fun r =>
      (smoothExponentialKernel c x ((H : ℝ)-(min r.toNNReal H : ℝ≥0)))^2 * D r ω) volume 0 H)
    (hDi : Integrable (fun ω => ∫ r in (0 : ℝ)..(H : ℝ), |D r ω|) μ) :
    ∃ J A : ℝ≥0 → Ω → ℝ,
      Martingale J F μ ∧ (∀ t, MemLp (J t) 2 μ) ∧
      (∀ᵐ ω ∂μ, ContinuousOn (fun t => J t ω) (Iic H)) ∧
      (∀ t ≤ H, A t =ᵐ[μ] fun ω =>
        ∫ r in (0 : ℝ)..(t : ℝ), (smoothExponentialKernel c x ((H : ℝ)-r))^2 * D r ω) ∧
      Martingale (fun t => J (min t H) * J (min t H) - A t) F μ ∧
      J H =ᵐ[μ] fun ω =>
        smoothKernelMartingaleConvolution c x (fun r : ℝ => M r.toNNReal ω) H := by
  let K := smoothExponentialKernel c x
  let k := smoothExponentialKernelDerivative c x
  let w (r : ℝ) := K (r-1)
  have hw : ContDiff ℝ 1 w := contDiff_smoothKernel_shift c x
  have hW (s : ℝ≥0) : affinePreterminalWeight w 1 H s = K ((H : ℝ)-(min s H : ℝ≥0)) := by
    unfold affinePreterminalWeight w
    congr 1
    ring
  obtain ⟨J, A, hJ, hJ₂, hJc, hConv, hA, hJA⟩ := exists_affine_preterminal_weighted_martingale
    (d := (1 : ℝ)) (w := w) (by norm_num) H hw.continuous.continuousOn
    hM hM₂ hMc hMC hCi hCmon hC hD (by simpa only [hW] using hWD) hDi
  have hA' (t : ℝ≥0) (ht : t ≤ H) : A t =ᵐ[μ] fun ω =>
      ∫ r in (0 : ℝ)..(t : ℝ), (K ((H : ℝ)-r))^2 * D r ω := by
    filter_upwards [hA t] with ω hω
    rw [hω, min_eq_left ht]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le t.coe_nonneg] at hr
    have hrH : r.toNNReal ≤ H :=
      NNReal.coe_le_coe.mp ((Real.coe_toNNReal r hr.1).trans_le (hr.2.trans (NNReal.coe_le_coe.mpr ht)))
    simp only [hW, min_eq_left hrH, Real.coe_toNNReal r hr.1]
  refine ⟨J, A, hJ, hJ₂, hJc, hA', hJA, ?_⟩
  have hTerm := affine_weighted_integral_eq_by_parts (d := (1 : ℝ)) (w := w)
    (by norm_num) (le_refl H) (fun s _ => hw.contDiffAt) hM hM₂ hMc (hConv H le_rfl)
  have hd (r : ℝ) : deriv w r = k (r-1) := by
    have h := (smoothExponentialKernel_hasDerivAt c x (r-1)).comp r ((hasDerivAt_id r).sub_const 1)
    change HasDerivAt w (k (r-1)*1) r at h
    simpa only [mul_one] using h.deriv
  filter_upwards [hTerm, hM₀] with ω hω h₀
  have hzero : M 0 ω = 0 := h₀
  rw [hω, hzero, mul_zero, sub_zero]
  unfold smoothKernelMartingaleConvolution
  rw [show (w (1 + (H : ℝ) - (H : ℝ))) = K 0 by
    unfold w
    congr 1
    ring]
  simp only [Real.toNNReal_coe]
  congr 1
  apply intervalIntegral.integral_congr
  intro r _
  change deriv w (1+(H:ℝ)-r)*M r.toNNReal ω = k ((H:ℝ)-r)*M r.toNNReal ω
  rw [hd]
  congr 2
  ring

#print axioms RoughHeston.exists_smooth_kernel_weighted_martingale

end RoughHeston
