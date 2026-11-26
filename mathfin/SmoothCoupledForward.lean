import SmoothCoupledRealization
import SmoothForwardPointwise

/-! The actual smooth coupled system in pointwise direct-kernel form. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

set_option maxHeartbeats 900000

variable {ι η ξ : Type*} [Fintype ι] [Fintype η] [Fintype ξ] [DecidableEq ι]

local notation "S" => SmoothCoupledState ι η

/-- The deterministic integration-by-parts expression for convolution
of a smooth kernel against a zero-start martingale. -/
noncomputable def smoothKernelMartingaleConvolution (c rate : ξ → ℝ) (M : ℝ → ℝ) (t : ℝ) : ℝ :=
  smoothExponentialKernel c rate 0 * M t +
    ∫ r in (0 : ℝ)..t, smoothExponentialKernelDerivative c rate (t-r)*M r

/-- Splitting the smooth forward expression into its ordinary drift
convolution and the martingale convolution. -/
theorem smooth_firstKind_inverse_pointwise_forward_split
    (c rate : ξ → ℝ) {L U M f : ℝ → ℝ} {a T : ℝ} (hT : 0 < T)
    (hL : Continuous L) (hU : Continuous U) (hM : Continuous M)
    (hf : Measurable f) (hfi : ∀ x y, IntervalIntegrable f volume x y)
    (hKL : ∀ s ∈ Icc (0 : ℝ) T, a*smoothExponentialKernel c rate s +
      volterraConvolution L (smoothExponentialKernel c rate) s = 1)
    (hJ : ∀ s ∈ Icc (0 : ℝ) T, M s + (∫ r in (0 : ℝ)..s, f r) =
      a*U s + volterraConvolution L U s) :
    ∀ t ∈ Icc (0 : ℝ) T,
      U t = (∫ r in (0 : ℝ)..t, smoothExponentialKernel c rate (t-r)*f r) +
        smoothKernelMartingaleConvolution c rate M t := by
  let A (t : ℝ) := ∫ r in (0 : ℝ)..t, f r
  have hA : Continuous A := intervalIntegral.continuous_primitive hfi 0
  intro t ht
  have hJc : Continuous (fun t => M t + A t) := hM.add hA
  have h := smooth_firstKind_inverse_pointwise_forward c rate hT hL hU hJc hKL hJ t ht
  let hK (r : ℝ) := smoothExponentialKernelDerivative c rate (t-r)
  have hKc : Continuous hK := (continuous_smoothExponentialKernelDerivative c rate).comp
    (continuous_const.sub continuous_id)
  have hDrift := smoothKernelDerivative_convolution_primitive c rate ht.1 hf
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mp (hfi 0 t))
  change U t = smoothExponentialKernel c rate 0*(M t + A t) +
    ∫ r in (0 : ℝ)..t, hK r*(M r + A r) at h
  simp_rw [mul_add] at h
  have hmi : IntervalIntegrable (fun r => hK r*M r) volume 0 t := (hKc.mul hM).intervalIntegrable _ _
  have hai : IntervalIntegrable (fun r => hK r*A r) volume 0 t := (hKc.mul hA).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hmi hai] at h
  unfold smoothKernelMartingaleConvolution
  rw [← hDrift]
  linarith

/-- On the same jointly coupled law, all physical coordinates satisfy
the direct smooth-kernel equations, with the given deterministic forcing. -/
theorem ae_smoothCoupled_pointwise_forward
    {T : ℝ≥0} (hT : 0 < T) (K₀ κ ℓ₀ : ℝ) (hK₀ : K₀ ≠ 0)
    (v : Option ι → ℝ) (q rate : η → ℝ) (β : Option ι → ℝ≥0 → ℝ)
    (c x : ξ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B)
    (hKL : ∀ s ∈ Icc (0 : ℝ) (T : ℝ), (1/K₀)*smoothExponentialKernel c x s +
      volterraConvolution (smoothExponentialResolvent ℓ₀ q rate) (smoothExponentialKernel c x) s = 1)
    {μ : Measure (CanonicalPath T S)}
    (hInverse : ∀ᵐ p ∂μ, ∀ i : Option ι, ∀ t ∈ Icc 0 T,
      smoothExponentialInverse K₀ ℓ₀ q rate (v i)
        (fun r : ℝ => smoothCoupledPath T K₀ β r.toNNReal p (i, none)) t =
      smoothCoupledMartingale T K₀ κ ℓ₀ v q rate β (i, none) t p / K₀ +
        ∫ r in (0 : ℝ)..(t : ℝ), (β i r.toNNReal -
          κ*smoothCoupledPath T K₀ β r.toNNReal p (i, none))) :
    ∀ᵐ p ∂μ, ∀ i : Option ι, ∀ t ∈ Icc 0 T,
      smoothCoupledPath T K₀ β t p (i, none) = v i +
        (∫ r in (0 : ℝ)..(t : ℝ), smoothExponentialKernel c x ((t : ℝ)-r)*
          (β i r.toNNReal - κ*smoothCoupledPath T K₀ β r.toNNReal p (i, none))) +
        smoothKernelMartingaleConvolution c x
          (fun r : ℝ => smoothCoupledMartingale T K₀ κ ℓ₀ v q rate β (i, none) r.toNNReal p / K₀) t := by
  filter_upwards [hInverse] with p hp i t ht
  let V (r : ℝ) := smoothCoupledPath T K₀ β r.toNNReal p (i, (none : Option η))
  let U (r : ℝ) := V r - v i
  let M (r : ℝ) := smoothCoupledMartingale T K₀ κ ℓ₀ v q rate β (i, none) r.toNNReal p / K₀
  let f (r : ℝ) := β i r.toNNReal - κ*V r
  have hX : Continuous (fun r : ℝ≥0 => smoothCoupledPath T K₀ β r p) :=
    continuous_translatedCanonicalState_time T
      (continuous_smoothCoupledImmigrationPrimitive T K₀ β hB hβ hβB) p
  have hV : Continuous V := (continuous_apply (i, none)).comp (hX.comp continuous_real_toNNReal)
  have hU : Continuous U := hV.sub continuous_const
  have hM : Continuous M :=
    ((continuous_smoothCoupledMartingale_time T K₀ κ ℓ₀ v q rate β hB hβ hβB (i, none) p).comp
      continuous_real_toNNReal).div_const _
  have hβr : Measurable (fun r : ℝ => β i r.toNNReal) :=
    (hβ i).comp continuous_real_toNNReal.measurable
  have hf : Measurable f := hβr.sub (measurable_const.mul hV.measurable)
  have hfi (a b : ℝ) : IntervalIntegrable f volume a b := by
    have hβI : IntervalIntegrable (fun r : ℝ => β i r.toNNReal) volume a b := by
      rw [intervalIntegrable_iff]
      have hC : IntervalIntegrable (fun _ : ℝ => B) volume a b := intervalIntegrable_const
      rw [intervalIntegrable_iff] at hC
      exact hC.mono' hβr.stronglyMeasurable.aestronglyMeasurable
        (Eventually.of_forall fun r => hβB i r.toNNReal)
    exact hβI.sub (hV.intervalIntegrable a b |>.const_mul κ)
  have hEq (s : ℝ) (hs : s ∈ Icc 0 (T : ℝ)) : M s + (∫ r in (0 : ℝ)..s, f r) =
      (1/K₀)*U s + volterraConvolution (smoothExponentialResolvent ℓ₀ q rate) U s := by
    have hs' : s.toNNReal ∈ Icc (0 : ℝ≥0) T :=
      ⟨zero_le, by exact_mod_cast (Real.coe_toNNReal s hs.1).trans_le hs.2⟩
    have h := (hp i _ hs').symm
    rw [Real.coe_toNNReal _ hs.1] at h
    rw [h]
    unfold smoothExponentialInverse volterraConvolution
    rw [intervalIntegral.integral_of_le hs.1]
    change U s / K₀ + _ = (1/K₀)*U s + _
    rw [div_eq_mul_inv, one_div, mul_comm (U s)]
  have ht' : (t : ℝ) ∈ Icc 0 (T : ℝ) := ⟨t.coe_nonneg, by exact_mod_cast ht.2⟩
  have h := smooth_firstKind_inverse_pointwise_forward_split c x
    (show 0 < (T : ℝ) by exact_mod_cast hT)
    (continuous_smoothExponentialResolvent ℓ₀ q rate) hU hM hf hfi hKL hEq t ht'
  change V (t : ℝ) - v i = _ at h
  have hVt : V (t : ℝ) = smoothCoupledPath T K₀ β t p (i, none) := by simp [V]
  rw [hVt] at h
  linarith

#print axioms RoughHeston.smooth_firstKind_inverse_pointwise_forward_split
#print axioms RoughHeston.ae_smoothCoupled_pointwise_forward

end RoughHeston
