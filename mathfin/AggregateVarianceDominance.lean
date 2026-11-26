import AggregateSamplewiseForward
import TiltingItoPairing
import FractionalSmoothNoiseIncrements
import CanonicalPathIntegrals

/-! Mean reversion is sign-definite in the direct aggregate equation.
Only the bounded deterministic convolution and centered noise enter the
upper moment induction. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston.GirsanovPort

set_option maxHeartbeats 1500000

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {T : ℝ≥0} {B U : ℝ≥0 → Ω → ℝ}

theorem fixedHestonConvolutionLp_zero {α : ℝ} (hα : 1/2 < α)
    (hB₂ : ∀ t, MemLp (B t) 2 P) (hU : IsStronglyPredictable F U)
    (hn : ∀ t ω, 0 ≤ U t ω) (hi : ∀ t, Integrable (U t) P)
    {A : ℝ} (hA : ∀ t, (∫ ω, U t ω ∂P) ≤ A) :
    fixedHestonConvolutionLp (T := T) hα hB₂ hU hn hi hA 0 = 0 := by
  unfold fixedHestonConvolutionLp
  change jointItoIntegralCLM T hB₂ (hestonKernelFamilyLp hα hU hn hi hA (realTimeOnHorizon T 0)) = 0
  suffices h : hestonKernelFamilyLp hα hU hn hi hA (realTimeOnHorizon T 0) = 0 by rw [h, map_zero]
  apply Lp.ext
  filter_upwards [hestonKernelFamilyLp_ae hα hU hn hi hA (realTimeOnHorizon T 0),
    Lp.coeFn_zero ℝ 2 (jointPredictableMeasure F P T)] with z hz hzero
  have h : ((realTimeOnHorizon T 0).val:ℝ) = 0 := by
    change ((min (Real.toNNReal (0:ℝ)) T : ℝ≥0):ℝ) = 0
    simp
  rw [hz, hzero]
  simp only [Function.uncurry, hestonConvolutionWeight, h, Pi.zero_apply, zero_sub]
  rw [hestonKernel, if_neg (not_lt.mpr (neg_nonpos.mpr z.1.coe_nonneg)), zero_mul]

theorem aggregateVariance_ae_le_deterministic_plus_noise
    {α κ σ : ℝ} (hα : 0 < α) (hκ : 0 ≤ κ)
    (hU : IsStronglyPredictable F U) (hU₀ : ∀ s ω, 0 ≤ U s ω)
    {v : ℝ → Lp ℝ 2 P} (hvm : StronglyMeasurable v) (hvc : ContinuousOn v (Icc 0 (T:ℝ)))
    (hvRep : ∀ s, ⇑(v s) =ᵐ[P] U s.toNNReal)
    {s : ℝ} (hs : s ∈ Icc 0 (T:ℝ)) {D : ℝ} {N : Lp ℝ 2 P}
    (he : v s = clusterDeterministicInputLp P (fun _ => D) s +
      volterraSmulConvolution (hestonKernel α) (fun r => (-κ:ℝ) • v r) s+σ • N) :
    ∀ᵐ ω ∂P, U s.toNNReal ω ≤ D+(σ • N) ω := by
  let k (r : ℝ) := hestonKernel α (s-r)
  let G := volterraSmulConvolution (hestonKernel α) (fun r => (-κ:ℝ) • v r) s
  let d₀ := clusterDeterministicInputLp P (fun _ => D) s
  let Ureal (r : ℝ) (ω : Ω) := U r.toNNReal ω
  let g (r : ℝ) := (-κ:ℝ) • v r
  have hUm : Measurable (Function.uncurry Ureal) :=
    (hU.mono F.predictable_le_prod).measurable.comp
      (continuous_real_toNNReal.measurable.prodMap (measurable_id : Measurable (@id Ω)))
  have hGm : Measurable (Function.uncurry (fun r ω => (-κ)*Ureal r ω)) := hUm.const_mul _
  have hgM : StronglyMeasurable g := by
    change StronglyMeasurable ((-κ:ℝ) • v)
    exact hvm.const_smul (-κ)
  have hgC : ContinuousOn g (Icc 0 (T:ℝ)) := by
    change ContinuousOn ((-κ:ℝ) • v) _
    exact hvc.const_smul (-κ)
  have hk : Measurable k := (hestonKernel_measurable α).comp (measurable_const.sub measurable_id)
  have hkI : IntegrableOn k (Ioc (0:ℝ) s) := by
    have hEq : hestonKernel α = fractionalK α := by
      funext t
      by_cases ht : 0 < t <;> simp [hestonKernel, fractionalK, ht, le_of_not_gt]
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hs.1).1
    have h := (intervalIntegrable_iff_integrableOn_Ioc_of_le hs.1).2 (fractionalK_integrableOn_Ioc hα s)
    simpa only [sub_self, sub_zero, k, hEq] using (h.comp_sub_left s).symm
  have hgI := pulse_weighted_reflected_integrableOn (hestonKernel_measurable α) hkI hgM
    (hgC.mono (Icc_subset_Icc_right hs.2))
  have hgRep (r : ℝ) : ⇑(g r) =ᵐ[P] fun ω => (-κ)*Ureal r ω := by
    filter_upwards [Lp.coeFn_smul (-κ) (v r), hvRep r] with ω h1 h2
    change ((-κ:ℝ) • v r) ω = _
    rw [h1, Pi.smul_apply, smul_eq_mul, h2]
  have hG := coeFn_integral_weighted_L2_path_ae hk hGm hgI hgRep
  have hd₀ : ⇑d₀ =ᵐ[P] fun _ => D := by
    let one : Lp ℝ 2 P := (memLp_const (1:ℝ)).toLp (fun _ => 1)
    filter_upwards [Lp.coeFn_smul D one, (memLp_const (1:ℝ) (μ := P)).coeFn_toLp] with ω h1 h2
    change (D • one) ω = D
    rw [h1, Pi.smul_apply, smul_eq_mul, h2, mul_one]
  filter_upwards [hG, hd₀, hvRep s, Lp.coeFn_add (d₀+G) (σ • N), Lp.coeFn_add d₀ G] with ω hGω hdω hω ha₁ ha₂
  have hEq := congrArg (fun z : Lp ℝ 2 P => z ω) he
  change v s ω = (d₀+G+σ • N) ω at hEq
  rw [hω, ha₁, Pi.add_apply, ha₂, Pi.add_apply, hdω] at hEq
  change G ω = _ at hGω
  rw [hGω] at hEq
  have hNeg : (∫ r in Ioc (0:ℝ) s, k r*((-κ)*Ureal r ω)) ≤ 0 := by
    apply integral_nonpos
    intro r
    have hKnonneg : 0 ≤ k r := by dsimp [k, hestonKernel]; split_ifs <;> positivity
    exact mul_nonpos_of_nonneg_of_nonpos hKnonneg (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr hκ) (hU₀ _ _))
  linarith

/-- The stochastic convolution has mean zero in its terminal representative. -/
theorem integral_scaled_fixedHestonConvolutionLp_zero {α σ : ℝ} (hα : 1/2 < α)
    (hB₂ : ∀ t, MemLp (B t) 2 P) (hB : Martingale B F P)
    (hclock : Martingale (fun t ω => B t ω^2-((min t T:ℝ≥0):ℝ)) F P)
    (hU : IsStronglyPredictable F U) (hn : ∀ t ω, 0 ≤ U t ω) (hi : ∀ t, Integrable (U t) P)
    {A : ℝ} (hA : ∀ t, (∫ ω, U t ω ∂P) ≤ A) (s : ℝ) :
    (∫ ω, (σ • fixedHestonConvolutionLp (T := T) hα hB₂ hU hn hi hA s) ω ∂P) = 0 := by
  let V := hestonKernelFamilyLp hα hU hn hi hA (realTimeOnHorizon T s)
  change (∫ ω, (σ • jointItoIntegralCLM T hB₂ V) ω ∂P) = 0
  rw [← map_smul]
  exact integral_jointItoIntegralCLM_eq_zero T hB₂ hB hclock _

#print axioms RoughHeston.GirsanovPort.fixedHestonConvolutionLp_zero
#print axioms RoughHeston.GirsanovPort.aggregateVariance_ae_le_deterministic_plus_noise
#print axioms RoughHeston.GirsanovPort.integral_scaled_fixedHestonConvolutionLp_zero

end RoughHeston.GirsanovPort
