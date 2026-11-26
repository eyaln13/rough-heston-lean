import TheoremStatement
import MathFin.Probability.Brownian.Ito.ItoIntegralHorizonDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Filter Set
open scoped MeasureTheory ENNReal NNReal Topology

namespace RoughHeston

variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
variable {τ : Measure S} {μ : Measure Ω}

/-- A bound on the mean of a nonnegative variance weight controls the
product-space energy of its square root times a deterministic kernel. -/
theorem memLp_kernel_mul_sqrt_of_uniform_mean [IsFiniteMeasure μ]
    {k : S → ℝ} (hk : MemLp k 2 τ) {V : S → Ω → ℝ}
    (hVmeas : Measurable (Function.uncurry V)) (hVnonneg : ∀ s ω, 0 ≤ V s ω)
    (hVint : ∀ s, Integrable (V s) μ) {C : ℝ}
    (hmean : ∀ s, (∫ ω, V s ω ∂μ) ≤ C) :
    MemLp (fun z : S × Ω => k z.1 * Real.sqrt (V z.1 z.2)) 2 (τ.prod μ) := by
  have hkm : AEStronglyMeasurable (fun z : S × Ω => k z.1) (τ.prod μ) :=
    (hk.comp_fst μ).aestronglyMeasurable
  have hVm : Measurable (fun z : S × Ω => V z.1 z.2) := hVmeas
  have hf : AEStronglyMeasurable
      (fun z : S × Ω => k z.1 * Real.sqrt (V z.1 z.2)) (τ.prod μ) :=
    hkm.mul hVm.sqrt.aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq hf).2 ?_
  simp_rw [mul_pow, Real.sq_sqrt (hVnonneg _ _)]
  let g (z : S × Ω) : ℝ := k z.1 ^ 2 * V z.1 z.2
  have hg : AEStronglyMeasurable g (τ.prod μ) :=
    (hkm.aemeasurable.pow_const 2).aestronglyMeasurable.mul hVm.aestronglyMeasurable
  refine (integrable_prod_iff hg).2 ⟨?_, ?_⟩
  · exact Eventually.of_forall fun s => (hVint s).const_mul (k s ^ 2)
  · refine (hk.integrable_sq.mul_const C).mono_nonneg hg.norm.integral_prod_right'
      (Eventually.of_forall fun s => integral_nonneg fun _ => norm_nonneg _) ?_
    refine Eventually.of_forall fun s => ?_
    have hn (ω : Ω) : ‖g (s, ω)‖ = g (s, ω) :=
      Real.norm_of_nonneg (mul_nonneg (sq_nonneg (k s)) (hVnonneg s ω))
    simp_rw [hn, g, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hmean s) (sq_nonneg (k s))

/-- Lebesgue measure on the open time interval, viewed as a measure on
the nonnegative times used by the stochastic processes. -/
noncomputable def hestonTimeMeasure (t : ℝ≥0) : Measure ℝ≥0 :=
  Measure.map Real.toNNReal (volume.restrict (Ioo (0 : ℝ) (t : ℝ)))

/-- The cutoff construction and the joint predictable integral use the
same finite-horizon time measure. The endpoint carries zero mass. -/
theorem hestonTimeMeasure_eq_horizon (t : ℝ≥0) :
    hestonTimeMeasure t = MathFin.ItoIntegralCLM.timeMeasureHorizon t := by
  ext A hA
  have hcast : ((↑) : ℝ≥0 → ℝ) '' (A ∩ Ioc 0 t) =
      Real.toNNReal ⁻¹' A ∩ Ioc (0 : ℝ) (t : ℝ) := by
    ext s
    constructor
    · rintro ⟨u, ⟨hu, hu₀, hut⟩, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · change (u : ℝ).toNNReal ∈ A
        simpa only [Real.toNNReal_coe] using hu
      · exact_mod_cast hu₀
      · exact_mod_cast hut
    · rintro ⟨hs, hs₀, hst⟩
      have he : (s.toNNReal : ℝ) = s := Real.coe_toNNReal s hs₀.le
      have h₀ : (0 : ℝ) < (s.toNNReal : ℝ) := by rwa [he]
      have ht : (s.toNNReal : ℝ) ≤ (t : ℝ) := by rwa [he]
      exact ⟨s.toNNReal, ⟨hs, by exact_mod_cast h₀, by exact_mod_cast ht⟩, he⟩
  rw [hestonTimeMeasure, Measure.restrict_congr_set Ioo_ae_eq_Ioc,
    Measure.map_apply continuous_real_toNNReal.measurable hA,
    Measure.restrict_apply (continuous_real_toNNReal.measurable hA),
    MathFin.ItoIntegralCLM.timeMeasureHorizon, Measure.restrict_apply hA,
    MathFin.ItoIntegralL2.timeMeasure,
    MathFin.ItoIntegralL2.measurableEmbedding_nnrealCoe.comap_apply, hcast]

theorem ae_time_lt_hestonTimeMeasure (t : ℝ≥0) :
    ∀ᵐ s ∂hestonTimeMeasure t, s < t := by
  have hm : MeasurableSet {s : ℝ≥0 | s < t} :=
    measurableSet_lt measurable_id measurable_const
  apply (ae_map_iff continuous_real_toNNReal.measurable.aemeasurable hm).2
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have h : (s.toNNReal : ℝ) < (t : ℝ) := by
    rw [Real.coe_toNNReal s hs.1.le]
    exact hs.2
  exact_mod_cast h

theorem ae_fst_lt_hestonTimeMeasure_prod (t : ℝ≥0) :
    ∀ᵐ z : ℝ≥0 × Ω ∂(hestonTimeMeasure t).prod μ, z.1 < t :=
  Measure.quasiMeasurePreserving_fst.ae (ae_time_lt_hestonTimeMeasure t)

/-- Translate and reflect the deterministic kernel on the finite time
interval to obtain the square-integrable time-to-maturity weight. -/
theorem heston_shifted_kernel_memLp_two {α : ℝ} (hα : 1 / 2 < α) (t : ℝ≥0) :
    MemLp (fun s : ℝ≥0 => hestonKernel α ((t : ℝ) - (s : ℝ))) 2 (hestonTimeMeasure t) := by
  have hi : IntervalIntegrable (fun s => hestonKernel α s ^ 2) volume 0 (t : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (NNReal.coe_nonneg t)).2
      (hestonKernel_memLp_two hα t).integrable_sq
  have hi' : IntervalIntegrable (fun s => hestonKernel α ((t : ℝ) - s) ^ 2)
      volume (t : ℝ) 0 := by
    simpa only [sub_zero, sub_self] using hi.comp_sub_left (t : ℝ)
  have hmeas : Measurable (fun s : ℝ => hestonKernel α ((t : ℝ) - s)) :=
    (hestonKernel_measurable α).comp (measurable_const.sub measurable_id)
  have hreflected : MemLp (fun s : ℝ => hestonKernel α ((t : ℝ) - s)) 2
      (volume.restrict (Ioc (0 : ℝ) (t : ℝ))) :=
    (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le (NNReal.coe_nonneg t)).1 hi'.symm)
  have hsmall : MemLp (fun s : ℝ => hestonKernel α ((t : ℝ) - s)) 2
      (volume.restrict (Ioo (0 : ℝ) (t : ℝ))) :=
    hreflected.mono_measure (Measure.restrict_mono Ioo_subset_Ioc_self le_rfl)
  have htarget : Measurable (fun s : ℝ≥0 => hestonKernel α ((t : ℝ) - (s : ℝ))) :=
    hmeas.comp measurable_subtype_coe
  apply (memLp_map_measure_iff htarget.aestronglyMeasurable
    continuous_real_toNNReal.measurable.aemeasurable).2
  refine MemLp.ae_eq ?_ hsmall
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  simp only [Function.comp_apply, Real.coe_toNNReal s hs.1.le]

/-- A uniform first-moment bound makes the Heston convolution weight
square integrable on the product of time and sample space. -/
theorem heston_convolution_weight_memLp_two [IsFiniteMeasure μ]
    {α : ℝ} (hα : 1 / 2 < α) (t : ℝ≥0) {V : ℝ≥0 → Ω → ℝ}
    (hVmeas : Measurable (Function.uncurry V)) (hVnonneg : ∀ s ω, 0 ≤ V s ω)
    (hVint : ∀ s, Integrable (V s) μ) {C : ℝ}
    (hmean : ∀ s, (∫ ω, V s ω ∂μ) ≤ C) :
    MemLp (fun z : ℝ≥0 × Ω => hestonConvolutionWeight α t V z.1 z.2) 2
      ((hestonTimeMeasure t).prod μ) :=
  memLp_kernel_mul_sqrt_of_uniform_mean (heston_shifted_kernel_memLp_two hα t)
    hVmeas hVnonneg hVint hmean

/-- The regularized convolution weights converge to the singular
weight in the product-space energy norm under a uniform first-moment
bound. -/
theorem heston_cutoff_weight_L2_of_uniform_mean [IsFiniteMeasure μ]
    {α : ℝ} (hα : 1 / 2 < α) (hα' : α ≤ 1) (t : ℝ≥0) {V : ℝ≥0 → Ω → ℝ}
    (hVmeas : Measurable (Function.uncurry V)) (hVnonneg : ∀ s ω, 0 ≤ V s ω)
    (hVint : ∀ s, Integrable (V s) μ) {C : ℝ}
    (hmean : ∀ s, (∫ ω, V s ω ∂μ) ≤ C) :
    Tendsto (fun n => eLpNorm
      (fun z : ℝ≥0 × Ω => hestonCutoffWeight α t V n z.1 z.2 -
        hestonConvolutionWeight α t V z.1 z.2) 2 ((hestonTimeMeasure t).prod μ))
      atTop (𝓝 0) :=
  heston_cutoff_weight_L2 (by linarith) hα' t hVmeas (ae_fst_lt_hestonTimeMeasure_prod t)
    (heston_convolution_weight_memLp_two hα t hVmeas hVnonneg hVint hmean)

end RoughHeston

#print axioms RoughHeston.memLp_kernel_mul_sqrt_of_uniform_mean
#print axioms RoughHeston.ae_fst_lt_hestonTimeMeasure_prod
#print axioms RoughHeston.hestonTimeMeasure_eq_horizon
#print axioms RoughHeston.heston_shifted_kernel_memLp_two
#print axioms RoughHeston.heston_convolution_weight_memLp_two
#print axioms RoughHeston.heston_cutoff_weight_L2_of_uniform_mean
