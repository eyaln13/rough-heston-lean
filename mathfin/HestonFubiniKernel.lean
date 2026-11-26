import FractionalKernelL1
import JointHestonWeights

open MeasureTheory ProbabilityTheory Set Filter
open scoped MeasureTheory ProbabilityTheory NNReal ENNReal

namespace RoughHeston

private theorem hestonKernel_eq_fractionalK (α x : ℝ) :
    hestonKernel α x = fractionalK α x := by
  unfold hestonKernel fractionalK
  by_cases hx : 0 < x
  · simp [hx, not_le.mpr hx]
  · simp [hx, le_of_not_gt hx]

/-- Integrate the two causal kernels over the outer time parameter.
The product time measure and the Lebesgue Volterra identity give the
same result for every positive inner time below the horizon. -/
theorem heston_fractional_composition_at {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1)
    {s t : ℝ≥0} (hs : s ∈ Ioo 0 t) :
    (∫ u : ℝ≥0, fractionalL α ((t : ℝ) - (u : ℝ)) *
      hestonKernel α ((u : ℝ) - (s : ℝ)) ∂hestonTimeMeasure t) = 1 := by
  have hφ : Measurable (fun u : ℝ≥0 => fractionalL α ((t : ℝ) - (u : ℝ)) *
      hestonKernel α ((u : ℝ) - (s : ℝ))) :=
    ((fractionalL_measurable α).comp (measurable_const.sub measurable_subtype_coe)).mul
      ((hestonKernel_measurable α).comp (measurable_subtype_coe.sub measurable_const))
  have hto : Measurable Real.toNNReal := continuous_real_toNNReal.measurable
  rw [hestonTimeMeasure, integral_map hto.aemeasurable hφ.aestronglyMeasurable]
  have hsr : (s : ℝ) ∈ Ioc (0 : ℝ) (t : ℝ) := ⟨by exact_mod_cast hs.1, by exact_mod_cast hs.2.le⟩
  have hg : 0 < (t : ℝ) - (s : ℝ) := sub_pos.mpr (by exact_mod_cast hs.2)
  calc
    _ = ∫ u in Ioo (0 : ℝ) (t : ℝ), fractionalL α ((t : ℝ) - u) *
          fractionalK α (u - (s : ℝ)) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      simp only [Real.coe_toNNReal u hu.1.le, hestonKernel_eq_fractionalK]
    _ = ∫ u in Ioc (0 : ℝ) (t : ℝ), fractionalL α ((t : ℝ) - u) *
          fractionalK α (u - (s : ℝ)) := setIntegral_congr_set Ioo_ae_eq_Ioc
    _ = volterraConvolution (fractionalL α) (fractionalK α) ((t : ℝ) - (s : ℝ)) :=
      volterra_shifted_kernel_integral (fun x hx => by simp [fractionalK, hx]) hsr
    _ = 1 := fractional_causal_kernel_inverse hα₀ hα₁ hg

variable {Ω : Type*}

/-- The integrated representative in the fractional stochastic
Fubini step is the square-root amplitude. -/
theorem heston_fubini_integrated_weight {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1)
    {s t : ℝ≥0} (hs : s ∈ Ioo 0 t) (V : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    (∫ u : ℝ≥0, fractionalL α ((t : ℝ) - (u : ℝ)) *
      hestonConvolutionWeight α u V s ω ∂hestonTimeMeasure t) = Real.sqrt (V s ω) := by
  have he : (fun u : ℝ≥0 => fractionalL α ((t : ℝ) - (u : ℝ)) *
      hestonConvolutionWeight α u V s ω) =
      fun u : ℝ≥0 => (fractionalL α ((t : ℝ) - (u : ℝ)) *
        hestonKernel α ((u : ℝ) - (s : ℝ))) * Real.sqrt (V s ω) := by
    funext u
    simp only [hestonConvolutionWeight, mul_assoc]
  rw [he, integral_mul_const, heston_fractional_composition_at hα₀ hα₁ hs, one_mul]

variable {m : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℝ≥0 m}

private theorem ae_heston_time_mem_Ioo (t : ℝ≥0) :
    ∀ᵐ s ∂hestonTimeMeasure t, s ∈ Ioo 0 t := by
  apply (ae_map_iff continuous_real_toNNReal.measurable.aemeasurable measurableSet_Ioo).2
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  change u.toNNReal ∈ Ioo 0 t
  have he : (u.toNNReal : ℝ) = u := Real.coe_toNNReal u hu.1.le
  have h₀ : (0 : ℝ) < (u.toNNReal : ℝ) := by rw [he]; exact hu.1
  have ht : (u.toNNReal : ℝ) < (t : ℝ) := by rw [he]; exact hu.2
  exact ⟨by exact_mod_cast h₀, by exact_mod_cast ht⟩

/-- The predictable measure is concentrated on strictly interior
integration times. -/
theorem ae_fst_mem_Ioo_jointPredictableMeasure (t : ℝ≥0) :
    ∀ᵐ z : ℝ≥0 × Ω ∂jointPredictableMeasure 𝒢 μ t, z.1 ∈ Ioo 0 t := by
  let E := (Prod.fst : ℝ≥0 × Ω → ℝ≥0) ⁻¹' Ioo 0 t
  have hE : MeasurableSet[𝒢.predictable] E :=
    measurable_fst_jointPredictable 𝒢 measurableSet_Ioo
  have hraw : (hestonTimeMeasure t).prod μ Eᶜ = 0 :=
    ae_iff.mp (Measure.quasiMeasurePreserving_fst.ae (ae_heston_time_mem_Ioo t))
  have htrim : jointPredictableMeasure 𝒢 μ t Eᶜ = 0 := by
    unfold jointPredictableMeasure
    rw [trim_measurableSet_eq 𝒢.predictable_le_prod hE.compl, ← hestonTimeMeasure_eq_horizon]
    exact hraw
  exact ae_iff.mpr htrim

/-- The integrated and clamped representative is the unweighted
square-root amplitude, almost surely for the predictable measure. -/
theorem heston_fubini_integrated_weight_ae {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1)
    (t : ℝ≥0) (V : ℝ≥0 → Ω → ℝ) :
    ∀ᵐ z : ℝ≥0 × Ω ∂jointPredictableMeasure 𝒢 μ t,
      (∫ u : ℝ≥0, fractionalL α ((t : ℝ) - (u : ℝ)) *
        hestonConvolutionWeight α (min u t) V z.1 z.2 ∂hestonTimeMeasure t) =
        Real.sqrt (V z.1 z.2) := by
  filter_upwards [ae_fst_mem_Ioo_jointPredictableMeasure (𝒢 := 𝒢) (μ := μ) t] with z hz
  calc
    _ = ∫ u : ℝ≥0, fractionalL α ((t : ℝ) - (u : ℝ)) *
        hestonConvolutionWeight α u V z.1 z.2 ∂hestonTimeMeasure t := by
      apply integral_congr_ae
      filter_upwards [ae_time_lt_hestonTimeMeasure t] with u hu
      rw [min_eq_left hu.le]
    _ = _ := heston_fubini_integrated_weight hα₀ hα₁ hz V z.2

/-- The square-root amplitude itself belongs to the same predictable
L² space as the Heston kernel weights. -/
theorem sqrt_variance_memLp_joint [IsFiniteMeasure μ] (t : ℝ≥0) {V : ℝ≥0 → Ω → ℝ}
    (hVp : IsStronglyPredictable 𝒢 V) (hVnonneg : ∀ s ω, 0 ≤ V s ω)
    (hVint : ∀ s, Integrable (V s) μ) {C : ℝ}
    (hmean : ∀ s, (∫ ω, V s ω ∂μ) ≤ C) :
    MemLp (fun z : ℝ≥0 × Ω => Real.sqrt (V z.1 z.2)) 2 (jointPredictableMeasure 𝒢 μ t) := by
  have hVsm : StronglyMeasurable[𝒢.predictable] (Function.uncurry V) := hVp
  have hSm : StronglyMeasurable[𝒢.predictable] (fun z : ℝ≥0 × Ω => Real.sqrt (V z.1 z.2)) :=
    (hVsm.measurable.sqrt).stronglyMeasurable
  have hν : IsFiniteMeasure (hestonTimeMeasure t) := by
    rw [hestonTimeMeasure_eq_horizon]
    infer_instance
  have hK : MemLp (fun _ : ℝ≥0 => (1 : ℝ)) 2 (hestonTimeMeasure t) := memLp_const 1
  have hraw : MemLp (fun z : ℝ≥0 × Ω => Real.sqrt (V z.1 z.2)) 2 ((hestonTimeMeasure t).prod μ) := by
    simpa only [one_mul] using memLp_kernel_mul_sqrt_of_uniform_mean hK
      (hVsm.mono 𝒢.predictable_le_prod).measurable hVnonneg hVint hmean
  exact (le_of_eq (eLpNorm_jointPredictableMeasure_eq_product t hSm)).trans_lt hraw

end RoughHeston

#print axioms RoughHeston.heston_fractional_composition_at
#print axioms RoughHeston.heston_fubini_integrated_weight

#print axioms RoughHeston.ae_fst_mem_Ioo_jointPredictableMeasure
#print axioms RoughHeston.heston_fubini_integrated_weight_ae
#print axioms RoughHeston.sqrt_variance_memLp_joint
