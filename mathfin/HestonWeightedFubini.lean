import HestonKernelFamilyMeasurable
import HestonFubiniIntegrability
import HestonFubiniKernel
import JointItoAssembly

open MeasureTheory ProbabilityTheory Set Filter
open scoped MeasureTheory ProbabilityTheory NNReal ENNReal

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℝ≥0 m} {M V : ℝ≥0 → Ω → ℝ}

def hestonNNRealHorizonPoint (t u : ℝ≥0) : Icc (0 : ℝ≥0) t :=
  ⟨min u t, zero_le, min_le_right _ _⟩

private theorem reflected_kernel_integrable_hestonTimeMeasure
    {f : ℝ → ℝ} (t : ℝ≥0) (hm : Measurable f) (hi : IntegrableOn f (Ioc 0 (t : ℝ))) :
    Integrable (fun u : ℝ≥0 => f ((t : ℝ) - (u : ℝ))) (hestonTimeMeasure t) := by
  have hf : Measurable (fun u : ℝ≥0 => f ((t : ℝ)-(u : ℝ))) :=
    hm.comp (measurable_const.sub measurable_subtype_coe)
  have hreflected : IntervalIntegrable (fun u : ℝ => f ((t : ℝ)-u)) volume 0 (t : ℝ) := by
    have h := (intervalIntegrable_iff_integrableOn_Ioc_of_le (NNReal.coe_nonneg t)).2 hi
    simpa only [sub_zero, sub_self] using (h.comp_sub_left (t : ℝ)).symm
  have hIoo := hreflected.1.mono_set Ioo_subset_Ioc_self
  apply (integrable_map_measure hf.aestronglyMeasurable
    continuous_real_toNNReal.measurable.aemeasurable).2
  refine hIoo.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  simp only [Function.comp_apply, Real.coe_toNNReal u hu.1.le]

private theorem hestonKernel_eq_fractionalK_for_weight (α x : ℝ) :
    hestonKernel α x = fractionalK α x := by
  unfold hestonKernel fractionalK
  by_cases h : 0 < x
  · simp [h, not_le.mpr h]
  · simp [h, le_of_not_gt h]

private theorem heston_kernel_composition_with_weight {α : ℝ} {f : ℝ → ℝ}
    (hm : Measurable f) {s t : ℝ≥0} (hs : s ∈ Ioo 0 t) :
    (∫ u : ℝ≥0, f ((t : ℝ)-(u : ℝ)) *
      hestonKernel α ((u : ℝ)-(s : ℝ)) ∂hestonTimeMeasure t) =
      volterraConvolution f (fractionalK α) ((t : ℝ)-(s : ℝ)) := by
  have hφ : Measurable (fun u : ℝ≥0 => f ((t : ℝ)-(u : ℝ)) *
      hestonKernel α ((u : ℝ)-(s : ℝ))) :=
    (hm.comp (measurable_const.sub measurable_subtype_coe)).mul
      ((hestonKernel_measurable α).comp (measurable_subtype_coe.sub measurable_const))
  rw [hestonTimeMeasure, integral_map continuous_real_toNNReal.measurable.aemeasurable
    hφ.aestronglyMeasurable]
  have hsr : (s : ℝ) ∈ Ioc (0 : ℝ) (t : ℝ) := ⟨by exact_mod_cast hs.1, by exact_mod_cast hs.2.le⟩
  calc
    _ = ∫ u in Ioo (0 : ℝ) (t : ℝ), f ((t : ℝ)-u) *
          fractionalK α (u-(s : ℝ)) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      simp only [Real.coe_toNNReal u hu.1.le, hestonKernel_eq_fractionalK_for_weight]
    _ = ∫ u in Ioc (0 : ℝ) (t : ℝ), f ((t : ℝ)-u) *
          fractionalK α (u-(s : ℝ)) := setIntegral_congr_set Ioo_ae_eq_Ioc
    _ = _ := volterra_shifted_kernel_integral (fun x hx => by simp [fractionalK, hx]) hsr

/-- Integrating the fractional stochastic convolution against any
integrable deterministic weight gives the terminal Itô integral of its
convolution kernel. The input weight may be singular at zero. -/
theorem heston_weighted_stochastic_fubini [IsFiniteMeasure μ] {α : ℝ}
    (hα : 1/2 < α) (hα' : α ≤ 1) (t : ℝ≥0) (hM₂ : ∀ r, MemLp (M r) 2 μ)
    (hVp : IsStronglyPredictable 𝒢 V) (hVnonneg : ∀ s ω, 0 ≤ V s ω)
    (hVint : ∀ s, Integrable (V s) μ) {C : ℝ} (hmean : ∀ s, (∫ ω, V s ω ∂μ) ≤ C)
    {f : ℝ → ℝ} (hfm : Measurable f) (hfi : IntegrableOn f (Ioc 0 (t : ℝ))) :
    let I := jointItoIntegralCLM (𝒢 := 𝒢) t hM₂
    let φ (u : ℝ≥0) := hestonKernelFamilyLp hα hVp hVnonneg hVint hmean (hestonNNRealHorizonPoint t u)
    let F (u : ℝ≥0) := f ((t : ℝ)-(u : ℝ))
    ∃ g : Lp ℝ 2 (jointPredictableMeasure 𝒢 μ t),
      (⇑g =ᵐ[jointPredictableMeasure 𝒢 μ t] fun z =>
        volterraConvolution f (fractionalK α) ((t : ℝ)-(z.1 : ℝ)) *
          Real.sqrt (V z.1 z.2)) ∧
      (∫ u, F u • I (φ u) ∂hestonTimeMeasure t) = I g := by
  dsimp only
  let I := jointItoIntegralCLM (𝒢 := 𝒢) t hM₂
  let φ u := hestonKernelFamilyLp hα hVp hVnonneg hVint hmean (hestonNNRealHorizonPoint t u)
  let F (u : ℝ≥0) := f ((t : ℝ)-(u : ℝ))
  let ψ (u : ℝ≥0) (z : ℝ≥0 × Ω) :=
    F u * hestonConvolutionWeight α (min u t) V z.1 z.2
  have hν : IsFiniteMeasure (hestonTimeMeasure t) := by
    rw [hestonTimeMeasure_eq_horizon]
    infer_instance
  have hFm : Measurable F := hfm.comp (measurable_const.sub measurable_subtype_coe)
  have hF : Integrable F (hestonTimeMeasure t) :=
    reflected_kernel_integrable_hestonTimeMeasure t hfm hfi
  have hcm : Measurable (hestonNNRealHorizonPoint t) := (measurable_id.min measurable_const).subtype_mk
  have hφm : StronglyMeasurable φ :=
    (hestonKernelFamilyLp_stronglyMeasurable hα hα' hVp hVnonneg hVint hmean).comp_measurable hcm
  have hr (u : ℝ≥0) : ⇑(φ u) =ᵐ[jointPredictableMeasure 𝒢 μ t]
      Function.uncurry (hestonConvolutionWeight α (min u t) V) :=
    hestonKernelFamilyLp_ae hα hVp hVnonneg hVint hmean (hestonNNRealHorizonPoint t u)
  have hφi : Integrable (fun u => F u • φ u) (hestonTimeMeasure t) := by
    let D := Real.sqrt (C * (∫ r in (0 : ℝ)..(t : ℝ), hestonKernel α r ^ 2))
    refine (hF.norm.mul_const D).mono' (hFm.aestronglyMeasurable.smul hφm.aestronglyMeasurable) ?_
    filter_upwards [ae_time_lt_hestonTimeMeasure t] with u hu
    have hr' : ⇑(φ u) =ᵐ[jointPredictableMeasure 𝒢 μ t]
      Function.uncurry (hestonConvolutionWeight α u V) := by
      simpa only [min_eq_left hu.le] using hr u
    have henergy := heston_convolution_weight_energy_le hα hu.le hVp hVnonneg hVint hmean
    have he : ‖φ u‖ = (eLpNorm (Function.uncurry (hestonConvolutionWeight α u V)) 2
        (jointPredictableMeasure 𝒢 μ t)).toReal := by
      rw [Lp.norm_def, eLpNorm_congr_ae hr']
    have hb := Real.sqrt_le_sqrt henergy
    rw [← he, Real.sqrt_sq (norm_nonneg _)] at hb
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
  have hrep (u : ℝ≥0) : ⇑(F u • φ u) =ᵐ[jointPredictableMeasure 𝒢 μ t] ψ u := by
    filter_upwards [Lp.coeFn_smul (F u) (φ u), hr u] with z hs hz
    rw [hs, Pi.smul_apply, smul_eq_mul, hz]
    rfl
  have hψ : @Measurable (ℝ≥0 × (ℝ≥0 × Ω)) ℝ
      ((inferInstance : MeasurableSpace ℝ≥0).prod 𝒢.predictable) _ (Function.uncurry ψ) := by
    let : MeasurableSpace (ℝ≥0 × Ω) := 𝒢.predictable
    have hp : Measurable (fun z : ℝ≥0 × (ℝ≥0 × Ω) => min z.1 t) :=
      measurable_fst.min measurable_const
    have hs : Measurable (fun z : ℝ≥0 × (ℝ≥0 × Ω) => z.2.1) :=
      (measurable_fst_jointPredictable 𝒢).comp measurable_snd
    have hshift : Measurable (fun z : ℝ≥0 × (ℝ≥0 × Ω) =>
        ((min z.1 t : ℝ≥0) : ℝ)-(z.2.1 : ℝ)) :=
      (measurable_subtype_coe.comp hp).sub (measurable_subtype_coe.comp hs)
    have hVm : Measurable (Function.uncurry V) := StronglyMeasurable.measurable hVp
    exact (hFm.comp measurable_fst).mul
      (((hestonKernel_measurable α).comp hshift).mul (hVm.comp measurable_snd).sqrt)
  have hjoint := jointIntegrable_of_integrable_L2_family (fun u => F u • φ u) hφi
    hψ.aestronglyMeasurable (Eventually.of_forall hrep)
  let g := ∫ u, F u • φ u ∂hestonTimeMeasure t
  have hg := MathFin.StochasticFubini.coeFn_integral_ae_eq (fun u => F u • φ u)
    hφi ψ hjoint hrep
  have heq : ∀ᵐ z ∂jointPredictableMeasure 𝒢 μ t, (∫ u, ψ u z ∂hestonTimeMeasure t) =
      volterraConvolution f (fractionalK α) ((t : ℝ)-(z.1 : ℝ)) * Real.sqrt (V z.1 z.2) := by
    filter_upwards [ae_fst_mem_Ioo_jointPredictableMeasure (𝒢 := 𝒢) (μ := μ) t] with z hz
    have hclamp : (∫ u, ψ u z ∂hestonTimeMeasure t) =
        ∫ u, (F u * hestonKernel α ((u : ℝ)-(z.1 : ℝ))) * Real.sqrt (V z.1 z.2)
          ∂hestonTimeMeasure t := by
      apply integral_congr_ae
      filter_upwards [ae_time_lt_hestonTimeMeasure t] with u hu
      simp only [ψ, min_eq_left hu.le, hestonConvolutionWeight, mul_assoc]
    rw [hclamp, integral_mul_const, heston_kernel_composition_with_weight hfm hz]
  refine ⟨g, hg.trans heq, ?_⟩
  have hfub := jointItoIntegralCLM_fubini t hM₂ (fun u => F u • φ u) hφi ψ hjoint hrep g hg
  change (∫ u, F u • I (φ u) ∂hestonTimeMeasure t) = I g
  simpa only [map_smul] using hfub


theorem volterraConvolution_comm_at {f g : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) :
    volterraConvolution f g t = volterraConvolution g f t := by
  unfold volterraConvolution
  rw [← intervalIntegral.integral_of_le ht, ← intervalIntegral.integral_of_le ht]
  have he := intervalIntegral.integral_comp_sub_left (a := 0) (b := t)
    (fun u : ℝ => f (t-u)*g u) t
  simpa only [sub_self, sub_zero, sub_sub_cancel, mul_comm] using he.symm

/-- The terminal integral of a Riccati kernel is the sum of the
point-charge integral and the weighted Volterra stochastic convolution. -/
theorem heston_riccati_stochastic_term [IsFiniteMeasure μ] {α q : ℝ}
    (hα : 1/2 < α) (hα' : α ≤ 1) (t : ℝ≥0) (hM₂ : ∀ r, MemLp (M r) 2 μ)
    (hVp : IsStronglyPredictable 𝒢 V) (hVnonneg : ∀ s ω, 0 ≤ V s ω)
    (hVint : ∀ s, Integrable (V s) μ) {C : ℝ} (hmean : ∀ s, (∫ ω, V s ω ∂μ) ≤ C)
    {f w : ℝ → ℝ} (hfm : Measurable f) (hfi : IntegrableOn f (Ioc 0 (t : ℝ)))
    (hw : ∀ s ∈ Ioc 0 (t : ℝ), w s =
      q * fractionalK α s + volterraConvolution (fractionalK α) f s) :
    let I := jointItoIntegralCLM (𝒢 := 𝒢) t hM₂
    let φ (u : ℝ≥0) := hestonKernelFamilyLp hα hVp hVnonneg hVint hmean (hestonNNRealHorizonPoint t u)
    let F (u : ℝ≥0) := f ((t : ℝ)-(u : ℝ))
    ∃ W : Lp ℝ 2 (jointPredictableMeasure 𝒢 μ t),
      (⇑W =ᵐ[jointPredictableMeasure 𝒢 μ t] fun z =>
        w ((t : ℝ)-(z.1 : ℝ)) * Real.sqrt (V z.1 z.2)) ∧
      I W = q • I (φ t) + ∫ u, F u • I (φ u) ∂hestonTimeMeasure t := by
  dsimp only
  let φ (u : ℝ≥0) := hestonKernelFamilyLp hα hVp hVnonneg hVint hmean (hestonNNRealHorizonPoint t u)
  obtain ⟨G, hG, hEq⟩ := heston_weighted_stochastic_fubini hα hα' t hM₂
    hVp hVnonneg hVint hmean hfm hfi
  refine ⟨q • φ t + G, ?_, ?_⟩
  · have hφ := hestonKernelFamilyLp_ae hα hVp hVnonneg hVint hmean (hestonNNRealHorizonPoint t t)
    filter_upwards [hG, hφ, Lp.coeFn_add (q • φ t) G, Lp.coeFn_smul q (φ t),
      ae_fst_mem_Ioo_jointPredictableMeasure (𝒢 := 𝒢) (μ := μ) t] with z hGz hφz hadd hs hz
    have hp : 0 < (t : ℝ)-(z.1 : ℝ) := sub_pos.mpr (by exact_mod_cast hz.2)
    have hsT : (t : ℝ)-(z.1 : ℝ) ≤ (t : ℝ) := sub_le_self _ (NNReal.coe_nonneg _)
    change (q • φ t + G) z = w ((t : ℝ)-(z.1 : ℝ)) * Real.sqrt (V z.1 z.2)
    change (φ t) z = hestonConvolutionWeight α (min t t) V z.1 z.2 at hφz
    rw [hadd, Pi.add_apply, hs, Pi.smul_apply, smul_eq_mul, hφz, hGz, min_self,
      hestonConvolutionWeight, hestonKernel_eq_fractionalK_for_weight, hw _ ⟨hp, hsT⟩,
      volterraConvolution_comm_at hp.le]
    ring
  · rw [map_add, map_smul, hEq]

end RoughHeston

#print axioms RoughHeston.heston_weighted_stochastic_fubini

#print axioms RoughHeston.heston_riccati_stochastic_term
