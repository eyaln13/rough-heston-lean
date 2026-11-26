import HestonKernelFamilyMeasurable
import HestonFubiniIntegrability
import HestonFubiniKernel
import JointItoAssembly

open MeasureTheory ProbabilityTheory Set Filter
open scoped MeasureTheory ProbabilityTheory NNReal ENNReal

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℝ≥0 m} {M V : ℝ≥0 → Ω → ℝ}

private def clampToHorizon (t u : ℝ≥0) : Icc (0 : ℝ≥0) t :=
  ⟨min u t, zero_le, min_le_right _ _⟩

private theorem measurable_clampToHorizon (t : ℝ≥0) : Measurable (clampToHorizon t) :=
  (measurable_id.min measurable_const).subtype_mk

/-- The fractional Volterra stochastic Fubini identity in terminal L²
on the joint filtration. The inverse convolution of the forward
stochastic convolution is the integral of the square-root amplitude. -/
theorem heston_fractionalVolterra_fubini [IsFiniteMeasure μ] {α : ℝ}
    (hα : 1 / 2 < α) (hα' : α < 1) (t : ℝ≥0) (hM₂ : ∀ r, MemLp (M r) 2 μ)
    (hVp : IsStronglyPredictable 𝒢 V) (hVnonneg : ∀ s ω, 0 ≤ V s ω)
    (hVint : ∀ s, Integrable (V s) μ) {C : ℝ} (hmean : ∀ s, (∫ ω, V s ω ∂μ) ≤ C) :
    let I := jointItoIntegralCLM (𝒢 := 𝒢) t hM₂
    let φ (u : ℝ≥0) := hestonKernelFamilyLp hα hVp hVnonneg hVint hmean (clampToHorizon t u)
    let ha := sqrt_variance_memLp_joint t hVp hVnonneg hVint hmean
    (∫ u : ℝ≥0, fractionalL α ((t : ℝ) - (u : ℝ)) • I (φ u) ∂hestonTimeMeasure t) =
      I (ha.toLp (fun z : ℝ≥0 × Ω => Real.sqrt (V z.1 z.2))) := by
  dsimp only
  let I := jointItoIntegralCLM (𝒢 := 𝒢) t hM₂
  let φ (u : ℝ≥0) := hestonKernelFamilyLp hα hVp hVnonneg hVint hmean (clampToHorizon t u)
  let L (u : ℝ≥0) := fractionalL α ((t : ℝ) - (u : ℝ))
  let ψ := hestonFubiniRepresentative α t V
  let ha := sqrt_variance_memLp_joint t hVp hVnonneg hVint hmean
  let a := ha.toLp (fun z : ℝ≥0 × Ω => Real.sqrt (V z.1 z.2))
  have hα₀ : 0 < α := lt_trans (by norm_num) hα
  have hν : IsFiniteMeasure (hestonTimeMeasure t) := by
    rw [hestonTimeMeasure_eq_horizon]
    infer_instance
  have hm : StronglyMeasurable φ :=
    (hestonKernelFamilyLp_stronglyMeasurable hα hα'.le hVp hVnonneg hVint hmean).comp_measurable
      (measurable_clampToHorizon t)
  have hr (u : ℝ≥0) : ⇑(φ u) =ᵐ[jointPredictableMeasure 𝒢 μ t]
      Function.uncurry (hestonConvolutionWeight α (min u t) V) :=
    hestonKernelFamilyLp_ae hα hVp hVnonneg hVint hmean (clampToHorizon t u)
  have hInt := integrable_fractionalL_smul_heston_family hα hα' t hVp hVnonneg hVint hmean
    φ hm.aestronglyMeasurable (fun u hu => by simpa only [min_eq_left hu] using hr u)
  have hrep (u : ℝ≥0) : ⇑(L u • φ u) =ᵐ[jointPredictableMeasure 𝒢 μ t] ψ u :=
    heston_fubini_representative_ae_eq α t u (φ u) (hr u)
  have hjoint := heston_fubini_jointIntegrable α t hVp (fun u => L u • φ u)
    hInt (Eventually.of_forall hrep)
  have hw : (fun z => ∫ u, ψ u z ∂hestonTimeMeasure t) =ᵐ[jointPredictableMeasure 𝒢 μ t]
      (fun z => Real.sqrt (V z.1 z.2)) :=
    heston_fubini_integrated_weight_ae hα₀ hα' t V
  have hg : ⇑a =ᵐ[jointPredictableMeasure 𝒢 μ t] fun z => ∫ u, ψ u z ∂hestonTimeMeasure t :=
    ha.coeFn_toLp.trans hw.symm
  have h := jointItoIntegralCLM_fubini t hM₂ (fun u => L u • φ u) hInt ψ hjoint hrep a hg
  change (∫ u, L u • I (φ u) ∂hestonTimeMeasure t) = I a
  simpa only [map_smul] using h

end RoughHeston

#print axioms RoughHeston.heston_fractionalVolterra_fubini
