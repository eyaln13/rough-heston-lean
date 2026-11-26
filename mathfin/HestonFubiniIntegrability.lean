import HestonKernelMomentBound
import FractionalKernelL1
import MathFin.Probability.Brownian.Ito.StochasticFubini

open MeasureTheory Filter Set
open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℝ≥0 m}

/-- The reflected inverse kernel times the Heston L² family is Bochner
integrable whenever the parameter family is almost everywhere strongly
measurable. A representative is needed only on the horizon. -/
theorem integrable_fractionalL_smul_heston_family [IsFiniteMeasure μ]
    {α : ℝ} (hα : 1 / 2 < α) (hα' : α < 1) (t : ℝ≥0) {V : ℝ≥0 → Ω → ℝ}
    (hV : IsStronglyPredictable 𝒢 V) (hVnonneg : ∀ s ω, 0 ≤ V s ω)
    (hVint : ∀ s, Integrable (V s) μ) {C : ℝ}
    (hmean : ∀ s, (∫ ω, V s ω ∂μ) ≤ C)
    (φ : ℝ≥0 → Lp ℝ 2 (jointPredictableMeasure 𝒢 μ t))
    (hφ : AEStronglyMeasurable φ (hestonTimeMeasure t))
    (hrep : ∀ u ≤ t, ⇑(φ u) =ᵐ[jointPredictableMeasure 𝒢 μ t]
      Function.uncurry (hestonConvolutionWeight α u V)) :
    Integrable (fun u : ℝ≥0 => fractionalL α ((t : ℝ) - (u : ℝ)) • φ u)
      (hestonTimeMeasure t) := by
  let g (u : ℝ≥0) := fractionalL α ((t : ℝ) - (u : ℝ))
  let D := Real.sqrt (C * (∫ r in (0 : ℝ)..(t : ℝ), hestonKernel α r ^ 2))
  have hg : Integrable g (hestonTimeMeasure t) :=
    fractionalL_reflected_integrable_hestonTimeMeasure hα' t
  refine (hg.norm.mul_const D).mono' (hg.aestronglyMeasurable.smul hφ) ?_
  filter_upwards [ae_time_lt_hestonTimeMeasure t] with u hu
  have hb : ‖φ u‖ ≤ D := by
    have henergy := heston_convolution_weight_energy_le hα hu.le hV hVnonneg hVint hmean
    have hn : ‖φ u‖ = (eLpNorm (Function.uncurry (hestonConvolutionWeight α u V)) 2
        (jointPredictableMeasure 𝒢 μ t)).toReal := by
      rw [Lp.norm_def, eLpNorm_congr_ae (hrep u hu.le)]
    have hsq := Real.sqrt_le_sqrt henergy
    rw [← hn, Real.sqrt_sq (norm_nonneg _)] at hsq
    exact hsq
  change ‖g u • φ u‖ ≤ ‖g u‖ * D
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)

private theorem integral_norm_lp_two_le {S : Type*} {mS : MeasurableSpace S}
    {κ : Measure S} [IsFiniteMeasure κ] (f : Lp ℝ 2 κ) :
    (∫ z, ‖f z‖ ∂κ) ≤ ‖f‖ * (κ univ ^ (1 / 2 : ℝ)).toReal := by
  have hf := Lp.aestronglyMeasurable f
  have hi := (Lp.memLp f).integrable one_le_two
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) one_le_two hf
  have hexp : (1 : ℝ) / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal = 1 / 2 := by
    norm_num
  rw [hexp] at h
  have hfinite : κ univ ^ (1 / 2 : ℝ) ≠ ∞ :=
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (measure_ne_top κ _)).ne
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f) hfinite) h
  rw [ENNReal.toReal_mul, ← Lp.norm_def,
    eLpNorm_one_eq_lintegral_enorm hf, ← ofReal_integral_norm_eq_lintegral_enorm hi,
    ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _)] at hr
  exact hr

/-- For a finite inner measure, a Bochner integrable L² family with
jointly measurable representatives supplies the joint integrability
hypothesis of stochastic Fubini. -/
theorem jointIntegrable_of_integrable_L2_family {A S : Type*}
    {mA : MeasurableSpace A} {mS : MeasurableSpace S}
    {ν : Measure A} {κ : Measure S} [IsFiniteMeasure κ]
    (φ : A → Lp ℝ 2 κ) (hφ : Integrable φ ν) {ψ : A → S → ℝ}
    (hψ : AEStronglyMeasurable (Function.uncurry ψ) (ν.prod κ))
    (hrep : ∀ᵐ u ∂ν, ⇑(φ u) =ᵐ[κ] ψ u) :
    MathFin.StochasticFubini.JointIntegrable ψ ν κ := by
  refine (integrable_prod_iff hψ).2 ⟨?_, ?_⟩
  · exact hrep.mono fun u hu => ((Lp.memLp (φ u)).integrable one_le_two).congr hu
  · refine (hφ.norm.mul_const (κ univ ^ (1 / 2 : ℝ)).toReal).mono_nonneg
      hψ.norm.integral_prod_right'
      (Eventually.of_forall fun u => integral_nonneg fun _ => norm_nonneg _) ?_
    filter_upwards [hrep] with u hu
    have hEq : (∫ x, ‖ψ u x‖ ∂κ) = ∫ x, ‖φ u x‖ ∂κ :=
      integral_congr_ae (hu.symm.mono fun _ h => congrArg norm h)
    change (∫ x, ‖ψ u x‖ ∂κ) ≤ _
    rw [hEq]
    exact integral_norm_lp_two_le (φ u)

/-- The real representatives of the weighted L² family, with the inner
observation time clamped to the fixed horizon. -/
noncomputable def hestonFubiniRepresentative (α : ℝ) (t : ℝ≥0)
    (V : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) (z : ℝ≥0 × Ω) : ℝ :=
  fractionalL α ((t : ℝ) - (u : ℝ)) *
    hestonConvolutionWeight α (min u t) V z.1 z.2

theorem heston_fubini_representative_ae_eq
    (α : ℝ) (t u : ℝ≥0) {V : ℝ≥0 → Ω → ℝ}
    (φ : Lp ℝ 2 (jointPredictableMeasure 𝒢 μ t))
    (hφ : ⇑φ =ᵐ[jointPredictableMeasure 𝒢 μ t]
      Function.uncurry (hestonConvolutionWeight α (min u t) V)) :
    ⇑(fractionalL α ((t : ℝ) - (u : ℝ)) • φ) =ᵐ[jointPredictableMeasure 𝒢 μ t]
      hestonFubiniRepresentative α t V u := by
  filter_upwards [Lp.coeFn_smul (fractionalL α ((t : ℝ) - (u : ℝ))) φ, hφ] with z hs hz
  rw [hs, Pi.smul_apply, smul_eq_mul, hz]
  rfl

theorem heston_fubini_representative_measurable
    (α : ℝ) (t : ℝ≥0) {V : ℝ≥0 → Ω → ℝ} (hV : IsStronglyPredictable 𝒢 V) :
    @Measurable (ℝ≥0 × (ℝ≥0 × Ω)) ℝ
      ((inferInstance : MeasurableSpace ℝ≥0).prod 𝒢.predictable) _
      (Function.uncurry (hestonFubiniRepresentative α t V)) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := 𝒢.predictable
  have hp : Measurable (fun z : ℝ≥0 × (ℝ≥0 × Ω) => min z.1 t) :=
    measurable_fst.min measurable_const
  have hs : Measurable (fun z : ℝ≥0 × (ℝ≥0 × Ω) => z.2.1) :=
    (measurable_fst_jointPredictable 𝒢).comp measurable_snd
  have hu : Measurable (fun z : ℝ≥0 × (ℝ≥0 × Ω) => (z.1 : ℝ)) :=
    measurable_subtype_coe.comp measurable_fst
  have hshift : Measurable (fun z : ℝ≥0 × (ℝ≥0 × Ω) =>
      ((min z.1 t : ℝ≥0) : ℝ) - (z.2.1 : ℝ)) :=
    (measurable_subtype_coe.comp hp).sub (measurable_subtype_coe.comp hs)
  have hVm : Measurable (Function.uncurry V) := StronglyMeasurable.measurable hV
  exact ((fractionalL_measurable α).comp (measurable_const.sub hu)).mul
    (((hestonKernel_measurable α).comp hshift).mul (hVm.comp measurable_snd).sqrt)

theorem heston_fubini_jointIntegrable [IsFiniteMeasure μ]
    (α : ℝ) (t : ℝ≥0) {V : ℝ≥0 → Ω → ℝ} (hV : IsStronglyPredictable 𝒢 V)
    (φ : ℝ≥0 → Lp ℝ 2 (jointPredictableMeasure 𝒢 μ t))
    (hφ : Integrable φ (hestonTimeMeasure t))
    (hrep : ∀ᵐ u ∂hestonTimeMeasure t, ⇑(φ u) =ᵐ[jointPredictableMeasure 𝒢 μ t]
      hestonFubiniRepresentative α t V u) :
    MathFin.StochasticFubini.JointIntegrable (hestonFubiniRepresentative α t V)
      (hestonTimeMeasure t) (jointPredictableMeasure 𝒢 μ t) :=
  jointIntegrable_of_integrable_L2_family φ hφ
    (heston_fubini_representative_measurable α t hV).aestronglyMeasurable hrep

end RoughHeston

#print axioms RoughHeston.integrable_fractionalL_smul_heston_family
#print axioms RoughHeston.jointIntegrable_of_integrable_L2_family
#print axioms RoughHeston.heston_fubini_representative_ae_eq
#print axioms RoughHeston.heston_fubini_representative_measurable
#print axioms RoughHeston.heston_fubini_jointIntegrable
