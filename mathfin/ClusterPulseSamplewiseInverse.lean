import ClusterPulseInverse

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Interval

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {B U : ℝ≥0 → Ω → ℝ}

set_option maxHeartbeats 350000 in
/-- Recover the direct cluster equation from its samplewise inverse
equation and its focal amplitude cutoff integral. -/
theorem rectangularPulse_L2_equation_of_samplewise_inverse
    {T : ℝ≥0} {α κ σ ε d : ℝ} (hα : 1/2 < α) (hα' : α < 1) (hT : 0 < T)
    (hε : 0 ≤ ε) (hd : 0 < d) (hσ : 0 ≤ σ)
    (hB₂ : ∀ r, MemLp (B r) 2 P) (hB : Martingale B F P)
    (hBclock : Martingale (fun r ω => B r ω ^ 2 - ((min r T : ℝ≥0) : ℝ)) F P)
    (hU : IsStronglyPredictable F U) (hUa : StronglyAdapted F U)
    (hUc : ∀ᵐ ω ∂P, ContinuousOn (fun t => U t ω) (Icc 0 T))
    (hU₀ : ∀ s ω, 0 ≤ U s ω) (hUi : ∀ s, Integrable (U s) P)
    {A : ℝ} (hMean : ∀ s, (∫ ω, U s ω ∂P) ≤ A)
    {M : ℝ≥0 → Ω → ℝ}
    (hM : HasAmplitudeCutoffIntegral F P T B M (fun s ω => σ * Real.sqrt (U s ω)))
    (v : ℝ → Lp ℝ 2 P) (hvM : StronglyMeasurable v) (hvC : ContinuousOn v (Icc 0 (T : ℝ)))
    (hvRep : ∀ s, ⇑(v s) =ᵐ[P] U s.toNNReal)
    (hInv : ∀ u : ℝ≥0, u ≤ T →
      (fun ω => ∫ s in Ioc (0 : ℝ) (u : ℝ), fractionalL α ((u : ℝ) - s) * U s.toNNReal ω) =ᵐ[P]
      (fun ω => (∫ s in Ioc (0 : ℝ) (u : ℝ), rectangularPulseRate ε d s - κ * U s.toNNReal ω) + M u ω)) :
    ∀ s ∈ Icc 0 (T : ℝ), v s =
      volterraSmulConvolution (fractionalK α)
        (fun u => clusterDeterministicInputLp P (rectangularPulseRate ε d) u - κ • v u) s +
        σ • fixedHestonConvolutionLp (T := T) hα hB₂ hU hU₀ hUi hMean s := by
  apply rectangularPulse_L2_of_inverse hα hα' hT hε hd hB₂ hB hBclock hU hU₀ hUi hMean v hvM hvC
  intro u hu
  let a (s : ℝ≥0) (ω : Ω) := Real.sqrt (U s ω)
  let scale (s : ℝ≥0) (ω : Ω) := σ * a s ω
  let ha : MemLp (Function.uncurry a) 2 (jointPredictableMeasure F P T) :=
    sqrt_variance_memLp_joint T hU hU₀ hUi hMean
  have hscale : MemLp (Function.uncurry scale) 2 (jointPredictableMeasure F P T) := ha.const_mul σ
  have has : StronglyAdapted F scale := fun s => ((hUa s).measurable.sqrt.const_mul σ).stronglyMeasurable
  have hsp : StronglyMeasurable[F.predictable] (Function.uncurry scale) :=
    (hU.measurable.sqrt.const_mul σ).stronglyMeasurable
  have hsc : ∀ᵐ ω ∂P, ContinuousOn (fun t => scale t ω) (Icc 0 u) :=
    hUc.mono fun ω hω => continuousOn_const.mul (Real.continuous_sqrt.comp_continuousOn
      (hω.mono (Icc_subset_Icc_right hu)))
  have hs₀ (s : ℝ≥0) (ω : Ω) : 0 ≤ scale s ω := mul_nonneg hσ (Real.sqrt_nonneg _)
  have hMs := hM.ae_eq_jointIto_fixed_horizon hu hB hB₂ hBclock has hsp hsc hs₀ hscale
  let sa := jointAmplitudeSectionLp (a := a) u ha
  let ss := jointAmplitudeSectionLp (a := scale) u hscale
  have hsEq : ss = σ • sa := by
    apply Lp.ext
    filter_upwards [jointAmplitudeSectionLp_ae (𝒢 := F) (μ := P) (T := T) (a := scale) u hscale,
      jointAmplitudeSectionLp_ae (𝒢 := F) (μ := P) (T := T) (a := a) u ha,
      Lp.coeFn_smul σ sa] with p hsp hap hσp
    change ss p = (σ • sa) p
    rw [hσp, Pi.smul_apply, smul_eq_mul, hsp, hap]
    by_cases hp : p ∈ Ioc (0 : ℝ≥0) u ×ˢ (univ : Set Ω)
    · simp [hp, Function.uncurry, scale]
    · simp [hp]
  let I := jointItoIntegralCLM (𝒢 := F) T hB₂
  have hMs' : M u =ᵐ[P] ((σ • I sa : Lp ℝ 2 P) : Ω → ℝ) := by
    change M u =ᵐ[P] (I ss : Ω → ℝ) at hMs
    rwa [hsEq, map_smul] at hMs
  let k (s : ℝ) := fractionalL α ((u : ℝ) - s)
  let j := rectangularPulseRate ε d
  let g (s : ℝ) := clusterDeterministicInputLp P j s - κ • v s
  let Ureal (s : ℝ) (ω : Ω) := U s.toNNReal ω
  let greal (s : ℝ) (ω : Ω) := j s - κ * Ureal s ω
  let one : Lp ℝ 2 P := (memLp_const (1 : ℝ)).toLp (fun _ => 1)
  have hone : ⇑one =ᵐ[P] fun _ => 1 := (memLp_const (1 : ℝ)).coeFn_toLp
  have hUreal : Measurable (Function.uncurry Ureal) :=
    (hU.mono F.predictable_le_prod).measurable.comp
      (continuous_real_toNNReal.measurable.prodMap (measurable_id : Measurable (@id Ω)))
  have hj : Measurable j := measurable_const.indicator measurableSet_Ioc
  have hgreal : Measurable (Function.uncurry greal) :=
    (hj.comp measurable_fst).sub (hUreal.const_mul κ)
  have hrep (s : ℝ) : ⇑(g s) =ᵐ[P] greal s := by
    filter_upwards [Lp.coeFn_sub (j s • one) (κ • v s), Lp.coeFn_smul (j s) one,
      Lp.coeFn_smul κ (v s), hvRep s, hone] with ω hsub hjω hκω hvω h₁
    change (j s • one - κ • v s) ω = _
    rw [hsub, Pi.sub_apply, hjω, hκω]
    simp only [Pi.smul_apply, smul_eq_mul, h₁, mul_one, hvω, greal, Ureal]
  have hu' : Icc 0 (u : ℝ) ⊆ Icc 0 (T : ℝ) := Icc_subset_Icc_right (NNReal.coe_le_coe.mpr hu)
  have hki := fractionalL_reflected_integrableOn_Ioc hα' u.prop
  have hvi := pulse_weighted_reflected_integrableOn (fractionalL_measurable α) hki hvM (hvC.mono hu')
  have hk : Measurable k := (fractionalL_measurable α).comp (measurable_const.sub measurable_id)
  have hVL := coeFn_integral_weighted_L2_path_ae hk hUreal hvi hvRep
  have hgi : IntegrableOn g (Ioc 0 (u : ℝ)) := by
    have hvI : IntegrableOn v (Ioc 0 (u : ℝ)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le u.prop).1
        ((hvC.mono hu').intervalIntegrable_of_Icc u.prop)
    exact (pulse_Lp_input_integrable (P := P) (ε := ε) (d := d)).sub (hvI.smul κ)
  have hGL := coeFn_integral_weighted_L2_path_ae (measurable_const (a := (1 : ℝ))) hgreal
    (show IntegrableOn (fun s => (1 : ℝ) • g s) (Ioc 0 (u : ℝ)) from by simpa only [one_smul] using hgi)
    hrep
  let G := ∫ s in Ioc (0 : ℝ) (u : ℝ), g s
  change volterraSmulConvolution (fractionalL α) v (u : ℝ) = G + σ • I sa
  apply Lp.ext
  filter_upwards [hVL, hGL, hMs', hInv u hu, Lp.coeFn_add G (σ • I sa)] with ω hVLω hGLω hMsω hInvω hsum
  change volterraSmulConvolution (fractionalL α) v (u : ℝ) ω = (G + σ • I sa) ω
  simp only [one_smul, one_mul] at hGLω
  rw [hsum, Pi.add_apply, ← hMsω, hGLω, ← hInvω]
  exact hVLω

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.rectangularPulse_L2_equation_of_samplewise_inverse
