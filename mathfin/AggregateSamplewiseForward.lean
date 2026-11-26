import AggregateDeterministicForcingInverse
import ClusterPulseSamplewiseInverse

/-! The shifted aggregate inverse equation in samplewise form gives the
actual direct `L²` equation with immigration centered out. -/

open MeasureTheory Set Filter ProbabilityTheory
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston.GirsanovPort

set_option maxHeartbeats 1500000

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {B U : ℝ≥0 → Ω → ℝ}

private theorem aggregate_deterministicInput_convolution {α : ℝ} {β : ℝ → ℝ} (s : ℝ) :
    volterraSmulConvolution (fractionalK α) (clusterDeterministicInputLp P β) s =
      clusterDeterministicInputLp P (volterraConvolution (fractionalK α) β) s := by
  unfold volterraSmulConvolution volterraConvolution clusterDeterministicInputLp
  simp only [← mul_smul]
  rw [integral_smul_const]

/-- The forward equation on the original continuous variance, with a
bounded deterministic immigration separated from the stochastic terms. -/
theorem aggregate_samplewise_forward_centered_L2
    {T : ℝ≥0} {α κ σ v₀ : ℝ} (hα : 1/2 < α) (hα' : α < 1) (hT : 0 < T) (hσ : 0 ≤ σ)
    {β : ℝ → ℝ} (hβ : Measurable β) {D : ℝ} (hβD : ∀ t, ‖β t‖ ≤ D)
    (hConv : Continuous (volterraConvolution (fractionalK α) β))
    (hB₂ : ∀ r, MemLp (B r) 2 P) (hB : Martingale B F P)
    (hBclock : Martingale (fun r ω => B r ω^2-((min r T:ℝ≥0):ℝ)) F P)
    (hU : IsStronglyPredictable F U) (hUa : StronglyAdapted F U)
    (hUc : ∀ᵐ ω ∂P, ContinuousOn (fun t => U t ω) (Icc 0 T))
    (hU₀ : ∀ s ω, 0 ≤ U s ω) (hUi : ∀ s, Integrable (U s) P)
    {A : ℝ} (hMean : ∀ s, (∫ ω, U s ω ∂P) ≤ A)
    {M : ℝ≥0 → Ω → ℝ}
    (hM : HasAmplitudeCutoffIntegral F P T B M (fun s ω => σ*Real.sqrt (U s ω)))
    (v : ℝ → Lp ℝ 2 P) (hvm : StronglyMeasurable v) (hvc : ContinuousOn v (Icc 0 (T : ℝ)))
    (hvRep : ∀ s, ⇑(v s) =ᵐ[P] U s.toNNReal)
    (hInv : ∀ u : ℝ≥0, u ≤ T →
      (fun ω => ∫ s in Ioc (0:ℝ) (u:ℝ), fractionalL α ((u:ℝ)-s)*(U s.toNNReal ω-v₀)) =ᵐ[P]
      (fun ω => (∫ s in Ioc (0:ℝ) (u:ℝ), β s-κ*U s.toNNReal ω)+M u ω)) :
    ∀ s ∈ Icc (0:ℝ) (T:ℝ),
      v s - clusterDeterministicInputLp P (fun _ => v₀) s -
        clusterDeterministicInputLp P (volterraConvolution (fractionalK α) β) s =
      volterraSmulConvolution (hestonKernel α) (fun r => (-κ) • v r) s +
        σ • fixedHestonConvolutionLp (T := T) hα hB₂ hU hU₀ hUi hMean s := by
  let one : Lp ℝ 2 P := (memLp_const (1:ℝ)).toLp (fun _ => 1)
  let v' := fun s => v s-v₀ • one
  let g := (-κ:ℝ) • v
  let j := clusterDeterministicInputLp P β
  have hvm' : StronglyMeasurable v' := hvm.sub stronglyMeasurable_const
  have hvc' : ContinuousOn v' (Icc 0 (T:ℝ)) := hvc.sub continuousOn_const
  have hgm : StronglyMeasurable g := by
    change StronglyMeasurable ((-κ:ℝ) • v)
    exact hvm.const_smul (-κ)
  have hgc : ContinuousOn g (Icc 0 (T:ℝ)) := hvc.const_smul (-κ)
  have hj : StronglyMeasurable j := hβ.stronglyMeasurable.smul stronglyMeasurable_const
  have hjI (u : ℝ≥0) : IntegrableOn j (Ioc 0 (u:ℝ)) := by
    refine (integrable_const (D*‖one‖)).mono' hj.aestronglyMeasurable ?_
    exact ae_of_all _ fun r => by
      change ‖β r • one‖ ≤ D*‖one‖
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hβD _) (norm_nonneg _)
  have hD : Continuous (volterraSmulConvolution (fractionalK α) j) := by
    rw [show volterraSmulConvolution (fractionalK α) j = _ from
      funext (aggregate_deterministicInput_convolution (P := P) (α := α) (β := β))]
    exact hConv.smul continuous_const
  have hForward := heston_L2_centered_of_inverse (σ := σ) hα hα' hT hB₂ hB hBclock hU hU₀ hUi hMean
      hvm' hvc' hgm hgc hj (fun u _ => hjI u) hD
  suffices h : ∀ u : ℝ≥0, u ≤ T →
      volterraSmulConvolution (fractionalL α) v' (u:ℝ) =
        (∫ s in Ioc (0:ℝ) (u:ℝ), j s+g s) + σ • jointItoIntegralCLM T hB₂
        (jointAmplitudeSectionLp (a := fun s ω => Real.sqrt (U s ω)) u
          (sqrt_variance_memLp_joint T hU hU₀ hUi hMean)) by
    intro s hs
    rw [← aggregate_deterministicInput_convolution]
    exact hForward h s hs
  intro u hu
  let a (s : ℝ≥0) (ω : Ω) := Real.sqrt (U s ω)
  let scale (s : ℝ≥0) (ω : Ω) := σ*a s ω
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
    by_cases hp : p ∈ Ioc (0:ℝ≥0) u ×ˢ (univ : Set Ω)
    · simp [hp, Function.uncurry, scale]
    · simp [hp]
  let I := jointItoIntegralCLM (𝒢 := F) T hB₂
  have hMs' : M u =ᵐ[P] ((σ • I sa : Lp ℝ 2 P) : Ω → ℝ) := by
    change M u =ᵐ[P] (I ss : Ω → ℝ) at hMs
    rwa [hsEq, map_smul] at hMs
  let k (s : ℝ) := fractionalL α ((u:ℝ)-s)
  let Ureal (s : ℝ) (ω : Ω) := U s.toNNReal ω
  let greal (s : ℝ) (ω : Ω) := β s-κ*Ureal s ω
  let vreal (s : ℝ) (ω : Ω) := Ureal s ω-v₀
  have hUreal : Measurable (Function.uncurry Ureal) :=
    (hU.mono F.predictable_le_prod).measurable.comp
      (continuous_real_toNNReal.measurable.prodMap (measurable_id : Measurable (@id Ω)))
  have hgreal : Measurable (Function.uncurry greal) :=
    (hβ.comp measurable_fst).sub (hUreal.const_mul κ)
  have hvreal : Measurable (Function.uncurry vreal) := hUreal.sub_const v₀
  have hone : ⇑one =ᵐ[P] fun _ => 1 := (memLp_const (1:ℝ)).coeFn_toLp
  have hvr (s : ℝ) : ⇑(v' s) =ᵐ[P] vreal s := by
    filter_upwards [Lp.coeFn_sub (v s) (v₀ • one), Lp.coeFn_smul v₀ one, hvRep s, hone] with ω hsub hsm hvω h1
    change (v s-v₀ • one) ω = _
    rw [hsub, Pi.sub_apply, hsm]
    simp only [Pi.smul_apply, smul_eq_mul, hvω, h1, mul_one, vreal, Ureal]
  have hRep (s : ℝ) : ⇑(j s + g s) =ᵐ[P] greal s := by
    filter_upwards [Lp.coeFn_add (β s • one) ((-κ) • v s), Lp.coeFn_smul (β s) one,
      Lp.coeFn_smul (-κ) (v s), hvRep s, hone] with ω ha hjω hgω hvω h1
    change (β s • one+(-κ) • v s) ω = _
    rw [ha, Pi.add_apply, hjω, hgω]
    simp only [Pi.smul_apply, smul_eq_mul, h1, mul_one, hvω, greal, Ureal, neg_mul, sub_eq_add_neg]
  have hu' : Icc 0 (u:ℝ) ⊆ Icc 0 (T:ℝ) := Icc_subset_Icc_right (NNReal.coe_le_coe.mpr hu)
  have hki := fractionalL_reflected_integrableOn_Ioc hα' u.prop
  have hvi := pulse_weighted_reflected_integrableOn (fractionalL_measurable α) hki hvm' (hvc'.mono hu')
  have hk : Measurable k := (fractionalL_measurable α).comp (measurable_const.sub measurable_id)
  have hVL := coeFn_integral_weighted_L2_path_ae hk hvreal hvi hvr
  have hgI : IntegrableOn (fun s => j s+g s) (Ioc 0 (u:ℝ)) :=
    (hjI u).add ((intervalIntegrable_iff_integrableOn_Ioc_of_le u.prop).1
      ((hgc.mono hu').intervalIntegrable_of_Icc u.prop))
  have hGL := coeFn_integral_weighted_L2_path_ae (measurable_const (a := (1:ℝ))) hgreal
    (show IntegrableOn (fun s => (1:ℝ) • (j s+g s)) (Ioc 0 (u:ℝ)) from by simpa only [one_smul] using hgI)
    hRep
  let G := ∫ s in Ioc (0:ℝ) (u:ℝ), j s+g s
  change volterraSmulConvolution (fractionalL α) v' (u:ℝ) = G+σ • I sa
  apply Lp.ext
  filter_upwards [hVL, hGL, hMs', hInv u hu, Lp.coeFn_add G (σ • I sa)] with ω hVLω hGLω hMsω hInvω hsum
  change volterraSmulConvolution (fractionalL α) v' (u:ℝ) ω = (G+σ • I sa) ω
  simp only [one_smul, one_mul] at hGLω
  rw [hsum, Pi.add_apply, ← hMsω, hGLω, ← hInvω]
  exact hVLω

#print axioms RoughHeston.GirsanovPort.aggregate_samplewise_forward_centered_L2

end RoughHeston.GirsanovPort
