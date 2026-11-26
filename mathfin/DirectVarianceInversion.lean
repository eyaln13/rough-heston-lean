import BanachHestonInversion
import VarianceSolutionOfIto

open MeasureTheory ProbabilityTheory Filter Set
open scoped MeasureTheory ProbabilityTheory Topology NNReal ENNReal

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  {𝒢 : Filtration ℝ≥0 m} {V B : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

private theorem hestonKernel_reflected_integrableOn_Ioc {α t : ℝ}
    (hα : 0 < α) (ht : 0 ≤ t) :
    IntegrableOn (fun s : ℝ => hestonKernel α (t - s)) (Ioc 0 t) := by
  have hK : hestonKernel α = fractionalK α := by
    funext x
    unfold hestonKernel fractionalK
    by_cases hx : 0 < x
    · simp [hx, not_le.mpr hx]
    · simp [hx, le_of_not_gt hx]
  rw [hK]
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).2
    (fractionalK_integrableOn_Ioc hα t)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).1
    (by simpa only [sub_zero, sub_self] using (hi.comp_sub_left t).symm)

omit [IsFiniteMeasure μ] in
private theorem integrableOn_weighted_L2_path {A : ℝ → Lp ℝ 2 μ} {k : ℝ → ℝ}
    {t : ℝ} (hA : StronglyMeasurable A) (hAc : ContinuousOn A (Icc 0 t))
    (hk : Measurable k) (hki : IntegrableOn k (Ioc 0 t)) :
    IntegrableOn (fun s => k s • A s) (Ioc 0 t) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hAc
  refine (hki.norm.mul_const C).mono' (hk.stronglyMeasurable.smul hA).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hC s ⟨hs.1.le, hs.2⟩) (norm_nonneg _)

/-- From the inverse equation in terminal L², recover the direct sample-path
variance equation with the exact dyadic-cutoff definition of the convolution. -/
theorem isHestonVarianceSolution_of_L2_inverse {α σ v₀ κ θ : ℝ}
    (hα : 1 / 2 < α) (hα' : α < 1) (hT : 0 < T) (hσ : σ ≠ 0)
    (hB₂ : ∀ r, MemLp (B r) 2 μ) (hB : Martingale B 𝒢 μ)
    (hclock : Martingale (fun s ω => B s ω ^ 2 - ((min s T : ℝ≥0) : ℝ)) 𝒢 μ)
    (hVp : IsStronglyPredictable 𝒢 V) (hVa : StronglyAdapted 𝒢 V)
    (hVc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => V t ω) (Icc 0 T))
    (hVnonneg : ∀ s ω, 0 ≤ V s ω) (hVint : ∀ s, Integrable (V s) μ)
    {C : ℝ} (hmean : ∀ s, (∫ ω, V s ω ∂μ) ≤ C)
    {f g : ℝ → Lp ℝ 2 μ}
    (hf : StronglyMeasurable f) (hfc : ContinuousOn f (Icc 0 (T : ℝ)))
    (hg : StronglyMeasurable g) (hgc : ContinuousOn g (Icc 0 (T : ℝ)))
    (hfRep : ∀ s, ⇑(f s) =ᵐ[μ] fun ω => V s.toNNReal ω - v₀)
    (hgRep : ∀ s, ⇑(g s) =ᵐ[μ] fun ω => κ * (θ - V s.toNNReal ω))
    (hInv : ∀ u : ℝ≥0, u ≤ T →
      let ha := sqrt_variance_memLp_joint T hVp hVnonneg hVint hmean
      volterraSmulConvolution (fractionalL α) f (u : ℝ) =
        (∫ s in Ioc (0 : ℝ) (u : ℝ), g s) + σ • jointItoIntegralCLM T hB₂
          (jointAmplitudeSectionLp (a := fun s ω => Real.sqrt (V s ω)) u ha)) :
    IsHestonVarianceSolution μ 𝒢 T α v₀ κ θ σ B V := by
  apply isHestonVarianceSolution_of_fixed_time_equations hσ hVa hVc
    (ae_of_all μ fun ω t _ => hVnonneg t ω)
  intro t ht
  let u : Icc (0 : ℝ≥0) T := ⟨t, zero_le, ht⟩
  let Z := jointItoIntegralCLM T hB₂ (hestonKernelFamilyLp hα hVp hVnonneg hVint hmean u)
  have hZ := isHestonConvolutionAt_jointIto_fixed_horizon u hα hα'.le hB hB₂ hclock hVp hVa
    (hVc.mono fun _ h => h.mono (Icc_subset_Icc le_rfl ht)) hVnonneg hVint hmean
  refine ⟨Z, hZ, ?_⟩
  let D := volterraSmulConvolution (hestonKernel α) g (t : ℝ)
  have hS : fixedHestonConvolutionLp (T := T) hα hB₂ hVp hVnonneg hVint hmean (t : ℝ) = Z := by
    unfold fixedHestonConvolutionLp Z
    congr 2
    apply Subtype.ext
    change min ((t : ℝ).toNNReal) T = t
    simp [min_eq_left ht]
  have he := heston_L2_of_inverse hα hα' hT hB₂ hB hclock hVp hVnonneg hVint hmean
    hf hfc hg hgc hInv (t : ℝ) ⟨t.prop, NNReal.coe_le_coe.mpr ht⟩
  rw [hS] at he
  change f (t : ℝ) = D + σ • Z at he
  have hVsm : StronglyMeasurable[𝒢.predictable] (Function.uncurry V) := hVp
  have hVm := (hVsm.mono 𝒢.predictable_le_prod).measurable.comp
    (continuous_real_toNNReal.measurable.prodMap (measurable_id : Measurable (@id Ω)))
  let k (s : ℝ) := hestonKernel α ((t : ℝ) - s)
  have hk : Measurable k := (hestonKernel_measurable α).comp (measurable_const.sub measurable_id)
  have hi := integrableOn_weighted_L2_path hg (hgc.mono
    (Icc_subset_Icc le_rfl (NNReal.coe_le_coe.mpr ht))) hk
    (hestonKernel_reflected_integrableOn_Ioc (by linarith : 0 < α) t.prop)
  have hDrep : ⇑D =ᵐ[μ] hestonVarianceDrift α κ θ V t := by
    have hrep := coeFn_integral_weighted_L2_path_ae hk
      (measurable_const.mul (measurable_const.sub hVm)) hi hgRep
    filter_upwards [hrep] with ω hω
    exact hω.trans (intervalIntegral.integral_of_le (μ := volume)
      (f := fun s : ℝ => k s * (κ * (θ - V s.toNNReal ω))) (NNReal.coe_nonneg t)).symm
  filter_upwards [hfRep (t : ℝ), hDrep, Lp.coeFn_add D (σ • Z), Lp.coeFn_smul σ Z] with
    ω hfω hdω haω hsω
  have hω := congrArg (fun x : Lp ℝ 2 μ => x ω) he
  rw [haω, Pi.add_apply, hsω, Pi.smul_apply, smul_eq_mul, hdω, hfω, Real.toNNReal_coe] at hω
  linarith

/-- A samplewise inverse variance identity with the recovered amplitude
martingale gives the inverse equation in the common terminal L² space. -/
theorem heston_L2_inverse_of_samplewise {α σ v₀ κ θ : ℝ}
    (hα' : α < 1) (hσ : 0 ≤ σ)
    (hB₂ : ∀ r, MemLp (B r) 2 μ) (hB : Martingale B 𝒢 μ)
    (hclock : Martingale (fun s ω => B s ω ^ 2 - ((min s T : ℝ≥0) : ℝ)) 𝒢 μ)
    (hVp : IsStronglyPredictable 𝒢 V) (hVa : StronglyAdapted 𝒢 V)
    (hVc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => V t ω) (Icc 0 T))
    (hVnonneg : ∀ s ω, 0 ≤ V s ω) (hVint : ∀ s, Integrable (V s) μ)
    {C : ℝ} (hmean : ∀ s, (∫ ω, V s ω ∂μ) ≤ C)
    {f g : ℝ → Lp ℝ 2 μ}
    (hf : StronglyMeasurable f) (hfc : ContinuousOn f (Icc 0 (T : ℝ)))
    (hg : StronglyMeasurable g) (hgc : ContinuousOn g (Icc 0 (T : ℝ)))
    (hfRep : ∀ s, ⇑(f s) =ᵐ[μ] fun ω => V s.toNNReal ω - v₀)
    (hgRep : ∀ s, ⇑(g s) =ᵐ[μ] fun ω => κ * (θ - V s.toNNReal ω))
    {M : ℝ≥0 → Ω → ℝ}
    (hM : HasAmplitudeCutoffIntegral 𝒢 μ T B M (fun s ω => σ * Real.sqrt (V s ω)))
    (hInv : ∀ u : ℝ≥0, u ≤ T →
      (fun ω => ∫ s in Ioc (0 : ℝ) (u : ℝ), fractionalL α ((u : ℝ) - s) *
        (V s.toNNReal ω - v₀)) =ᵐ[μ]
      (fun ω => (∫ s in Ioc (0 : ℝ) (u : ℝ), κ * (θ - V s.toNNReal ω)) + M u ω)) :
    ∀ u : ℝ≥0, u ≤ T →
      let ha := sqrt_variance_memLp_joint T hVp hVnonneg hVint hmean
      volterraSmulConvolution (fractionalL α) f (u : ℝ) =
        (∫ s in Ioc (0 : ℝ) (u : ℝ), g s) + σ • jointItoIntegralCLM T hB₂
          (jointAmplitudeSectionLp (a := fun s ω => Real.sqrt (V s ω)) u ha) := by
  intro u hu
  let a (s : ℝ≥0) (ω : Ω) := Real.sqrt (V s ω)
  let A (s : ℝ≥0) (ω : Ω) := σ * a s ω
  let ha : MemLp (Function.uncurry a) 2 (jointPredictableMeasure 𝒢 μ T) :=
    sqrt_variance_memLp_joint T hVp hVnonneg hVint hmean
  let hA : MemLp (Function.uncurry A) 2 (jointPredictableMeasure 𝒢 μ T) := ha.const_mul σ
  have ha₂ : StronglyAdapted 𝒢 A := fun s =>
    stronglyMeasurable_const.mul (hVa s).measurable.sqrt.stronglyMeasurable
  have hVsm : StronglyMeasurable[𝒢.predictable] (Function.uncurry V) := hVp
  have hAsm : StronglyMeasurable[𝒢.predictable] (Function.uncurry A) :=
    stronglyMeasurable_const.mul hVsm.measurable.sqrt.stronglyMeasurable
  have hAc : ∀ᵐ ω ∂μ, ContinuousOn (fun s => A s ω) (Icc 0 u) :=
    hVc.mono fun ω hω => continuousOn_const.mul (Real.continuous_sqrt.comp_continuousOn
      (hω.mono (Icc_subset_Icc le_rfl hu)))
  have hA₀ (s : ℝ≥0) (ω : Ω) : 0 ≤ A s ω := mul_nonneg hσ (Real.sqrt_nonneg _)
  have hAe := hM.ae_eq_jointIto_fixed_horizon hu hB hB₂ hclock ha₂ hAsm hAc hA₀ hA
  let aStop := jointAmplitudeSectionLp u ha
  let AStop := jointAmplitudeSectionLp u hA
  have heq : AStop = σ • aStop := by
    apply Lp.ext
    filter_upwards [jointAmplitudeSectionLp_ae u hA, jointAmplitudeSectionLp_ae u ha,
      Lp.coeFn_smul σ aStop] with z hAz haz hσz
    change AStop z = (σ • aStop) z
    rw [hσz, Pi.smul_apply, smul_eq_mul, hAz, haz]
    by_cases hz : z ∈ Ioc (0 : ℝ≥0) u ×ˢ (univ : Set Ω)
    · simp [hz, Function.uncurry, A]
    · simp [hz]
  let I := jointItoIntegralCLM (𝒢 := 𝒢) T hB₂
  have hAm : M u =ᵐ[μ] ((σ • I aStop : Lp ℝ 2 μ) : Ω → ℝ) := by
    change M u =ᵐ[μ] (I AStop : Ω → ℝ) at hAe
    rwa [heq, map_smul] at hAe
  have hVmeas := (hVsm.mono 𝒢.predictable_le_prod).measurable.comp
    (continuous_real_toNNReal.measurable.prodMap (measurable_id : Measurable (@id Ω)))
  let k (s : ℝ) := fractionalL α ((u : ℝ) - s)
  have hk : Measurable k := (fractionalL_measurable α).comp (measurable_const.sub measurable_id)
  have hu' : (u : ℝ) ≤ (T : ℝ) := NNReal.coe_le_coe.mpr hu
  have hfi := integrableOn_weighted_L2_path hf (hfc.mono (Icc_subset_Icc le_rfl hu')) hk
    (fractionalL_reflected_integrableOn_Ioc hα' u.prop)
  have hfEq := coeFn_integral_weighted_L2_path_ae hk (hVmeas.sub measurable_const) hfi hfRep
  have hgi := integrableOn_weighted_L2_path hg
    (hgc.mono (Icc_subset_Icc le_rfl hu')) (measurable_const (a := (1 : ℝ)))
    (integrable_const (1 : ℝ))
  have hgEq := coeFn_integral_weighted_L2_path_ae (measurable_const (a := (1 : ℝ)))
    (measurable_const.mul (measurable_const.sub hVmeas)) hgi hgRep
  let G := ∫ s in Ioc (0 : ℝ) (u : ℝ), g s
  change volterraSmulConvolution (fractionalL α) f (u : ℝ) = G + σ • I aStop
  apply Lp.ext
  filter_upwards [hfEq, hgEq, hAm, hInv u hu, Lp.coeFn_add G (σ • I aStop)] with
    ω hfω hgω hMω hInvω hsumω
  change volterraSmulConvolution (fractionalL α) f (u : ℝ) ω = (G + σ • I aStop) ω
  simp only [one_mul, one_smul] at hgω
  rw [hsumω, Pi.add_apply, ← hMω, hgω, ← hInvω]
  exact hfω

end RoughHeston

#print axioms RoughHeston.isHestonVarianceSolution_of_L2_inverse

#print axioms RoughHeston.heston_L2_inverse_of_samplewise
