import BochnerVolterraInversion
import FixedHestonHorizon
import HestonFractionalFubini
import HestonKernelFamilyContinuous

open MeasureTheory ProbabilityTheory Filter Set
open scoped MeasureTheory ProbabilityTheory Topology NNReal ENNReal

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  {𝒢 : Filtration ℝ≥0 m} {V B : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

private def realHorizonPoint (T : ℝ≥0) (u : ℝ) : Icc (0 : ℝ≥0) T :=
  ⟨min u.toNNReal T, zero_le, min_le_right _ _⟩

private theorem continuous_realHorizonPoint (T : ℝ≥0) : Continuous (realHorizonPoint T) :=
  (continuous_real_toNNReal.min continuous_const).subtype_mk _

/-- The forward stochastic convolution as a continuous-time path in terminal `L²`. -/
noncomputable def fixedHestonConvolutionLp {α : ℝ} (hα : 1 / 2 < α)
    (hB₂ : ∀ r, MemLp (B r) 2 μ) (hVp : IsStronglyPredictable 𝒢 V)
    (hVnonneg : ∀ s ω, 0 ≤ V s ω) (hVint : ∀ s, Integrable (V s) μ)
    {C : ℝ} (hmean : ∀ s, (∫ ω, V s ω ∂μ) ≤ C) (u : ℝ) : Lp ℝ 2 μ :=
  jointItoIntegralCLM T hB₂
    (hestonKernelFamilyLp hα hVp hVnonneg hVint hmean (realHorizonPoint T u))

theorem fixedHestonConvolutionLp_continuous {α : ℝ} (hα : 1 / 2 < α) (hα' : α ≤ 1)
    (hB₂ : ∀ r, MemLp (B r) 2 μ) (hVp : IsStronglyPredictable 𝒢 V)
    (hVnonneg : ∀ s ω, 0 ≤ V s ω) (hVint : ∀ s, Integrable (V s) μ)
    {C : ℝ} (hmean : ∀ s, (∫ ω, V s ω ∂μ) ≤ C) :
    Continuous (fixedHestonConvolutionLp (T := T) hα hB₂ hVp hVnonneg hVint hmean) :=
  (jointItoIntegralCLM (𝒢 := 𝒢) T hB₂).continuous.comp
    ((hestonKernelFamilyLp_continuous hα hα' hVp hVnonneg hVint hmean).comp
      (continuous_realHorizonPoint T))

set_option maxHeartbeats 1200000 in
/-- Fractional stochastic Fubini at every observation time, with a
single ambient Itô map on the full horizon. -/
theorem fixedHestonConvolutionLp_fractional_inverse {α : ℝ} (hα : 1 / 2 < α) (hα' : α < 1)
    {u : ℝ≥0} (hu : u ≤ T)
    (hB₂ : ∀ r, MemLp (B r) 2 μ) (hB : Martingale B 𝒢 μ)
    (hclock : Martingale (fun s ω => B s ω ^ 2 - ((min s T : ℝ≥0) : ℝ)) 𝒢 μ)
    (hVp : IsStronglyPredictable 𝒢 V)
    (hVnonneg : ∀ s ω, 0 ≤ V s ω) (hVint : ∀ s, Integrable (V s) μ)
    {C : ℝ} (hmean : ∀ s, (∫ ω, V s ω ∂μ) ≤ C) :
    let ha := sqrt_variance_memLp_joint T hVp hVnonneg hVint hmean
    volterraSmulConvolution (fractionalL α)
      (fixedHestonConvolutionLp (T := T) hα hB₂ hVp hVnonneg hVint hmean) (u : ℝ) =
      jointItoIntegralCLM T hB₂ (jointAmplitudeSectionLp (a := fun s ω => Real.sqrt (V s ω)) u ha) := by
  dsimp only
  let S := fixedHestonConvolutionLp (T := T) hα hB₂ hVp hVnonneg hVint hmean
  let hB₂u (s : ℝ≥0) := hB₂ (min s u)
  let I := jointItoIntegralCLM (𝒢 := 𝒢) T hB₂
  let J := jointItoIntegralCLM (𝒢 := 𝒢) u hB₂u
  let g (z : ℝ≥0 × Ω) := Real.sqrt (V z.1 z.2)
  let hg := sqrt_variance_memLp_joint u hVp hVnonneg hVint hmean
  let hG := sqrt_variance_memLp_joint T hVp hVnonneg hVint hmean
  let p (s : ℝ≥0) : Icc (0 : ℝ≥0) u := ⟨min s u, zero_le, min_le_right _ _⟩
  let φ (s : ℝ≥0) := hestonKernelFamilyLp hα hVp hVnonneg hVint hmean (p s)
  have hfub := heston_fractionalVolterra_fubini hα hα' u hB₂u hVp hVnonneg hVint hmean
  change (∫ s : ℝ≥0, fractionalL α ((u : ℝ) - (s : ℝ)) • J (φ s) ∂hestonTimeMeasure u) =
    J (hg.toLp g) at hfub
  have hJ (s : ℝ≥0) (hs : s ≤ u) : J (φ s) = S (s : ℝ) := by
    let q : Icc (0 : ℝ≥0) T := ⟨s, zero_le, hs.trans hu⟩
    let w := Function.uncurry (hestonConvolutionWeight α s V)
    have hw : MemLp w 2 (jointPredictableMeasure 𝒢 μ u) :=
      heston_convolution_weight_memLp_two_joint_horizon hα hs hVp hVnonneg hVint hmean
    have hp : (p s : ℝ≥0) = s := min_eq_left hs
    have hq : realHorizonPoint T (s : ℝ) = q := by
      apply Subtype.ext
      change min ((s : ℝ).toNNReal) T = s
      simp [min_eq_left (hs.trans hu)]
    have hz : ∀ z : ℝ≥0 × Ω, u < z.1 → w z = 0 := by
      intro z hz
      have hn : ¬ 0 < (s : ℝ) - (z.1 : ℝ) :=
        not_lt.mpr (sub_nonpos.mpr (NNReal.coe_le_coe.mpr (hs.trans hz.le)))
      simp [w, Function.uncurry, hestonConvolutionWeight, hestonKernel, hn]
    have hφ : φ s = hw.toLp w := by
      apply Lp.ext
      exact (((hestonKernelFamilyLp_ae hα hVp hVnonneg hVint hmean (p s)).trans
        (Eventually.of_forall fun z => by rw [hp])).trans hw.coeFn_toLp.symm)
    have he : jointBandExtend 𝒢 μ hu (φ s) =
        hestonKernelFamilyLp hα hVp hVnonneg hVint hmean q := by
      rw [hφ]
      exact Lp.ext ((jointBandExtend_toLp_ae_eq 𝒢 μ hu hz hw).trans
        (hestonKernelFamilyLp_ae hα hVp hVnonneg hVint hmean q).symm)
    change jointItoIntegralCLM u hB₂u (φ s) =
      I (hestonKernelFamilyLp hα hVp hVnonneg hVint hmean (realHorizonPoint T (s : ℝ)))
    rw [jointItoIntegralCLM_cross_horizon 𝒢 μ hu hB₂ hB hclock, hq, he]
  have hA : J (hg.toLp g) = I (jointAmplitudeSectionLp (a := fun s ω => Real.sqrt (V s ω)) u hG) := by
    change jointItoIntegralCLM u hB₂u (hg.toLp g) = I (jointAmplitudeSectionLp (a := fun s ω => Real.sqrt (V s ω)) u hG)
    rw [jointItoIntegralCLM_cross_horizon 𝒢 μ hu hB₂ hB hclock]
    congr 1
    exact Lp.ext ((jointBandExtend_coeFn 𝒢 μ hu (hg.toLp g)).trans
      ((joint_timeBand_indicator_ae_eq 𝒢 μ hu hg.coeFn_toLp).trans
        (jointAmplitudeSectionLp_ae (a := fun s ω => Real.sqrt (V s ω)) u hG).symm))
  have hS : Continuous S := fixedHestonConvolutionLp_continuous hα hα'.le hB₂ hVp hVnonneg hVint hmean
  let L (s : ℝ) := fractionalL α ((u : ℝ) - s)
  have hsm : StronglyMeasurable (fun s : ℝ≥0 => L (s : ℝ) • S (s : ℝ)) :=
    ((fractionalL_measurable α).comp (measurable_const.sub measurable_subtype_coe)).stronglyMeasurable.smul
      (hS.stronglyMeasurable.comp_measurable measurable_subtype_coe)
  calc
    volterraSmulConvolution (fractionalL α) S (u : ℝ) =
        ∫ s : ℝ≥0, L (s : ℝ) • S (s : ℝ) ∂hestonTimeMeasure u := by
      rw [volterraSmulConvolution, hestonTimeMeasure,
        integral_map_of_stronglyMeasurable continuous_real_toNNReal.measurable hsm,
        ← Measure.restrict_congr_set (Ioo_ae_eq_Ioc : Ioo (0 : ℝ) (u : ℝ) =ᵐ[volume] Ioc 0 (u : ℝ))]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      simp only [Real.coe_toNNReal s hs.1.le, L]
    _ = ∫ s : ℝ≥0, L (s : ℝ) • J (φ s) ∂hestonTimeMeasure u := by
      apply integral_congr_ae
      rw [hestonTimeMeasure_eq_horizon, MathFin.ItoIntegralCLM.timeMeasureHorizon]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      rw [hJ s hs.2]
    _ = I (jointAmplitudeSectionLp (a := fun s ω => Real.sqrt (V s ω)) u hG) := hfub.trans hA

section Deterministic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

private def clampRealHorizon (T x : ℝ) : ℝ := max 0 (min x T)

private theorem clampRealHorizon_mem {T : ℝ} (hT : 0 ≤ T) (x : ℝ) :
    clampRealHorizon T x ∈ Icc 0 T :=
  ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

private theorem clampRealHorizon_eq {T x : ℝ} (hx : x ∈ Icc 0 T) : clampRealHorizon T x = x := by
  simp [clampRealHorizon, min_eq_left hx.2, max_eq_right hx.1]

private theorem continuous_clampRealHorizon (T : ℝ) : Continuous (clampRealHorizon T) :=
  continuous_const.max (continuous_id.min continuous_const)

omit [CompleteSpace E] in
/-- Causal convolution by an integrable kernel is continuous on a compact
horizon for a Banach-valued forcing continuous on that horizon. -/
theorem continuousOn_volterra_forcing {k : ℝ → ℝ} {g : ℝ → E} {T : ℝ}
    (hT : 0 ≤ T) (hk : Measurable k) (hki : IntegrableOn k (Ioc 0 T))
    (hg : ContinuousOn g (Icc 0 T)) : ContinuousOn (volterraSmulConvolution k g) (Icc 0 T) := by
  let U := Icc (0 : ℝ) T
  let ge := g ∘ clampRealHorizon T
  have hge : Continuous ge := hg.comp_continuous (continuous_clampRealHorizon T) (clampRealHorizon_mem hT)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hg
  have hC₀ : 0 ≤ C := (norm_nonneg (g 0)).trans (hC 0 ⟨le_rfl, hT⟩)
  let F (t s : ℝ) := if s ≤ t then k s • ge (t - s) else 0
  let ν := volume.restrict (Ioc (0 : ℝ) T)
  have hF (t : ℝ) : StronglyMeasurable (F t) :=
    (hk.stronglyMeasurable.smul (hge.comp (continuous_const.sub continuous_id)).stronglyMeasurable).ite
      measurableSet_Iic stronglyMeasurable_const
  have hcont : Continuous (fun t => ∫ s, F t s ∂ν) := by
    rw [continuous_iff_continuousAt]
    intro t
    refine tendsto_integral_filter_of_dominated_convergence (fun s => ‖k s‖ * C)
      (Eventually.of_forall fun r => (hF r).aestronglyMeasurable)
      (Eventually.of_forall fun r => Eventually.of_forall fun s => ?_) (hki.norm.mul_const C) ?_
    · by_cases h : s ≤ r
      · simp only [F, ite_eq_left h, norm_smul]
        exact mul_le_mul_of_nonneg_left (hC _ (clampRealHorizon_mem hT _)) (norm_nonneg _)
      · simp only [F, ite_eq_right h, norm_zero]
        exact mul_nonneg (norm_nonneg _) hC₀
    · filter_upwards [ν.ae_ne t] with s hs
      rcases lt_or_gt_of_ne hs with hst | hts
      · have htF : F t s = k s • ge (t - s) := ite_eq_left hst.le
        rw [htF]
        have hc : Continuous (fun r : ℝ => k s • ge (r - s)) :=
          (hge.comp (continuous_id.sub continuous_const)).const_smul _
        refine (hc.continuousAt (x := t)).tendsto.congr' ?_
        filter_upwards [eventually_gt_nhds hst] with r hr
        exact (ite_eq_left hr.le).symm
      · have htF : F t s = 0 := ite_eq_right (not_le_of_gt hts)
        rw [htF]
        have hc : Tendsto (fun _ : ℝ => (0 : E)) (𝓝 t) (𝓝 0) := tendsto_const_nhds
        refine hc.congr' ?_
        filter_upwards [Iio_mem_nhds hts] with r hr
        exact (ite_eq_right (not_le_of_gt hr)).symm
  refine hcont.continuousOn.congr ?_
  intro t ht
  have ht₀ : 0 ≤ t := ht.1
  have hG (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) t) : F t s = k s • g (t - s) := by
    have hm : t - s ∈ U := ⟨sub_nonneg.mpr hs.2, (sub_le_self _ hs.1.le).trans ht.2⟩
    simp only [F, ite_eq_left hs.2, ge, Function.comp_apply, clampRealHorizon_eq hm]
  have hsub : Ioc (0 : ℝ) t ⊆ Ioc 0 T := Ioc_subset_Ioc_right ht.2
  have hzero (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) T \ Ioc 0 t) : F t s = 0 := by
    exact ite_eq_right (fun h => hs.2 ⟨hs.1.1, h⟩)
  calc
    volterraSmulConvolution k g t = ∫ s in Ioc (0 : ℝ) t, k s • g (t - s) := by
      rw [volterraSmulConvolution, ← intervalIntegral.integral_of_le ht₀,
        ← intervalIntegral.integral_of_le ht₀]
      simpa only [sub_self, sub_zero, sub_sub_cancel] using
        (intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := t)
          (fun s => k s • g (t - s)) t)
    _ = ∫ s in Ioc (0 : ℝ) t, F t s := setIntegral_congr_fun measurableSet_Ioc fun s hs => (hG s hs).symm
    _ = ∫ s, F t s ∂ν := (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc hsub hzero).symm

omit [CompleteSpace E] in
private theorem integrable_fractionalL_smul_path {α t T : ℝ} {g : ℝ → E}
    (hα : α < 1) (ht : t ∈ Icc 0 T) (hg : StronglyMeasurable g) (hgc : ContinuousOn g (Icc 0 T)) :
    IntegrableOn (fun s => fractionalL α (t - s) • g s) (Ioc 0 t) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hgc
  have h := (fractionalL_reflected_integrableOn_Ioc hα ht.1).norm.mul_const C
  refine h.mono' (((fractionalL_measurable α).comp (measurable_const.sub measurable_id)).stronglyMeasurable.smul
        hg).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hC s ⟨hs.1.le, hs.2.trans ht.2⟩) (norm_nonneg _)

/-- A continuous Banach-valued path is identified by its inverse fractional convolution. -/
private theorem fractional_volterra_smul_identification {α T σ : ℝ} {f g S : ℝ → E}
    (hα₀ : 0 < α) (hα₁ : α < 1) (hT : 0 < T)
    (hf : StronglyMeasurable f) (hfc : ContinuousOn f (Icc 0 T))
    (hg : StronglyMeasurable g) (hgc : ContinuousOn g (Icc 0 T))
    (hS : Continuous S)
    (hInv : ∀ t ∈ Icc (0 : ℝ) T,
      volterraSmulConvolution (fractionalL α) f t =
        (∫ s in Ioc (0 : ℝ) t, g s) + σ • volterraSmulConvolution (fractionalL α) S t) :
    ∀ t ∈ Icc (0 : ℝ) T, f t = volterraSmulConvolution (fractionalK α) g t + σ • S t := by
  let D := volterraSmulConvolution (fractionalK α) g
  have hDc : ContinuousOn D (Icc 0 T) :=
    continuousOn_volterra_forcing hT.le (fractionalK_measurable α) (fractionalK_integrableOn_Ioc hα₀ T) hgc
  let G := D ∘ clampRealHorizon T
  have hG : Continuous G := hDc.comp_continuous (continuous_clampRealHorizon T) (clampRealHorizon_mem hT.le)
  have hDG (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) : G u = D u := by
    simp only [G, Function.comp_apply, clampRealHorizon_eq hu]
  let R (u : ℝ) := f u - (G u + σ • S u)
  have hR : StronglyMeasurable R := hf.sub (hG.stronglyMeasurable.add (hS.const_smul σ).stronglyMeasurable)
  have hRc : ContinuousOn R (Icc 0 T) := hfc.sub (hG.add (hS.const_smul σ)).continuousOn
  have h0 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : volterraSmulConvolution (fractionalL α) R t = 0 := by
    let L (s : ℝ) := fractionalL α (t - s)
    let ν := volume.restrict (Ioc (0 : ℝ) t)
    have hfi : Integrable (fun s => L s • f s) ν := integrable_fractionalL_smul_path hα₁ ht hf hfc
    have hGi : Integrable (fun s => L s • G s) ν :=
      integrable_fractionalL_smul_path hα₁ ht hG.stronglyMeasurable hG.continuousOn
    have hSi : Integrable (fun s => L s • (σ • S s)) ν :=
      integrable_fractionalL_smul_path hα₁ ht (hS.const_smul σ).stronglyMeasurable
        (hS.const_smul σ).continuousOn
    have hD : (∫ s, L s • G s ∂ν) = ∫ s in Ioc (0 : ℝ) t, g s := by
      calc
        _ = volterraSmulConvolution (fractionalL α) D t := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro s hs
          change L s • G s = L s • D s
          rw [hDG s ⟨hs.1.le, hs.2.trans ht.2⟩]
        _ = _ := fractional_volterra_smul_inverts_drift hα₀ hα₁ hg
          ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).1
            (ContinuousOn.intervalIntegrable_of_Icc ht.1 (hgc.mono (Icc_subset_Icc le_rfl ht.2))))
    have hσ : (∫ s, L s • (σ • S s) ∂ν) = σ • volterraSmulConvolution (fractionalL α) S t := by
      rw [volterraSmulConvolution, ← integral_smul]
      exact integral_congr_ae (Eventually.of_forall fun s => smul_comm (L s) σ (S s))
    change (∫ s, L s • (f s - (G s + σ • S s)) ∂ν) = 0
    simp only [smul_sub, smul_add]
    have hsum : Integrable (fun s => L s • G s + L s • (σ • S s)) ν := hGi.add hSi
    rw [integral_sub hfi hsum, integral_add hGi hSi, hD, hσ]
    exact sub_eq_zero.mpr (hInv t ht)
  intro t ht
  have hz := fractionalL_smul_zero_implies_path_zero hα₀ hα₁ hT hR hRc h0 t ht
  exact (sub_eq_zero.mp hz).trans (congrArg (fun x => x + σ • S t) (hDG t ht))

end Deterministic

/-- The `L²` inverse identity determines the variance path as the sum of the
forward drift convolution and the fixed-horizon stochastic convolution. -/
theorem heston_L2_of_inverse {α σ : ℝ} (hα : 1 / 2 < α) (hα' : α < 1) (hT : 0 < T)
    (hB₂ : ∀ r, MemLp (B r) 2 μ) (hB : Martingale B 𝒢 μ)
    (hclock : Martingale (fun s ω => B s ω ^ 2 - ((min s T : ℝ≥0) : ℝ)) 𝒢 μ)
    (hVp : IsStronglyPredictable 𝒢 V)
    (hVnonneg : ∀ s ω, 0 ≤ V s ω) (hVint : ∀ s, Integrable (V s) μ)
    {C : ℝ} (hmean : ∀ s, (∫ ω, V s ω ∂μ) ≤ C)
    {f g : ℝ → Lp ℝ 2 μ}
    (hf : StronglyMeasurable f) (hfc : ContinuousOn f (Icc 0 (T : ℝ)))
    (hg : StronglyMeasurable g) (hgc : ContinuousOn g (Icc 0 (T : ℝ)))
    (hInv : ∀ u : ℝ≥0, u ≤ T →
      let ha := sqrt_variance_memLp_joint T hVp hVnonneg hVint hmean
      volterraSmulConvolution (fractionalL α) f (u : ℝ) =
        (∫ s in Ioc (0 : ℝ) (u : ℝ), g s) + σ • jointItoIntegralCLM T hB₂
          (jointAmplitudeSectionLp (a := fun s ω => Real.sqrt (V s ω)) u ha)) :
    ∀ t ∈ Icc (0 : ℝ) (T : ℝ),
      f t = volterraSmulConvolution (hestonKernel α) g t + σ •
        fixedHestonConvolutionLp (T := T) hα hB₂ hVp hVnonneg hVint hmean t := by
  have hK : hestonKernel α = fractionalK α := by
    funext s
    by_cases hs : s ≤ 0
    · simp [hestonKernel, fractionalK, hs, not_lt.mpr hs]
    · simp [hestonKernel, fractionalK, hs, lt_of_not_ge hs]
  rw [hK]
  let S := fixedHestonConvolutionLp (T := T) hα hB₂ hVp hVnonneg hVint hmean
  have hS : Continuous S := fixedHestonConvolutionLp_continuous hα hα'.le hB₂ hVp hVnonneg hVint hmean
  apply fractional_volterra_smul_identification (σ := σ) (by linarith : 0 < α) hα'
    (NNReal.coe_pos.mpr hT) hf hfc hg hgc hS
  intro t ht
  let u : ℝ≥0 := ⟨t, ht.1⟩
  have hu : u ≤ T := NNReal.coe_le_coe.mp ht.2
  have h := hInv u hu
  dsimp only at h
  rw [← fixedHestonConvolutionLp_fractional_inverse hα hα' hu hB₂ hB hclock hVp hVnonneg hVint hmean] at h
  exact h

end RoughHeston

#print axioms RoughHeston.fixedHestonConvolutionLp_continuous
#print axioms RoughHeston.fixedHestonConvolutionLp_fractional_inverse

#print axioms RoughHeston.heston_L2_of_inverse

#print axioms RoughHeston.continuousOn_volterra_forcing
