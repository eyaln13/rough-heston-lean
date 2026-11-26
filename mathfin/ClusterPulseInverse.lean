import ClusterResolventPulseMeans
import DirectVarianceInversion
import FractionalKernelIncrements

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Interval

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {B U : ℝ≥0 → Ω → ℝ}

private theorem pulse_integral_profile {α ε d t : ℝ} (hα : 0 < α) (hε : 0 ≤ ε) (hd : 0 < d) :
    volterraConvolution (fractionalK α) (rectangularPulseRate ε d) t =
      (ε/d) * ((max t 0)^α / (Real.Gamma α * α) - (max (t-d) 0)^α / (Real.Gamma α * α)) := by
  by_cases ht : 0 ≤ t
  · let a := t - min d t
    have ha : 0 ≤ a := sub_nonneg.mpr (min_le_right _ _)
    have haMax : a = max (t-d) 0 := by
      dsimp [a]
      rcases le_total d t with h | h
      · rw [min_eq_left h, max_eq_left (sub_nonneg.mpr h)]
      · rw [min_eq_right h, sub_self, max_eq_right (sub_nonpos.mpr h)]
    have hi (u : ℝ) (hu : 0 ≤ u) : IntervalIntegrable (fractionalK α) volume 0 u :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hu).2 (fractionalK_integrableOn_Ioc hα _)
    have hk : fractionalK α = hestonKernel α := by
      funext u
      by_cases hu : 0 < u <;> simp [fractionalK, hestonKernel, hu, le_of_not_gt]
    rw [← rectangularPulseMeasure_integral_eq_convolution hε hd, rectangularPulseMeasure,
      integral_smul_measure, ENNReal.toReal_ofReal (div_nonneg hε hd.le), smul_eq_mul,
      ← intervalIntegral.integral_of_le (le_min hd.le ht), intervalIntegral.integral_comp_sub_left,
      sub_zero, ← show a = t - min d t from rfl,
      ← intervalIntegral.integral_interval_sub_left (hi t ht) (hi a ha),
      hk, hestonKernel_integral hα ht, hestonKernel_integral hα ha, max_eq_left ht, haMax]
  · have ht' : t ≤ 0 := le_of_not_ge ht
    rw [volterraConvolution, Ioc_eq_empty_of_le ht', setIntegral_empty, max_eq_right ht',
      max_eq_right (by linarith : t-d ≤ 0), sub_self, mul_zero]

theorem pulse_fractional_convolution_continuous {α ε d : ℝ}
    (hα : 0 < α) (hε : 0 ≤ ε) (hd : 0 < d) :
    Continuous (volterraConvolution (fractionalK α) (rectangularPulseRate ε d)) := by
  rw [show volterraConvolution (fractionalK α) (rectangularPulseRate ε d) =
    (fun t => (ε/d) * ((max t 0)^α / (Real.Gamma α * α) -
      (max (t-d) 0)^α / (Real.Gamma α * α))) from
    funext fun _ => pulse_integral_profile hα hε hd]
  have hpow : Continuous (fun u : ℝ => u ^ α) := Real.continuous_rpow_const hα.le
  exact continuous_const.mul
    (((hpow.comp (continuous_id.max continuous_const)).div_const _).sub
      ((hpow.comp ((continuous_id.sub continuous_const).max continuous_const)).div_const _))

private theorem pulse_Lp_convolution_eq {α ε d t : ℝ} :
    volterraSmulConvolution (fractionalK α)
      (clusterDeterministicInputLp P (rectangularPulseRate ε d)) t =
      clusterDeterministicInputLp P
        (volterraConvolution (fractionalK α) (rectangularPulseRate ε d)) t := by
  unfold volterraSmulConvolution clusterDeterministicInputLp volterraConvolution
  simp_rw [smul_smul]
  exact integral_smul_const _ _

private theorem pulse_Lp_input_measurable {ε d : ℝ} :
    StronglyMeasurable (clusterDeterministicInputLp P (rectangularPulseRate ε d)) := by
  have hj : Measurable (rectangularPulseRate ε d) := measurable_const.indicator measurableSet_Ioc
  exact hj.stronglyMeasurable.smul stronglyMeasurable_const

theorem pulse_Lp_input_integrable {ε d t : ℝ} :
    IntegrableOn (clusterDeterministicInputLp P (rectangularPulseRate ε d)) (Ioc 0 t) := by
  let ν := volume.restrict (Ioc (0 : ℝ) t)
  have : IsFiniteMeasure ν := ⟨by simp [ν, Real.volume_Ioc]⟩
  let one : Lp ℝ 2 P := (memLp_const (1 : ℝ)).toLp (fun _ => 1)
  refine (integrable_const (|ε/d| * ‖one‖)).mono'
    (pulse_Lp_input_measurable (P := P)).aestronglyMeasurable ?_
  exact ae_of_all _ fun s => by
    change ‖rectangularPulseRate ε d s • one‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    by_cases h : s ∈ Ioc (0 : ℝ) d
    · simp [rectangularPulseRate, h]
    · simp [rectangularPulseRate, h]

omit [IsProbabilityMeasure P] in
theorem pulse_weighted_reflected_integrableOn {k : ℝ → ℝ} {T : ℝ}
    (hk : Measurable k) (hki : IntegrableOn (fun s => k (T-s)) (Ioc 0 T))
    {v : ℝ → Lp ℝ 2 P} (hvM : StronglyMeasurable v) (hvC : ContinuousOn v (Icc 0 T)) :
    IntegrableOn (fun s => k (T-s) • v s) (Ioc 0 T) := by
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hvC
  refine (hki.norm.mul_const D).mono'
    (((hk.comp (measurable_const.sub measurable_id)).stronglyMeasurable).smul hvM).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hD s (Ioc_subset_Icc_self hs)) (norm_nonneg _)

/-- The rectangular input rate is discontinuous. Subtract its explicit
continuous convolution before applying the Banach-valued inverse theorem. -/
theorem rectangularPulse_L2_of_inverse
    {T : ℝ≥0} {α κ σ ε d : ℝ} (hα : 1/2 < α) (hα' : α < 1) (hT : 0 < T)
    (hε : 0 ≤ ε) (hd : 0 < d)
    (hB₂ : ∀ r, MemLp (B r) 2 P) (hB : Martingale B F P)
    (hBclock : Martingale (fun r ω => B r ω ^ 2 - ((min r T : ℝ≥0) : ℝ)) F P)
    (hU : IsStronglyPredictable F U) (hU₀ : ∀ s ω, 0 ≤ U s ω)
    (hUi : ∀ s, Integrable (U s) P) {A : ℝ} (hMean : ∀ s, (∫ ω, U s ω ∂P) ≤ A)
    (v : ℝ → Lp ℝ 2 P) (hvM : StronglyMeasurable v) (hvC : ContinuousOn v (Icc 0 (T : ℝ)))
    (hInv : ∀ u : ℝ≥0, u ≤ T →
      let ha := sqrt_variance_memLp_joint T hU hU₀ hUi hMean
      volterraSmulConvolution (fractionalL α) v (u : ℝ) =
        (∫ s in Ioc (0 : ℝ) (u : ℝ),
          clusterDeterministicInputLp P (rectangularPulseRate ε d) s - κ • v s) +
        σ • jointItoIntegralCLM T hB₂ (jointAmplitudeSectionLp (a := fun s ω => Real.sqrt (U s ω)) u ha)) :
    ∀ s ∈ Icc 0 (T : ℝ), v s =
      volterraSmulConvolution (fractionalK α)
        (fun u => clusterDeterministicInputLp P (rectangularPulseRate ε d) u - κ • v u) s +
        σ • fixedHestonConvolutionLp (T := T) hα hB₂ hU hU₀ hUi hMean s := by
  let j := clusterDeterministicInputLp P (rectangularPulseRate ε d)
  let D := volterraSmulConvolution (fractionalK α) j
  let f := v - D
  let g := (-κ) • v
  let S := fixedHestonConvolutionLp (T := T) hα hB₂ hU hU₀ hUi hMean
  have hαp : 0 < α := by linarith
  have hDc : Continuous D := by
    have hEq (s : ℝ) : D s = clusterDeterministicInputLp P
          (volterraConvolution (fractionalK α) (rectangularPulseRate ε d)) s := pulse_Lp_convolution_eq
    rw [funext hEq]
    exact (pulse_fractional_convolution_continuous hαp hε hd).smul continuous_const
  have hfc : ContinuousOn f (Icc 0 (T : ℝ)) := hvC.sub hDc.continuousOn
  have hfm : StronglyMeasurable f := hvM.sub hDc.stronglyMeasurable
  have hgc : ContinuousOn g (Icc 0 (T : ℝ)) := hvC.const_smul _
  have hgm : StronglyMeasurable g := hvM.const_smul _
  have hInv' (u : ℝ≥0) (hu : u ≤ T) :
      volterraSmulConvolution (fractionalL α) f (u : ℝ) =
        (∫ s in Ioc (0 : ℝ) (u : ℝ), g s) + σ • jointItoIntegralCLM T hB₂
          (jointAmplitudeSectionLp (a := fun s ω => Real.sqrt (U s ω)) u
            (sqrt_variance_memLp_joint T hU hU₀ hUi hMean)) := by
    let ν := volume.restrict (Ioc (0 : ℝ) (u : ℝ))
    have hui : Icc 0 (u : ℝ) ⊆ Icc 0 (T : ℝ) := Icc_subset_Icc_right (NNReal.coe_le_coe.mpr hu)
    have hki := fractionalL_reflected_integrableOn_Ioc hα' u.prop
    have hvk := pulse_weighted_reflected_integrableOn (fractionalL_measurable α) hki hvM (hvC.mono hui)
    have hDk := pulse_weighted_reflected_integrableOn (fractionalL_measurable α) hki hDc.stronglyMeasurable
      hDc.continuousOn
    have hDi : volterraSmulConvolution (fractionalL α) D (u : ℝ) = ∫ s, j s ∂ν :=
      fractional_volterra_smul_inverts_drift hαp hα' pulse_Lp_input_measurable pulse_Lp_input_integrable
    have hgI : IntegrableOn g (Ioc 0 (u : ℝ)) :=
      ((hgc.mono hui).intervalIntegrable_of_Icc u.prop).1
    have hjI : IntegrableOn j (Ioc 0 (u : ℝ)) := pulse_Lp_input_integrable
    have he : (fun s => clusterDeterministicInputLp P (rectangularPulseRate ε d) s - κ • v s) =
        fun s => j s + g s := by funext s; simp [j, g, sub_eq_add_neg, neg_smul]
    have hI := hInv u hu
    dsimp only at hI
    rw [he, integral_add hjI hgI] at hI
    have hdiff : volterraSmulConvolution (fractionalL α) f (u : ℝ) =
        volterraSmulConvolution (fractionalL α) v (u : ℝ) -
          volterraSmulConvolution (fractionalL α) D (u : ℝ) := by
      unfold volterraSmulConvolution
      simp only [f, Pi.sub_apply, smul_sub]
      exact integral_sub hvk hDk
    rw [hdiff, hI, hDi]
    abel
  have hK : hestonKernel α = fractionalK α := by
    funext s
    by_cases hs : 0 < s <;> simp [fractionalK, hestonKernel, hs, le_of_not_gt]
  have h := heston_L2_of_inverse hα hα' hT hB₂ hB hBclock hU hU₀ hUi hMean hfm hfc hgm hgc hInv'
  rw [hK] at h
  intro s hs
  have hki : IntegrableOn (fun r => fractionalK α (s-r)) (Ioc 0 s) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hs.1).1
    have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le hs.1).2
      (fractionalK_integrableOn_Ioc hαp s)
    simpa only [sub_zero, sub_self] using (hi.comp_sub_left s).symm
  have hgj := pulse_weighted_reflected_integrableOn (fractionalK_measurable α) hki hgm
    (hgc.mono (Icc_subset_Icc_right hs.2))
  have hjk : IntegrableOn (fun r => fractionalK α (s-r) • j r) (Ioc 0 s) := by
    let one : Lp ℝ 2 P := (memLp_const (1 : ℝ)).toLp (fun _ => 1)
    refine (hki.norm.mul_const (|ε/d| * ‖one‖)).mono'
      (((fractionalK_measurable α).comp (measurable_const.sub measurable_id)).stronglyMeasurable.smul
        pulse_Lp_input_measurable).aestronglyMeasurable ?_
    exact ae_of_all _ fun r => by
      rw [norm_smul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      change ‖rectangularPulseRate ε d r • one‖ ≤ _
      rw [norm_smul, Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      by_cases hr : r ∈ Ioc (0 : ℝ) d
      · simp [rectangularPulseRate, hr]
      · simp [rectangularPulseRate, hr]
  have heq : volterraSmulConvolution (fractionalK α)
      (fun u => clusterDeterministicInputLp P (rectangularPulseRate ε d) u - κ • v u) s =
        D s + volterraSmulConvolution (fractionalK α) g s := by
    change (∫ r in Ioc (0 : ℝ) s, fractionalK α (s-r) • (j r - κ • v r)) =
      (∫ r in Ioc (0 : ℝ) s, fractionalK α (s-r) • j r) +
        ∫ r in Ioc (0 : ℝ) s, fractionalK α (s-r) • g r
    rw [← integral_add hjk hgj]
    apply integral_congr_ae
    exact ae_of_all _ fun r => by simp [g, sub_eq_add_neg, smul_add]
  have hsEq := h s hs
  change v s - D s = volterraSmulConvolution (fractionalK α) g s + σ • S s at hsEq
  rw [heq]
  rw [sub_eq_iff_eq_add] at hsEq
  exact hsEq.trans (by abel)

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.pulse_fractional_convolution_continuous
#print axioms RoughHeston.GirsanovPort.rectangularPulse_L2_of_inverse

