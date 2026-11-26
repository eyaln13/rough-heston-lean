import ClusterResolventPulseMeans

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Interval

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {B M C U : ℝ≥0 → Ω → ℝ}

private theorem clusterOldMean_measurable (hU : IsStronglyPredictable F U) :
    Measurable (fun s : ℝ => ∫ ω, U s.toNNReal ω ∂P) :=
  (hU.mono F.predictable_le_prod).integral_prod_right'.measurable.comp continuous_real_toNNReal.measurable

theorem cluster_integrable_on_realTime {T : ℝ≥0}
    (hU : IsStronglyPredictable F U) (hU₀ : ∀ s ω, 0 ≤ U s ω)
    (hUi : ∀ s, Integrable (U s) P) {A : ℝ} (hMean : ∀ s, (∫ ω, U s ω ∂P) ≤ A) :
    Integrable (fun p : ℝ × Ω => U p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod P) := by
  let ν := volume.restrict (Ioc (0 : ℝ) (T : ℝ))
  have : IsFiniteMeasure ν := ⟨by simp [ν, Real.volume_Ioc]⟩
  have hUm : Measurable (fun p : ℝ × Ω => U p.1.toNNReal p.2) :=
    (hU.mono F.predictable_le_prod).measurable.comp
      ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)
  refine (integrable_prod_iff (μ := ν) (ν := P) hUm.aestronglyMeasurable).2 ⟨?_, ?_⟩
  · exact ae_of_all _ fun s => hUi s.toNNReal
  · refine (integrable_const A).mono' hUm.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable ?_
    exact ae_of_all _ fun s => by
      simp_rw [Real.norm_of_nonneg (hU₀ _ _)]
      rw [Real.norm_of_nonneg (integral_nonneg (hU₀ _))]
      exact hMean _

/-- The covariance weight and bracket density against the actual old
cluster mean are integrable on the observation interval. -/
theorem cluster_resolvent_mean_integrable {T : ℝ≥0} {α : ℝ} (hα : 0 < α)
    {R : ℝ → ℝ} (hR : Measurable R)
    (hLoc : ∀ s ∈ Ioc 0 (T : ℝ), |R s| ≤ 2 * fractionalK α s)
    (hU : IsStronglyPredictable F U) (hU₀ : ∀ s ω, 0 ≤ U s ω)
    {A : ℝ} (hMean : ∀ s, (∫ ω, U s ω ∂P) ≤ A) :
    let m (s : ℝ) := ∫ ω, U s.toNNReal ω ∂P
    IntegrableOn m (Ioc (0 : ℝ) (T : ℝ)) ∧
      IntegrableOn (fun s => R ((T : ℝ)-s) * m s) (Ioc (0 : ℝ) (T : ℝ)) := by
  let m (s : ℝ) := ∫ ω, U s.toNNReal ω ∂P
  let ν := volume.restrict (Ioc (0 : ℝ) (T : ℝ))
  have : IsFiniteMeasure ν := ⟨by simp [ν, Real.volume_Ioc]⟩
  have hm : Measurable m := clusterOldMean_measurable hU
  have hm₀ (s : ℝ) : 0 ≤ m s := integral_nonneg (hU₀ _)
  refine ⟨(integrable_const A).mono' hm.aestronglyMeasurable
    (ae_of_all _ fun s => by rw [Real.norm_of_nonneg (hm₀ s)]; exact hMean _), ?_⟩
  have hK : Integrable (fun s => fractionalK α ((T : ℝ)-s)) ν := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mp
    have h := (intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mpr
      (fractionalK_integrableOn_Ioc hα (T : ℝ))
    simpa only [sub_zero, sub_self] using (h.comp_sub_left (T : ℝ)).symm
  refine (hK.const_mul (2*A)).mono' ((hR.comp (measurable_const.sub measurable_id)).mul hm).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae (volume.ae_ne (T : ℝ))] with s hs hne
  have h₀ : 0 < (T : ℝ) - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hne)
  have hK₀ : 0 ≤ fractionalK α ((T : ℝ)-s) := by
    rw [fractionalK, ite_eq_right (not_le_of_gt h₀)]
    exact div_nonneg (Real.rpow_nonneg h₀.le _) (Real.Gamma_pos_of_pos hα).le
  rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (hm₀ s)]
  exact (mul_le_mul (hLoc _ ⟨h₀, sub_le_self _ hs.1.le⟩) (hMean _)
    (hm₀ s) (mul_nonneg (by norm_num) hK₀)).trans_eq (by ring)

/-- Exact old and size-biased means of the actual rectangular-pulse
cluster and its focal martingale, expressed in real time. -/
theorem rectangularPulse_sizeBiased_realTime_means
    {T : ℝ≥0} {α κ σ ε d : ℝ} (hα : 1/2 < α) (hα' : α ≤ 1) (hT : 0 < T)
    (hB₂ : ∀ r, MemLp (B r) 2 P) (hB : Martingale B F P)
    (hBclock : Martingale (fun r ω => B r ω ^ 2 - ((min r T : ℝ≥0) : ℝ)) F P)
    (hU : IsStronglyPredictable F U) (hU₀ : ∀ s ω, 0 ≤ U s ω)
    (hUi : ∀ s, Integrable (U s) P) {A : ℝ} (hMean : ∀ s, (∫ ω, U s ω ∂P) ≤ A)
    (hLoc : ∀ s ∈ Ioc 0 (T : ℝ), |fractionalSecondKindResolvent α κ s| ≤
      2 * fractionalK α s)
    (v : ℝ → Lp ℝ 2 P) (hvM : StronglyMeasurable v) (hvC : ContinuousOn v (Icc 0 (T : ℝ)))
    (hvU : ⇑(v (T : ℝ)) =ᵐ[P] U T)
    (hEq : ∀ s ∈ Icc 0 (T : ℝ), v s =
      volterraSmulConvolution (fractionalK α)
        (fun u => clusterDeterministicInputLp P (rectangularPulseRate ε d) u - κ • v u) s +
        σ • fixedHestonConvolutionLp (T := T) hα hB₂ hU hU₀ hUi hMean s)
    (hM : Martingale M F P) (hC : Martingale (fun t => M t * M t - C t) F P)
    (hM₂ : MemLp (M T) 2 P) (hM₀ : M 0 =ᵐ[P] 0) (hC₀ : C 0 =ᵐ[P] 0)
    (hCeq : C T =ᵐ[P] fun ω => ∫ s in (0 : ℝ)..(T : ℝ), σ ^ 2 * U s.toNNReal ω)
    (g : Lp ℝ 2 (jointPredictableMeasure F P T))
    (hg : ⇑g =ᵐ[jointPredictableMeasure F P T] fun p => σ * Real.sqrt (U p.1 p.2))
    (hMt : M T =ᵐ[P] jointItoIntegralCLM T hB₂ g)
    (hε : 0 < ε) (hZ : ∀ᵐ ω ∂P, 0 ≤ ε + M T ω) :
    let R := fractionalSecondKindResolvent α κ
    let m (s : ℝ) := ∫ ω, U s.toNNReal ω ∂P
    let Z (ω : Ω) := ε + M T ω
    let Q := sizeBiasedLaw P Z ε
    IsProbabilityMeasure Q ∧
      m (T : ℝ) = volterraConvolution R (rectangularPulseRate ε d) (T : ℝ) ∧
      (∫ ω, U T ω ∂Q) = m (T : ℝ) + (σ ^ 2 / ε) *
        ∫ s in Ioc (0 : ℝ) (T : ℝ), R ((T : ℝ)-s) * m s ∧
      (∫ ω, Z ω ∂Q) = ε + (σ ^ 2 / ε) *
        ∫ s in Ioc (0 : ℝ) (T : ℝ), m s := by
  let R := fractionalSecondKindResolvent α κ
  let m (s : ℝ) := ∫ ω, U s.toNNReal ω ∂P
  let u := volterraConvolution R (rectangularPulseRate ε d) (T : ℝ)
  let Z (ω : Ω) := ε + M T ω
  let Q := sizeBiasedLaw P Z ε
  obtain ⟨f, hf, hUt, hOldMean⟩ := rectangularPulse_resolvent_equation_and_mean hα hα' hT
    hB₂ hB hBclock hU hU₀ hUi hMean hLoc v hvM hvC hvU hEq
  have hmT : m (T : ℝ) = u := by simpa only [m, Real.toNNReal_coe] using hOldMean
  have hR : Measurable R := fractionalSecondKindResolvent_measurable α κ
  obtain ⟨hQ, -, hQMean, hQZ⟩ := clusterResolvent_sizeBiased_mean
    hM hC hM₂ hM₀ hC₀ hB₂ hB hBclock hU hU₀ hR f g hf hg hMt hUt hε hZ
  refine ⟨hQ, hmT, ?_, ?_⟩
  · rw [hQMean, cluster_covariance_integral_realTime hR hU]
    change u + _ = m (T : ℝ) + _
    rw [hmT]
  · rw [hQZ, expected_clusterClock_eq hCeq (cluster_integrable_on_realTime hU hU₀ hUi hMean),
      intervalIntegral.integral_of_le T.coe_nonneg]
    ring

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.cluster_integrable_on_realTime
#print axioms RoughHeston.GirsanovPort.cluster_resolvent_mean_integrable
#print axioms RoughHeston.GirsanovPort.rectangularPulse_sizeBiased_realTime_means
