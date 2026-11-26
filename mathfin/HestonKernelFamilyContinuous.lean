import HestonKernelFamilyMeasurable

/-! The energy in a shrinking strip next to the diagonal is uniformly small. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped MeasureTheory ProbabilityTheory NNReal ENNReal Topology

namespace RoughHeston

/-- The squared Heston kernel restricted to positive lags of length at most δ. -/
noncomputable def hestonDiagonalSq (α δ : ℝ) : ℝ → ℝ :=
  (Ioc (0 : ℝ) δ).indicator (fun r => hestonKernel α r ^ 2)

private theorem hestonDiagonalSq_nonneg (α δ r : ℝ) : 0 ≤ hestonDiagonalSq α δ r := by
  by_cases h : r ∈ Ioc (0 : ℝ) δ
  · simp only [hestonDiagonalSq, indicator_of_mem h, sq_nonneg]
  · simp only [hestonDiagonalSq, indicator_of_notMem h, le_rfl]

/-- Reflection sends the strip next to the shifted diagonal to the
initial segment of the untranslated squared kernel. -/
theorem integral_heston_diagonal_sq_horizon {α : ℝ} (hα : 1 / 2 < α)
    {u T : ℝ≥0} (huT : u ≤ T) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫ s : ℝ≥0, hestonDiagonalSq α δ ((u : ℝ) - (s : ℝ)) ∂hestonTimeMeasure T) =
      ∫ r in (0 : ℝ)..min (u : ℝ) δ, hestonKernel α r ^ 2 := by
  let h := hestonDiagonalSq α δ
  have hm : Measurable h := ((hestonKernel_measurable α).pow_const 2).indicator measurableSet_Ioc
  have hu : 0 ≤ (u : ℝ) := NNReal.coe_nonneg u
  have hT : 0 ≤ (T : ℝ) := NNReal.coe_nonneg T
  have huT' : (u : ℝ) ≤ (T : ℝ) := by exact_mod_cast huT
  have hbase : IntervalIntegrable h volume 0 (u : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hu).2
      ((hestonKernel_memLp_two hα u).integrable_sq.indicator measurableSet_Ioc)
  let f (s : ℝ) := h ((u : ℝ) - s)
  have hbefore : IntervalIntegrable f volume 0 (u : ℝ) := by
    simpa only [f, sub_zero, sub_self] using (hbase.comp_sub_left (u : ℝ)).symm
  have hzero (s : ℝ) (hs : (u : ℝ) ≤ s) : f s = 0 := by
    apply indicator_of_notMem
    intro hs'
    exact (not_lt_of_ge (sub_nonpos.mpr hs)) hs'.1
  have hafter : IntervalIntegrable f volume (u : ℝ) (T : ℝ) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le huT').2
    have hz : Integrable (fun _ : ℝ => (0 : ℝ)) (volume.restrict (Ioc (u : ℝ) T)) :=
      integrable_zero _ _ _
    refine hz.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact (hzero s hs.1.le).symm
  have hIA : (∫ s in (u : ℝ)..(T : ℝ), f s) = 0 := by
    apply intervalIntegral.integral_zero_ae
    refine Eventually.of_forall fun s hs => ?_
    rw [uIoc_of_le huT'] at hs
    exact hzero s hs.1.le
  have hm' : Measurable (fun s : ℝ≥0 => h ((u : ℝ) - (s : ℝ))) :=
    hm.comp (measurable_const.sub measurable_subtype_coe)
  calc
    _ = ∫ s in Ioo (0 : ℝ) (T : ℝ), f s := by
      rw [hestonTimeMeasure,
        integral_map_of_stronglyMeasurable continuous_real_toNNReal.measurable hm'.stronglyMeasurable]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      simp only [f, Real.coe_toNNReal s hs.1.le]
    _ = ∫ s in (0 : ℝ)..(T : ℝ), f s := by
      rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc, intervalIntegral.integral_of_le hT]
    _ = ∫ s in (0 : ℝ)..(u : ℝ), f s := by
      rw [← intervalIntegral.integral_add_adjacent_intervals hbefore hafter, hIA, add_zero]
    _ = ∫ r in (0 : ℝ)..(u : ℝ), h r := by
      simpa only [f, sub_self, sub_zero] using
        intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := (u : ℝ)) h (u : ℝ)
    _ = _ := by
      rw [intervalIntegral.integral_of_le hu, intervalIntegral.integral_of_le (le_min hu hδ)]
      unfold h hestonDiagonalSq
      rw [setIntegral_indicator measurableSet_Ioc, Ioc_inter_Ioc, max_self, min_comm]

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℝ≥0 m} {V : ℝ≥0 → Ω → ℝ}

/-- A uniform variance moment bound controls the energy of every
shifted kernel on a strip of width δ. -/
theorem heston_diagonal_energy_le [IsFiniteMeasure μ] {α : ℝ} (hα : 1 / 2 < α)
    {u T : ℝ≥0} (huT : u ≤ T) {δ : ℝ} (hδ : 0 ≤ δ)
    (hVp : IsStronglyPredictable 𝒢 V) (hVnonneg : ∀ s ω, 0 ≤ V s ω)
    (hVint : ∀ s, Integrable (V s) μ) {C : ℝ}
    (hmean : ∀ s, (∫ ω, V s ω ∂μ) ≤ C) :
    (∫ z : ℝ≥0 × Ω, hestonDiagonalSq α δ ((u : ℝ) - z.1) * V z.1 z.2
        ∂jointPredictableMeasure 𝒢 μ T) ≤
      C * (∫ r in (0 : ℝ)..δ, hestonKernel α r ^ 2) := by
  let k (s : ℝ≥0) := hestonKernel α ((u : ℝ) - s)
  let A := {s : ℝ≥0 | (u : ℝ) - (s : ℝ) ∈ Ioc (0 : ℝ) δ}
  have hA : MeasurableSet A := (measurable_const.sub measurable_subtype_coe) measurableSet_Ioc
  let k' := A.indicator k
  have hk' : MemLp k' 2 (hestonTimeMeasure T) :=
    (heston_shifted_kernel_memLp_two_horizon hα huT).indicator hA.nullMeasurableSet
  have hkeq (s : ℝ≥0) : k' s ^ 2 = hestonDiagonalSq α δ ((u : ℝ) - s) := by
    by_cases hs : (u : ℝ) - (s : ℝ) ∈ Ioc (0 : ℝ) δ
    · rw [show k' s = k s from indicator_of_mem (show s ∈ A from hs) k]
      rw [hestonDiagonalSq, indicator_of_mem hs]
    · rw [show k' s = 0 from indicator_of_notMem (show s ∉ A from hs) k]
      rw [hestonDiagonalSq, indicator_of_notMem hs, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  have hVsm : StronglyMeasurable[𝒢.predictable] (Function.uncurry V) := hVp
  have hVprod := (hVsm.mono 𝒢.predictable_le_prod).measurable
  have hprod := memLp_kernel_mul_sqrt_of_uniform_mean hk' hVprod hVnonneg hVint hmean
  let G (z : ℝ≥0 × Ω) := hestonDiagonalSq α δ ((u : ℝ) - z.1) * V z.1 z.2
  have hsm : StronglyMeasurable[𝒢.predictable] G := by
    let : MeasurableSpace (ℝ≥0 × Ω) := 𝒢.predictable
    have hm : Measurable (hestonDiagonalSq α δ) :=
      ((hestonKernel_measurable α).pow_const 2).indicator measurableSet_Ioc
    have ht : Measurable (fun z : ℝ≥0 × Ω => (u : ℝ) - (z.1 : ℝ)) :=
      measurable_const.sub (measurable_subtype_coe.comp (measurable_fst_jointPredictable 𝒢))
    exact ((hm.comp ht).mul hVsm.measurable).stronglyMeasurable
  have hGint : Integrable G ((hestonTimeMeasure T).prod μ) := by
    refine hprod.integrable_sq.congr (Eventually.of_forall fun z => ?_)
    change (k' z.1 * Real.sqrt (V z.1 z.2)) ^ 2 = G z
    rw [mul_pow, Real.sq_sqrt (hVnonneg _ _), hkeq]
  have hdiagInt : Integrable
      (fun s : ℝ≥0 => hestonDiagonalSq α δ ((u : ℝ) - s)) (hestonTimeMeasure T) :=
    hk'.integrable_sq.congr (Eventually.of_forall hkeq)
  let : IsFiniteMeasure (hestonTimeMeasure T) := by unfold hestonTimeMeasure; infer_instance
  have hC : 0 ≤ C := (integral_nonneg (hVnonneg 0)).trans (hmean 0)
  change (∫ z, G z ∂jointPredictableMeasure 𝒢 μ T) ≤ _
  unfold jointPredictableMeasure
  rw [← integral_trim 𝒢.predictable_le_prod hsm, ← hestonTimeMeasure_eq_horizon,
    integral_prod _ hGint]
  have hEq (s : ℝ≥0) : (∫ ω, G (s, ω) ∂μ) =
      hestonDiagonalSq α δ ((u : ℝ) - s) * ∫ ω, V s ω ∂μ := by
    change (∫ ω, hestonDiagonalSq α δ ((u : ℝ) - s) * V s ω ∂μ) = _
    rw [integral_const_mul]
  have hδK : IntervalIntegrable (fun r => hestonKernel α r ^ 2) volume 0 δ := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hδ).2
    change Integrable _ (volume.restrict (Ioc (0 : ℝ) δ))
    simpa only [Real.coe_toNNReal _ hδ] using (hestonKernel_memLp_two hα δ.toNNReal).integrable_sq
  calc
    _ ≤ ∫ s : ℝ≥0, hestonDiagonalSq α δ ((u : ℝ) - s) * C ∂hestonTimeMeasure T :=
      integral_mono hGint.integral_prod_left (hdiagInt.mul_const C)
        (fun s => (hEq s).trans_le (mul_le_mul_of_nonneg_left (hmean s) (hestonDiagonalSq_nonneg ..)))
    _ = C * (∫ r in (0 : ℝ)..min (u : ℝ) δ, hestonKernel α r ^ 2) := by
      rw [integral_mul_const, mul_comm _ C, integral_heston_diagonal_sq_horizon hα huT hδ]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (intervalIntegral.integral_mono_interval le_rfl (le_min (NNReal.coe_nonneg u) hδ)
        (min_le_right _ _) (Eventually.of_forall fun _ => sq_nonneg _)
        hδK) hC


/-- Integrability of the variance on the fixed predictable space. -/
theorem jointVariance_integrable [IsFiniteMeasure μ] (T : ℝ≥0)
    (hVp : IsStronglyPredictable 𝒢 V) (hVnonneg : ∀ s ω, 0 ≤ V s ω)
    (hVint : ∀ s, Integrable (V s) μ) {C : ℝ}
    (hmean : ∀ s, (∫ ω, V s ω ∂μ) ≤ C) :
    Integrable (Function.uncurry V) (jointPredictableMeasure 𝒢 μ T) := by
  have hVsm : StronglyMeasurable[𝒢.predictable] (Function.uncurry V) := hVp
  let : IsFiniteMeasure (hestonTimeMeasure T) := by unfold hestonTimeMeasure; infer_instance
  have hk : MemLp (fun _ : ℝ≥0 => (1 : ℝ)) 2 (hestonTimeMeasure T) := memLp_const _
  have h := memLp_kernel_mul_sqrt_of_uniform_mean hk (hVsm.mono 𝒢.predictable_le_prod).measurable
    hVnonneg hVint hmean
  have hi : Integrable (Function.uncurry V) ((hestonTimeMeasure T).prod μ) := by
    refine h.integrable_sq.congr (Eventually.of_forall fun z => ?_)
    change ((1 : ℝ) * Real.sqrt (V z.1 z.2)) ^ 2 = V z.1 z.2
    rw [one_mul, Real.sq_sqrt (hVnonneg _ _)]
  unfold jointPredictableMeasure
  rw [← hestonTimeMeasure_eq_horizon]
  exact hi.trim 𝒢.predictable_le_prod hVsm

/-- The untruncated variance amplitude times a deterministic shifted kernel. -/
noncomputable def shiftedVarianceWeight (k : ℝ → ℝ) (u : ℝ≥0)
    (V : ℝ≥0 → Ω → ℝ) (z : ℝ≥0 × Ω) : ℝ :=
  k ((u : ℝ) - z.1) * Real.sqrt (V z.1 z.2)

private theorem shiftedVarianceWeight_measurable (k : ℝ → ℝ) (hk : Measurable k)
    (u : ℝ≥0) (hVp : IsStronglyPredictable 𝒢 V) :
    StronglyMeasurable[𝒢.predictable] (shiftedVarianceWeight k u V) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := 𝒢.predictable
  have ht : Measurable (fun z : ℝ≥0 × Ω => (u : ℝ) - (z.1 : ℝ)) :=
    measurable_const.sub (measurable_subtype_coe.comp (measurable_fst_jointPredictable 𝒢))
  have hv : StronglyMeasurable (Function.uncurry V) := hVp
  exact ((hk.comp ht).mul hv.measurable.sqrt).stronglyMeasurable

/-- The shifted weight of a bounded kernel is in predictable L². -/
theorem shiftedVarianceWeight_memLp (T : ℝ≥0) (k : ℝ → ℝ) (hk : Measurable k)
    {D : ℝ} (hD : ∀ r, ‖k r‖ ≤ D) (u : ℝ≥0) (hVp : IsStronglyPredictable 𝒢 V)
    (hVnonneg : ∀ s ω, 0 ≤ V s ω)
    (hVi : Integrable (Function.uncurry V) (jointPredictableMeasure 𝒢 μ T)) :
    MemLp (shiftedVarianceWeight k u V) 2 (jointPredictableMeasure 𝒢 μ T) := by
  have hm := shiftedVarianceWeight_measurable k hk u hVp
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2
  refine (hVi.const_mul (D ^ 2)).mono_nonneg (hm.aestronglyMeasurable.pow _)
    (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall fun z => ?_)
  change (k ((u : ℝ) - z.1) * Real.sqrt (V z.1 z.2)) ^ 2 ≤ D ^ 2 * V z.1 z.2
  rw [mul_pow, Real.sq_sqrt (hVnonneg _ _)]
  have hk_sq : k ((u : ℝ) - z.1) ^ 2 ≤ D ^ 2 := by
    rw [← sq_abs (k ((u : ℝ) - z.1))]
    exact pow_le_pow_left₀ (abs_nonneg _)
      (by simpa only [Real.norm_eq_abs] using hD ((u : ℝ) - z.1)) 2
  exact mul_le_mul_of_nonneg_right hk_sq (hVnonneg _ _)

set_option maxHeartbeats 1000000 in
/-- Bounded continuous kernels give continuous sections in fixed
predictable L² without truncating the variance amplitude. -/
theorem continuous_shiftedVarianceWeight_toLp (T : ℝ≥0) (k : ℝ → ℝ) (hk : Continuous k)
    {D : ℝ} (hD : ∀ r, ‖k r‖ ≤ D) (hVp : IsStronglyPredictable 𝒢 V)
    (hVnonneg : ∀ s ω, 0 ≤ V s ω)
    (hVi : Integrable (Function.uncurry V) (jointPredictableMeasure 𝒢 μ T)) :
    Continuous (fun u : ℝ≥0 => (shiftedVarianceWeight_memLp T k hk.measurable hD u hVp
      hVnonneg hVi).toLp (shiftedVarianceWeight k u V)) := by
  let ν := jointPredictableMeasure 𝒢 μ T
  let f (u : ℝ≥0) := shiftedVarianceWeight k u V
  let hF (u : ℝ≥0) : MemLp (f u) 2 ν :=
    shiftedVarianceWeight_memLp T k hk.measurable hD u hVp hVnonneg hVi
  apply continuous_iff_continuousAt.mpr
  intro u
  change Tendsto (fun v => (hF v).toLp (f v)) (𝓝 u) (𝓝 ((hF u).toLp (f u)))
  have hlim_sq : Tendsto (fun v : ℝ≥0 => ∫ z, (f v z - f u z)^2 ∂ν) (𝓝 u) (𝓝 0) := by
    have hdom (v : ℝ≥0) : ∀ᵐ z ∂ν, ‖(f v z - f u z)^2‖ ≤ (D+D)^2 * V z.1 z.2 := by
      filter_upwards with z
      let kv := k ((v : ℝ) - z.1)
      let ku := k ((u : ℝ) - z.1)
      change ‖(kv * Real.sqrt (V z.1 z.2) - ku * Real.sqrt (V z.1 z.2)) ^ 2‖ ≤ _
      rw [← sub_mul, Real.norm_of_nonneg (sq_nonneg _), mul_pow, Real.sq_sqrt (hVnonneg _ _)]
      have hdiff : |kv - ku| ≤ D + D := by
        rw [← Real.norm_eq_abs]
        exact (norm_sub_le _ _).trans (add_le_add (hD _) (hD _))
      rw [← sq_abs (kv - ku)]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hdiff 2) (hVnonneg _ _)
    have hpoint : ∀ᵐ z ∂ν, Tendsto (fun v : ℝ≥0 => (f v z - f u z)^2)
        (𝓝 u) (𝓝 ((0 : ℝ≥0 × Ω → ℝ) z)) := by
      filter_upwards with z
      have hf : Continuous (fun v => f v z) :=
        (hk.comp (continuous_subtype_val.sub continuous_const)).mul continuous_const
      simpa only [sub_self, Pi.zero_apply, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
        ((hf.tendsto u).sub (tendsto_const_nhds (x := f u z))).pow 2
    have hm (v : ℝ≥0) : AEStronglyMeasurable[𝒢.predictable] (fun z => (f v z - f u z)^2) ν :=
      ((hF v).sub (hF u)).aestronglyMeasurable.pow 2
    simpa only [Pi.zero_apply, integral_zero] using tendsto_integral_filter_of_dominated_convergence
      (μ := ν) (fun z => (D+D)^2 * V z.1 z.2)
      (Eventually.of_forall hm) (Eventually.of_forall hdom) (hVi.const_mul _) hpoint
  apply tendsto_iff_dist_tendsto_zero.mpr
  have he (v : ℝ≥0) : Real.sqrt (∫ z, (f v z - f u z)^2 ∂ν) =
      dist ((hF v).toLp (f v)) ((hF u).toLp (f u)) := by
    rw [← dist_toLp_two_sq (hF v) (hF u), Real.sqrt_sq dist_nonneg]
  simpa only [Function.comp_def, he, Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hlim_sq


private noncomputable def taperKernel (α δ r : ℝ) : ℝ :=
  min 1 (max r 0 / δ) * hestonKernel α (max δ r)

private theorem continuous_taperKernel (α : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Continuous (taperKernel α δ) := by
  have hk : Continuous (fun r : ℝ => hestonKernel α (max δ r)) := by
    have hp (r : ℝ) : 0 < max δ r := hδ.trans_le (le_max_left _ _)
    have he : (fun r : ℝ => hestonKernel α (max δ r)) =
        fun r => (max δ r) ^ (α - 1) / Real.Gamma α := by
      funext r
      exact ite_eq_left (hp r)
    rw [he]
    exact ((continuous_const.max continuous_id).rpow_const
      (fun r => Or.inl (hp r).ne')).div_const _
  exact (continuous_const.min ((continuous_id.max continuous_const).div_const δ)).mul hk

private theorem kernel_mono_pos {α a b : ℝ} (hα : 0 < α) (hα' : α ≤ 1)
    (ha : 0 < a) (hab : a ≤ b) : hestonKernel α b ≤ hestonKernel α a := by
  simp only [hestonKernel, ite_eq_left ha, ite_eq_left (ha.trans_le hab)]
  exact div_le_div_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos ha hab (sub_nonpos.mpr hα')) (Real.Gamma_pos_of_pos hα).le

private theorem kernel_nonneg_pos {α r : ℝ} (hα : 0 < α) (hr : 0 < r) :
    0 ≤ hestonKernel α r := by
  rw [hestonKernel, ite_eq_left hr]
  exact div_nonneg (Real.rpow_nonneg hr.le _) (Real.Gamma_pos_of_pos hα).le

private theorem taperKernel_bounds {α δ : ℝ} (hα : 0 < α) (hα' : α ≤ 1)
    (hδ : 0 < δ) (r : ℝ) : 0 ≤ taperKernel α δ r ∧
      taperKernel α δ r ≤ hestonKernel α δ ∧ taperKernel α δ r ≤ hestonKernel α r := by
  have hp := kernel_nonneg_pos hα (hδ.trans_le (le_max_left δ r))
  have h₁ : taperKernel α δ r ≤ hestonKernel α (max δ r) := by
    simpa only [taperKernel, one_mul] using
      mul_le_mul_of_nonneg_right (min_le_left (1 : ℝ) (max r 0 / δ)) hp
  refine ⟨mul_nonneg (le_min zero_le_one (div_nonneg (le_max_right _ _) hδ.le)) hp,
    h₁.trans (kernel_mono_pos hα hα' hδ (le_max_left _ _)), ?_⟩
  by_cases hr : 0 < r
  · exact h₁.trans (kernel_mono_pos hα hα' hr (le_max_right _ _))
  · simp [taperKernel, max_eq_right (not_lt.mp hr), hestonKernel, hr]

private theorem taperKernel_error {α δ : ℝ} (hα : 0 < α) (hα' : α ≤ 1)
    (hδ : 0 < δ) (r : ℝ) :
    (taperKernel α δ r - hestonKernel α r) ^ 2 ≤ hestonDiagonalSq α δ r := by
  by_cases hr : r ∈ Ioc (0 : ℝ) δ
  · obtain ⟨h₀, _, h₁⟩ := taperKernel_bounds hα hα' hδ r
    rw [hestonDiagonalSq, indicator_of_mem hr, ← sq_abs (taperKernel α δ r - hestonKernel α r),
      abs_of_nonpos (sub_nonpos.mpr h₁), neg_sub]
    exact pow_le_pow_left₀ (sub_nonneg.mpr h₁) (sub_le_self _ h₀) 2
  · rw [hestonDiagonalSq, indicator_of_notMem hr]
    by_cases hr₀ : r ≤ 0
    · simp [taperKernel, max_eq_right hr₀, hestonKernel, not_lt.mpr hr₀]
    · have hδr : δ ≤ r := le_of_not_ge fun h => hr ⟨lt_of_not_ge hr₀, h⟩
      have hdiv : 1 ≤ r / δ := (le_div_iff₀ hδ).2 (by simpa only [one_mul] using hδr)
      simp [taperKernel, max_eq_left (lt_of_not_ge hr₀).le, max_eq_right hδr, min_eq_left hdiv]

set_option maxHeartbeats 1000000 in
/-- Continuity of the singular Heston kernel family into the fixed
predictable L² space. The tapered kernel error is supported in a strip
of vanishing width uniformly over the observation time. -/
theorem hestonKernelFamilyLp_continuous [IsFiniteMeasure μ] {α : ℝ} {T : ℝ≥0}
    (hα : 1 / 2 < α) (hα' : α ≤ 1) (hVp : IsStronglyPredictable 𝒢 V)
    (hVnonneg : ∀ s ω, 0 ≤ V s ω) (hVint : ∀ s, Integrable (V s) μ)
    {C : ℝ} (hmean : ∀ s, (∫ ω, V s ω ∂μ) ≤ C) :
    Continuous (hestonKernelFamilyLp (T := T) hα hVp hVnonneg hVint hmean) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := 𝒢.predictable
  let ν := jointPredictableMeasure 𝒢 μ T
  let U := Icc (0 : ℝ≥0) T
  let F := hestonKernelFamilyLp (T := T) hα hVp hVnonneg hVint hmean
  let d (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹
  have hd (n : ℕ) : 0 < d n := by dsimp [d]; positivity
  have hα₀ : 0 < α := by linarith
  let k (n : ℕ) := taperKernel α (d n)
  have hk (n : ℕ) : Continuous (k n) := continuous_taperKernel α (hd n)
  have hb (n : ℕ) (r : ℝ) : ‖k n r‖ ≤ hestonKernel α (d n) := by
    obtain ⟨h₀, h₁, _⟩ := taperKernel_bounds hα₀ hα' (hd n) r
    simpa only [k, Real.norm_of_nonneg h₀] using h₁
  have hVi := jointVariance_integrable T hVp hVnonneg hVint hmean
  let w (n : ℕ) (u : U) := shiftedVarianceWeight (k n) (u : ℝ≥0) V
  let hw (n : ℕ) (u : U) : MemLp (w n u) 2 ν :=
    shiftedVarianceWeight_memLp T (k n) (hk n).measurable (hb n) u hVp hVnonneg hVi
  let G (n : ℕ) (u : U) := (hw n u).toLp (w n u)
  have hG (n : ℕ) : Continuous (G n) :=
    (continuous_shiftedVarianceWeight_toLp T (k n) (hk n) (hb n) hVp hVnonneg hVi).comp
      continuous_subtype_val
  have hbound (n : ℕ) (u : U) :
      dist (G n u) (F u) ^ 2 ≤ C * (∫ r in (0 : ℝ)..d n, hestonKernel α r ^ 2) := by
    let f := Function.uncurry (hestonConvolutionWeight α u V)
    have hf : MemLp f 2 ν :=
      heston_convolution_weight_memLp_two_joint_horizon hα u.property.2 hVp hVnonneg hVint hmean
    let A := {z : ℝ≥0 × Ω | (u : ℝ) - (z.1 : ℝ) ∈ Ioc (0 : ℝ) (d n)}
    have ht : Measurable (fun z : ℝ≥0 × Ω => (u : ℝ) - (z.1 : ℝ)) :=
      measurable_const.sub (measurable_subtype_coe.comp (measurable_fst_jointPredictable 𝒢))
    have hA : MeasurableSet A := ht measurableSet_Ioc
    let B (z : ℝ≥0 × Ω) := hestonDiagonalSq α (d n) ((u : ℝ) - z.1) * V z.1 z.2
    have hB : Integrable B ν := by
      refine (hf.integrable_sq.indicator hA).congr (Eventually.of_forall fun z => ?_)
      by_cases hz : (u : ℝ) - (z.1 : ℝ) ∈ Ioc (0 : ℝ) (d n)
      · rw [indicator_of_mem (show z ∈ A from hz)]
        change (hestonKernel α ((u : ℝ) - z.1) * Real.sqrt (V z.1 z.2)) ^ 2 =
          hestonDiagonalSq α (d n) ((u : ℝ) - z.1) * V z.1 z.2
        rw [mul_pow, Real.sq_sqrt (hVnonneg _ _), hestonDiagonalSq, indicator_of_mem hz]
      · rw [indicator_of_notMem (show z ∉ A from hz)]
        simp only [B, hestonDiagonalSq, indicator_of_notMem hz, zero_mul]
    change dist ((hw n u).toLp (w n u)) (hf.toLp f) ^ 2 ≤ _
    rw [dist_toLp_two_sq]
    refine (integral_mono ((hw n u).sub hf).integrable_sq hB (fun z => ?_)).trans
      (heston_diagonal_energy_le hα u.property.2 (hd n).le hVp hVnonneg hVint hmean)
    change (k n ((u : ℝ) - z.1) * Real.sqrt (V z.1 z.2) -
      hestonKernel α ((u : ℝ) - z.1) * Real.sqrt (V z.1 z.2)) ^ 2 ≤ B z
    rw [← sub_mul, mul_pow, Real.sq_sqrt (hVnonneg _ _)]
    exact mul_le_mul_of_nonneg_right (taperKernel_error hα₀ hα' (hd n) _) (hVnonneg _ _)
  have hdlim : Tendsto d atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_mono (fun (n : ℕ) => le_add_of_nonneg_right zero_le_one)
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  have hdn (n : ℕ) : d n ≤ 1 := by
    change ((n : ℝ) + 1)⁻¹ ≤ 1
    exact (inv_le_one₀ (by positivity : 0 < (n : ℝ) + 1)).2
      (le_add_of_nonneg_left (Nat.cast_nonneg n))
  have hi : IntervalIntegrable (fun r => hestonKernel α r ^ 2) volume (0 : ℝ) 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
    change Integrable _ (volume.restrict (Ioc (0 : ℝ) 1))
    simpa only [NNReal.coe_one] using (hestonKernel_memLp_two hα 1).integrable_sq
  have hc := intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc
  have hdw : Tendsto d atTop (𝓝[uIcc (0 : ℝ) 1] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hdlim, Eventually.of_forall fun n => by
      rw [uIcc_of_le zero_le_one]
      exact ⟨(hd n).le, hdn n⟩⟩
  have hprim : Tendsto (fun b : ℝ => ∫ r in (0 : ℝ)..b, hestonKernel α r ^ 2)
      (𝓝[uIcc (0 : ℝ) 1] 0) (𝓝 ((∫ r in (0 : ℝ)..(0 : ℝ), hestonKernel α r ^ 2))) :=
    hc _ left_mem_uIcc
  have hsmall : Tendsto (fun n => C * (∫ r in (0 : ℝ)..d n, hestonKernel α r ^ 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, intervalIntegral.integral_same, mul_zero] using
      (tendsto_const_nhds (x := C)).mul (hprim.comp hdw)
  have hU : TendstoUniformly G F atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [hsmall.eventually_lt_const (sq_pos_of_pos hε)] with n hn u
    rw [dist_comm]
    nlinarith [hbound n u, dist_nonneg (x := G n u) (y := F u)]
  exact hU.continuous (Eventually.of_forall hG).frequently

end RoughHeston

#print axioms RoughHeston.integral_heston_diagonal_sq_horizon
#print axioms RoughHeston.heston_diagonal_energy_le
#print axioms RoughHeston.jointVariance_integrable
#print axioms RoughHeston.continuous_shiftedVarianceWeight_toLp
#print axioms RoughHeston.hestonKernelFamilyLp_continuous
