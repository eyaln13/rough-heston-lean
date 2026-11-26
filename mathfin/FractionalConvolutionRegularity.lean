import RiccatiComparison
import Mathlib.Analysis.Calculus.Deriv.Slope

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RoughHeston

private noncomputable def fractionalKernelDeriv (α u : ℝ) : ℝ :=
  (α - 1) * u ^ (α - 2) / Real.Gamma α

private theorem measurable_fractionalKernelDeriv (α : ℝ) : Measurable (fractionalKernelDeriv α) :=
  ((measurable_id.pow_const _).const_mul _).div_const _

private theorem fractionalKernel_hasDerivAt {α u : ℝ} (hu : 0 < u) :
    HasDerivAt (fractionalK α) (fractionalKernelDeriv α u) u := by
  have hd := (Real.hasDerivAt_rpow_const (x := u) (p := α - 1) (Or.inl hu.ne')).div_const (Real.Gamma α)
  have hh : HasDerivAt (fun x : ℝ => x ^ (α - 1) / Real.Gamma α) (fractionalKernelDeriv α u) u := by
    simpa only [fractionalKernelDeriv, show α - 1 - 1 = α - 2 by ring] using hd
  refine hh.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hu] with x hx
  exact ite_eq_right (not_le.mpr (show 0 < x from hx))

private theorem fractionalKernel_nonneg {α : ℝ} (hα : 0 < α) (u : ℝ) :
    0 ≤ fractionalK α u := by
  unfold fractionalK
  split
  · exact le_rfl
  · rename_i h
    exact div_nonneg (Real.rpow_nonneg (lt_of_not_ge h).le _) (Real.Gamma_pos_of_pos hα).le

private theorem norm_fractionalKernelDeriv {α u : ℝ} (hα : 0 < α) (hα' : α < 1) (hu : 0 < u) :
    ‖fractionalKernelDeriv α u‖ = ((1 - α) / Real.Gamma α) * u ^ (α - 2) := by
  rw [fractionalKernelDeriv, Real.norm_eq_abs, abs_div, abs_mul,
    abs_of_nonpos (sub_nonpos.mpr hα'.le), abs_of_pos (Real.Gamma_pos_of_pos hα),
    abs_of_nonneg (Real.rpow_nonneg hu.le _), neg_sub]
  ring

private theorem fractionalKernel_increment_norm {α u h : ℝ} (hα : 0 < α) (hα' : α < 1)
    (hu : 0 < u) (hh : 0 ≤ h) :
    ‖fractionalK α (u + h) - fractionalK α u‖ ≤
      (((1 - α) / Real.Gamma α) * u ^ (α - 2)) * h := by
  have hC : 0 ≤ (1 - α) / Real.Gamma α := by positivity
  have hb : u ≤ u + h := le_add_of_nonneg_right hh
  have H := norm_image_sub_le_of_norm_deriv_le_segment'
    (f' := fractionalKernelDeriv α)
    (fun v (hv : v ∈ Icc u (u+h)) => (fractionalKernel_hasDerivAt (hu.trans_le hv.1)).hasDerivWithinAt)
    (C := ((1 - α) / Real.Gamma α) * u ^ (α - 2))
    (fun v (hv : v ∈ Ico u (u+h)) => by
      rw [norm_fractionalKernelDeriv hα hα' (hu.trans_le hv.1)]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hu hv.1 (by linarith)) hC)
    (u + h) ⟨hb, le_rfl⟩
  simpa only [add_sub_cancel_left] using H

private theorem fractionalKernel_integral {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, fractionalK α s) = t ^ α / (Real.Gamma α * α) := by
  have he : (∫ s in (0 : ℝ)..t, fractionalK α s) =
      ∫ s in (0 : ℝ)..t, s ^ (α - 1) / Real.Gamma α := by
    rw [intervalIntegral.integral_of_le ht, intervalIntegral.integral_of_le ht]
    exact setIntegral_congr_fun measurableSet_Ioc fun _ hs => ite_eq_right (not_le.mpr hs.1)
  rw [he, intervalIntegral.integral_div, integral_rpow (Or.inl (by linarith)),
    sub_add_cancel, Real.zero_rpow hα.ne', sub_zero, div_div, mul_comm α]

private theorem fractionalKernel_reflected_integrable {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t) :
    IntegrableOn (fun s => fractionalK α (t-s)) (Ioc 0 t) := by
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr
    (fractionalK_integrableOn_Ioc hα t)
  have hr := hi.symm.comp_sub_left t
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp (by
    simpa only [sub_self, sub_zero] using hr)

private theorem fractionalKernel_reflected_mass {α a t : ℝ} (hα : 0 < α) (hat : a ≤ t) :
    (∫ s in Ioc a t, fractionalK α (t-s)) = (t-a) ^ α / (Real.Gamma α * α) := by
  have he := intervalIntegral.integral_comp_sub_left (f := fractionalK α) (a := a) (b := t) t
  rw [sub_self, intervalIntegral.integral_of_le hat] at he
  exact he.trans (fractionalKernel_integral hα (sub_nonneg.mpr hat))

private theorem integrableOn_mul_bounded {k f : ℝ → ℝ} {s : Set ℝ}
    (hs : MeasurableSet s) (hi : IntegrableOn k s)
    (hm : Measurable k) (hfm : Measurable f) {B : ℝ} (hf : ∀ u ∈ s, ‖f u‖ ≤ B) :
    IntegrableOn (fun u => k u * f u) s := by
  refine (hi.norm.mul_const B).mono' (hm.mul hfm).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem hs] with u hu
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hf u hu) (norm_nonneg _)

/-- The continuous derivative formula uses the cancellation (f(s)-f(t))
against the differentiated kernel. -/
noncomputable def fractionalVolterraDerivative (α : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  fractionalK α t * f t +
    ∫ s in Ioc (0 : ℝ) t, fractionalKernelDeriv α (t-s) * (f s - f t)

private theorem fractionalVolterra_old_quotient_limit
    {α γ H t : ℝ} {f : ℝ → ℝ} (hα : 0 < α) (hα' : α < 1)
    (hαγ : 1 < α + γ) (ht : 0 < t)
    (hfm : Measurable f)
    (hholder : ∀ s ∈ Icc 0 t, ‖f s - f t‖ ≤ H * (t-s) ^ γ) :
    Tendsto (fun h : ℝ => ∫ s in Ioc (0 : ℝ) t,
      h⁻¹ * (fractionalK α (t-s+h) - fractionalK α (t-s)) * (f s-f t))
      (𝓝[>] 0) (𝓝 (∫ s in Ioc (0 : ℝ) t, fractionalKernelDeriv α (t-s) * (f s-f t))) := by
  let C := (1-α) / Real.Gamma α
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let B (s : ℝ) := (C*H) * (t-s) ^ (α-2+γ)
  have hpow : -1 < α-2+γ := by linarith
  have hi : IntervalIntegrable (fun u : ℝ => (C*H) * u ^ (α-2+γ)) volume 0 t :=
    (intervalIntegral.intervalIntegrable_rpow' hpow).const_mul _
  have hBI : IntegrableOn B (Ioc 0 t) := by
    have hr := hi.symm.comp_sub_left t
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mp
    simpa only [B, sub_self, sub_zero] using hr
  refine tendsto_integral_filter_of_dominated_convergence B ?_ ?_ hBI ?_
  · refine Eventually.of_forall fun h => ?_
    have hmt : Measurable (fun s : ℝ => t-s) := measurable_const.sub measurable_id
    have hm₀ := (fractionalK_measurable α).comp hmt
    have hm₁ := (fractionalK_measurable α).comp (hmt.add_const h)
    have hmF : Measurable (fun s : ℝ => f s-f t) := hfm.sub measurable_const
    exact (((hm₁.sub hm₀).const_mul h⁻¹).mul hmF).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with h hh
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_mono Measure.restrict_le_self (volume.ae_ne t)]
      with s hs hst
    have hh' : 0 < h := hh
    have hst' : s < t := lt_of_le_of_ne hs.2 hst
    have hu : 0 < t-s := sub_pos.mpr hst'
    have hd := fractionalKernel_increment_norm hα hα' hu hh'.le
    have hx : ‖h⁻¹ * (fractionalK α (t-s+h) - fractionalK α (t-s))‖ ≤ C * (t-s)^(α-2) := by
      rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr hh'.le)]
      calc
        _ ≤ h⁻¹ * ((C * (t-s)^(α-2)) * h) := mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hh'.le)
        _ = _ := by field_simp
    rw [norm_mul]
    calc
      _ ≤ (C*(t-s)^(α-2)) * (H * (t-s)^γ) := mul_le_mul hx
        (hholder s (Ioc_subset_Icc_self hs)) (norm_nonneg _) (by positivity)
      _ = B s := by
        dsimp [B]
        rw [Real.rpow_add hu]
        ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_mono Measure.restrict_le_self (volume.ae_ne t)]
      with s hs hst
    have hu : 0 < t-s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
    have hq := (fractionalKernel_hasDerivAt (α := α) hu).tendsto_slope_zero
    have hl : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) :=
      nhdsWithin_mono _ (fun x hx => (show 0 < x from hx).ne')
    have hq' := (hq.mono_left hl).mul_const (f s-f t)
    simpa only [smul_eq_mul] using hq'

private theorem fractionalVolterra_new_quotient_limit
    {α γ H t T : ℝ} {f : ℝ → ℝ} (hα : 0 < α) (hαγ : 1 < α + γ)
    (hγ : 0 ≤ γ) (ht : 0 ≤ t) (hT : t < T) (hH : 0 ≤ H)
    (hfm : Measurable f)
    (hholder : ∀ s ∈ Icc t T, ‖f s-f t‖ ≤ H * (s-t)^γ) :
    Tendsto (fun h : ℝ => h⁻¹ * ∫ s in Ioc t (t+h),
      fractionalK α (t+h-s) * (f s-f t)) (𝓝[>] 0) (𝓝 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  have hE : 0 < α + γ - 1 := by linarith
  let C := H / (Real.Gamma α * α)
  have hlim : Tendsto (fun h : ℝ => C * h ^ (α + γ - 1)) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun h : ℝ => C * h ^ (α + γ - 1)) 0 :=
      (continuous_const.mul (Real.continuous_rpow_const hE.le)).continuousAt
    simpa only [Real.zero_rpow hE.ne', mul_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (sub_pos.mpr hT))]
    with h hh hsmall
  have hh' : 0 < h := hh
  have hsmall' : h < T-t := hsmall
  have hth : t ≤ t+h := le_add_of_nonneg_right hh'.le
  let k (s : ℝ) := fractionalK α (t+h-s)
  have hki : IntegrableOn k (Ioc t (t+h)) :=
    (fractionalKernel_reflected_integrable hα (ht.trans hth)).mono_set (Ioc_subset_Ioc_left ht)
  have hkm : Measurable k := (fractionalK_measurable α).comp (measurable_const.sub measurable_id)
  have hb (s : ℝ) (hs : s ∈ Ioc t (t+h)) : ‖f s-f t‖ ≤ H * h^γ :=
    (hholder s ⟨hs.1.le, hs.2.trans (by linarith)⟩).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (sub_nonneg.mpr hs.1.le) (by linarith [hs.2]) hγ) hH)
  have hProd := integrableOn_mul_bounded measurableSet_Ioc hki hkm
    (hfm.sub measurable_const) hb
  have hest : ‖∫ s in Ioc t (t+h), k s * (f s-f t)‖ ≤
      (∫ s in Ioc t (t+h), k s) * (H*h^γ) := by
    rw [← integral_mul_const]
    refine (norm_integral_le_integral_norm _).trans
      (setIntegral_mono_on hProd.norm (hki.mul_const _) measurableSet_Ioc ?_)
    intro s hs
    rw [norm_mul, Real.norm_of_nonneg (fractionalKernel_nonneg hα _)]
    exact mul_le_mul_of_nonneg_left (hb s hs) (fractionalKernel_nonneg hα _)
  have hm : (∫ s in Ioc t (t+h), k s) = h^α / (Real.Gamma α * α) := by
    simpa only [k, add_sub_cancel_left] using fractionalKernel_reflected_mass hα hth
  rw [hm] at hest
  rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr hh'.le)]
  refine (mul_le_mul_of_nonneg_left hest (inv_nonneg.mpr hh'.le)).trans_eq ?_
  dsimp [C]
  have hp : h ^ (α + γ - 1) = h^α * h^γ * h⁻¹ := by
    rw [Real.rpow_sub hh', Real.rpow_add hh', Real.rpow_one, div_eq_mul_inv]
  rw [hp]
  ring

private theorem fractionalVolterra_center_eq {α x : ℝ} {f : ℝ → ℝ}
    (hα : 0 < α) (hx : 0 ≤ x) (hf : Measurable f) {B : ℝ}
    (hB : ∀ s ∈ Ioc 0 x, ‖f s‖ ≤ B) (m : ℝ) :
    volterraConvolution (fractionalK α) f x =
      volterraConvolution (fractionalK α) (fun s => f s-m) x +
        m * (x^α / (Real.Gamma α * α)) := by
  let k (s : ℝ) := fractionalK α (x-s)
  have hk : IntegrableOn k (Ioc 0 x) := fractionalKernel_reflected_integrable hα hx
  have hkm : Measurable k := (fractionalK_measurable α).comp (measurable_const.sub measurable_id)
  have hi := integrableOn_mul_bounded measurableSet_Ioc hk hkm hf hB
  unfold volterraConvolution
  change (∫ s in Ioc (0 : ℝ) x, k s * f s) =
    (∫ s in Ioc (0 : ℝ) x, k s * (f s-m)) + m * _
  simp_rw [mul_sub]
  rw [integral_sub hi (hk.mul_const m), integral_mul_const,
    show (∫ s in Ioc (0 : ℝ) x, k s) = x^α / (Real.Gamma α * α) from
      by simpa only [sub_zero] using fractionalKernel_reflected_mass hα hx]
  ring

private theorem fractionalVolterra_increment_split {α t x : ℝ} {f : ℝ → ℝ}
    (hα : 0 < α) (ht : 0 ≤ t) (htx : t ≤ x) (hf : Measurable f) {B : ℝ}
    (hB : ∀ s ∈ Ioc 0 x, ‖f s‖ ≤ B) :
    volterraConvolution (fractionalK α) f x - volterraConvolution (fractionalK α) f t =
      (∫ s in Ioc (0 : ℝ) t, (fractionalK α (x-s) - fractionalK α (t-s)) * f s) +
      ∫ s in Ioc t x, fractionalK α (x-s) * f s := by
  let k₀ (s : ℝ) := fractionalK α (t-s)
  let k₁ (s : ℝ) := fractionalK α (x-s)
  have hkm₀ : Measurable k₀ := (fractionalK_measurable α).comp (measurable_const.sub measurable_id)
  have hkm₁ : Measurable k₁ := (fractionalK_measurable α).comp (measurable_const.sub measurable_id)
  have hi₀ : IntegrableOn k₀ (Ioc 0 t) := fractionalKernel_reflected_integrable hα ht
  have hi₁ : IntegrableOn k₁ (Ioc 0 x) := fractionalKernel_reflected_integrable hα (ht.trans htx)
  have h₀ := integrableOn_mul_bounded measurableSet_Ioc hi₀ hkm₀ hf
    (fun s hs => hB s (Ioc_subset_Ioc_right htx hs))
  have h₁ := integrableOn_mul_bounded measurableSet_Ioc (hi₁.mono_set (Ioc_subset_Ioc_right htx))
    hkm₁ hf (fun s hs => hB s (Ioc_subset_Ioc_right htx hs))
  have h₂ := integrableOn_mul_bounded measurableSet_Ioc (hi₁.mono_set (Ioc_subset_Ioc_left ht))
    hkm₁ hf (fun s hs => hB s (Ioc_subset_Ioc_left ht hs))
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr h₁)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le htx).mpr h₂)
  simp only [intervalIntegral.integral_of_le ht, intervalIntegral.integral_of_le htx,
    intervalIntegral.integral_of_le (ht.trans htx)] at hsplit
  unfold volterraConvolution
  change (∫ s in Ioc (0 : ℝ) x, k₁ s * f s) - (∫ s in Ioc (0 : ℝ) t, k₀ s * f s) =
    (∫ s in Ioc (0 : ℝ) t, (k₁ s - k₀ s) * f s) + ∫ s in Ioc t x, k₁ s * f s
  rw [← hsplit, add_sub_right_comm, ← integral_sub h₁ h₀]
  simp only [sub_mul]

private theorem fractionalKernel_mass_hasDerivAt {α t : ℝ} (hα : 0 < α) (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => x^α / (Real.Gamma α * α)) (fractionalK α t) t := by
  have hh := (Real.hasDerivAt_rpow_const (x := t) (p := α) (Or.inl ht.ne')).div_const
    (Real.Gamma α * α)
  convert hh using 1
  rw [fractionalK, ite_eq_right (not_le.mpr ht)]
  field_simp [(Real.Gamma_pos_of_pos hα).ne', hα.ne']

private theorem tendsto_sub_time_right (t : ℝ) :
    Tendsto (fun x : ℝ => x-t) (𝓝[>]t) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have hc : ContinuousAt (fun x : ℝ => x-t) t := (continuous_id.sub continuous_const).continuousAt
    simpa only [sub_self] using hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>]t ≤ 𝓝 t)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact sub_pos.mpr (show t < x from hx)

/-- Right derivative of the fractional Volterra integral against a
Hölder input, with gain past one derivative when `α + γ > 1`. -/
theorem fractionalVolterra_hasDerivWithinAt_right_of_holder
    {α γ H t T : ℝ} {f : ℝ → ℝ} (hα : 0 < α) (hα' : α < 1)
    (hαγ : 1 < α + γ) (hγ : 0 ≤ γ) (ht : t ∈ Ioo 0 T) (hH : 0 ≤ H)
    (hf : Measurable f) (hfcont : ContinuousOn f (Icc 0 T))
    (hholder : ∀ x ∈ Icc 0 T, ∀ y ∈ Icc 0 T, x ≤ y → ‖f y-f x‖ ≤ H * (y-x)^γ) :
    HasDerivWithinAt (volterraConvolution (fractionalK α) f)
      (fractionalVolterraDerivative α f t) (Ioi t) t := by
  have htT : t ∈ Icc 0 T := ⟨ht.1.le, ht.2.le⟩
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hfcont.norm
  have hBf (s : ℝ) (hs : s ∈ Icc 0 T) : ‖f s‖ ≤ B := hB ⟨s, hs, rfl⟩
  have hOldH (s : ℝ) (hs : s ∈ Icc 0 t) : ‖f s-f t‖ ≤ H * (t-s)^γ := by
    rw [norm_sub_rev]
    exact hholder s ⟨hs.1, hs.2.trans ht.2.le⟩ t htT hs.2
  have hNewH (s : ℝ) (hs : s ∈ Icc t T) : ‖f s-f t‖ ≤ H * (s-t)^γ :=
    hholder t htT s ⟨ht.1.le.trans hs.1, hs.2⟩ hs.1
  have hOld := fractionalVolterra_old_quotient_limit hα hα' hαγ ht.1 hf hOldH
  have hNew := fractionalVolterra_new_quotient_limit hα hαγ hγ ht.1.le ht.2 hH hf hNewH
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) :=
    nhdsWithin_mono _ (fun x hx => (show 0 < x from hx).ne')
  have hConst := ((fractionalKernel_mass_hasDerivAt hα ht.1).tendsto_slope_zero
    |>.mono_left hle).mul_const (f t)
  have Hlim : Tendsto (fun h : ℝ => h⁻¹ *
      (volterraConvolution (fractionalK α) f (t+h) - volterraConvolution (fractionalK α) f t))
      (𝓝[>] 0) (𝓝 (fractionalVolterraDerivative α f t)) := by
    have H0 := (hConst.add hOld).add hNew
    simp only [smul_eq_mul, add_zero] at H0
    apply H0.congr'
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (sub_pos.mpr ht.2))] with h hh hsmall
    have hh' : 0 < h := hh
    have hsmall' : h < T-t := hsmall
    have hth : t ≤ t+h := le_add_of_nonneg_right hh'.le
    have htx : t+h ≤ T := by linarith
    have hB₀ (s : ℝ) (hs : s ∈ Ioc 0 t) : ‖f s‖ ≤ B :=
      hBf s ⟨hs.1.le, hs.2.trans ht.2.le⟩
    have hB₁ (s : ℝ) (hs : s ∈ Ioc 0 (t+h)) : ‖f s‖ ≤ B :=
      hBf s ⟨hs.1.le, hs.2.trans htx⟩
    have hB₃ (s : ℝ) (hs : s ∈ Ioc 0 (t+h)) : ‖f s-f t‖ ≤ B + ‖f t‖ :=
      (norm_sub_le _ _).trans (add_le_add (hB₁ s hs) le_rfl)
    have hsplit := fractionalVolterra_increment_split hα ht.1.le hth
      (f := fun s => f s-f t) (hf.sub measurable_const) hB₃
    rw [fractionalVolterra_center_eq hα (ht.1.le.trans hth) hf hB₁ (f t),
      fractionalVolterra_center_eq hα ht.1.le hf hB₀ (f t),
      add_sub_add_comm, hsplit]
    have hOldE :
        (∫ s in Ioc (0 : ℝ) t, h⁻¹ * (fractionalK α (t-s+h) - fractionalK α (t-s)) * (f s-f t)) =
        ∫ s in Ioc (0 : ℝ) t, h⁻¹ * ((fractionalK α (t+h-s) - fractionalK α (t-s)) * (f s-f t)) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s _
      change h⁻¹ * (fractionalK α (t-s+h) - fractionalK α (t-s)) * (f s-f t) =
        h⁻¹ * ((fractionalK α (t+h-s) - fractionalK α (t-s)) * (f s-f t))
      rw [show t-s+h=t+h-s by ring, mul_assoc]
    rw [hOldE, integral_const_mul]
    ring
  refine (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mpr ?_
  apply (Hlim.comp (tendsto_sub_time_right t)).congr'
  refine Eventually.of_forall fun x => ?_
  simp [slope, smul_eq_mul]

private theorem continuousOn_truncated_integral {T : ℝ} {G : ℝ → ℝ → ℝ} {B : ℝ → ℝ}
    (hm : ∀ x, Measurable (G x)) (hBI : IntegrableOn B (Ioc 0 T))
    (hBn : ∀ u ∈ Ioc 0 T, 0 ≤ B u)
    (hBound : ∀ x ∈ Ioo 0 T, ∀ u ∈ Ioc 0 x, ‖G x u‖ ≤ B u)
    (hCont : ∀ x ∈ Ioo 0 T, ∀ u ∈ Ioo 0 x, ContinuousAt (fun y => G y u) x) :
    ContinuousOn (fun x => ∫ u in Ioc (0 : ℝ) x, G x u) (Ioo 0 T) := by
  let W (x u : ℝ) := (Iic x).indicator (G x) u
  let ν := volume.restrict (Ioc 0 T)
  have heq (x : ℝ) (hx : x ∈ Ioo 0 T) :
      (∫ u in Ioc (0 : ℝ) x, G x u) = ∫ u, W x u ∂ν := by
    unfold W ν
    rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      Iic_inter_Ioc_of_le hx.2.le]
  intro x hx
  have hW : ContinuousAt (fun x => ∫ u, W x u ∂ν) x := by
    refine continuousAt_of_dominated
      (Eventually.of_forall fun y => ((hm y).indicator measurableSet_Iic).aestronglyMeasurable)
      ?_ hBI ?_
    · filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      by_cases hUy : u ∈ Iic y
      · dsimp only [W]
        rw [indicator_of_mem hUy]
        exact hBound y hy u ⟨hu.1, hUy⟩
      · dsimp only [W]
        rw [indicator_of_notMem hUy, norm_zero]
        exact hBn u hu
    · filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_mono Measure.restrict_le_self (volume.ae_ne x)]
        with u hu hne
      rcases lt_or_gt_of_ne hne with h | h
      · apply (hCont x hx u ⟨hu.1, h⟩).congr_of_eventuallyEq
        filter_upwards [Ioi_mem_nhds h] with y hy
        exact indicator_of_mem (show u ∈ Iic y from (show u < y from hy).le) _
      · apply (show ContinuousAt (fun _ : ℝ => (0 : ℝ)) x from continuousAt_const).congr_of_eventuallyEq
        filter_upwards [Iio_mem_nhds h] with y hy
        exact indicator_of_notMem (show u ∉ Iic y from not_le.mpr (show y < u from hy)) _
  apply ContinuousAt.continuousWithinAt
  apply hW.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact heq y hy

private theorem setIntegral_reflect_zero {t : ℝ} (ht : 0 ≤ t) (f : ℝ → ℝ) :
    (∫ s in Ioc (0 : ℝ) t, f (t-s)) = ∫ u in Ioc (0 : ℝ) t, f u := by
  have he := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := t) f t
  simpa only [sub_self, sub_zero, intervalIntegral.integral_of_le ht] using he

private theorem fractionalVolterra_continuousOn_of_continuous_input
    {α T : ℝ} {f : ℝ → ℝ} (hα : 0 < α) (hm : Measurable f)
    (hf : ContinuousOn f (Icc 0 T)) :
    ContinuousOn (volterraConvolution (fractionalK α) f) (Ioo 0 T) := by
  intro t ht
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hf.norm
  have hB₀ : 0 ≤ B := (norm_nonneg (f t)).trans (hB ⟨t, Ioo_subset_Icc_self ht, rfl⟩)
  let G (x u : ℝ) := fractionalK α u * f (x-u)
  have hG : ContinuousOn (fun x => ∫ u in Ioc (0 : ℝ) x, G x u) (Ioo 0 T) := by
    apply continuousOn_truncated_integral (B := fun u => fractionalK α u * B)
    · intro x
      exact (fractionalK_measurable α).mul (hm.comp (measurable_const.sub measurable_id))
    · exact (fractionalK_integrableOn_Ioc hα T).mul_const _
    · exact fun u _ => mul_nonneg (fractionalKernel_nonneg hα u) hB₀
    · intro x hx u hu
      have hxu : x-u ∈ Icc 0 T := ⟨sub_nonneg.mpr hu.2, (sub_le_self x hu.1.le).trans hx.2.le⟩
      dsimp only [G]
      rw [norm_mul, Real.norm_of_nonneg (fractionalKernel_nonneg hα u)]
      exact mul_le_mul_of_nonneg_left (hB ⟨x-u, hxu, rfl⟩) (fractionalKernel_nonneg hα u)
    · intro x hx u hu
      have hu₀ : 0 < x-u := sub_pos.mpr hu.2
      have huT : x-u < T := (sub_lt_self x hu.1).trans hx.2
      have hp : ContinuousAt (fun y : ℝ => y-u) x := (continuous_id.sub continuous_const).continuousAt
      have hf' : ContinuousAt f (x-u) := hf.continuousAt (Icc_mem_nhds hu₀ huT)
      exact continuousAt_const.mul (ContinuousAt.comp' (f := fun y : ℝ => y-u) hf' hp)
  have he (x : ℝ) (hx : x ∈ Ioo 0 T) :
      volterraConvolution (fractionalK α) f x = ∫ u in Ioc (0 : ℝ) x, G x u := by
    have hh := setIntegral_reflect_zero hx.1.le (G x)
    simpa only [volterraConvolution, G, sub_sub_cancel] using hh
  exact (hG t ht).congr (fun x hx => he x hx) (he t ht)

theorem fractionalVolterraDerivative_continuousOn
    {α γ H T : ℝ} {f : ℝ → ℝ} (hα : 0 < α) (hα' : α < 1)
    (hαγ : 1 < α + γ) (hH : 0 ≤ H)
    (hm : Measurable f) (hf : ContinuousOn f (Icc 0 T))
    (hholder : ∀ x ∈ Icc 0 T, ∀ y ∈ Icc 0 T, x ≤ y → ‖f y-f x‖ ≤ H * (y-x)^γ) :
    ContinuousOn (fractionalVolterraDerivative α f) (Ioo 0 T) := by
  let G (x u : ℝ) := fractionalKernelDeriv α u * (f (x-u) - f x)
  let C := ((1-α) / Real.Gamma α) * H
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hG : ContinuousOn (fun x => ∫ u in Ioc (0 : ℝ) x, G x u) (Ioo 0 T) := by
    apply continuousOn_truncated_integral (B := fun u => C * u ^ (α-2+γ))
    · intro x
      exact (measurable_fractionalKernelDeriv α).mul
        ((hm.comp (measurable_const.sub measurable_id)).sub measurable_const)
    · have hp : -1 < α-2+γ := by linarith
      exact ((intervalIntegral.intervalIntegrable_rpow' hp).const_mul C).1
    · exact fun u hu => mul_nonneg hC (Real.rpow_nonneg hu.1.le _)
    · intro x hx u hu
      have hxu : x-u ∈ Icc 0 T := ⟨sub_nonneg.mpr hu.2, (sub_le_self x hu.1.le).trans hx.2.le⟩
      have hh := hholder (x-u) hxu x (Ioo_subset_Icc_self hx) (sub_le_self x hu.1.le)
      rw [sub_sub_cancel, norm_sub_rev] at hh
      dsimp only [G, C]
      rw [norm_mul, norm_fractionalKernelDeriv hα hα' hu.1, Real.rpow_add hu.1]
      have hn : 0 ≤ ((1-α) / Real.Gamma α) * u ^ (α-2) :=
        mul_nonneg (div_nonneg (sub_nonneg.mpr hα'.le) (Real.Gamma_pos_of_pos hα).le)
          (Real.rpow_nonneg hu.1.le _)
      exact (mul_le_mul_of_nonneg_left hh hn).trans_eq (by ring)
    · intro x hx u hu
      have hu₀ : 0 < x-u := sub_pos.mpr hu.2
      have huT : x-u < T := (sub_lt_self x hu.1).trans hx.2
      have hp : ContinuousAt (fun y : ℝ => y-u) x := (continuous_id.sub continuous_const).continuousAt
      have hf' : ContinuousAt f (x-u) := hf.continuousAt (Icc_mem_nhds hu₀ huT)
      have hfc : ContinuousAt f x := hf.continuousAt (Icc_mem_nhds hx.1 hx.2)
      exact continuousAt_const.mul ((ContinuousAt.comp' (f := fun y : ℝ => y-u) hf' hp).sub hfc)
  have hKf : ContinuousOn (fun x => fractionalK α x * f x) (Ioo 0 T) := by
    intro x hx
    exact (((fractionalKernel_hasDerivAt hx.1).continuousAt).mul
      (hf.continuousAt (Icc_mem_nhds hx.1 hx.2))).continuousWithinAt
  apply (hKf.add hG).congr
  intro x hx
  unfold fractionalVolterraDerivative
  have hh := setIntegral_reflect_zero hx.1.le (G x)
  simp only [G, sub_sub_cancel] at hh
  rw [hh]
  rfl

private theorem contDiffOn_one_of_continuous_right_derivative
    {T : ℝ} {F D : ℝ → ℝ}
    (hF : ContinuousOn F (Ioo 0 T)) (hD : ContinuousOn D (Ioo 0 T))
    (hR : ∀ t ∈ Ioo 0 T, HasDerivWithinAt F (D t) (Ioi t) t) :
    ContDiffOn ℝ 1 F (Ioo 0 T) := by
  have hadd (t : ℝ) (ht : t ∈ Ioo 0 T) : HasDerivAt F (D t) t := by
    let a := t / 2
    let b := (t+T) / 2
    have ha : 0 < a := div_pos ht.1 (by norm_num)
    have hat : a < t := by dsimp [a]; linarith [ht.1]
    have htb : t < b := by dsimp [b]; linarith [ht.2]
    have hb : b < T := by dsimp [b]; linarith [ht.2]
    have hInt {x : ℝ} (hx : x ∈ Ioo a b) : IntervalIntegrable D volume a x := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hx.1.le]
      exact hD.mono (fun u hu => ⟨ha.trans_le hu.1, hu.2.trans_lt (hx.2.trans hb)⟩)
    have hFTC (x : ℝ) (hx : x ∈ Ioo a b) : (∫ s in a..x, D s) = F x - F a := by
      refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hx.1.le (hF.mono ?_)
        (fun u hu => hR u ⟨ha.trans hu.1, hu.2.trans (hx.2.trans hb)⟩) (hInt hx)
      intro u hu
      exact ⟨ha.trans_le hu.1, hu.2.trans_lt (hx.2.trans hb)⟩
    have hFTC' := intervalIntegral.integral_hasDerivAt_right (hInt ⟨hat, htb⟩)
      (hD.stronglyMeasurableAtFilter isOpen_Ioo t ht) (hD.continuousAt (Ioo_mem_nhds ht.1 ht.2))
    apply (hFTC'.const_add (F a)).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hat htb] with x hx
    rw [hFTC x hx, add_sub_cancel]
  refine (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Ioo _ _)).mpr ⟨?_, ?_⟩
  · exact fun t ht => (hadd t ht).differentiableAt.differentiableWithinAt
  · exact hD.congr (fun t ht => (hadd t ht).hasDerivWithinAt.derivWithin (uniqueDiffOn_Ioo _ _ t ht))

/-- On the interior of a finite horizon, convolution with the fractional
kernel maps a Hölder input into C¹ when the two exponents add to more than one. -/
theorem fractionalVolterra_contDiffOn_of_holder
    {α γ H T : ℝ} {f : ℝ → ℝ} (hα : 0 < α) (hα' : α < 1)
    (hαγ : 1 < α + γ) (hγ : 0 ≤ γ) (hH : 0 ≤ H)
    (hm : Measurable f) (hf : ContinuousOn f (Icc 0 T))
    (hholder : ∀ x ∈ Icc 0 T, ∀ y ∈ Icc 0 T, x ≤ y → ‖f y-f x‖ ≤ H * (y-x)^γ) :
    ContDiffOn ℝ 1 (volterraConvolution (fractionalK α) f) (Ioo 0 T) :=
  contDiffOn_one_of_continuous_right_derivative
    (fractionalVolterra_continuousOn_of_continuous_input hα hm hf)
    (fractionalVolterraDerivative_continuousOn hα hα' hαγ hH hm hf hholder)
    (fun _ ht => fractionalVolterra_hasDerivWithinAt_right_of_holder hα hα' hαγ hγ ht hH hm hf hholder)

private theorem fractionalKernel_mono_positive {α d u : ℝ} (hα : 0 < α) (hα' : α < 1)
    (hd : 0 < d) (hdu : d ≤ u) : fractionalK α u ≤ fractionalK α d := by
  simp only [fractionalK, ite_eq_right (not_le.mpr hd), ite_eq_right (not_le.mpr (hd.trans_le hdu))]
  exact div_le_div_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos hd hdu (by linarith)) (Real.Gamma_pos_of_pos hα).le

private theorem fractionalKernel_history_integrable {α a t : ℝ} {f : ℝ → ℝ}
    (hα : 0 < α) (hα' : α < 1) (hat : a<t)
    (hm : Measurable f) (hi : IntegrableOn f (Ioc 0 a)) :
    IntegrableOn (fun s => fractionalK α (t-s) * f s) (Ioc 0 a) := by
  have hMeas : Measurable (fun s => fractionalK α (t-s) * f s) :=
    ((fractionalK_measurable α).comp (measurable_const.sub measurable_id)).mul hm
  refine (hi.norm.const_mul (fractionalK α (t-a))).mono' hMeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [norm_mul, Real.norm_of_nonneg (fractionalKernel_nonneg hα _)]
  exact mul_le_mul_of_nonneg_right
    (fractionalKernel_mono_positive hα hα' (sub_pos.mpr hat) (sub_le_sub_left hs.2 t))
    (norm_nonneg _)

private theorem contDiffOn_fractionalVolterra_old_history {α a : ℝ} {f : ℝ → ℝ}
    (hα : 0 < α) (hα' : α < 1)
    (hm : Measurable f) (hi : IntegrableOn f (Ioc 0 a)) :
    ContDiffOn ℝ 1 (fun t => ∫ s in Ioc (0 : ℝ) a, fractionalK α (t-s) * f s) (Ioi a) := by
  let ν := volume.restrict (Ioc 0 a)
  let F (t s : ℝ) := fractionalK α (t-s) * f s
  let D (t s : ℝ) := fractionalKernelDeriv α (t-s) * f s
  have hFm (t : ℝ) : Measurable (F t) :=
    ((fractionalK_measurable α).comp (measurable_const.sub measurable_id)).mul hm
  have hDm (t : ℝ) : Measurable (D t) :=
    ((measurable_fractionalKernelDeriv α).comp (measurable_const.sub measurable_id)).mul hm
  have hb (t : ℝ) (ht : a<t) :
      ∃ B : ℝ, (∀ᵐ s ∂ν, ∀ x ∈ Ioi ((a+t)/2), ‖D x s‖ ≤ B * ‖f s‖) ∧
        0 ≤ B := by
    let d := (t-a)/2
    have hd : 0 < d := by dsimp [d]; linarith
    let C := ((1-α) / Real.Gamma α) * d ^ (α-2)
    have hC : 0 ≤ C := by dsimp [C]; positivity
    refine ⟨C, ?_, hC⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs x hx
    have hds : d ≤ x-s := by dsimp [d]; linarith [show (a+t)/2 < x from hx, hs.2]
    dsimp only [D]
    rw [norm_mul, norm_fractionalKernelDeriv hα hα' (hd.trans_le hds)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hd hds (by linarith)) (by positivity)) (norm_nonneg _)
  have hDeriv (t : ℝ) (ht : t ∈ Ioi a) :
      HasDerivAt (fun t => ∫ s, F t s ∂ν) (∫ s, D t s ∂ν) t := by
    obtain ⟨B, hB, _⟩ := hb t ht
    have hmid : (a+t)/2 < t := by linarith [show a<t from ht]
    have hDiff : ∀ᵐ s ∂ν, ∀ x ∈ Ioi ((a+t)/2), HasDerivAt (fun x => F x s) (D x s) x := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs x hx
      have hp : 0 < x-s := by linarith [show (a+t)/2 < x from hx, hs.2, show a<t from ht]
      have hd := ((fractionalKernel_hasDerivAt (α := α) hp).comp x
        ((hasDerivAt_id x).sub_const s)).mul_const (f s)
      change HasDerivAt (fun y => fractionalK α (y-s) * f s)
        ((fractionalKernelDeriv α (x-s) * 1) * f s) x at hd
      simpa only [F, D, mul_one] using hd
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Ioi_mem_nhds hmid)
      (Eventually.of_forall fun x => (hFm x).aestronglyMeasurable)
      (fractionalKernel_history_integrable hα hα' ht hm hi)
      (hDm t).aestronglyMeasurable hB (hi.norm.const_mul B) hDiff).2
  have hc : ContinuousOn (fun t => ∫ s, D t s ∂ν) (Ioi a) := by
    intro t ht
    obtain ⟨B, hB, _⟩ := hb t ht
    have hmid : (a+t)/2 < t := by linarith [show a<t from ht]
    apply ContinuousAt.continuousWithinAt
    refine continuousAt_of_dominated (Eventually.of_forall fun x => (hDm x).aestronglyMeasurable)
      ?_ (hi.norm.const_mul B) ?_
    · filter_upwards [Ioi_mem_nhds hmid] with x hx
      exact hB.mono fun s hs => hs x hx
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hp : 0 < t-s := sub_pos.mpr (hs.2.trans_lt ht)
      have hC : ContinuousAt (fun x : ℝ => fractionalKernelDeriv α x) (t-s) := by
        unfold fractionalKernelDeriv
        exact (continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inl hp.ne'))).div_const _
      have hp' : ContinuousAt (fun x : ℝ => x-s) t := (continuous_id.sub continuous_const).continuousAt
      exact (ContinuousAt.comp' (f := fun x : ℝ => x-s) hC hp').mul continuousAt_const
  refine (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Ioi a)).mpr ⟨?_, ?_⟩
  · exact fun t ht => (hDeriv t ht).differentiableAt.differentiableWithinAt
  · exact hc.congr (fun t ht => (hDeriv t ht).hasDerivWithinAt.derivWithin (uniqueDiffOn_Ioi a t ht))

/-- The early history can be only L¹. Hölder regularity is required on
the recent segment, and the derivative is continuous on its interior. -/
theorem fractionalVolterra_contDiffOn_of_local_holder
    {α γ H a T : ℝ} {f : ℝ → ℝ} (hα : 0 < α) (hα' : α < 1)
    (hαγ : 1 < α + γ) (hγ : 0 ≤ γ) (hH : 0 ≤ H)
    (ha : 0 ≤ a) (hm : Measurable f) (hi : IntegrableOn f (Ioc 0 a))
    (hf : ContinuousOn f (Icc a T))
    (hholder : ∀ x ∈ Icc a T, ∀ y ∈ Icc a T, x ≤ y → ‖f y-f x‖ ≤ H * (y-x)^γ) :
    ContDiffOn ℝ 1 (volterraConvolution (fractionalK α) f) (Ioo a T) := by
  let g (s : ℝ) := f (s+a)
  have hmap : MapsTo (fun s : ℝ => s+a) (Icc 0 (T-a)) (Icc a T) := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hgc : ContinuousOn g (Icc 0 (T-a)) := hf.comp (continuous_id.add continuous_const).continuousOn hmap
  have hgm : Measurable g := hm.comp (measurable_id.add_const a)
  have hgH (x : ℝ) (hx : x ∈ Icc 0 (T-a)) (y : ℝ) (hy : y ∈ Icc 0 (T-a)) (hxy : x ≤ y) :
      ‖g y-g x‖ ≤ H * (y-x)^γ := by
    simpa only [g, add_sub_add_right_eq_sub] using
      hholder (x+a) (hmap hx) (y+a) (hmap hy) (add_le_add hxy le_rfl)
  have hNew := fractionalVolterra_contDiffOn_of_holder hα hα' hαγ hγ hH hgm hgc hgH
  have hNew' : ContDiffOn ℝ 1 (fun t => volterraConvolution (fractionalK α) g (t-a)) (Ioo a T) :=
    hNew.comp (contDiff_id.sub contDiff_const).contDiffOn (fun t ht =>
      ⟨sub_pos.mpr ht.1, sub_lt_sub_right ht.2 a⟩)
  have hOld := (contDiffOn_fractionalVolterra_old_history hα hα' hm hi).mono
    (Ioo_subset_Ioi_self : Ioo a T ⊆ Ioi a)
  apply (hOld.add hNew').congr
  intro x hx
  have hax : a ≤ x := hx.1.le
  have hx₀ : 0 ≤ x := ha.trans hax
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hf.norm
  let F (s : ℝ) := fractionalK α (x-s) * f s
  have hIold : IntervalIntegrable F volume 0 a :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ha).mpr
      (fractionalKernel_history_integrable hα hα' hx.1 hm hi)
  have hInew : IntervalIntegrable F volume a x := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hax).mpr
    exact integrableOn_mul_bounded measurableSet_Ioc
      ((fractionalKernel_reflected_integrable hα hx₀).mono_set (Ioc_subset_Ioc_left ha))
      ((fractionalK_measurable α).comp (measurable_const.sub measurable_id)) hm
      (fun s hs => hB ⟨s, ⟨hs.1.le, hs.2.trans hx.2.le⟩, rfl⟩)
  have hshift := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := x-a) F a
  simp only [zero_add, sub_add_cancel] at hshift
  have hshift' : volterraConvolution (fractionalK α) g (x-a) = ∫ s in a..x, F s := by
    unfold volterraConvolution
    rw [← intervalIntegral.integral_of_le (sub_nonneg.mpr hax), ← hshift]
    apply intervalIntegral.integral_congr
    intro s _
    change fractionalK α (x-a-s) * f (s+a) = fractionalK α (x-(s+a)) * f (s+a)
    rw [show x-a-s = x-(s+a) by ring]
  change (∫ s in Ioc (0 : ℝ) x, F s) =
    (∫ s in Ioc (0 : ℝ) a, F s) + volterraConvolution (fractionalK α) g (x-a)
  rw [hshift', ← intervalIntegral.integral_of_le hx₀, ← intervalIntegral.integral_of_le ha,
    intervalIntegral.integral_add_adjacent_intervals hIold hInew]

/-- First regularity step for the actual point-charge solution. The
point charge is smooth away from zero and the drift convolution is locally
α-Hölder even when its old history is only integrable. -/
theorem point_charge_riccati_locally_holder
    {α q b c δ T A : ℝ} {w : ℝ → ℝ} (hα : 1 / 2 < α) (hα' : α < 1)
    (hδ : 0 < δ) (hδT : δ ≤ T)
    (hm : Measurable w) (hc : ContinuousOn w (Ioi 0))
    (hlim : Tendsto (fun s => s ^ (1-α) * w s) (𝓝[>] 0) (𝓝 A))
    (hvol : ∀ s ∈ Ioc 0 T, w s = q * fractionalK α s +
      volterraConvolution (fractionalK α) (fun u => b * w u + c * w u^2) s) :
    ∃ H : ℝ, 0 ≤ H ∧
      ∀ x ∈ Icc δ T, ∀ y ∈ Icc δ T, x ≤ y → ‖w y-w x‖ ≤ H * (y-x)^α := by
  have hα₀ : 0 < α := by linarith
  have hT := hδ.trans_le hδT
  let d := δ/2
  have hd : 0 < d := by dsimp [d]; positivity
  have hdδ : d ≤ δ := by dsimp [d]; linarith
  let f (s : ℝ) := b * w s + c * w s^2
  have hfm : Measurable f := (hm.const_mul b).add ((hm.pow_const 2).const_mul c)
  have hfc : ContinuousOn f (Ioi 0) :=
    (continuousOn_const.mul hc).add (continuousOn_const.mul (hc.pow 2))
  obtain ⟨hwi, hw₂i⟩ := integrableOn_riccati_powers_of_weighted_asymptotic hα hT hm hc hlim
  have hIall : IntegrableOn f (Ioc 0 T) := (hwi.const_mul b).add (hw₂i.const_mul c)
  have hI : IntegrableOn f (Ioc 0 d) :=
    hIall.mono_set (Ioc_subset_Ioc_right (hdδ.trans hδT))
  obtain ⟨F, hF⟩ := isCompact_Icc.bddAbove_image
    (hfc.mono (show Icc d T ⊆ Ioi 0 from fun _ hx => hd.trans_le hx.1)).norm
  obtain ⟨W, hW⟩ := isCompact_Icc.bddAbove_image
    (hc.mono (show Icc δ T ⊆ Ioi 0 from fun _ hx => hδ.trans_le hx.1)).norm
  let B := max F 0
  let B' := max W 0
  have hB : 0 ≤ B := le_max_right _ _
  have hB' : 0 ≤ B' := le_max_right _ _
  let J := ∫ s in Ioc (0 : ℝ) d, ‖f s‖
  have hJ : 0 ≤ J := integral_nonneg fun s => norm_nonneg _
  let P := ((1-α) / Real.Gamma α) * d ^ (α-2)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  let Q := 2 / (Real.Gamma α * α)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  let C := (‖q‖+J)*P + B*Q
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C + 2*B', by positivity, ?_⟩
  intro x hx y hy hxy
  let h := y-x
  have hh : 0 ≤ h := sub_nonneg.mpr hxy
  have hxy' : x+h=y := by dsimp [h]; ring
  have hbound_w (s : ℝ) (hs : s ∈ Icc δ T) : ‖w s‖ ≤ B' :=
    (hW ⟨s, hs, rfl⟩).trans (le_max_left _ _)
  by_cases h₁ : h ≤ 1
  · have hdc : d+d ≤ x := by dsimp [d]; linarith [hx.1]
    have hbound_f (s : ℝ) (hs : s ∈ Ioc d (x+h)) : ‖f s‖ ≤ B :=
      (hF ⟨s, ⟨hs.1.le, hs.2.trans (by simpa only [hxy'] using hy.2)⟩, rfl⟩).trans (le_max_left _ _)
    have hv := fractional_volterra_local_input_increment hα₀ hα'.le hd.le hd hdc hh hfm hI hB hbound_f
    rw [hxy'] at hv
    have hv' : ‖volterraConvolution (fractionalK α) f y - volterraConvolution (fractionalK α) f x‖ ≤
        P*h*J + B*(Q*h^α) := by
      refine hv.trans_eq ?_
      dsimp [P, Q, J]
      ring
    have hk := fractionalKernel_increment_norm hα₀ hα' (hδ.trans_le hx.1) hh
    rw [hxy'] at hk
    have hk' : ‖fractionalK α y - fractionalK α x‖ ≤ P*h := by
      apply hk.trans
      apply mul_le_mul_of_nonneg_right _ hh
      apply mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hd (hdδ.trans hx.1) (by linarith)) (by positivity)
    have hwa : ‖w y-w x‖ ≤ ((‖q‖+J)*P)*h + B*Q*h^α := by
      rw [hvol y ⟨hδ.trans_le hy.1, hy.2⟩, hvol x ⟨hδ.trans_le hx.1, hx.2⟩]
      change ‖(q * fractionalK α y + volterraConvolution (fractionalK α) f y) -
        (q * fractionalK α x + volterraConvolution (fractionalK α) f x)‖ ≤ _
      rw [add_sub_add_comm, ← mul_sub]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
      exact (add_le_add (mul_le_mul_of_nonneg_left hk' (norm_nonneg _)) hv').trans_eq (by ring)
    have hhpow : h ≤ h^α := by
      rcases eq_or_lt_of_le hh with he | hp
      · simp [← he, Real.zero_rpow hα₀.ne']
      · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hp h₁ hα'.le
    calc
      _ ≤ ((‖q‖+J)*P)*h + B*Q*h^α := hwa
      _ ≤ ((‖q‖+J)*P)*h^α + B*Q*h^α :=
        add_le_add (mul_le_mul_of_nonneg_left hhpow (by positivity)) le_rfl
      _ = C*h^α := by dsimp [C]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (Real.rpow_nonneg hh _)
  · have hp : 1 ≤ h^α := by
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow (zero_le_one : (0 : ℝ) ≤ 1) (le_of_not_ge h₁) hα₀.le
    calc
      _ ≤ ‖w y‖ + ‖w x‖ := norm_sub_le _ _
      _ ≤ B'+B' := add_le_add (hbound_w y hy) (hbound_w x hx)
      _ = 2*B' := by ring
      _ ≤ C + 2*B' := le_add_of_nonneg_left hC
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hp

private theorem norm_riccati_polynomial_increment {b c x y B : ℝ}
    (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B) :
    ‖(b*y+c*y^2)-(b*x+c*x^2)‖ ≤ (‖b‖+2*‖c‖*B)*‖y-x‖ := by
  rw [show (b*y+c*y^2)-(b*x+c*x^2) = b*(y-x) + c*((y+x)*(y-x)) by ring]
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul]
  have hb : ‖y+x‖ ≤ 2*B := (norm_add_le _ _).trans
    ((add_le_add hy hx).trans_eq (by ring))
  calc
    _ ≤ ‖b‖*‖y-x‖+‖c‖*((2*B)*‖y-x‖) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hb (norm_nonneg _)) (norm_nonneg _))
    _ = _ := by ring

/-- Second regularity step for an actual continuous point-charge solution.
Its polynomial forcing inherits α-Hölder regularity, so the gain past one
derivative is available from `2α>1`. -/
theorem point_charge_riccati_contDiffAt_of_volterra
    {α q b c t T A : ℝ} {w : ℝ → ℝ} (hα : 1 / 2 < α) (hα' : α < 1)
    (ht : t ∈ Ioo 0 T)
    (hm : Measurable w) (hc : ContinuousOn w (Ioi 0))
    (hlim : Tendsto (fun s => s ^ (1-α) * w s) (𝓝[>] 0) (𝓝 A))
    (hvol : ∀ s ∈ Ioc 0 T, w s = q * fractionalK α s +
      volterraConvolution (fractionalK α) (fun u => b * w u + c * w u^2) s) :
    ContDiffAt ℝ 1 w t := by
  have hα₀ : 0 < α := by linarith
  let d := t/2
  have hd : 0 < d := div_pos ht.1 (by norm_num)
  have hdt : d < t := by dsimp [d]; linarith [ht.1]
  have hdT := hdt.le.trans ht.2.le
  have hT := ht.1.trans ht.2
  let f (s : ℝ) := b * w s + c*w s^2
  have hfm : Measurable f := (hm.const_mul b).add ((hm.pow_const 2).const_mul c)
  have hfc : ContinuousOn f (Icc d T) := by
    have hw := hc.mono (show Icc d T ⊆ Ioi 0 from fun _ hx => hd.trans_le hx.1)
    exact (continuousOn_const.mul hw).add (continuousOn_const.mul (hw.pow 2))
  obtain ⟨hwI, hwI₂⟩ := integrableOn_riccati_powers_of_weighted_asymptotic hα hT hm hc hlim
  have hfiAll : IntegrableOn f (Ioc 0 T) := (hwI.const_mul b).add (hwI₂.const_mul c)
  have hfi : IntegrableOn f (Ioc 0 d) :=
    hfiAll.mono_set (Ioc_subset_Ioc_right hdT)
  obtain ⟨H, hH, hwh⟩ := point_charge_riccati_locally_holder hα hα' hd hdT hm hc hlim hvol
  obtain ⟨B₀, hB₀⟩ := isCompact_Icc.bddAbove_image
    (hc.mono (show Icc d T ⊆ Ioi 0 from fun _ hx => hd.trans_le hx.1)).norm
  let B := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hBw (s : ℝ) (hs : s ∈ Icc d T) : ‖w s‖ ≤ B :=
    (hB₀ ⟨s, hs, rfl⟩).trans (le_max_left _ _)
  let C := ‖b‖+2*‖c‖*B
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hfh (x : ℝ) (hx : x ∈ Icc d T) (y : ℝ) (hy : y ∈ Icc d T) (hxy : x ≤ y) :
      ‖f y-f x‖ ≤ (C*H)*(y-x)^α :=
    (norm_riccati_polynomial_increment (hBw x hx) (hBw y hy)).trans
      ((mul_le_mul_of_nonneg_left (hwh x hx y hy hxy) hC).trans_eq (by ring))
  have hConv := fractionalVolterra_contDiffOn_of_local_holder hα₀ hα' (by linarith : 1 < α+α)
    hα₀.le (mul_nonneg hC hH) hd.le hfm hfi hfc hfh
  have hCdt : ContDiffAt ℝ 1 (volterraConvolution (fractionalK α) f) t :=
    hConv.contDiffAt (Ioo_mem_nhds hdt ht.2)
  have hK : ContDiffAt ℝ 1 (fractionalK α) t := by
    have hK' : ContDiffAt ℝ 1 (fun s : ℝ => s^(α-1) / Real.Gamma α) t :=
      (Real.contDiffAt_rpow_const_of_ne ht.1.ne').div contDiffAt_const (Real.Gamma_pos_of_pos hα₀).ne'
    apply hK'.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht.1] with s hs
    exact ite_eq_right (not_le.mpr (show 0 < s from hs))
  have hQ : ContDiffAt ℝ 1 (fun s => q* fractionalK α s +
      volterraConvolution (fractionalK α) f s) t := (contDiffAt_const.mul hK).add hCdt
  apply hQ.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact hvol s (Ioo_subset_Ioc_self hs)

#print axioms fractionalVolterra_old_quotient_limit
#print axioms fractionalVolterra_new_quotient_limit
#print axioms fractionalVolterra_hasDerivWithinAt_right_of_holder
#print axioms fractionalVolterra_contDiffOn_of_holder
#print axioms fractionalVolterra_contDiffOn_of_local_holder
#print axioms point_charge_riccati_contDiffAt_of_volterra

end RoughHeston
