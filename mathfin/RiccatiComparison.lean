import RiccatiDifferential
import RiemannLiouvilleMemory
import FractionalPowerRiccati
import FractionalKernelIncrements

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RoughHeston

private theorem singularRiccatiProfile_measurable (α c : ℝ) :
    Measurable (singularRiccatiProfile α c) :=
  Measurable.ite (measurableSet_lt measurable_const measurable_id)
    ((measurable_id.pow_const _).const_mul _) measurable_const

private theorem singularRiccatiProfile_contDiffAt {α c t : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ 1 (singularRiccatiProfile α c) t := by
  have hd : ContDiffAt ℝ 1 (fun x : ℝ => c * x ^ (-α)) t :=
    contDiffAt_const.mul (Real.contDiffAt_rpow_const_of_ne ht.ne')
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact ite_eq_left (show 0 < s from hs)

private theorem singularRiccatiProfile_integrableOn {α c t : ℝ} (hα' : α < 1) :
    IntegrableOn (singularRiccatiProfile α c) (Ioc 0 t) := by
  have hp : -1 < -α := by linarith
  have hi : IntegrableOn (fun x : ℝ => c * x ^ (-α)) (Ioc 0 t) :=
    ((intervalIntegral.intervalIntegrable_rpow' hp).const_mul c).1
  exact hi.congr_fun (fun x hx => (ite_eq_left hx.1).symm) measurableSet_Ioc

/-- A finite weighted point-charge limit implies strict dominance by
every positive multiple of the more singular power near zero. -/
theorem eventually_lt_singularRiccatiProfile {α A c : ℝ} {w : ℝ → ℝ}
    (hα : 1 / 2 < α) (hc : 0 < c)
    (hw : Tendsto (fun t => t ^ (1 - α) * w t) (𝓝[>] 0) (𝓝 A)) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), w t < singularRiccatiProfile α c t := by
  have hp : 0 < 2 * α - 1 := by linarith
  have hpow : Tendsto (fun t : ℝ => t ^ (2 * α - 1)) (𝓝[>] 0) (𝓝 0) := by
    have hd : ContinuousAt (fun t : ℝ => t ^ (2 * α - 1)) 0 :=
      (Real.continuous_rpow_const hp.le).continuousAt
    simpa only [Real.zero_rpow hp.ne'] using hd.tendsto.mono_left nhdsWithin_le_nhds
  have hl : Tendsto (fun t => t ^ α * w t) (𝓝[>] 0) (𝓝 0) := by
    have hprod : Tendsto (fun t => t ^ (2 * α - 1) * (t ^ (1 - α) * w t))
        (𝓝[>] 0) (𝓝 0) := by simpa only [zero_mul] using hpow.mul hw
    apply hprod.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [← mul_assoc, ← Real.rpow_add (show 0 < t from ht),
      show 2 * α - 1 + (1 - α) = α by ring]
  filter_upwards [self_mem_nhdsWithin, hl.eventually (Iio_mem_nhds hc)] with t ht htc
  have ht' : 0 < t := ht
  have hv : t ^ α * singularRiccatiProfile α c t = c := by
    unfold singularRiccatiProfile
    rw [ite_eq_left ht', mul_left_comm, ← Real.rpow_add ht', add_neg_cancel, Real.rpow_zero, mul_one]
  have hcomp : t ^ α * w t < t ^ α * singularRiccatiProfile α c t := by
    rw [hv]
    exact htc
  exact (mul_lt_mul_iff_of_pos_left (Real.rpow_pos_of_pos ht' α)).mp hcomp

theorem exists_initial_singularRiccatiProfile_dominance {α A c : ℝ} {w : ℝ → ℝ}
    (hα : 1 / 2 < α) (hc : 0 < c)
    (hw : Tendsto (fun t => t ^ (1 - α) * w t) (𝓝[>] 0) (𝓝 A)) :
    ∃ s : ℝ, 0 < s ∧ ∀ t ∈ Ioc 0 s, w t < singularRiccatiProfile α c t := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp (eventually_lt_singularRiccatiProfile hα hc hw))
  refine ⟨r / 2, by positivity, fun t ht => hball ?_ ht.1⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
  linarith [ht.2]

private theorem weighted_riccati_bounded_on_positive_horizon {α A T : ℝ} {w : ℝ → ℝ}
    (hT : 0 < T) (hcont : ContinuousOn w (Ioi 0))
    (hlim : Tendsto (fun s => s ^ (1 - α) * w s) (𝓝[>] 0) (𝓝 A)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Ioc 0 T, ‖s ^ (1 - α) * w s‖ ≤ C := by
  let U (s : ℝ) := s ^ (1 - α) * w s
  have hU : ContinuousOn U (Ioi 0) :=
    (continuousOn_id.rpow_const (fun _ hs => Or.inl (ne_of_gt (show 0 < _ from hs)))).mul hcont
  have hlimN : Tendsto (fun s => ‖U s‖) (𝓝[>] 0) (𝓝 ‖A‖) := hlim.norm
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp (hlimN.eventually (Iio_mem_nhds (lt_add_one ‖A‖))))
  let d := min T (r / 2)
  have hd : 0 < d := lt_min hT (by positivity)
  have hdr : d < r := (min_le_right _ _).trans_lt (by linarith)
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image
    (hU.mono (show Icc d T ⊆ Ioi 0 from fun _ hs => hd.trans_le hs.1)).norm
  refine ⟨max (‖A‖ + 1) B, by positivity, fun s hs => ?_⟩
  change ‖U s‖ ≤ max (‖A‖ + 1) B
  by_cases ho : s ≤ d
  · have hsr : dist s (0 : ℝ) < r := by
      simpa only [Real.dist_eq, sub_zero, abs_of_pos hs.1] using ho.trans_lt hdr
    exact (hball hsr hs.1).le.trans (le_max_left _ _)
  · exact (hB ⟨s, ⟨le_of_not_ge ho, hs.2⟩, rfl⟩).trans (le_max_right _ _)

/-- The weighted asymptotic and positive-time continuity supply the
two time-integrability hypotheses needed for the Riccati equation. -/
theorem integrableOn_riccati_powers_of_weighted_asymptotic {α A T : ℝ} {w : ℝ → ℝ}
    (hα : 1 / 2 < α) (hT : 0 < T) (hmeas : Measurable w) (hcont : ContinuousOn w (Ioi 0))
    (hlim : Tendsto (fun s => s ^ (1 - α) * w s) (𝓝[>] 0) (𝓝 A)) :
    IntegrableOn w (Ioc 0 T) ∧ IntegrableOn (fun s => w s ^ 2) (Ioc 0 T) := by
  obtain ⟨C, hC, hbound⟩ := weighted_riccati_bounded_on_positive_horizon hT hcont hlim
  have hq₁ : -1 < α-1 := by linarith
  have hq₂ : -1 < (α-1) + (α-1) := by linarith
  have hI₁ : IntegrableOn (fun s : ℝ => s ^ (α-1)) (Ioc 0 T) :=
    (intervalIntegral.intervalIntegrable_rpow' hq₁).1
  have hI₂ : IntegrableOn (fun s : ℝ => s ^ ((α-1) + (α-1))) (Ioc 0 T) :=
    (intervalIntegral.intervalIntegrable_rpow' hq₂).1
  have hpoint (s : ℝ) (hs : s ∈ Ioc 0 T) : ‖w s‖ ≤ s ^ (α-1) * C := by
    have he : s ^ (α-1) * (s ^ (1-α) * w s) = w s := by
      rw [← mul_assoc, ← Real.rpow_add hs.1, show α-1+(1-α)=0 by ring, Real.rpow_zero, one_mul]
    rw [← he, norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg hs.1.le _)]
    exact mul_le_mul_of_nonneg_left (hbound s hs) (Real.rpow_nonneg hs.1.le _)
  refine ⟨(hI₁.mul_const C).mono' hmeas.aestronglyMeasurable ?_,
    (hI₂.mul_const (C^2)).mono' (hmeas.pow_const 2).aestronglyMeasurable ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hpoint s hs
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [norm_pow]
    calc
      _ ≤ (s ^ (α-1) * C)^2 := pow_le_pow_left₀ (norm_nonneg _) (hpoint s hs) 2
      _ = _ := by rw [mul_pow, pow_two (s ^ (α-1)), ← Real.rpow_add hs.1]

private theorem fractionalMemory_sub_at {α t : ℝ} {v w : ℝ → ℝ}
    (hv : IntervalIntegrable (fun u => (α * u ^ (-α - 1) / Real.Gamma (1 - α)) *
      (v t - v (t-u))) volume 0 t)
    (hw : IntervalIntegrable (fun u => (α * u ^ (-α - 1) / Real.Gamma (1 - α)) *
      (w t - w (t-u))) volume 0 t) :
    IntervalIntegrable (fun u => (α * u ^ (-α - 1) / Real.Gamma (1 - α)) *
      ((v t - w t) - (v (t-u) - w (t-u)))) volume 0 t ∧
    fractionalMemory α 0 (fun u => v u - w u) t =
      fractionalMemory α 0 v t - fractionalMemory α 0 w t := by
  have he (u : ℝ) : (α * u ^ (-α - 1) / Real.Gamma (1 - α)) *
      ((v t - w t) - (v (t-u) - w (t-u))) =
    (α * u ^ (-α - 1) / Real.Gamma (1 - α)) * (v t - v (t-u)) -
    (α * u ^ (-α - 1) / Real.Gamma (1 - α)) * (w t - w (t-u)) := by ring
  constructor
  · simp_rw [he]
    exact hv.sub hw
  unfold fractionalMemory
  dsimp only
  simp_rw [he]
  rw [intervalIntegral.integral_sub hv hw]
  ring

/-- A point-charge Riccati solution stays strictly below the positive
singular undamped solution on its entire positive horizon. -/
theorem point_charge_riccati_lt_singular_profile {α q κ a T A : ℝ} {w : ℝ → ℝ}
    (hα : 1 / 2 < α) (hα' : α < 1) (hκ : 0 ≤ κ) (ha : 0 < a) (hT : 0 < T)
    (hm : Measurable w) (hwC1 : ∀ t, 0 < t → ContDiffAt ℝ 1 w t)
    (hvol : ∀ t ∈ Ioc 0 T, w t = q * fractionalK α t +
      volterraConvolution (fractionalK α) (fun s => -κ * w s + -a * w s ^ 2) t)
    (hlim : Tendsto (fun t => t ^ (1 - α) * w t) (𝓝[>] 0) (𝓝 A)) :
    ∀ t ∈ Ioc 0 T, w t < singularRiccatiProfile α (singularRiccatiCoefficient α a) t := by
  have hα₀ : 0 < α := by linarith
  let c := singularRiccatiCoefficient α a
  let v := singularRiccatiProfile α c
  have hc : 0 < c := singularRiccatiCoefficient_pos hα hα' ha
  have hvc (t : ℝ) (ht : 0 < t) : ContDiffAt ℝ 1 v t := singularRiccatiProfile_contDiffAt ht
  have hvm : Measurable v := singularRiccatiProfile_measurable _ _
  have hwcont : ContinuousOn w (Ioi 0) := fun t ht => (hwC1 t ht).continuousAt.continuousWithinAt
  obtain ⟨hwi, hwi₂⟩ := integrableOn_riccati_powers_of_weighted_asymptotic hα hT hm hwcont hlim
  have hf : IntegrableOn (fun s => -κ * w s + -a * w s ^ 2) (Ioc 0 T) :=
    (hwi.const_mul (-κ)).add (hwi₂.const_mul (-a))
  obtain ⟨d, hd, hstart⟩ := exists_initial_singularRiccatiProfile_dominance hα hc hlim
  intro t ht
  by_cases htd : t ≤ d
  · exact hstart t ⟨ht.1, htd⟩
  let g (u : ℝ) := v u - w u
  have hgc : ContinuousOn g (Icc d T) := by
    intro s hs
    have hpos := hd.trans_le hs.1
    exact ((hvc s hpos).continuousAt.sub (hwC1 s hpos).continuousAt).continuousWithinAt
  have hcontact (s : ℝ) (hs : s ∈ Icc d T) (hz : g s = 0) :
      IntervalIntegrable (fun u => (α * u ^ (-α-1) / Real.Gamma (1-α)) *
        (g s - g (s-u))) volume 0 s ∧ 0 ≤ fractionalMemory α 0 g s := by
    have hs₀ := hd.trans_le hs.1
    have hsT : s ∈ Ioc 0 T := ⟨hs₀, hs.2⟩
    have hvI : IntegrableOn v (Ioc 0 s) := singularRiccatiProfile_integrableOn hα'
    have hwI : IntegrableOn w (Ioc 0 s) := hwi.mono_set (Ioc_subset_Ioc_right hs.2)
    obtain ⟨hvM, hvD⟩ := fractional_rl_hasDerivAt_memory hα₀ hα' hs₀ hvm hvI (hvc s hs₀)
    obtain ⟨hwM, hwD⟩ := fractional_rl_hasDerivAt_memory hα₀ hα' hs₀ hm hwI (hwC1 s hs₀)
    have heqv : fractionalMemory α 0 v s = -a * v s ^ 2 :=
      hvD.deriv.symm.trans (singularRiccatiProfile_solves hα' ha hs₀).deriv
    have hdw := fractional_riccati_rl_hasDerivWithinAt hα₀ hα' hsT hm hwcont hf hvol
    have hu := uniqueDiffOn_Ioc (0 : ℝ) T s hsT
    have heqw : fractionalMemory α 0 w s = -κ * w s + -a * w s ^ 2 :=
      (hwD.hasDerivWithinAt.derivWithin hu).symm.trans (hdw.derivWithin hu)
    obtain ⟨hgM, hM⟩ := fractionalMemory_sub_at hvM hwM
    refine ⟨hgM, ?_⟩
    have hEq : v s = w s := sub_eq_zero.mp hz
    have hvpos : 0 < v s := by
      change 0 < singularRiccatiProfile α c s
      rw [singularRiccatiProfile, ite_eq_left hs₀]
      exact mul_pos hc (Real.rpow_pos_of_pos hs₀ _)
    have hgap : fractionalMemory α 0 g s = κ * w s := by
      rw [show fractionalMemory α 0 g s =
          fractionalMemory α 0 (fun u => v u - w u) s from rfl,
        hM, heqv, heqw, hEq]
      ring
    rw [hgap]
    exact mul_nonneg hκ (hEq ▸ hvpos.le)
  have hh := fractional_first_contact_comparison hα₀ hα' (le_refl (0 : ℝ)) hd hgc
    (fun s hs => sub_pos.mpr (hstart s hs)) hcontact t ⟨le_of_not_ge htd, ht.2⟩
  exact sub_pos.mp hh

private theorem fractionalK_eq_hestonKernel' (α : ℝ) : fractionalK α = hestonKernel α := by
  funext x
  by_cases hx : x ≤ 0
  · simp [fractionalK, hestonKernel, hx, not_lt.mpr hx]
  · simp [fractionalK, hestonKernel, hx, lt_of_not_ge hx]

private theorem fractionalK_nonnegative' {α : ℝ} (hα : 0 < α) (x : ℝ) :
    0 ≤ fractionalK α x := by
  unfold fractionalK
  split
  · exact le_rfl
  · rename_i hx
    exact div_nonneg (Real.rpow_nonneg (le_of_lt (lt_of_not_ge hx)) _)
      (Real.Gamma_pos_of_pos hα).le

private theorem fractionalK_reflected_integrableOn_Ioc' {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t) :
    IntegrableOn (fun s : ℝ => fractionalK α (t - s)) (Ioc 0 t) := by
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).2
    (fractionalK_integrableOn_Ioc hα t)
  have hr := hi.comp_sub_left t
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).1
  simpa only [sub_zero, sub_self] using hr.symm

private theorem bounded_input_setIntegral_mul {k f : ℝ → ℝ} {S : Set ℝ}
    (hS : MeasurableSet S) (hk : IntegrableOn k S) (hkm : Measurable k) (hfm : Measurable f)
    {B : ℝ} (hB : ∀ s ∈ S, ‖f s‖ ≤ B) :
    IntegrableOn (fun s => k s * f s) S ∧
      ‖∫ s in S, k s * f s‖ ≤ (∫ s in S, ‖k s‖) * B := by
  have hi : IntegrableOn (fun s => ‖k s‖ * B) S := hk.norm.mul_const B
  have hbound (s : ℝ) (hs : s ∈ S) : ‖k s * f s‖ ≤ ‖k s‖ * B := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB s hs) (norm_nonneg _)
  have hki : IntegrableOn (fun s => k s * f s) S :=
    hi.mono' (hkm.mul hfm).aestronglyMeasurable
      ((ae_restrict_mem hS).mono hbound)
  refine ⟨hki, ?_⟩
  rw [← integral_mul_const]
  exact (norm_integral_le_integral_norm _).trans (setIntegral_mono_on hki.norm hi hS hbound)

/-- A bounded input gains the fractional Hölder exponent, with a constant
uniform in the observation times of the convolution. -/
theorem fractional_volterra_bounded_input_increment {α t h B : ℝ} {f : ℝ → ℝ}
    (hα : 0 < α) (hα' : α ≤ 1) (ht : 0 ≤ t) (hh : 0 ≤ h)
    (hf : Measurable f) (hB₀ : 0 ≤ B) (hB : ∀ s ∈ Ioc 0 (t+h), ‖f s‖ ≤ B) :
    ‖volterraConvolution (fractionalK α) f (t+h) - volterraConvolution (fractionalK α) f t‖ ≤
      B * ((2 / (Real.Gamma α * α)) * h ^ α) := by
  let k := fractionalK α
  let k₀ (s : ℝ) := k (t-s)
  let k₁ (s : ℝ) := k (t+h-s)
  let kd (s : ℝ) := k₁ s - k₀ s
  have hth : t ≤ t+h := le_add_of_nonneg_right hh
  have ht₁ : 0 ≤ t+h := ht.trans hth
  have hkm : Measurable k := fractionalK_measurable α
  have hm₀ : Measurable k₀ := hkm.comp (measurable_const.sub measurable_id)
  have hm₁ : Measurable k₁ := hkm.comp (measurable_const.sub measurable_id)
  have hi₀ : IntegrableOn k₀ (Ioc 0 t) := fractionalK_reflected_integrableOn_Ioc' hα ht
  have hi₁ : IntegrableOn k₁ (Ioc 0 (t+h)) := fractionalK_reflected_integrableOn_Ioc' hα ht₁
  have hi₁₀ := hi₁.mono_set (Ioc_subset_Ioc_right hth)
  have hi₁₁ := hi₁.mono_set (Ioc_subset_Ioc_left ht)
  have hBo s (hs : s ∈ Ioc (0 : ℝ) t) := hB s (Ioc_subset_Ioc_right hth hs)
  have hBn s (hs : s ∈ Ioc t (t+h)) := hB s (Ioc_subset_Ioc_left ht hs)
  have hOld := bounded_input_setIntegral_mul measurableSet_Ioc
    (show IntegrableOn kd (Ioc 0 t) from hi₁₀.sub hi₀) (hm₁.sub hm₀) hf hBo
  have hNew := bounded_input_setIntegral_mul measurableSet_Ioc hi₁₁ hm₁ hf hBn
  have hBase := bounded_input_setIntegral_mul measurableSet_Ioc hi₀ hm₀ hf hBo
  have hWide := bounded_input_setIntegral_mul measurableSet_Ioc hi₁₀ hm₁ hf hBo
  have hsplit : (∫ s in Ioc (0 : ℝ) t, k₁ s * f s) +
      (∫ s in Ioc t (t+h), k₁ s * f s) = ∫ s in Ioc (0 : ℝ) (t+h), k₁ s * f s := by
    have hi := intervalIntegral.integral_add_adjacent_intervals
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr hWide.1)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hth).mpr hNew.1)
    simpa only [intervalIntegral.integral_of_le ht, intervalIntegral.integral_of_le hth,
      intervalIntegral.integral_of_le ht₁] using hi
  have he :
      volterraConvolution k f (t+h) - volterraConvolution k f t =
        (∫ s in Ioc (0 : ℝ) t, kd s * f s) + ∫ s in Ioc t (t+h), k₁ s * f s := by
    change (∫ s in Ioc (0 : ℝ) (t+h), k₁ s * f s) - (∫ s in Ioc (0 : ℝ) t, k₀ s * f s) = _
    rw [← hsplit, add_sub_right_comm, ← integral_sub hWide.1 hBase.1]
    simp only [kd, sub_mul]
  have he₀ : (∫ s in Ioc (0 : ℝ) t, ‖kd s‖) = ∫ s in (0 : ℝ)..t, |k (s+h) - k s| := by
    rw [← intervalIntegral.integral_of_le ht]
    have hr := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := t)
      (fun s => |k (s+h) - k s|) t
    simp only [sub_self, sub_zero] at hr
    rw [← hr]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp [kd, k₁, k₀]
    rw [show t+h-s=t-s+h by ring]
  have he₁ : (∫ s in Ioc t (t+h), ‖k₁ s‖) = ∫ s in (0 : ℝ)..h, k s := by
    rw [← intervalIntegral.integral_of_le hth]
    have hr := intervalIntegral.integral_comp_sub_left (a := t) (b := t+h) k (t+h)
    simp only [sub_self, add_sub_cancel_left] at hr
    simpa only [k₁, k, Real.norm_of_nonneg (fractionalK_nonnegative' hα _)] using hr
  have hinc := hestonKernel_increment_L1 hα hα' ht hh
  rw [← fractionalK_eq_hestonKernel' α] at hinc
  change (∫ s in (0 : ℝ)..h, k s) + (∫ s in (0 : ℝ)..t, |k (s+h) - k s|) ≤ _ at hinc
  change ‖volterraConvolution k f (t+h) - volterraConvolution k f t‖ ≤ _
  rw [he]
  calc
    _ ≤ ‖∫ s in Ioc (0 : ℝ) t, kd s * f s‖ + ‖∫ s in Ioc t (t+h), k₁ s * f s‖ :=
      norm_add_le _ _
    _ ≤ _ := add_le_add hOld.2 hNew.2
    _ = B * ((∫ s in (0 : ℝ)..h, k s) + ∫ s in (0 : ℝ)..t, |k (s+h) - k s|) := by
      change (∫ s in Ioc (0 : ℝ) t, ‖kd s‖) * B +
        (∫ s in Ioc t (t+h), ‖k₁ s‖) * B = _
      rw [he₀, he₁]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hinc hB₀

private theorem fractionalK_decreasing_pos' {α d x : ℝ} (hα : 0 < α) (hα' : α ≤ 1)
    (hd : 0 < d) (hx : d ≤ x) : fractionalK α x ≤ fractionalK α d := by
  simp only [fractionalK, ite_eq_right (not_le.mpr hd), ite_eq_right (not_le.mpr (hd.trans_le hx))]
  exact div_le_div_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos hd hx (sub_nonpos.mpr hα'))
    (Real.Gamma_pos_of_pos hα).le

private theorem fractionalK_hasDerivAt_pos' {α x : ℝ} (hx : 0 < x) :
    HasDerivAt (fractionalK α) ((α - 1) * x ^ (α - 2) / Real.Gamma α) x := by
  have hd := (Real.hasDerivAt_rpow_const (x := x) (p := α-1) (Or.inl hx.ne')).div_const (Real.Gamma α)
  have hd' : HasDerivAt (fun x : ℝ => x ^ (α-1) / Real.Gamma α)
      ((α-1) * x ^ (α-2) / Real.Gamma α) x := by
    simpa only [show α-1-1=α-2 by ring] using hd
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with u hu
  exact ite_eq_right (not_le.mpr (show 0 < u from hu))

private theorem fractionalK_lipschitz_away_zero {α d x y : ℝ}
    (hα : 0 < α) (hα' : α ≤ 1) (hd : 0 < d) (hdx : d ≤ x) (hxy : x ≤ y) :
    ‖fractionalK α y - fractionalK α x‖ ≤
      (((1-α) * d ^ (α-2)) / Real.Gamma α) * (y-x) := by
  have hΓ := Real.Gamma_pos_of_pos hα
  apply norm_image_sub_le_of_norm_deriv_le_segment'
    (f' := fun u => (α - 1) * u ^ (α - 2) / Real.Gamma α)
    (fun u hu => (fractionalK_hasDerivAt_pos' (hd.trans_le (hdx.trans hu.1))).hasDerivWithinAt)
    ?_ y ⟨hxy, le_rfl⟩
  intro u hu
  have hdu := hdx.trans hu.1
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonpos (sub_nonpos.mpr hα'),
    abs_of_nonneg (Real.rpow_nonneg (hd.trans_le hdu).le _), abs_of_pos hΓ, neg_sub]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hd hdu (by linarith)) (sub_nonneg.mpr hα'))
    hΓ.le

/-- The Volterra integral gains the fractional Hölder exponent locally
under integrability of the old history and boundedness of the recent input.
The two contributions have explicit constants. -/
theorem fractional_volterra_local_input_increment {α a d t h B : ℝ} {f : ℝ → ℝ}
    (hα : 0 < α) (hα' : α ≤ 1) (ha : 0 ≤ a) (hd : 0 < d) (hdt : a+d ≤ t)
    (hh : 0 ≤ h) (hfm : Measurable f) (hI : IntegrableOn f (Ioc 0 a))
    (hB₀ : 0 ≤ B) (hB : ∀ s ∈ Ioc a (t+h), ‖f s‖ ≤ B) :
    ‖volterraConvolution (fractionalK α) f (t+h) - volterraConvolution (fractionalK α) f t‖ ≤
      (((1-α) * d ^ (α-2)) / Real.Gamma α) * h * (∫ s in Ioc (0 : ℝ) a, ‖f s‖) +
        B * ((2 / (Real.Gamma α * α)) * h ^ α) := by
  let k := fractionalK α
  let J (x : ℝ) := ∫ s in Ioc (0 : ℝ) a, k (x-s) * f s
  let g (s : ℝ) := f (s+a)
  let C := ((1-α) * d ^ (α-2)) / Real.Gamma α
  have hKm : Measurable k := fractionalK_measurable α
  have hgm : Measurable g := hfm.comp (measurable_id.add_const a)
  have hat : a < t := lt_of_lt_of_le (lt_add_of_pos_right a hd) hdt
  have hold (x : ℝ) (hx : a+d ≤ x) :
      IntegrableOn (fun s => k (x-s) * f s) (Ioc 0 a) := by
    have hm : Measurable (fun s => k (x-s) * f s) :=
      (hKm.comp (measurable_const.sub measurable_id)).mul hfm
    refine (hI.norm.const_mul (k d)).mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hdu : d ≤ x-u := by linarith [hu.2]
    rw [norm_mul, Real.norm_of_nonneg (fractionalK_nonnegative' hα _)]
    exact mul_le_mul_of_nonneg_right (fractionalK_decreasing_pos' hα hα' hd hdu) (norm_nonneg _)
  have hJ : ‖J (t+h) - J t‖ ≤ C * h * (∫ s in Ioc (0 : ℝ) a, ‖f s‖) := by
    have h1 := hold (t+h) (hdt.trans (le_add_of_nonneg_right hh))
    have h0 := hold t hdt
    have hm : IntegrableOn (fun s => C * h * ‖f s‖) (Ioc 0 a) := hI.norm.const_mul (C*h)
    unfold J
    rw [← integral_sub h1 h0, ← integral_const_mul]
    refine (norm_integral_le_integral_norm _).trans
      (setIntegral_mono_on (h1.sub h0).norm hm measurableSet_Ioc ?_)
    intro s hs
    rw [← sub_mul, norm_mul]
    have hds : d ≤ t-s := by linarith [hs.2]
    have hle : t-s ≤ t+h-s := by linarith
    have hb := fractionalK_lipschitz_away_zero hα hα' hd hds hle
    rw [show (t+h-s) - (t-s) = h by ring] at hb
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  have hsplit {x : ℝ} (hx : a+d ≤ x) (hxt : x ≤ t+h) :
      volterraConvolution k f x = J x + volterraConvolution k g (x-a) := by
    have hax : a ≤ x := by linarith
    have hx₀ : 0 ≤ x := ha.trans hax
    have hKa := (fractionalK_reflected_integrableOn_Ioc' hα hx₀).mono_set (Ioc_subset_Ioc_left ha)
    have hma : Measurable (fun s => k (x-s)) := hKm.comp (measurable_const.sub measurable_id)
    have hBa (s : ℝ) (hs : s ∈ Ioc a x) := hB s (Ioc_subset_Ioc_right hxt hs)
    have hrecent := (bounded_input_setIntegral_mul measurableSet_Ioc hKa hma hfm hBa).1
    have hs := intervalIntegral.integral_add_adjacent_intervals
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha).mpr (hold x hx))
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hax).mpr hrecent)
    have hshift := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := x-a)
      (fun s => k (x-s) * f s) a
    simp only [zero_add, sub_add_cancel] at hshift
    have hshift' : volterraConvolution k g (x-a) =
        ∫ s in a..x, k (x-s) * f s := by
      unfold volterraConvolution
      rw [← intervalIntegral.integral_of_le (sub_nonneg.mpr hax), ← hshift]
      apply intervalIntegral.integral_congr
      intro s _
      change k (x-a-s) * f (s+a) = k (x-(s+a)) * f (s+a)
      rw [show x-a-s = x-(s+a) by ring]
    rw [hshift']
    unfold J volterraConvolution
    rw [← intervalIntegral.integral_of_le ha, hs, intervalIntegral.integral_of_le hx₀]
  have htshift : 0 ≤ t-a := sub_nonneg.mpr hat.le
  have hBshift (s : ℝ) (hs : s ∈ Ioc 0 ((t-a)+h)) : ‖g s‖ ≤ B := by
    apply hB
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hshifted := fractional_volterra_bounded_input_increment hα hα' htshift hh hgm hB₀ hBshift
  rw [hsplit (hdt.trans (le_add_of_nonneg_right hh)) le_rfl,
    hsplit hdt (le_add_of_nonneg_right hh), show t+h-a = (t-a)+h by ring]
  rw [show J (t+h) + volterraConvolution k g ((t-a)+h) -
      (J t + volterraConvolution k g (t-a)) =
      (J (t+h)-J t) + (volterraConvolution k g ((t-a)+h)-volterraConvolution k g (t-a)) by ring]
  exact (norm_add_le _ _).trans (add_le_add hJ hshifted)

#print axioms eventually_lt_singularRiccatiProfile
#print axioms integrableOn_riccati_powers_of_weighted_asymptotic
#print axioms point_charge_riccati_lt_singular_profile
#print axioms fractional_volterra_bounded_input_increment
#print axioms fractional_volterra_local_input_increment

end RoughHeston
