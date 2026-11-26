import FractionalKernelL1

open MeasureTheory Set Filter
open scoped Interval NNReal Topology

namespace RoughHeston

private theorem integral_shift_sub_eq_boundary {q : ℝ → ℝ} {T h : ℝ}
    (hT : 0 ≤ T) (hh : 0 ≤ h) (hq : IntervalIntegrable q volume 0 (T + h)) :
    (∫ s in (0 : ℝ)..T, q s - q (s + h)) =
      (∫ s in (0 : ℝ)..h, q s) - (∫ s in T..(T + h), q s) := by
  have hTh : T ≤ T + h := le_add_of_nonneg_right hh
  have hhT : h ≤ T + h := le_add_of_nonneg_left hT
  have hsub {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T + h) :
      IntervalIntegrable q volume a b := by
    apply hq.mono_set
    rw [uIcc_of_le hab, uIcc_of_le (add_nonneg hT hh)]
    exact Icc_subset_Icc ha hb
  have ha : IntervalIntegrable q volume 0 T := hsub le_rfl hT hTh
  have hb : IntervalIntegrable q volume h (T + h) := hsub hh hhT le_rfl
  have hc : IntervalIntegrable (fun s => q (s + h)) volume 0 T := by
    simpa only [sub_self, add_sub_cancel_right] using hb.comp_add_right h
  rw [intervalIntegral.integral_sub ha hc, intervalIntegral.integral_comp_add_right, zero_add]
  have he₁ := intervalIntegral.integral_add_adjacent_intervals ha (hsub hT hTh le_rfl)
  have he₂ := intervalIntegral.integral_add_adjacent_intervals (hsub le_rfl hh hhT) hb
  linarith only [he₁, he₂]

/-- For a nonnegative, nonincreasing kernel the squared increments are
controlled by its squared mass on the first `h` units of time. -/
theorem nonnegative_decreasing_kernel_sq_increment {k : ℝ → ℝ} {T h : ℝ}
    (hT : 0 ≤ T) (hh : 0 ≤ h) (hkm : Measurable k)
    (hk₀ : ∀ s > 0, 0 ≤ k s) (hk : AntitoneOn k (Ioi 0))
    (hki : IntervalIntegrable (fun s => k s ^ 2) volume 0 (T + h)) :
    (∫ s in (0 : ℝ)..T, (k (s + h) - k s) ^ 2) ≤ ∫ s in (0 : ℝ)..h, k s ^ 2 := by
  let q (s : ℝ) := k s ^ 2
  let f (s : ℝ) := (k (s + h) - k s) ^ 2
  let g (s : ℝ) := q s - q (s + h)
  let ν := volume.restrict (Ioc (0 : ℝ) T)
  have hpoint : ∀ᵐ s ∂ν, f s ≤ g s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hs' : 0 < s + h := hs.1.trans_le (le_add_of_nonneg_right hh)
    have hmon := hk hs.1 hs' (le_add_of_nonneg_right hh)
    have hprod := mul_nonneg (hk₀ (s + h) hs') (sub_nonneg.mpr hmon)
    dsimp only [f, g, q]
    nlinarith only [hprod]
  have hTh : T ≤ T + h := le_add_of_nonneg_right hh
  have hhT : h ≤ T + h := le_add_of_nonneg_left hT
  have hsub {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T + h) :
      IntervalIntegrable q volume a b := by
    apply hki.mono_set
    rw [uIcc_of_le hab, uIcc_of_le (add_nonneg hT hh)]
    exact Icc_subset_Icc ha hb
  have hq : Integrable q ν := (hsub le_rfl hT hTh).1
  have hq' : IntervalIntegrable (fun s => q (s + h)) volume 0 T := by
    simpa only [sub_self, add_sub_cancel_right] using (hsub hh hhT le_rfl).comp_add_right h
  have hgi : Integrable g ν := hq.sub hq'.1
  have hfm : Measurable f := ((hkm.comp (measurable_id.add_const h)).sub hkm).pow_const 2
  have hfi : Integrable f ν := hgi.mono' hfm.aestronglyMeasurable
    (hpoint.mono fun s hs => by rwa [Real.norm_of_nonneg (sq_nonneg _)])
  have h₀ : 0 ≤ ∫ s in T..(T + h), q s :=
    intervalIntegral.integral_nonneg_of_forall hTh (fun _ => sq_nonneg _)
  calc
    (∫ s in (0 : ℝ)..T, (k (s + h) - k s) ^ 2) ≤ ∫ s in (0 : ℝ)..T, g s := by
      rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT]
      exact integral_mono_ae hfi hgi hpoint
    _ = (∫ s in (0 : ℝ)..h, q s) - (∫ s in T..(T + h), q s) :=
      integral_shift_sub_eq_boundary hT hh hki
    _ ≤ ∫ s in (0 : ℝ)..h, k s ^ 2 := sub_le_self _ h₀

/-- Exact initial squared mass of the fractional Heston kernel. -/
theorem hestonKernel_integral_sq {α h : ℝ} (hα : 1 / 2 < α) (hh : 0 ≤ h) :
    (∫ s in (0 : ℝ)..h, hestonKernel α s ^ 2) =
      h ^ (2 * α - 1) / (Real.Gamma α ^ 2 * (2 * α - 1)) := by
  have hβ : 0 < 2 * α - 1 := by linarith
  have hpow : ∀ s > 0, hestonKernel α s ^ 2 = s ^ (2 * α - 2) / Real.Gamma α ^ 2 := by
    intro s hs
    have he : s ^ ((α - 1) * 2) = (s ^ (α - 1)) ^ 2 :=
      (Real.rpow_mul hs.le _ _).trans (Real.rpow_two _)
    rw [hestonKernel, ite_eq_left hs, div_pow, ← he, show (α - 1) * 2 = 2 * α - 2 by ring]
  have he : (∫ s in (0 : ℝ)..h, hestonKernel α s ^ 2) =
      ∫ s in (0 : ℝ)..h, s ^ (2 * α - 2) / Real.Gamma α ^ 2 := by
    rw [intervalIntegral.integral_of_le hh, intervalIntegral.integral_of_le hh]
    exact setIntegral_congr_fun measurableSet_Ioc (fun s hs => hpow s hs.1)
  rw [he, intervalIntegral.integral_div, integral_rpow (Or.inl (by linarith)),
    show 2 * α - 2 + 1 = 2 * α - 1 by ring, Real.zero_rpow hβ.ne', sub_zero,
    div_div, mul_comm (2 * α - 1)]

/-- Positive decreasing kernel approximations dominated by the fractional
kernel satisfy the fractional squared-increment bound uniformly. -/
theorem heston_dominated_kernel_increment_L2 {α T h : ℝ} {k : ℝ → ℝ}
    (hα : 1 / 2 < α) (hT : 0 ≤ T) (hh : 0 ≤ h) (hkm : Measurable k)
    (hk₀ : ∀ s > 0, 0 ≤ k s) (hk : AntitoneOn k (Ioi 0))
    (hkK : ∀ s > 0, k s ≤ hestonKernel α s) :
    (∫ s in (0 : ℝ)..h, k s ^ 2) + (∫ s in (0 : ℝ)..T, (k (s + h) - k s) ^ 2) ≤
      (2 / (Real.Gamma α ^ 2 * (2 * α - 1))) * h ^ (2 * α - 1) := by
  have hbase (S : ℝ) (hS : 0 ≤ S) : IntegrableOn (fun s => hestonKernel α s ^ 2) (Ioc 0 S) := by
    let t : ℝ≥0 := ⟨S, hS⟩
    exact (hestonKernel_memLp_two hα t).integrable_sq
  have hsq (S : ℝ) : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) S), k s ^ 2 ≤ hestonKernel α s ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact pow_le_pow_left₀ (hk₀ s hs.1) (hkK s hs.1) _
  have hki (S : ℝ) (hS : 0 ≤ S) : IntegrableOn (fun s => k s ^ 2) (Ioc 0 S) :=
    (hbase S hS).mono' (hkm.pow_const 2).aestronglyMeasurable
      ((hsq S).mono fun s hs => by rwa [Real.norm_of_nonneg (sq_nonneg _)])
  have hfirst : (∫ s in (0 : ℝ)..h, k s ^ 2) ≤ ∫ s in (0 : ℝ)..h, hestonKernel α s ^ 2 := by
    rw [intervalIntegral.integral_of_le hh, intervalIntegral.integral_of_le hh]
    exact integral_mono_ae (hki h hh) (hbase h hh) (hsq h)
  have hinc := nonnegative_decreasing_kernel_sq_increment hT hh hkm hk₀ hk
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (add_nonneg hT hh)).2 (hki _ (add_nonneg hT hh)))
  have hsum := add_le_add hfirst (hinc.trans hfirst)
  rw [hestonKernel_integral_sq hα hh] at hsum
  convert hsum using 1
  ring


private theorem hestonKernel_nonnegative {α : ℝ} (hα : 0 < α) (s : ℝ) (hs : 0 < s) :
    0 ≤ hestonKernel α s := by
  rw [hestonKernel, ite_eq_left hs]
  exact div_nonneg (Real.rpow_nonneg hs.le _) (Real.Gamma_pos_of_pos hα).le

private theorem hestonKernel_decreasing {α : ℝ} (hα : 0 < α) (hα' : α ≤ 1) :
    AntitoneOn (hestonKernel α) (Ioi 0) := by
  intro s hs t ht hst
  simp only [mem_Ioi] at hs ht
  simp only [hestonKernel, ite_eq_left hs, ite_eq_left ht]
  exact div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hs hst (sub_nonpos.mpr hα'))
    (Real.Gamma_pos_of_pos hα).le

/-- The same explicit squared-increment estimate for the fractional kernel itself. -/
theorem hestonKernel_increment_L2 {α T h : ℝ}
    (hα : 1 / 2 < α) (hα' : α ≤ 1) (hT : 0 ≤ T) (hh : 0 ≤ h) :
    (∫ s in (0 : ℝ)..h, hestonKernel α s ^ 2) +
        (∫ s in (0 : ℝ)..T, (hestonKernel α (s + h) - hestonKernel α s) ^ 2) ≤
      (2 / (Real.Gamma α ^ 2 * (2 * α - 1))) * h ^ (2 * α - 1) := by
  have ha : 0 < α := by linarith
  exact heston_dominated_kernel_increment_L2 hα hT hh (hestonKernel_measurable α)
    (hestonKernel_nonnegative ha) (hestonKernel_decreasing ha hα') (fun _ _ => le_rfl)

/-- The initial mass controls the absolute increments of a decreasing
integrable nonnegative kernel. -/
theorem nonnegative_decreasing_kernel_abs_increment {k : ℝ → ℝ} {T h : ℝ}
    (hT : 0 ≤ T) (hh : 0 ≤ h) (hk₀ : ∀ s > 0, 0 ≤ k s) (hk : AntitoneOn k (Ioi 0))
    (hki : IntervalIntegrable k volume 0 (T + h)) :
    (∫ s in (0 : ℝ)..T, |k (s + h) - k s|) ≤ ∫ s in (0 : ℝ)..h, k s := by
  have hcongr : (∫ s in (0 : ℝ)..T, |k (s + h) - k s|) =
      ∫ s in (0 : ℝ)..T, k s - k (s + h) := by
    rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    have hle : s ≤ s + h := le_add_of_nonneg_right hh
    change |k (s + h) - k s| = k s - k (s + h)
    rw [abs_of_nonpos (sub_nonpos.mpr (hk hs.1 (hs.1.trans_le hle) hle)), neg_sub]
  rw [hcongr, integral_shift_sub_eq_boundary hT hh hki]
  apply sub_le_self
  rw [intervalIntegral.integral_of_le (le_add_of_nonneg_right hh)]
  apply setIntegral_nonneg_of_ae_restrict
  exact (ae_restrict_mem measurableSet_Ioc).mono fun s hs => hk₀ s (hT.trans_lt hs.1)

/-- Exact initial mass of the fractional Heston kernel. -/
theorem hestonKernel_integral {α h : ℝ} (hα : 0 < α) (hh : 0 ≤ h) :
    (∫ s in (0 : ℝ)..h, hestonKernel α s) = h ^ α / (Real.Gamma α * α) := by
  have he : (∫ s in (0 : ℝ)..h, hestonKernel α s) =
      ∫ s in (0 : ℝ)..h, s ^ (α - 1) / Real.Gamma α := by
    rw [intervalIntegral.integral_of_le hh, intervalIntegral.integral_of_le hh]
    exact setIntegral_congr_fun measurableSet_Ioc fun s hs => ite_eq_left hs.1
  rw [he, intervalIntegral.integral_div, integral_rpow (Or.inl (by linarith)),
    sub_add_cancel, Real.zero_rpow hα.ne', sub_zero, div_div, mul_comm α]

/-- Positive decreasing kernel approximations dominated by the fractional
kernel satisfy the absolute-increment estimate for drift terms uniformly. -/
theorem heston_dominated_kernel_increment_L1 {α T h : ℝ} {k : ℝ → ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (hh : 0 ≤ h) (hkm : Measurable k)
    (hk₀ : ∀ s > 0, 0 ≤ k s) (hk : AntitoneOn k (Ioi 0))
    (hkK : ∀ s > 0, k s ≤ hestonKernel α s) :
    (∫ s in (0 : ℝ)..h, k s) + (∫ s in (0 : ℝ)..T, |k (s + h) - k s|) ≤
      (2 / (Real.Gamma α * α)) * h ^ α := by
  have he : hestonKernel α = fractionalK α := by
    funext s
    by_cases hs : s ≤ 0
    · simp [hestonKernel, fractionalK, hs, not_lt.mpr hs]
    · simp [hestonKernel, fractionalK, hs, lt_of_not_ge hs]
  have hbase (S : ℝ) : IntegrableOn (hestonKernel α) (Ioc 0 S) := by
    rw [he]
    exact fractionalK_integrableOn_Ioc hα S
  have hK (S : ℝ) : k ≤ᵐ[volume.restrict (Ioc (0 : ℝ) S)] hestonKernel α :=
    (ae_restrict_mem measurableSet_Ioc).mono fun s hs => hkK s hs.1
  have hki (S : ℝ) : IntegrableOn k (Ioc 0 S) := by
    refine (hbase S).mono' hkm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [Real.norm_of_nonneg (hk₀ s hs.1)]
    exact hkK s hs.1
  have hfirst : (∫ s in (0 : ℝ)..h, k s) ≤ ∫ s in (0 : ℝ)..h, hestonKernel α s := by
    rw [intervalIntegral.integral_of_le hh, intervalIntegral.integral_of_le hh]
    exact integral_mono_ae (hki h) (hbase h) (hK h)
  have hinc := nonnegative_decreasing_kernel_abs_increment hT hh hk₀ hk
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (add_nonneg hT hh)).2 (hki _))
  have hsum := add_le_add hfirst (hinc.trans hfirst)
  rw [hestonKernel_integral hα hh] at hsum
  convert hsum using 1
  ring

/-- The explicit absolute-increment bound for the fractional kernel itself. -/
theorem hestonKernel_increment_L1 {α T h : ℝ}
    (hα : 0 < α) (hα' : α ≤ 1) (hT : 0 ≤ T) (hh : 0 ≤ h) :
    (∫ s in (0 : ℝ)..h, hestonKernel α s) +
        (∫ s in (0 : ℝ)..T, |hestonKernel α (s + h) - hestonKernel α s|) ≤
      (2 / (Real.Gamma α * α)) * h ^ α :=
  heston_dominated_kernel_increment_L1 hα hT hh (hestonKernel_measurable α)
    (hestonKernel_nonnegative hα) (hestonKernel_decreasing hα hα') (fun _ _ => le_rfl)

/-- Euler's gamma integral gives the positive Laplace-mixture formula. -/
theorem hestonKernel_laplace_integral {α t : ℝ} (hα : 0 < α) (hα' : α < 1) (ht : 0 < t) :
    hestonKernel α t = ∫ x in Ioi (0 : ℝ),
      Real.exp (-(x * t)) * (x ^ (-α) / (Real.Gamma α * Real.Gamma (1 - α))) := by
  have hΓ : Real.Gamma (1 - α) ≠ 0 := (Real.Gamma_pos_of_pos (sub_pos.mpr hα')).ne'
  have hr := Real.integral_rpow_mul_exp_neg_mul_Ioi (sub_pos.mpr hα') ht
  have hg : (fun x : ℝ => Real.exp (-(x * t)) * (x ^ (-α) / (Real.Gamma α * Real.Gamma (1 - α)))) =
      fun x => (x ^ ((1 - α) - 1) * Real.exp (-(t * x))) / (Real.Gamma α * Real.Gamma (1 - α)) := by
    funext x
    rw [show 1 - α - 1 = -α by ring, mul_comm x t]
    ring
  rw [hg, integral_div, hr, hestonKernel, ite_eq_left ht, one_div, ← Real.rpow_neg_eq_inv_rpow,
    show -(1 - α) = α - 1 by ring]
  field_simp [hΓ, (Real.Gamma_pos_of_pos hα).ne']

/-- A nonnegative finite exponential mixture is measurable, nonnegative,
and decreasing. -/
theorem positive_exponential_mixture_properties {ι : Type*} (F : Finset ι) (c x : ι → ℝ)
    (hc : ∀ i ∈ F, 0 ≤ c i) (hx : ∀ i ∈ F, 0 ≤ x i) :
    let k (s : ℝ) := ∑ i ∈ F, c i * Real.exp (-(x i * s))
    Continuous k ∧ (∀ s, 0 ≤ k s) ∧ Antitone k := by
  dsimp only
  refine ⟨continuous_finsetSum F (fun i _ => continuous_const.mul
    (continuous_const.mul continuous_id).neg.rexp), ?_, ?_⟩
  · intro s
    exact Finset.sum_nonneg fun i hi => mul_nonneg (hc i hi) (Real.exp_pos _).le
  · intro s t hst
    refine Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hc i hi)
    exact neg_le_neg (mul_le_mul_of_nonneg_left hst (hx i hi))

/-- The inverse convolutions of dominated approximating kernels lie in
`[0,1]` and tend to one at every strictly positive time. -/
theorem fractionalL_convolution_approximation {α t : ℝ} {k : ℕ → ℝ → ℝ}
    (hα : 0 < α) (hα' : α < 1) (ht : 0 < t)
    (hkm : ∀ n, Measurable (k n)) (hk₀ : ∀ n s, 0 < s → 0 ≤ k n s)
    (hkK : ∀ n s, 0 < s → k n s ≤ hestonKernel α s)
    (hconv : ∀ s > 0, Tendsto (fun n => k n s) atTop (𝓝 (hestonKernel α s))) :
    (∀ n, volterraConvolution (fractionalL α) (k n) t ∈ Icc (0 : ℝ) 1) ∧
      Tendsto (fun n => volterraConvolution (fractionalL α) (k n) t) atTop (𝓝 1) := by
  let ν := volume.restrict (Ioc (0 : ℝ) t)
  let L (s : ℝ) := fractionalL α (t - s)
  let b (s : ℝ) := L s * hestonKernel α s
  let f (n : ℕ) (s : ℝ) := L s * k n s
  have hkEq : hestonKernel α = fractionalK α := by
    funext s
    by_cases hs : s ≤ 0
    · simp [hestonKernel, fractionalK, hs, not_lt.mpr hs]
    · simp [hestonKernel, fractionalK, hs, lt_of_not_ge hs]
  have hB : (∫ s, b s ∂ν) = 1 := by
    change volterraConvolution (fractionalL α) (hestonKernel α) t = 1
    rw [hkEq, fractional_causal_kernel_inverse hα hα' ht]
  have hBi : Integrable b ν := by
    by_contra hi
    rw [integral_undef hi] at hB
    norm_num at hB
  have hLm : Measurable L := (fractionalL_measurable α).comp (measurable_const.sub measurable_id)
  have hL₀ (s : ℝ) : 0 ≤ L s := by
    change 0 ≤ fractionalL α (t - s)
    by_cases hs : t - s ≤ 0
    · rw [fractionalL, ite_eq_left hs]
    · rw [fractionalL, ite_eq_right hs]
      exact div_nonneg (Real.rpow_nonneg (le_of_lt (lt_of_not_ge hs)) _)
        (Real.Gamma_pos_of_pos (sub_pos.mpr hα')).le
  have hf₀ (n : ℕ) : ∀ᵐ s ∂ν, 0 ≤ f n s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact mul_nonneg (hL₀ s) (hk₀ n s hs.1)
  have hfb (n : ℕ) : ∀ᵐ s ∂ν, f n s ≤ b s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact mul_le_mul_of_nonneg_left (hkK n s hs.1) (hL₀ s)
  have hfm (n : ℕ) : AEStronglyMeasurable (f n) ν := (hLm.mul (hkm n)).aestronglyMeasurable
  have hnorm (n : ℕ) : ∀ᵐ s ∂ν, ‖f n s‖ ≤ b s := by
    filter_upwards [hf₀ n, hfb n] with s hs hs'
    rwa [Real.norm_of_nonneg hs]
  refine ⟨fun n => ⟨integral_nonneg_of_ae (hf₀ n), ?_⟩, ?_⟩
  · change (∫ s, f n s ∂ν) ≤ 1
    rw [← hB]
    exact integral_mono_ae (hBi.mono' (hfm n) (hnorm n)) hBi (hfb n)
  · have hlim : ∀ᵐ s ∂ν, Tendsto (fun n => f n s) atTop (𝓝 (b s)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact tendsto_const_nhds.mul (hconv s hs.1)
    rw [← hB]
    exact tendsto_integral_filter_of_dominated_convergence b
      (Eventually.of_forall hfm) (Eventually.of_forall hnorm) hBi hlim

end RoughHeston

#print axioms RoughHeston.nonnegative_decreasing_kernel_sq_increment
#print axioms RoughHeston.hestonKernel_integral_sq
#print axioms RoughHeston.heston_dominated_kernel_increment_L2
#print axioms RoughHeston.hestonKernel_increment_L2

#print axioms RoughHeston.nonnegative_decreasing_kernel_abs_increment
#print axioms RoughHeston.hestonKernel_integral
#print axioms RoughHeston.heston_dominated_kernel_increment_L1
#print axioms RoughHeston.hestonKernel_increment_L1

#print axioms RoughHeston.hestonKernel_laplace_integral
#print axioms RoughHeston.positive_exponential_mixture_properties
#print axioms RoughHeston.fractionalL_convolution_approximation
