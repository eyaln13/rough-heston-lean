import FractionalKernelL1
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

open Set Filter MeasureTheory
open scoped Topology Interval NNReal

namespace RoughHeston

private noncomputable def marchaudKernel (α u : ℝ) : ℝ :=
  α * u ^ (-α - 1) / Real.Gamma (1 - α)

private theorem marchaudKernel_measurable (α : ℝ) : Measurable (marchaudKernel α) :=
  ((measurable_id.pow_const _).const_mul _).div_const _

private theorem fractionalL_nonnegative {α : ℝ} (hα : α < 1) {u : ℝ} (hu : 0 < u) :
    0 ≤ fractionalL α u := by
  unfold fractionalL
  rw [ite_eq_right (not_le.mpr hu)]
  exact div_nonneg (Real.rpow_nonneg hu.le _) (Real.Gamma_pos_of_pos (by linarith)).le

private theorem marchaudKernel_nonnegative {α : ℝ} (hα : 0 ≤ α) (hα' : α < 1)
    {u : ℝ} (hu : 0 < u) : 0 ≤ marchaudKernel α u :=
  div_nonneg (mul_nonneg hα (Real.rpow_nonneg hu.le _))
    (Real.Gamma_pos_of_pos (by linarith)).le

private theorem hasDerivAt_fractionalL_pos {α u : ℝ} (hu : 0 < u) :
    HasDerivAt (fractionalL α) (-marchaudKernel α u) u := by
  have hd := (Real.hasDerivAt_rpow_const (x := u) (p := -α) (Or.inl hu.ne')).div_const
    (Real.Gamma (1 - α))
  have hd' : HasDerivAt (fun x => x ^ (-α) / Real.Gamma (1 - α)) (-marchaudKernel α u) u := by
    simpa only [marchaudKernel, neg_mul, neg_div] using hd
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hu] with s hs
  exact ite_eq_right (not_le.mpr (show 0 < s from hs))

private theorem marchaudKernel_mul_self {α u : ℝ} (hu : 0 < u) :
    marchaudKernel α u * u = α * fractionalL α u := by
  have hp : u ^ (-α - 1) * u = u ^ (-α) := by
    calc
      _ = u ^ (-α - 1) * u ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hu, sub_add_cancel]
  rw [fractionalL, ite_eq_right (not_le.mpr hu), marchaudKernel, ← hp]
  ring

private theorem fractionalL_mul_self {α u : ℝ} (hu : 0 < u) :
    fractionalL α u * u = u ^ (1 - α) / Real.Gamma (1 - α) := by
  have hp : u ^ (-α) * u = u ^ (1 - α) := by
    calc
      _ = u ^ (-α) * u ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hu, neg_add_eq_sub]
  rw [fractionalL, ite_eq_right (not_le.mpr hu), ← hp]
  ring

private theorem norm_sub_of_lipschitz_time {g : ℝ → ℝ} {K : ℝ≥0}
    (hK : LipschitzWith K g) (t : ℝ) {u : ℝ} (hu : 0 < u) :
    ‖g t - g (t - u)‖ ≤ (K : ℝ) * u := by
  simpa only [dist_eq_norm, sub_sub_cancel, Real.norm_of_nonneg hu.le] using
    hK.dist_le_mul t (t - u)

/-- Integration by parts in the reflected history variable, including the
vanishing boundary term at the singular endpoint. -/
private theorem marchaud_integral_of_deriv {α t : ℝ} {g : ℝ → ℝ} {K : ℝ≥0}
    (hα : 0 < α) (hα' : α < 1) (ht : 0 < t)
    (hg : ContDiff ℝ 1 g) (hK : LipschitzWith K g) (hg0 : g 0 = 0) :
    IntervalIntegrable (fun u => marchaudKernel α u * (g t - g (t - u))) volume 0 t ∧
    (∫ u in (0 : ℝ)..t, fractionalL α u * deriv g (t - u)) = fractionalMemory α 0 g t := by
  have hd : ∀ x, HasDerivAt g (deriv g x) x := fun x => (hg.differentiable one_ne_zero x).hasDerivAt
  have hc : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  have hΓ : 0 < Real.Gamma (1 - α) := Real.Gamma_pos_of_pos (by linarith)
  have hK₀ : 0 ≤ (K : ℝ) := NNReal.zero_le_coe
  let Δ (u : ℝ) := g t - g (t - u)
  have hΔ (u : ℝ) : HasDerivAt Δ (deriv g (t - u)) u := by
    have hh := (hasDerivAt_const u (g t)).sub
      ((hd (t-u)).comp u ((hasDerivAt_const u t).sub (hasDerivAt_id u)))
    change HasDerivAt (fun v => g t - g (t-v)) (0 - deriv g (t-u) * (0 - 1)) u at hh
    simpa [Δ] using hh
  have hL := fractionalL_integrableOn_Ioc hα' t
  have hP : IntervalIntegrable (fun u => fractionalL α u * deriv g (t-u)) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
    refine (hL.mul_const (K : ℝ)).mono'
      (((fractionalL_measurable α).mul (hc.measurable.comp (measurable_const.sub measurable_id)))
        |>.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [norm_mul, Real.norm_of_nonneg (fractionalL_nonnegative hα' hu.1)]
    exact mul_le_mul_of_nonneg_left (norm_deriv_le_of_lipschitz hK) (fractionalL_nonnegative hα' hu.1)
  have hD : IntervalIntegrable (fun u => marchaudKernel α u * Δ u) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
    have hm : Measurable (fun u => marchaudKernel α u * Δ u) :=
      (marchaudKernel_measurable α).mul (measurable_const.sub
        (hg.continuous.measurable.comp (measurable_const.sub measurable_id)))
    refine (hL.mul_const (α * (K : ℝ))).mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [norm_mul, Real.norm_of_nonneg (marchaudKernel_nonnegative hα.le hα' hu.1)]
    calc
      _ ≤ marchaudKernel α u * ((K : ℝ) * u) :=
        mul_le_mul_of_nonneg_left (norm_sub_of_lipschitz_time hK t hu.1)
          (marchaudKernel_nonnegative hα.le hα' hu.1)
      _ = (marchaudKernel α u * u) * (K : ℝ) := by ring
      _ = _ := by rw [marchaudKernel_mul_self hu.1]; ring
  have hnear : Tendsto (fun u => fractionalL α u * Δ u) (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    have hb : Tendsto (fun u : ℝ => ((K : ℝ) / Real.Gamma (1 - α)) * u ^ (1 - α))
        (𝓝[>] 0) (𝓝 0) := by
      have hh : ContinuousAt (fun u : ℝ => ((K : ℝ) / Real.Gamma (1 - α)) * u ^ (1 - α)) 0 :=
        (continuous_const.mul (Real.continuous_rpow_const (by linarith))).continuousAt
      simpa only [Real.zero_rpow (by linarith : 1 - α ≠ 0), mul_zero] using
        hh.tendsto.mono_left nhdsWithin_le_nhds
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hb
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu' : 0 < u := hu
    rw [norm_mul, Real.norm_of_nonneg (fractionalL_nonnegative hα' hu')]
    calc
      _ ≤ fractionalL α u * ((K : ℝ) * u) :=
        mul_le_mul_of_nonneg_left (norm_sub_of_lipschitz_time hK t hu')
          (fractionalL_nonnegative hα' hu')
      _ = (fractionalL α u * u) * (K : ℝ) := by ring
      _ = _ := by rw [fractionalL_mul_self hu']; ring
  have hfar : Tendsto (fun u => fractionalL α u * Δ u) (𝓝[<] t)
      (𝓝 (fractionalL α t * Δ t)) :=
    (((hasDerivAt_fractionalL_pos ht).mul (hΔ t)).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hprod (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) t) :
      HasDerivAt (fun u => fractionalL α u * Δ u)
        (fractionalL α u * deriv g (t - u) - marchaudKernel α u * Δ u) u := by
    convert (hasDerivAt_fractionalL_pos hu.1).mul (hΔ u) using 1; ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto ht hprod (hP.sub hD) hnear hfar
  change (∫ u in (0 : ℝ)..t, fractionalL α u * deriv g (t - u) - marchaudKernel α u * Δ u) = _ at he
  rw [intervalIntegral.integral_sub hP hD, sub_zero] at he
  have hcL : fractionalL α t * Δ t = g t * (t ^ (-α) / Real.Gamma (1 - α)) := by
    simp [Δ, hg0, fractionalL, not_le.mpr ht, mul_comm]
  rw [hcL] at he
  refine ⟨hD, ?_⟩
  unfold fractionalMemory
  change (∫ u in (0 : ℝ)..t, fractionalL α u * deriv g (t - u)) =
    (g t - 0) * (t ^ (-α) / Real.Gamma (1 - α)) +
      ∫ u in (0 : ℝ)..t, marchaudKernel α u * Δ u
  rw [sub_zero]
  linarith only [he]

/-- Genuine Marchaud memory formula for smooth causal functions. -/
theorem fractional_rl_hasDerivAt_memory_of_causal_C1 {α t : ℝ} {g : ℝ → ℝ} {K : ℝ≥0}
    (hα : 0 < α) (hα' : α < 1) (ht : 0 < t)
    (hg : ContDiff ℝ 1 g) (hK : LipschitzWith K g) (hz : ∀ s ≤ 0, g s = 0) :
    IntervalIntegrable (fun u => marchaudKernel α u * (g t - g (t - u))) volume 0 t ∧
    HasDerivAt (volterraConvolution (fractionalL α) g) (fractionalMemory α 0 g t) t := by
  have hc : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  let d := t + 1
  let ν := volume.restrict (Ioc 0 d)
  let F (x u : ℝ) := fractionalL α u * g (x-u)
  let F' (x u : ℝ) := fractionalL α u * deriv g (x-u)
  have hL : Integrable (fractionalL α) ν := fractionalL_integrableOn_Ioc hα' d
  have hFm (x : ℝ) : Measurable (F x) :=
    (fractionalL_measurable α).mul (hg.continuous.measurable.comp (measurable_const.sub measurable_id))
  have hF'm (x : ℝ) : Measurable (F' x) :=
    (fractionalL_measurable α).mul (hc.measurable.comp (measurable_const.sub measurable_id))
  have hFit : Integrable (F t) ν := by
    refine (hL.mul_const (‖g t‖ + (K : ℝ) * d)).mono' (hFm t).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hb : ‖g (t-u)‖ ≤ ‖g t‖ + (K : ℝ) * d := by
      calc
        _ = ‖g t + -(g t - g (t-u))‖ := by congr 1; ring
        _ ≤ ‖g t‖ + ‖g t - g (t-u)‖ := by
          simpa only [norm_neg] using norm_add_le (g t) (-(g t - g (t-u)))
        _ ≤ _ := add_le_add le_rfl
          ((norm_sub_of_lipschitz_time hK t hu.1).trans (mul_le_mul_of_nonneg_left hu.2 NNReal.zero_le_coe))
    unfold F
    rw [norm_mul, Real.norm_of_nonneg (fractionalL_nonnegative hα' hu.1)]
    exact mul_le_mul_of_nonneg_left hb (fractionalL_nonnegative hα' hu.1)
  have hdom : ∀ᵐ u ∂ν, ∀ x ∈ (univ : Set ℝ), ‖F' x u‖ ≤ fractionalL α u * (K : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu x _
    unfold F'
    rw [norm_mul, Real.norm_of_nonneg (fractionalL_nonnegative hα' hu.1)]
    exact mul_le_mul_of_nonneg_left (norm_deriv_le_of_lipschitz hK) (fractionalL_nonnegative hα' hu.1)
  have hdiff : ∀ᵐ u ∂ν, ∀ x ∈ (univ : Set ℝ), HasDerivAt (fun x => F x u) (F' x u) x := by
    refine ae_of_all _ fun u x _ => ?_
    have hgx := (hg.differentiable one_ne_zero (x-u)).hasDerivAt
    have hh := (hgx.comp x ((hasDerivAt_id x).sub_const u)).const_mul (fractionalL α u)
    change HasDerivAt (fun y => fractionalL α u * g (y-u))
      (fractionalL α u * (deriv g (x-u) * 1)) x at hh
    simpa only [F, F', mul_one] using hh
  have hD := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := univ)
    univ_mem (Eventually.of_forall fun x => (hFm x).aestronglyMeasurable)
    hFit (hF'm t).aestronglyMeasurable hdom (hL.mul_const (K : ℝ)) hdiff).2
  have heq (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) d) :
      volterraConvolution (fractionalL α) g x = ∫ u, F x u ∂ν := by
    unfold volterraConvolution
    rw [← intervalIntegral.integral_of_le hx.1.le]
    have hrefl := intervalIntegral.integral_comp_sub_left (a := 0) (b := x) (F x) x
    have hsub : Ioc (0 : ℝ) x ⊆ Ioc 0 d := Ioc_subset_Ioc_right hx.2.le
    have hext := setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (μ := volume) (f := F x) measurableSet_Ioc hsub (by
        intro u hu
        have hxu : x ≤ u := le_of_not_gt fun h => hu.2 ⟨hu.1.1, h.le⟩
        simp [F, hz _ (sub_nonpos.mpr hxu)])
    have hflip : (∫ s in (0 : ℝ)..x, fractionalL α (x-s) * g s) = ∫ u in Ioc 0 x, F x u := by
      simpa only [F, sub_sub_cancel, sub_self, sub_zero, intervalIntegral.integral_of_le hx.1.le] using
        hrefl
    exact hflip.trans hext.symm
  have hEq' : (∫ u, F' t u ∂ν) =
      ∫ u in (0 : ℝ)..t, fractionalL α u * deriv g (t - u) := by
    rw [intervalIntegral.integral_of_le ht.le]
    change (∫ u in Ioc (0 : ℝ) d, F' t u) = ∫ u in Ioc (0 : ℝ) t, F' t u
    have hsub : Ioc (0 : ℝ) t ⊆ Ioc 0 d := Ioc_subset_Ioc_right (by dsimp [d]; linarith)
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc hsub
    intro u hu
    have hu' : t < u := lt_of_not_ge fun h => hu.2 ⟨hu.1.1, h⟩
    have hd₀ : HasDerivAt g 0 (t-u) := by
      refine (hasDerivAt_const (t-u) (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds (sub_neg.mpr hu')] with y hy
      exact hz y (le_of_lt hy)
    simp only [F', hd₀.deriv, mul_zero]
  have hm := marchaud_integral_of_deriv hα hα' ht hg hK (hz 0 le_rfl)
  refine ⟨hm.1, ?_⟩
  rw [hEq', hm.2] at hD
  apply hD.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht (show t < d by dsimp [d]; linarith)] with x hx
  exact heq x hx

private theorem fractionalL_decreasing_pos {α x y : ℝ} (hα : 0 < α) (hα' : α < 1)
    (hx : 0 < x) (hxy : x ≤ y) : fractionalL α y ≤ fractionalL α x := by
  have hy := hx.trans_le hxy
  simp only [fractionalL, ite_eq_right (not_le.mpr hx), ite_eq_right (not_le.mpr hy)]
  exact div_le_div_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos hx hxy (neg_nonpos.mpr hα.le))
    (Real.Gamma_pos_of_pos (by linarith)).le

private theorem marchaudKernel_decreasing_pos {α x y : ℝ} (hα : 0 < α) (hα' : α < 1)
    (hx : 0 < x) (hxy : x ≤ y) : marchaudKernel α y ≤ marchaudKernel α x := by
  unfold marchaudKernel
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hx hxy (by linarith)) hα.le)
    (Real.Gamma_pos_of_pos (by linarith)).le

/-- Marchaud identification for history supported away from the contact
time. Only measurability and integrability of the old history are required. -/
theorem fractional_rl_hasDerivAt_memory_of_inactive_recent {α a b t : ℝ} {g : ℝ → ℝ}
    (hα : 0 < α) (hα' : α < 1) (ha : 0 ≤ a) (hat : a < t) (hbt : t < b)
    (hg : Measurable g) (hI : IntegrableOn g (Ioc 0 a))
    (hz : ∀ x ∈ Ioo a b, g x = 0) :
    IntervalIntegrable (fun u => marchaudKernel α u * (g t - g (t-u))) volume 0 t ∧
    HasDerivAt (volterraConvolution (fractionalL α) g) (fractionalMemory α 0 g t) t := by
  let d := (t - a) / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have htd : a + d < t := by dsimp [d]; linarith
  have ht := ha.trans_lt hat
  let ν := volume.restrict (Ioc 0 a)
  let F (x u : ℝ) := fractionalL α (x-u) * g u
  let D (x u : ℝ) := -marchaudKernel α (x-u) * g u
  have hFm (x : ℝ) : Measurable (F x) :=
    ((fractionalL_measurable α).comp (measurable_const.sub measurable_id)).mul hg
  have hDm (x : ℝ) : Measurable (D x) :=
    (((marchaudKernel_measurable α).comp (measurable_const.sub measurable_id)).neg).mul hg
  have hFint : Integrable (F t) ν := by
    refine (hI.norm.const_mul (fractionalL α d)).mono' (hFm t).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hdu : d ≤ t-u := by linarith [hu.2]
    unfold F
    rw [norm_mul, Real.norm_of_nonneg (fractionalL_nonnegative hα' (hd.trans_le hdu))]
    exact mul_le_mul_of_nonneg_right (fractionalL_decreasing_pos hα hα' hd hdu) (norm_nonneg _)
  have hdom : ∀ᵐ u ∂ν, ∀ x ∈ Ioo (a+d) b,
      ‖D x u‖ ≤ marchaudKernel α d * ‖g u‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu x hx
    have hdu : d ≤ x-u := by linarith [hu.2, hx.1]
    unfold D
    rw [norm_mul, norm_neg, Real.norm_of_nonneg (marchaudKernel_nonnegative hα.le hα' (hd.trans_le hdu))]
    exact mul_le_mul_of_nonneg_right (marchaudKernel_decreasing_pos hα hα' hd hdu) (norm_nonneg _)
  have hdiff : ∀ᵐ u ∂ν, ∀ x ∈ Ioo (a+d) b, HasDerivAt (fun x => F x u) (D x u) x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu x hx
    have hxu : 0 < x-u := by linarith [hu.2, hx.1]
    have hh := ((hasDerivAt_fractionalL_pos (α := α) hxu).comp x
      ((hasDerivAt_id x).sub_const u)).mul_const (g u)
    change HasDerivAt (fun y => fractionalL α (y-u) * g u)
      ((-marchaudKernel α (x-u) * 1) * g u) x at hh
    simpa only [F, D, mul_one] using hh
  obtain ⟨hDint, hD⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds htd hbt) (Eventually.of_forall fun x => (hFm x).aestronglyMeasurable)
    hFint (hDm t).aestronglyMeasurable hdom (hI.norm.const_mul (marchaudKernel α d)) hdiff
  have hzero {x u : ℝ} (hx : x ∈ Ioo (a+d) b) (hu : u ∈ Ioc (0 : ℝ) x \ Ioc 0 a) : g u = 0 :=
    hz u ⟨lt_of_not_ge (fun hua => hu.2 ⟨hu.1.1, hua⟩), hu.1.2.trans_lt hx.2⟩
  have hEq (x : ℝ) (hx : x ∈ Ioo (a+d) b) :
      volterraConvolution (fractionalL α) g x = ∫ u, F x u ∂ν := by
    have hax : a ≤ x := by linarith [hx.1]
    have hsub : Ioc (0 : ℝ) a ⊆ Ioc 0 x := Ioc_subset_Ioc_right hax
    exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc hsub
      (fun u hu => by simp [hzero hx hu])
  have hDext : IntegrableOn (D t) (Ioc 0 t) := by
    have hInd : Integrable ((Ioc (0 : ℝ) a).indicator (D t)) volume :=
      (integrable_indicator_iff measurableSet_Ioc).mpr hDint
    refine hInd.restrict.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    by_cases h : u ∈ Ioc (0 : ℝ) a
    · rw [indicator_of_mem h]
    · rw [indicator_of_notMem h]
      simp [D, hzero ⟨htd, hbt⟩ ⟨hu, h⟩]
  have hDinterval : IntervalIntegrable (D t) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mpr hDext
  have hg0 := hz t ⟨hat, hbt⟩
  have heqRef (u : ℝ) : D t (t-u) = marchaudKernel α u * (g t - g (t-u)) := by
    simp only [D, sub_sub_cancel, hg0, zero_sub, neg_mul, mul_neg]
  have hI' := hDinterval.symm.comp_sub_left t
  simp only [sub_self, sub_zero, heqRef] at hI'
  have hMemory : (∫ u, D t u ∂ν) = fractionalMemory α 0 g t := by
    have hsub : Ioc (0 : ℝ) a ⊆ Ioc 0 t := Ioc_subset_Ioc_right hat.le
    have hext := setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (μ := volume) (f := D t) measurableSet_Ioc hsub
      (fun u hu => by simp [D, hzero ⟨htd, hbt⟩ hu])
    have hrefl := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := t) (D t) t
    simp only [sub_self, sub_zero, heqRef] at hrefl
    unfold fractionalMemory
    change (∫ u in Ioc (0 : ℝ) a, D t u) = (g t - 0) * _ +
      ∫ u in (0 : ℝ)..t, marchaudKernel α u * (g t - g (t-u))
    rw [hrefl, hg0, sub_zero, zero_mul, zero_add, intervalIntegral.integral_of_le ht.le]
    exact hext.symm
  refine ⟨hI', ?_⟩
  rw [hMemory] at hD
  apply hD.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds htd hbt] with x hx
  exact hEq x hx

private theorem integrableOn_fractionalL_mul_bounded {α x : ℝ} {f : ℝ → ℝ}
    (hα : α < 1) (hx : 0 ≤ x) (hm : Measurable f)
    {B : ℝ} (hb : ∀ u ∈ Ioc (0 : ℝ) x, ‖f u‖ ≤ B) :
    IntegrableOn (fun u => fractionalL α (x-u) * f u) (Ioc 0 x) := by
  have hi := (fractionalL_reflected_integrableOn_Ioc hα hx).norm.mul_const B
  have hmeas : Measurable (fun u => fractionalL α (x-u) * f u) :=
    ((fractionalL_measurable α).comp (measurable_const.sub measurable_id)).mul hm
  refine hi.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hb u hu) (norm_nonneg _)

private theorem integrableOn_fractionalL_mul_old_history {α a b x : ℝ} {f : ℝ → ℝ}
    (hα : 0 < α) (hα' : α < 1) (hax : a < x) (hxb : x < b)
    (hm : Measurable f) (hi : IntegrableOn f (Ioc 0 a)) (hz : ∀ u ∈ Ioo a b, f u = 0) :
    IntegrableOn (fun u => fractionalL α (x-u) * f u) (Ioc 0 x) := by
  let F (u : ℝ) := fractionalL α (x-u) * f u
  have hmeas : Measurable F :=
    ((fractionalL_measurable α).comp (measurable_const.sub measurable_id)).mul hm
  have hF : IntegrableOn F (Ioc 0 a) := by
    refine (hi.norm.const_mul (fractionalL α (x-a))).mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hpos := sub_pos.mpr (hu.2.trans_lt hax)
    change ‖fractionalL α (x-u) * f u‖ ≤ fractionalL α (x-a) * ‖f u‖
    rw [norm_mul, Real.norm_of_nonneg (fractionalL_nonnegative hα' hpos)]
    exact mul_le_mul_of_nonneg_right
      (fractionalL_decreasing_pos hα hα' (sub_pos.mpr hax) (sub_le_sub_left hu.2 x))
      (norm_nonneg _)
  have hInd : Integrable ((Ioc (0 : ℝ) a).indicator F) volume :=
    (integrable_indicator_iff measurableSet_Ioc).mpr hF
  refine hInd.restrict.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  by_cases hua : u ∈ Ioc (0 : ℝ) a
  · exact indicator_of_mem hua _
  · have hau : a < u := lt_of_not_ge (fun h => hua ⟨hu.1, h⟩)
    rw [indicator_of_notMem hua]
    simp [hz u ⟨hau, hu.2.trans_lt hxb⟩]

/-- The Marchaud memory formula for a locally C¹ function with integrable
past. The past may be singular at zero. -/
theorem fractional_rl_hasDerivAt_memory {α t : ℝ} {g : ℝ → ℝ}
    (hα : 0 < α) (hα' : α < 1) (ht : 0 < t)
    (hm : Measurable g) (hI : IntegrableOn g (Ioc 0 t)) (hc : ContDiffAt ℝ 1 g t) :
    IntervalIntegrable
      (fun u => (α * u ^ (-α - 1) / Real.Gamma (1 - α)) * (g t - g (t-u))) volume 0 t ∧
    HasDerivAt (volterraConvolution (fractionalL α) g) (fractionalMemory α 0 g t) t := by
  obtain ⟨r₀, hr₀, hloc⟩ := Metric.eventually_nhds_iff.mp (hc.eventually (by simp))
  let r := min r₀ t
  have hr : 0 < r := lt_min hr₀ ht
  let B : ContDiffBump t := ⟨r/4, r/2, by positivity, by linarith⟩
  let G (x : ℝ) := B x * g x
  let H (x : ℝ) := g x - G x
  have hBc : ContDiff ℝ 1 (B : ℝ → ℝ) := B.contDiff
  have hG : ContDiff ℝ 1 G := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : dist z t < r
    · exact hBc.contDiffAt.mul (hloc (hz.trans_le (min_le_left _ _)))
    · have hthin : B.rOut < dist z t := by dsimp [B]; linarith [le_of_not_gt hz]
      have hd : ∀ᶠ x in 𝓝 z, B.rOut < dist x t :=
        continuousAt_const.eventually_lt (continuousAt_id.dist continuousAt_const) hthin
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hd] with x hx
      simp [G, B.zero_of_le_dist hx.le]
  have hG0 : ∀ x ≤ 0, G x = 0 := by
    intro x hx
    have hxt : dist x t = t-x := by rw [Real.dist_eq, abs_of_nonpos (by linarith)]; ring
    have hb : B.rOut ≤ dist x t := by
      rw [hxt]
      dsimp [B]
      linarith [show r ≤ t from min_le_right _ _]
    simp [G, B.zero_of_le_dist hb]
  have hGcap : HasCompactSupport G := B.hasCompactSupport.mul_right (f' := g)
  have hGd : Continuous (deriv G) := hG.continuous_deriv (by norm_num)
  have hGdcap : IsCompact (tsupport (deriv G)) := hGcap.deriv
  obtain ⟨K₀, hK₀⟩ := hGdcap.bddAbove_image hGd.norm.continuousOn
  let K : ℝ≥0 := ⟨max K₀ 0, le_max_right _ _⟩
  have hKbound (x : ℝ) : ‖deriv G x‖ ≤ (K : ℝ) := by
    by_cases hx : x ∈ tsupport (deriv G)
    · exact (hK₀ ⟨x, hx, rfl⟩).trans (le_max_left _ _)
    · have hz : deriv G x = 0 := by
        by_contra! hn
        exact hx (subset_closure hn)
      simp only [hz, norm_zero, NNReal.zero_le_coe]
  have hGlip : LipschitzWith K G := by
    refine lipschitzWith_of_nnnorm_deriv_le (hG.differentiable one_ne_zero) (fun x => ?_)
    exact_mod_cast hKbound x
  let a := t-r/4
  let b := t+r/4
  have ha : 0 ≤ a := by dsimp [a]; linarith [show r ≤ t from min_le_right _ _]
  have hat : a < t := by dsimp [a]; linarith
  have htb : t < b := by dsimp [b]; linarith
  have hH0 (x : ℝ) (hx : x ∈ Ioo a b) : H x = 0 := by
    have hball : x ∈ Metric.closedBall t B.rIn := by
      rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
      change -(r/4) ≤ x-t ∧ x-t ≤ r/4
      have hleft : t-r/4 < x := hx.1
      have hright : x < t+r/4 := hx.2
      exact ⟨by linarith, by linarith⟩
    simp [H, G, B.one_of_mem_closedBall hball]
  have hHit : IntegrableOn H (Ioc 0 a) :=
    (hI.mono_set (Ioc_subset_Ioc_right hat.le)).sub (hG.continuous.intervalIntegrable 0 a).1
  have hHm : Measurable H := hm.sub hG.continuous.measurable
  obtain ⟨hGint, hGderiv⟩ := fractional_rl_hasDerivAt_memory_of_causal_C1 hα hα' ht hG hGlip hG0
  obtain ⟨hHint, hHderiv⟩ :=
    fractional_rl_hasDerivAt_memory_of_inactive_recent hα hα' ha hat htb hHm hHit hH0
  have hsum (u : ℝ) : marchaudKernel α u * (g t - g (t-u)) =
      marchaudKernel α u * (G t - G (t-u)) + marchaudKernel α u * (H t - H (t-u)) := by
    dsimp [H]
    ring
  have hmemory : fractionalMemory α 0 g t = fractionalMemory α 0 G t + fractionalMemory α 0 H t := by
    unfold fractionalMemory
    change (g t - 0) * _ + (∫ u in (0 : ℝ)..t, marchaudKernel α u * (g t - g (t-u))) =
      ((G t - 0) * _ + ∫ u in (0 : ℝ)..t, marchaudKernel α u * (G t - G (t-u))) +
      ((H t - 0) * _ + ∫ u in (0 : ℝ)..t, marchaudKernel α u * (H t - H (t-u)))
    simp_rw [hsum]
    rw [intervalIntegral.integral_add hGint hHint]
    dsimp [H]
    ring
  refine ⟨?_, ?_⟩
  · change IntervalIntegrable (fun u => marchaudKernel α u * (g t - g (t-u))) volume 0 t
    simp_rw [hsum]
    exact hGint.add hHint
  · have hd := hGderiv.add hHderiv
    rw [← hmemory] at hd
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hat htb] with x hx
    have hxt : 0 ≤ x := ha.trans (le_of_lt hx.1)
    obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hG.continuous.norm.continuousOn
      (K := Icc (0 : ℝ) x)
    have hG' := integrableOn_fractionalL_mul_bounded hα' hxt hG.continuous.measurable
      (fun u hu => hC ⟨u, Ioc_subset_Icc_self hu, rfl⟩)
    have hH' := integrableOn_fractionalL_mul_old_history hα hα' hx.1 hx.2 hHm hHit hH0
    change volterraConvolution (fractionalL α) g x =
      volterraConvolution (fractionalL α) G x + volterraConvolution (fractionalL α) H x
    unfold volterraConvolution
    rw [← integral_add hG' hH']
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u _
    dsimp [H]
    ring

theorem fractional_memory_integral_of_deriv {α t : ℝ} {g : ℝ → ℝ} {K : ℝ≥0}
    (hα : 0 < α) (hα' : α < 1) (ht : 0 < t)
    (hg : ContDiff ℝ 1 g) (hK : LipschitzWith K g) (hg0 : g 0 = 0) :
    (∫ u in (0 : ℝ)..t, fractionalL α u * deriv g (t - u)) = fractionalMemory α 0 g t :=
  (marchaud_integral_of_deriv hα hα' ht hg hK hg0).2

#print axioms fractional_memory_integral_of_deriv
#print axioms fractional_rl_hasDerivAt_memory_of_causal_C1
#print axioms fractional_rl_hasDerivAt_memory_of_inactive_recent
#print axioms fractional_rl_hasDerivAt_memory

end RoughHeston
