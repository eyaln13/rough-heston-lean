import RiccatiPointLocal
import RiccatiDifferential
import FractionalKernelSemigroup
import BanachHestonInversion

open MeasureTheory Set Filter
open scoped Topology Interval NNReal

namespace RoughHeston

private theorem continuation_fractionalK_nonneg {α : ℝ} (hα : 0 < α) (s : ℝ) :
    0 ≤ fractionalK α s := by
  by_cases hs : s ≤ 0
  · simp [fractionalK, hs]
  · rw [fractionalK, ite_eq_right hs]
    exact div_nonneg (Real.rpow_nonneg (lt_of_not_ge hs).le _)
      (Real.Gamma_pos_of_pos hα).le

private theorem continuation_fractionalK_integrable {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t) :
    IntegrableOn (fun s => fractionalK α (t-s)) (Ioc 0 t) := by
  have h := ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr
    (fractionalK_integrableOn_Ioc hα t)).symm.comp_sub_left t
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp (by
    simpa only [sub_zero, sub_self] using h)

private theorem continuation_fractionalK_mass {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t) :
    (∫ s in Ioc (0 : ℝ) t, fractionalK α (t-s)) = t^α / Real.Gamma (α+1) := by
  rcases eq_or_lt_of_le ht with he | hp
  · subst t
    simp [Real.zero_rpow hα.ne']
  have h := fractionalK_convolution_add hα (show (0 : ℝ) < 1 from zero_lt_one) hp
  have he (s : ℝ) (hs : s ∈ Ioc 0 t) : fractionalK α (t-s) =
      fractionalK α (t-s) * fractionalK 1 s := by
    have hu : fractionalK 1 s = 1 := by simp [fractionalK, not_le.mpr hs.1, Real.Gamma_one]
    rw [hu, mul_one]
  rw [setIntegral_congr_fun measurableSet_Ioc he]
  change volterraConvolution (fractionalK α) (fractionalK 1) t = _
  rw [h, fractionalK, ite_eq_right (not_le.mpr hp), add_sub_cancel_right]

private theorem continuation_integrable_mul_bounded {α t : ℝ} {f : ℝ → ℝ}
    (hα : 0 < α) (ht : 0 ≤ t) (hf : Measurable f)
    {B : ℝ} (hb : ∀ s ∈ Ioc 0 t, ‖f s‖ ≤ B) :
    IntegrableOn (fun s => fractionalK α (t-s)*f s) (Ioc 0 t) := by
  have hi := (continuation_fractionalK_integrable hα ht).norm.mul_const B
  have hm : Measurable (fun s => fractionalK α (t-s)*f s) :=
    ((fractionalK_measurable α).comp (measurable_const.sub measurable_id)).mul hf
  refine hi.mono' hm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hb s hs) (norm_nonneg _)

private theorem continuation_convolution_difference_norm {α t : ℝ} {f g : ℝ → ℝ}
    (hα : 0 < α) (ht : 0 ≤ t) (hf : Measurable f) (hg : Measurable g)
    {F G D : ℝ}
    (hF : ∀ s ∈ Ioc 0 t, ‖f s‖ ≤ F) (hG : ∀ s ∈ Ioc 0 t, ‖g s‖ ≤ G)
    (hD : ∀ s ∈ Ioc 0 t, ‖f s-g s‖ ≤ D) :
    ‖volterraConvolution (fractionalK α) f t - volterraConvolution (fractionalK α) g t‖
      ≤ (t^α / Real.Gamma (α+1))*D := by
  let k (s : ℝ) := fractionalK α (t-s)
  have hfi := continuation_integrable_mul_bounded hα ht hf hF
  have hgi := continuation_integrable_mul_bounded hα ht hg hG
  unfold volterraConvolution
  rw [← integral_sub hfi hgi, ← continuation_fractionalK_mass hα ht, ← integral_mul_const]
  refine (norm_integral_le_integral_norm _).trans
    (setIntegral_mono_on (hfi.sub hgi).norm
      ((continuation_fractionalK_integrable hα ht).mul_const D) measurableSet_Ioc ?_)
  intro s hs
  change ‖k s*f s-k s*g s‖ ≤ k s*D
  rw [← mul_sub, norm_mul, Real.norm_of_nonneg (continuation_fractionalK_nonneg hα _)]
  exact mul_le_mul_of_nonneg_left (hD s hs) (continuation_fractionalK_nonneg hα _)

private noncomputable def continuation_clip (R x : ℝ) : ℝ := max (-R) (min x R)

private theorem continuation_clip_lipschitz (R : ℝ) : LipschitzWith 1 (continuation_clip R) :=
  (LipschitzWith.id.min_const R).const_max (-R)

private theorem continuation_clip_abs {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    ‖continuation_clip R x‖ ≤ R := by
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

private theorem continuation_clip_eq {R x : ℝ} (h : ‖x‖ ≤ R) : continuation_clip R x = x := by
  rw [Real.norm_eq_abs, abs_le] at h
  simp only [continuation_clip, min_eq_left h.2, max_eq_right h.1]

private theorem continuation_polynomial_lipschitz {b c R x y : ℝ}
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    ‖(b*x+c*x^2)-(b*y+c*y^2)‖ ≤ (‖b‖+2*‖c‖*R)*‖x-y‖ := by
  rw [show (b*x+c*x^2)-(b*y+c*y^2) = b*(x-y)+c*((x+y)*(x-y)) by ring]
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul]
  have hxy : ‖x+y‖ ≤ 2*R := (norm_add_le _ _).trans ((add_le_add hx hy).trans_eq (by ring))
  calc
    _ ≤ ‖b‖*‖x-y‖+‖c‖*((2*R)*‖x-y‖) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hxy (norm_nonneg _)) (norm_nonneg _))
    _ = _ := by ring

/-- Existence on a prescribed small interval for the Riccati equation
with a continuous forcing term. The interval criterion depends only
on the forcing bound and the drift coefficients. -/
theorem exists_forced_riccati_on_small_interval
    {α d b c B : ℝ} {A : ℝ → ℝ}
    (hα : 0 < α) (hd : 0 < d) (hB : 0 ≤ B)
    (hAc : ContinuousOn A (Icc 0 d))
    (hAb : ∀ s ∈ Icc 0 d, ‖A s‖ ≤ B)
    (hsmall : (‖b‖+2*‖c‖*(2*B+1))*(d^α/Real.Gamma (α+1)) ≤ 1/2) :
    ∃ y : ℝ → ℝ, Continuous y ∧ (∀ s, ‖y s‖ ≤ 2*B) ∧
      ∀ t ∈ Icc 0 d, y t = A t +
        volterraConvolution (fractionalK α) (fun s => b*y s+c*y s^2) t := by
  let R := 2*B+1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  let L := ‖b‖+2*‖c‖*R
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let X := C(Icc (0 : ℝ) d, ℝ)
  let G (φ : X) (s : ℝ) := continuation_clip R (riccatiTimeExtension hd.le φ s)
  let Q (φ : X) (s : ℝ) := b*G φ s+c*(G φ s)^2
  have hGc (φ : X) : Continuous (G φ) :=
    (continuation_clip_lipschitz R).continuous.comp (continuous_riccatiTimeExtension hd.le φ)
  have hQc (φ : X) : Continuous (Q φ) :=
    (continuous_const.mul (hGc φ)).add (continuous_const.mul ((hGc φ).pow 2))
  have hQb (φ : X) (s : ℝ) : ‖Q φ s‖ ≤ ‖b‖*R+‖c‖*R^2 := by
    have hx := continuation_clip_abs hR (riccatiTimeExtension hd.le φ s)
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_pow]
    exact add_le_add (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx 2) (norm_nonneg _))
  have hQlip (φ ψ : X) (s : ℝ) : ‖Q φ s-Q ψ s‖ ≤ L*‖φ-ψ‖ := by
    have hclip : ‖G φ s-G ψ s‖ ≤ ‖riccatiTimeExtension hd.le φ s-riccatiTimeExtension hd.le ψ s‖ := by
      simpa only [G, dist_eq_norm, NNReal.coe_one, one_mul] using
        (continuation_clip_lipschitz R).dist_le_mul (riccatiTimeExtension hd.le φ s)
          (riccatiTimeExtension hd.le ψ s)
    have hnorm : ‖riccatiTimeExtension hd.le φ s-riccatiTimeExtension hd.le ψ s‖ ≤ ‖φ-ψ‖ :=
      ContinuousMap.norm_coe_le_norm (φ-ψ) _
    exact (continuation_polynomial_lipschitz (continuation_clip_abs hR _) (continuation_clip_abs hR _)).trans
      (mul_le_mul_of_nonneg_left (hclip.trans hnorm) hL)
  have hVc (φ : X) : ContinuousOn (volterraConvolution (fractionalK α) (Q φ)) (Icc 0 d) := by
    have he : volterraSmulConvolution (fractionalK α) (Q φ) =
        volterraConvolution (fractionalK α) (Q φ) := by
      funext t
      simp only [volterraSmulConvolution, volterraConvolution, smul_eq_mul]
    rw [← he]
    exact continuousOn_volterra_forcing hd.le (fractionalK_measurable α)
      (fractionalK_integrableOn_Ioc hα d) (hQc φ).continuousOn
  let P (φ : X) : X :=
    ⟨fun t => A t + volterraConvolution (fractionalK α) (Q φ) t, (hAc.add (hVc φ)).domRestrict⟩
  have hlip (φ ψ : X) : ‖P φ-P ψ‖ ≤ (1/2)*‖φ-ψ‖ := by
    refine (ContinuousMap.norm_le _ (by positivity)).mpr ?_
    intro t
    have h := continuation_convolution_difference_norm hα t.property.1 (hQc φ).measurable
      (hQc ψ).measurable (fun s _ => hQb φ s) (fun s _ => hQb ψ s) (fun s _ => hQlip φ ψ s)
    change ‖(A t+volterraConvolution (fractionalK α) (Q φ) t)-
      (A t+volterraConvolution (fractionalK α) (Q ψ) t)‖ ≤ _
    rw [add_sub_add_left_eq_sub]
    calc
      _ ≤ (t.val^α/Real.Gamma (α+1))*(L*‖φ-ψ‖) := h
      _ ≤ (d^α/Real.Gamma (α+1))*(L*‖φ-ψ‖) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hL (norm_nonneg _))
        exact div_le_div_of_nonneg_right (Real.rpow_le_rpow t.property.1 t.property.2 hα.le)
          (Real.Gamma_pos_of_pos (by linarith)).le
      _ = (L*(d^α/Real.Gamma (α+1)))*‖φ-ψ‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
  have hP : ContractingWith (1/2 : ℝ≥0) P := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun φ ψ => ?_⟩
    have h := hlip φ ψ
    rw [← dist_eq_norm (P φ) (P ψ), ← dist_eq_norm φ ψ] at h
    simpa only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using h
  let φ := ContractingWith.fixedPoint P hP
  have hfixed : P φ = φ := hP.fixedPoint_isFixedPt
  have hP0 : ‖P 0‖ ≤ B := by
    refine (ContinuousMap.norm_le _ hB).mpr ?_
    intro t
    have ht : Q 0 = 0 := by
      funext s
      have hz : riccatiTimeExtension hd.le (0 : X) s = 0 := rfl
      have hh : continuation_clip R 0 = 0 := continuation_clip_eq (by simpa only [norm_zero] using hR)
      simp [Q, G, hz, hh]
    change ‖A t+volterraConvolution (fractionalK α) (Q 0) t‖ ≤ B
    simpa only [ht, volterraConvolution, Pi.zero_apply, mul_zero, integral_zero, add_zero]
      using hAb t t.property
  have hφb : ‖φ‖ ≤ 2*B := by
    have hh : ‖φ‖ ≤ (1/2)*‖φ‖+B := by
      calc
        ‖φ‖ = ‖P φ-P 0+P 0‖ := by rw [sub_add_cancel, hfixed]
        _ ≤ ‖P φ-P 0‖+‖P 0‖ := norm_add_le _ _
        _ ≤ _ := add_le_add (by simpa only [sub_zero] using hlip φ 0) hP0
    linarith
  let y := riccatiTimeExtension hd.le φ
  have hyb (s : ℝ) : ‖y s‖ ≤ 2*B := (ContinuousMap.norm_coe_le_norm φ _).trans hφb
  refine ⟨y, continuous_riccatiTimeExtension hd.le φ, hyb, ?_⟩
  intro t ht
  have he := congrArg (fun k : X => k ⟨t,ht⟩) hfixed.symm
  have hy : y t = φ ⟨t,ht⟩ := riccatiTimeExtension_apply_of_mem hd.le φ ⟨t,ht⟩
  have hQ : Q φ = fun s => b*y s+c*(y s)^2 := by
    funext s
    have hcl : continuation_clip R (y s) = y s :=
      continuation_clip_eq ((hyb s).trans (by dsimp [R]; linarith))
    change b*continuation_clip R (y s)+c*(continuation_clip R (y s))^2 = _
    rw [hcl]
  rw [hy]
  change φ ⟨t,ht⟩ = A t+volterraConvolution (fractionalK α) (Q φ) t at he
  rwa [hQ] at he

/-- A continuous forcing on a compact positive-time interval has a
local Riccati solution starting at the forcing's initial value. -/
theorem exists_local_forced_riccati {α b c H : ℝ} {A : ℝ → ℝ}
    (hα : 0 < α) (hH : 0 < H) (hAc : ContinuousOn A (Icc 0 H)) :
    ∃ d ∈ Ioc (0 : ℝ) H, ∃ y : ℝ → ℝ, Continuous y ∧
      ∀ t ∈ Icc 0 d, y t = A t +
        volterraConvolution (fractionalK α) (fun s => b*y s+c*y s^2) t := by
  obtain ⟨B₀, hB₀⟩ := isCompact_Icc.bddAbove_image hAc.norm
  let B := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  let L := ‖b‖+2*‖c‖*(2*B+1)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hΓ : 0 < Real.Gamma (α+1) := Real.Gamma_pos_of_pos (by linarith)
  obtain ⟨d, hd, hs⟩ := exists_small_fractional_riccati_scale
    (κ := L/Real.Gamma (α+1)) hα hH (show 0 < (1/2 : ℝ) by norm_num)
  rw [Real.norm_of_nonneg (div_nonneg hL hΓ.le)] at hs
  have hsmall : L*(d^α/Real.Gamma (α+1)) ≤ 1/2 :=
    (show L*(d^α/Real.Gamma (α+1)) = (L/Real.Gamma (α+1))*d^α by ring).trans_le hs.le
  have hsub : Icc (0 : ℝ) d ⊆ Icc 0 H := Icc_subset_Icc_right hd.2
  obtain ⟨y, hy, _, he⟩ := exists_forced_riccati_on_small_interval hα hd.1 hB (hAc.mono hsub)
    (fun s hs => (hB₀ ⟨s, hsub hs, rfl⟩).trans (le_max_left _ _)) hsmall
  exact ⟨d, hd, y, hy, he⟩

private theorem continuation_fractionalK_decreasing {α x y : ℝ}
    (hα : 0 < α) (hα' : α < 1) (hx : 0 < x) (hxy : x ≤ y) :
    fractionalK α y ≤ fractionalK α x := by
  rw [show fractionalK α y = y^(α-1)/Real.Gamma α from ite_eq_right (not_le.mpr (hx.trans_le hxy)),
    show fractionalK α x = x^(α-1)/Real.Gamma α from ite_eq_right (not_le.mpr hx)]
  exact div_le_div_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos hx hxy (by linarith)) (Real.Gamma_pos_of_pos hα).le

private theorem continuation_fractionalK_continuousAt {α x : ℝ} (hx : 0 < x) :
    ContinuousAt (fractionalK α) x := by
  apply ((Real.continuousAt_rpow_const x (α-1) (Or.inl hx.ne')).div_const (Real.Gamma α)).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with s hs
  exact ite_eq_right (not_le.mpr (show 0 < s from hs))

private theorem continuation_old_drift_integrable {α a : ℝ} {f : ℝ → ℝ}
    (hα : 0 < α) (hα' : α < 1) (ha : 0 < a) (hf : Measurable f)
    (hi : IntegrableOn f (Ioc 0 a)) (hc : ContinuousOn f (Ioc 0 a)) :
    IntegrableOn (fun s => fractionalK α (a-s)*f s) (Ioc 0 a) := by
  let d := a/2
  have hd : 0 < d := by dsimp [d]; positivity
  have hda : d ≤ a := by dsimp [d]; linarith
  let k (s : ℝ) := fractionalK α (a-s)
  have hm : Measurable (fun s => k s*f s) :=
    ((fractionalK_measurable α).comp (measurable_const.sub measurable_id)).mul hf
  have hI₁ : IntegrableOn (fun s => k s*f s) (Ioc 0 d) := by
    refine ((hi.mono_set (Ioc_subset_Ioc_right hda)).norm.const_mul (fractionalK α (a-d))).mono'
      hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hpos : 0 < a-d := by dsimp [d]; linarith
    have hle := continuation_fractionalK_decreasing hα hα' hpos (sub_le_sub_left hs.2 a)
    dsimp only [k]
    rw [norm_mul, Real.norm_of_nonneg (continuation_fractionalK_nonneg hα _)]
    exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)
  have hI₂ : IntegrableOn (fun s => k s*f s) (Ioc d a) := by
    obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image
      (hc.mono (show Icc d a ⊆ Ioc 0 a from fun _ hs => ⟨hd.trans_le hs.1, hs.2⟩)).norm
    have hK : IntegrableOn k (Ioc d a) :=
      (continuation_fractionalK_integrable hα ha.le).mono_set (Ioc_subset_Ioc_left hd.le)
    refine (hK.norm.mul_const B).mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB ⟨s, Ioc_subset_Icc_self hs, rfl⟩) (norm_nonneg _)
  rw [← Ioc_union_Ioc_eq_Ioc hd.le hda]
  exact hI₁.union hI₂

/-- The contribution of the charge and the known history at a
positive time `a`, expressed in the new elapsed-time coordinate. -/
noncomputable def riccatiShiftedHistory (α q a : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  q*fractionalK α (a+t) + ∫ s in Ioc (0 : ℝ) a, fractionalK α (a+t-s)*f s

/-- The translated old history is continuous up to the new initial
time, even if its drift has an integrable singularity at the original charge. -/
theorem continuousOn_riccatiShiftedHistory {α q a H : ℝ} {f : ℝ → ℝ}
    (hα : 0 < α) (hα' : α < 1) (ha : 0 < a) (hf : Measurable f)
    (hi : IntegrableOn f (Ioc 0 a)) (hc : ContinuousOn f (Ioc 0 a)) :
    ContinuousOn (riccatiShiftedHistory α q a f) (Icc 0 H) := by
  let ν := volume.restrict (Ioc 0 a)
  let F (x s : ℝ) := fractionalK α (a+x-s)*f s
  let B (s : ℝ) := fractionalK α (a-s)*‖f s‖
  have hb : Integrable B ν := by
    have hI := continuation_old_drift_integrable hα hα' ha hf hi hc
    refine hI.norm.congr (ae_of_all _ fun s => ?_)
    change ‖fractionalK α (a-s)*f s‖ = _
    rw [norm_mul, Real.norm_of_nonneg (continuation_fractionalK_nonneg hα _)]
  have hFm (x : ℝ) : Measurable (F x) :=
    ((fractionalK_measurable α).comp (measurable_const.sub measurable_id)).mul hf
  have hae : ∀ᵐ s ∂ν, s ∈ Ioo 0 a := by
    unfold ν
    rw [← restrict_Ioo_eq_restrict_Ioc]
    exact ae_restrict_mem measurableSet_Ioo
  intro t ht
  have hI : ContinuousWithinAt (fun x => ∫ s, F x s ∂ν) (Icc 0 H) t := by
    refine continuousWithinAt_of_dominated
      (Eventually.of_forall fun x => (hFm x).aestronglyMeasurable) ?_ hb ?_
    · filter_upwards [self_mem_nhdsWithin] with x hx
      filter_upwards [hae] with s hs
      have hxs : a-s ≤ a+x-s := by linarith [show 0 ≤ x from hx.1]
      have h := continuation_fractionalK_decreasing hα hα' (sub_pos.mpr hs.2) hxs
      change ‖fractionalK α (a+x-s)*f s‖ ≤ B s
      rw [norm_mul, Real.norm_of_nonneg (continuation_fractionalK_nonneg hα _)]
      exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
    · filter_upwards [hae] with s hs
      have hp : 0 < a+t-s := by linarith [ht.1, hs.2]
      have hInner : ContinuousAt (fun x : ℝ => a+x-s) t :=
        (continuous_const.add continuous_id).sub continuous_const |>.continuousAt
      have hK := ContinuousAt.comp' (f := fun x : ℝ => a+x-s)
        (continuation_fractionalK_continuousAt (α := α) hp) hInner
      exact (hK.mul continuousAt_const).continuousWithinAt
  have hp : 0 < a+t := by linarith [ht.1]
  have hInner : ContinuousAt (fun x : ℝ => a+x) t := (continuous_const.add continuous_id).continuousAt
  have hK := ContinuousAt.comp'
    (f := fun x : ℝ => a+x) (continuation_fractionalK_continuousAt (α := α) hp) hInner
  exact (continuousAt_const.mul hK).continuousWithinAt.add hI

/-- In the new time coordinate, the prehistory of a point-charge
solution supplies a continuous forcing and determines the value at zero. -/
theorem exists_shifted_point_charge_continuation
    {α q b c a H : ℝ} {w : ℝ → ℝ}
    (hα : 0 < α) (hα' : α < 1) (ha : 0 < a) (hH : 0 < H) (hm : Measurable w)
    (hc : ContinuousOn w (Ioc 0 a))
    (hi : IntegrableOn (fun s => b*w s+c*w s^2) (Ioc 0 a))
    (hvol : ∀ s ∈ Ioc 0 a, w s = q*fractionalK α s +
      volterraConvolution (fractionalK α) (fun u => b*w u+c*w u^2) s) :
    ∃ d ∈ Ioc (0 : ℝ) H, ∃ y : ℝ → ℝ, Continuous y ∧ y 0 = w a ∧
      ∀ t ∈ Icc 0 d, y t = riccatiShiftedHistory α q a (fun s => b*w s+c*w s^2) t +
        volterraConvolution (fractionalK α) (fun s => b*y s+c*y s^2) t := by
  have hf : Measurable (fun s => b*w s+c*w s^2) := (hm.const_mul b).add ((hm.pow_const 2).const_mul c)
  have hfC : ContinuousOn (fun s => b*w s+c*w s^2) (Ioc 0 a) :=
    (continuousOn_const.mul hc).add (continuousOn_const.mul (hc.pow 2))
  have hHist := continuousOn_riccatiShiftedHistory (q := q) (H := H) hα hα' ha hf hi hfC
  obtain ⟨d, hd, y, hy, he⟩ := exists_local_forced_riccati (b := b) (c := c) hα hH hHist
  refine ⟨d, hd, y, hy, ?_, he⟩
  rw [he 0 ⟨le_rfl, hd.1.le⟩, hvol a ⟨ha, le_rfl⟩]
  simp [riccatiShiftedHistory, volterraConvolution]

private theorem continuation_glue_continuousOn_pos {a : ℝ} {w y : ℝ → ℝ}
    (ha : 0 < a) (hw : ContinuousOn w (Ioc 0 a)) (hy : Continuous y) (hstart : y 0 = w a) :
    ContinuousOn (fun t => if t ≤ a then w t else y (t-a)) (Ioi 0) := by
  let W (t : ℝ) := if t ≤ a then w t else y (t-a)
  have hLeft {d : ℝ} (hd : 0 < d) : ContinuousOn W (Icc d a) :=
    (hw.mono (show Icc d a ⊆ Ioc 0 a from fun _ hs => ⟨hd.trans_le hs.1, hs.2⟩)).congr
      (fun s hs => ite_eq_left hs.2)
  have hRight (L : ℝ) : ContinuousOn W (Icc a L) := by
    have hY : Continuous (fun t : ℝ => y (t-a)) := hy.comp (continuous_id.sub continuous_const)
    apply hY.continuousOn.congr
    intro t ht
    rcases eq_or_lt_of_le ht.1 with he | hlt
    · subst t
      simp [W, hstart]
    · exact ite_eq_right (not_le.mpr hlt)
  intro t ht
  have ht₀ : 0 < t := ht
  let d := min a t/2
  let L := max a t+1
  have hd : 0 < d := div_pos (lt_min ha ht₀) (by norm_num)
  have hdt : d < t := by
    dsimp [d]
    linarith [min_le_right a t]
  have hda : d ≤ a := by
    dsimp [d]
    linarith [min_le_left a t]
  have haL : a ≤ L := (le_max_left a t).trans (le_add_of_nonneg_right zero_le_one)
  have htL : t < L := (le_max_right a t).trans_lt (lt_add_one _)
  have he : ContinuousOn W (Icc d L) := by
    rw [← Icc_union_Icc_eq_Icc hda haL, continuousOn_union_iff_of_isClosed isClosed_Icc isClosed_Icc]
    exact ⟨hLeft hd, hRight L⟩
  exact (he.continuousAt (Icc_mem_nhds hdt htL)).continuousWithinAt

/-- Local continuation of a point-charge Riccati solution past any
positive time where the old drift is integrable and the old solution
is continuous up to the endpoint. The continued path agrees with the
entire old history and satisfies the original, unshifted equation. -/
theorem exists_point_charge_riccati_continuation
    {α q b c a H : ℝ} {w : ℝ → ℝ}
    (hα : 0 < α) (hα' : α < 1) (ha : 0 < a) (hH : 0 < H) (hm : Measurable w)
    (hc : ContinuousOn w (Ioc 0 a))
    (hi : IntegrableOn (fun s => b*w s+c*w s^2) (Ioc 0 a))
    (hvol : ∀ s ∈ Ioc 0 a, w s = q*fractionalK α s +
      volterraConvolution (fractionalK α) (fun u => b*w u+c*w u^2) s) :
    ∃ d ∈ Ioc (0 : ℝ) H, ∃ W : ℝ → ℝ, Measurable W ∧ ContinuousOn W (Ioi 0) ∧
      EqOn W w (Iic a) ∧
      ∀ s ∈ Ioc 0 (a+d), W s = q*fractionalK α s +
        volterraConvolution (fractionalK α) (fun u => b*W u+c*W u^2) s := by
  obtain ⟨d, hd, y, hy, hy₀, hyVol⟩ :=
    exists_shifted_point_charge_continuation hα hα' ha hH hm hc hi hvol
  let W (s : ℝ) := if s ≤ a then w s else y (s-a)
  have hEq (s : ℝ) (hs : s ≤ a) : W s = w s := ite_eq_left hs
  have hEq' (s : ℝ) (hs : a < s) : W s = y (s-a) := ite_eq_right (not_le.mpr hs)
  have hY : Continuous (fun s => y (s-a)) := hy.comp (continuous_id.sub continuous_const)
  have hWm : Measurable W := Measurable.ite measurableSet_Iic hm hY.measurable
  have hWc : ContinuousOn W (Ioi 0) := continuation_glue_continuousOn_pos ha hc hy hy₀
  refine ⟨d, hd, W, hWm, hWc, fun s hs => hEq s hs, ?_⟩
  intro t ht
  by_cases hta : t ≤ a
  · rw [hEq t hta, hvol t ⟨ht.1, hta⟩]
    congr 1
    unfold volterraConvolution
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    simp only [hEq s (hs.2.trans hta)]
  · have hAt : a<t := lt_of_not_ge hta
    have hA : a+(t-a)=t := by ring
    have htd : t-a ∈ Icc 0 d := ⟨sub_nonneg.mpr hAt.le, by linarith [ht.2]⟩
    let f (s : ℝ) := b*w s+c*w s^2
    let fy (s : ℝ) := b*y s+c*y s^2
    let K (s : ℝ) := fractionalK α (t-s)
    let F (s : ℝ) := K s*(b*W s+c*W s^2)
    have hfm : Measurable f := (hm.const_mul b).add ((hm.pow_const 2).const_mul c)
    have hfc : ContinuousOn f (Ioc 0 a) :=
      (continuousOn_const.mul hc).add (continuousOn_const.mul (hc.pow 2))
    have hKm : Measurable K := (fractionalK_measurable α).comp (measurable_const.sub measurable_id)
    have hFm : Measurable F := hKm.mul ((hWm.const_mul b).add ((hWm.pow_const 2).const_mul c))
    have hOldA := continuation_old_drift_integrable hα hα' ha hfm hi hfc
    have hOld : IntegrableOn F (Ioc 0 a) := by
      refine hOldA.norm.mono' hFm.aestronglyMeasurable ?_
      have hae : ∀ᵐ s ∂volume.restrict (Ioc 0 a), s ∈ Ioo 0 a := by
        rw [← restrict_Ioo_eq_restrict_Ioc]
        exact ae_restrict_mem measurableSet_Ioo
      filter_upwards [hae] with s hs
      have hsA : 0 < a-s := sub_pos.mpr hs.2
      have hK := continuation_fractionalK_decreasing hα hα' hsA (sub_le_sub_right hAt.le s)
      change ‖fractionalK α (t-s)*(b*W s+c*W s^2)‖ ≤ ‖fractionalK α (a-s)*f s‖
      rw [hEq s hs.2.le, norm_mul, norm_mul,
        Real.norm_of_nonneg (continuation_fractionalK_nonneg hα (t-s)),
        Real.norm_of_nonneg (continuation_fractionalK_nonneg hα (a-s))]
      exact mul_le_mul_of_nonneg_right hK (norm_nonneg _)
    have hfy : Continuous fy :=
      (continuous_const.mul hy).add (continuous_const.mul (hy.pow 2))
    obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hfy.continuousOn.norm (K := Icc (0 : ℝ) d)
    have hK : IntegrableOn K (Ioc a t) :=
      (continuation_fractionalK_integrable hα ht.1.le).mono_set (Ioc_subset_Ioc_left ha.le)
    have hNew : IntegrableOn F (Ioc a t) := by
      refine (hK.norm.mul_const B).mono' hFm.aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hsd : s-a ∈ Icc 0 d := ⟨sub_nonneg.mpr hs.1.le, by linarith [hs.2, ht.2]⟩
      change ‖K s*(b*W s+c*W s^2)‖ ≤ ‖K s‖*B
      rw [norm_mul, hEq' s hs.1]
      exact mul_le_mul_of_nonneg_left (hB ⟨s-a, hsd, rfl⟩) (norm_nonneg _)
    have hOldEq :
        (∫ s in Ioc (0 : ℝ) a, fractionalK α (t-s)*f s) = ∫ s in Ioc (0 : ℝ) a, F s := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      simp only [F, K, f, hEq s hs.2]
    have hShift :
        volterraConvolution (fractionalK α) fy (t-a) = ∫ s in Ioc a t, F s := by
      let J (s : ℝ) := K s*fy (s-a)
      have he := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := t-a) J a
      simp only [zero_add, sub_add_cancel] at he
      have h₁ : volterraConvolution (fractionalK α) fy (t-a) = ∫ s in a..t, J s := by
        unfold volterraConvolution
        rw [← intervalIntegral.integral_of_le htd.1, ← he]
        apply intervalIntegral.integral_congr
        intro s _
        change fractionalK α (t-a-s)*fy s = fractionalK α (t-(s+a))*fy ((s+a)-a)
        rw [show t-a-s=t-(s+a) by ring, add_sub_cancel_right]
      rw [h₁, intervalIntegral.integral_of_le hAt.le]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      simp only [J, F, fy, hEq' s hs.1]
    have hsplit : (∫ s in Ioc (0 : ℝ) a, F s) + (∫ s in Ioc a t, F s) =
        ∫ s in Ioc (0 : ℝ) t, F s := by
      have he := intervalIntegral.integral_add_adjacent_intervals
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).mpr hOld)
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hAt.le).mpr hNew)
      simpa only [intervalIntegral.integral_of_le ha.le, intervalIntegral.integral_of_le hAt.le,
        intervalIntegral.integral_of_le ht.1.le] using he
    calc
      W t = y (t-a) := hEq' t hAt
      _ = q*fractionalK α t + (∫ s in Ioc (0 : ℝ) a, F s) + ∫ s in Ioc a t, F s := by
        rw [hyVol (t-a) htd, riccatiShiftedHistory, hA]
        change q*fractionalK α t + (∫ s in Ioc (0 : ℝ) a, fractionalK α (t-s)*f s) +
          volterraConvolution (fractionalK α) fy (t-a) = _
        rw [hOldEq, hShift]
      _ = _ := by rw [add_assoc, hsplit]; rfl

#print axioms exists_forced_riccati_on_small_interval
#print axioms continuousOn_riccatiShiftedHistory
#print axioms exists_shifted_point_charge_continuation
#print axioms exists_point_charge_riccati_continuation

end RoughHeston
