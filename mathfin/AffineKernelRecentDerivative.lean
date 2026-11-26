import RiccatiComparison
import FractionalKernelL1
import HistoryInputSplitting
import Mathlib.Analysis.Calculus.Deriv.Slope

open MeasureTheory Set Filter
open scoped Topology Interval NNReal

namespace RoughHeston

theorem right_increment_quotient_tendsto_of_hasDerivAt
    {f : ℝ → ℝ} {x d : ℝ} (hf : HasDerivAt f d x) :
    Tendsto (fun h => (f (x+h)-f x)/h) (𝓝[>] (0 : ℝ)) (𝓝 d) := by
  have hadd : HasDerivAt (fun h : ℝ => x+h) 1 0 := (hasDerivAt_id 0).const_add x
  have hcomp : HasDerivAt (fun h : ℝ => f (x+h)) d 0 := by
    have h := (show HasDerivAt f d (x+(0:ℝ)) by simpa only [add_zero] using hf).comp 0 hadd
    change HasDerivAt (fun z :ℝ => f (x+z)) (d*1) 0 at h
    simpa only [mul_one] using h
  have hs := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0:ℝ) ∉ Ioi 0)).mp
    hcomp.hasDerivWithinAt
  refine hs.congr' (Eventually.of_forall fun h => ?_)
  rw [slope_def_field, sub_zero, add_zero]

private theorem fractionalL_nonneg_for_affine {α : ℝ} (hα' : α < 1) (r : ℝ) :
    0 ≤ fractionalL α r := by
  by_cases hr : r ≤ 0
  · simp [fractionalL,hr]
  · rw [fractionalL,ite_eq_right hr]
    exact div_nonneg (Real.rpow_nonneg (lt_of_not_ge hr).le _) (Real.Gamma_pos_of_pos (by linarith)).le

private theorem fractionalL_antitone_pos_for_affine {α : ℝ} (hα : 0 < α)
    (hα' : α < 1) : AntitoneOn (fractionalL α) (Ioi 0) := by
  intro x hx y hy hxy
  have hx' : 0 < x := hx
  have hy' : 0 < y := hy
  simp only [fractionalL,ite_eq_right (not_le.mpr hx'),ite_eq_right (not_le.mpr hy')]
  exact div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hx' hxy (neg_nonpos.mpr hα.le))
    (Real.Gamma_pos_of_pos (by linarith)).le

private theorem fractionalL_continuousAt_for_affine {α x : ℝ} (hx : 0 < x) :
    ContinuousAt (fractionalL α) x := by
  refine ((Real.continuousAt_rpow_const x (-α) (Or.inl hx.ne')).div_const (Real.Gamma (1-α))).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hx] with y hy
  simp [fractionalL,not_le.mpr (show 0<y from hy)]

private theorem affine_recent_integral_lip_domination
    {α a y : ℝ} {w : ℝ → ℝ}
    (hα' : α < 1) (ha : 0 < a) (hay : a < y)
    (hw : ∀ x > 0, ContDiffAt ℝ 1 w x) :
    Tendsto (fun h => ((∫ s in Ioc a (y+h), fractionalL α (y+h-s)*w s) -
      (∫ s in Ioc a y, fractionalL α (y-s)*w s))/h)
      (𝓝[>] (0 : ℝ))
      (𝓝 (w a*fractionalL α (y-a) +
        ∫ r in Ioc (0 : ℝ) (y-a), fractionalL α r*deriv w (y-r))) := by
  let A := y+1
  let b := A-a
  have hyA : y < A := lt_add_one y
  have hA : a < A := hay.trans hyA
  have hb : 0 < b := sub_pos.mpr hA
  let c (x : ℝ) := max a (min A x)
  have hcm (x : ℝ) : c x ∈ Icc a A := ⟨le_max_left _ _,max_le hA.le (min_le_left _ _)⟩
  have hcc : Continuous c := continuous_const.max (continuous_const.min continuous_id)
  have hcL : LipschitzWith 1 c := by
    simpa only [c,id,min_comm] using (LipschitzWith.id.min_const A).const_max a
  have hca (x : ℝ) (hx : x ≤ a) : c x = a := by
    dsimp [c]
    rw [min_eq_right (hx.trans hA.le),max_eq_left hx]
  have hcx (x : ℝ) (hx : x ∈ Icc a A) : c x = x := by
    dsimp [c]
    rw [min_eq_right hx.2,max_eq_right hx.1]
  have hwOn : ContDiffOn ℝ 1 w (Ioi 0) := fun x hx => (hw x hx).contDiffWithinAt
  have hdOn : ContinuousOn (deriv w) (Ioi 0) :=
    hwOn.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
  have hsub : Icc a A ⊆ Ioi (0 : ℝ) := fun _ hx => ha.trans_le hx.1
  obtain ⟨C₀,hC₀⟩ := isCompact_Icc.bddAbove_image (hdOn.mono hsub).norm
  let C := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hBd (x : ℝ) (hx : x ∈ Icc a A) : ‖deriv w x‖ ≤ C :=
    (hC₀ ⟨x,hx,rfl⟩).trans (le_max_left _ _)
  let g (x : ℝ) := w (c x)-w a
  have hgc : Continuous g := ((hwOn.continuousOn.mono hsub).comp_continuous hcc hcm).sub continuous_const
  have hgZero (x : ℝ) (hx : x≤a) : g x = 0 := by simp [g,hca x hx]
  have hgx (x : ℝ) (hx : x ∈ Icc a A) : g x = w x-w a := by simp [g,hcx x hx]
  have hgl (x z : ℝ) : ‖g z-g x‖ ≤ C*‖z-x‖ := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun s hs => (hw s (hsub hs)).differentiableAt one_ne_zero)
      hBd (convex_Icc a A) (hcm x) (hcm z)
    have hcc' : ‖c z-c x‖ ≤ ‖z-x‖ := by
      simpa only [dist_eq_norm,NNReal.coe_one,one_mul] using hcL.dist_le_mul z x
    simpa only [g,sub_sub_sub_cancel_right] using h.trans (mul_le_mul_of_nonneg_left hcc' hC)
  let ν := volume.restrict (Ioc 0 b)
  let F (z r : ℝ) := fractionalL α r*g (z-r)
  let D (r : ℝ) := ((Iio (y-a)).indicator (fun r => fractionalL α r*deriv w (y-r))) r
  have hL : Integrable (fractionalL α) ν := fractionalL_integrableOn_Ioc hα' b
  have hFi (z : ℝ) : Integrable (F z) ν := by
    obtain ⟨K,hK⟩ := isCompact_Icc.bddAbove_image (K := Icc (0:ℝ) b)
      (hgc.comp (continuous_const.sub continuous_id)).continuousOn.norm
    refine (hL.norm.mul_const K).mono'
      ((fractionalL_measurable α).mul
        (hgc.measurable.comp (measurable_const.sub measurable_id))).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    change ‖fractionalL α r*g (z-r)‖ ≤ ‖fractionalL α r‖*K
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hK ⟨r,Ioc_subset_Icc_self hr,rfl⟩) (norm_nonneg _)
  have hDlim : ∀ᵐ r ∂ν,
      Tendsto (fun h => (F (y+h) r-F y r)/h) (𝓝[>] 0) (𝓝 (D r)) := by
    have hne : ∀ᵐ r ∂ν, r ≠ y-a := ae_mono Measure.restrict_le_self (volume.ae_ne _)
    filter_upwards [ae_restrict_mem measurableSet_Ioc,hne] with r hr hnr
    rcases lt_or_gt_of_ne hnr with hra | har
    · have hpos : a < y-r := by linarith
      have hA' : y-r < A := by linarith [hr.1]
      have hd : HasDerivAt g (deriv w (y-r)) (y-r) := by
        refine ((hw _ (ha.trans hpos)).differentiableAt one_ne_zero).hasDerivAt.sub_const
          (w a) |>.congr_of_eventuallyEq ?_
        filter_upwards [Ioo_mem_nhds hpos hA'] with s hs
        exact hgx s (Ioo_subset_Icc_self hs)
      have hfd : HasDerivAt (fun z => F z r) (D r) y := by
        have h := (hd.comp y ((hasDerivAt_id y).sub_const r)).const_mul (fractionalL α r)
        simpa only [F,D,Function.comp_apply, id, mul_one, indicator_of_mem (show r ∈ Iio (y-a) from hra)]
          using h
      exact right_increment_quotient_tendsto_of_hasDerivAt hfd
    · have hya : y-r < a := by linarith
      have hd : HasDerivAt g 0 (y-r) := by
        refine (hasDerivAt_const (y-r) (0:ℝ)).congr_of_eventuallyEq ?_
        filter_upwards [Iio_mem_nhds hya] with s hs
        exact hgZero s (show s<a from hs).le
      have hfd : HasDerivAt (fun z => F z r) (D r) y := by
        have h := (hd.comp y ((hasDerivAt_id y).sub_const r)).const_mul (fractionalL α r)
        simpa only [F,D,Function.comp_apply,id,mul_zero,mul_one, indicator_of_notMem (show r ∉ Iio (y-a) from
          not_lt.mpr har.le)] using h
      exact right_increment_quotient_tendsto_of_hasDerivAt hfd
  have hDivBound : ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ᵐ r ∂ν,
      ‖(F (y+h) r-F y r)/h‖ ≤ ‖fractionalL α r‖*C := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 < h := hh
    refine ae_of_all _ fun r => ?_
    dsimp [F]
    rw [← mul_sub,abs_div,abs_mul,abs_of_nonneg hh'.le]
    apply (div_le_iff₀ hh').mpr
    have hB := hgl (y-r) (y+h-r)
    rw [show y+h-r-(y-r)=h by ring,Real.norm_of_nonneg hh'.le] at hB
    simpa only [mul_assoc, Real.norm_eq_abs] using mul_le_mul_of_nonneg_left hB (norm_nonneg (fractionalL α r))
  have hM : ∀ᶠ h in 𝓝[>] (0:ℝ),
      AEStronglyMeasurable (fun r => (F (y+h) r-F y r)/h) ν :=
    Eventually.of_forall fun h => (((hFi (y+h)).sub (hFi y)).div_const h).aestronglyMeasurable
  have hFixed := tendsto_integral_filter_of_dominated_convergence
    (fun r => ‖fractionalL α r‖*C) hM hDivBound (hL.norm.mul_const C) hDlim
  let P (z : ℝ) := ∫ r, F z r ∂ν
  have hDQ : Tendsto (fun h => (P (y+h)-P y)/h) (𝓝[>] (0:ℝ)) (𝓝 (∫ r,D r ∂ν)) := by
    refine hFixed.congr' (Eventually.of_forall fun h => ?_)
    rw [integral_div,integral_sub (hFi (y+h)) (hFi y)]
  have hDIntegral : (∫ r,D r ∂ν) = ∫ r in Ioc (0 : ℝ) (y-a), fractionalL α r*deriv w (y-r) := by
    have hba : y-a < b := by dsimp [b]; linarith
    change (∫ r in Ioc (0:ℝ) b, (Iio (y-a)).indicator
      (fun r => fractionalL α r*deriv w (y-r)) r) = _
    rw [setIntegral_indicator measurableSet_Iio]
    have he : Ioc (0:ℝ) b ∩ Iio (y-a) = Ioo 0 (y-a) := by
      ext r
      exact ⟨fun h => ⟨h.1.1,h.2⟩,
        fun h => ⟨⟨h.1,h.2.le.trans hba.le⟩,h.2⟩⟩
    rw [he,restrict_Ioo_eq_restrict_Ioc]
  rw [hDIntegral] at hDQ
  let Q (z : ℝ) := ∫ r in (0:ℝ)..(z-a), fractionalL α r
  have hQd : HasDerivAt Q (fractionalL α (y-a)) y := by
    have hy' : 0 < y-a := sub_pos.mpr hay
    have hLi := (intervalIntegrable_iff_integrableOn_Ioc_of_le hy'.le).mpr
      (fractionalL_integrableOn_Ioc hα' (y-a))
    have hD := intervalIntegral.integral_hasDerivAt_right hLi
      (fractionalL_measurable α).aestronglyMeasurable.stronglyMeasurableAtFilter
      (fractionalL_continuousAt_for_affine hy')
    have h := hD.comp y ((hasDerivAt_id y).sub_const a)
    change HasDerivAt Q (fractionalL α (y-a)*1) y at h
    simpa only [mul_one] using h
  have hQ := right_increment_quotient_tendsto_of_hasDerivAt (hQd.const_mul (w a))
  have hRec (z : ℝ) (hz : z ∈ Ioo a A) :
      (∫ s in Ioc a z, fractionalL α (z-s)*w s) = w a*Q z+P z := by
    have hz' : 0 ≤ z-a := sub_nonneg.mpr hz.1.le
    let f (s : ℝ) := fractionalL α (z-s)*w s
    have hrefl := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := z-a) f z
    rw [sub_sub_cancel,sub_zero,intervalIntegral.integral_of_le hz.1.le,
      intervalIntegral.integral_of_le hz'] at hrefl
    change (∫ s in Ioc a z, f s) = _
    rw [← hrefl]
    have he : EqOn (fun r => f (z-r))
      (fun r => fractionalL α r*w a+F z r) (Ioc 0 (z-a)) := by
      intro r hr
      have hr' : z-r ∈ Icc a A := ⟨by linarith [hr.2],(sub_le_self z hr.1.le).trans hz.2.le⟩
      change fractionalL α (z-(z-r))*w (z-r) =
        fractionalL α r*w a+fractionalL α r*g (z-r)
      rw [sub_sub_cancel,hgx _ hr']
      ring
    rw [setIntegral_congr_fun measurableSet_Ioc he]
    have hs : Ioc (0:ℝ) (z-a) ⊆ Ioc 0 b :=
      Ioc_subset_Ioc_right (sub_le_sub_right hz.2.le a)
    have hOnL : IntegrableOn (fractionalL α) (Ioc 0 b) := hL
    have hOnF : IntegrableOn (F z) (Ioc 0 b) := hFi z
    have hsum : (∫ r in Ioc (0:ℝ) (z-a), fractionalL α r*w a+F z r) =
       (∫ r in Ioc (0:ℝ) (z-a),fractionalL α r*w a)+(∫ r in Ioc (0:ℝ) (z-a),F z r) :=
      integral_add ((hOnL.mono_set hs).mul_const _) (hOnF.mono_set hs)
    have hP : (∫ r in Ioc (0:ℝ) (z-a), F z r) = P z := by
      symm
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc hs
      intro r hr
      have hzr : z-r ≤ a := by
        by_contra! hh
        exact hr.2 ⟨hr.1.1,(by linarith : r ≤ z-a)⟩
      simp [F,hgZero _ hzr]
    rw [hsum,integral_mul_const,hP]
    unfold Q
    rw [intervalIntegral.integral_of_le hz',mul_comm (w a)]
  refine (hQ.add hDQ).congr' ?_
  have hevent : ∀ᶠ h in 𝓝[>] (0:ℝ), y+h ∈ Ioo a A := by
    have hadd : Continuous (fun h : ℝ => y+h) := continuous_const.add continuous_id
    apply nhdsWithin_le_nhds
    exact hadd.continuousAt.preimage_mem_nhds (Ioo_mem_nhds (by simpa using hay) (by simpa using hyA))
  filter_upwards [hevent] with h hh
  rw [hRec (y+h) hh,hRec y ⟨hay,hyA⟩]
  ring

/-- The inverse-variance preterminal coefficient dominates the derivative
of the full Riccati primitive. The remaining old-history correction is
nonnegative because the fractional L kernel is decreasing. -/
theorem affine_riccati_primitive_deriv_le_recent
    {α a y m : ℝ} {w : ℝ → ℝ}
    (hα : 0 < α) (hα' : α < 1) (ha : 0 < a) (hay : a < y)
    (hm : Measurable w) (hI : IntegrableOn w (Ioc 0 a))
    (hw : ∀ x > 0, ContDiffAt ℝ 1 w x)
    (hw₀ : ∀ x ∈ Ioc 0 a, 0 ≤ w x)
    (hDeriv : HasDerivAt (volterraConvolution (fractionalL α) w) m y) :
    m ≤ w a*fractionalL α (y-a) +
      ∫ r in Ioc (0 : ℝ) (y-a), fractionalL α r*deriv w (y-r) := by
  let P (z : ℝ) := volterraConvolution (fractionalL α) w z
  let J (z : ℝ) := ∫ s in Ioc (0:ℝ) a, fractionalL α (z-s)*w s
  let N (z : ℝ) := ∫ s in Ioc a z, fractionalL α (z-s)*w s
  have hInt (z : ℝ) (hz : a < z) : IntegrableOn (fun s => fractionalL α (z-s)*w s) (Ioc 0 a) := by
    refine (hI.norm.const_mul (fractionalL α (z-a))).mono'
      (((fractionalL_measurable α).comp (measurable_const.sub measurable_id)).mul hm).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [norm_mul, Real.norm_of_nonneg (fractionalL_nonneg_for_affine hα' _)]
    exact mul_le_mul_of_nonneg_right (fractionalL_antitone_pos_for_affine hα hα'
      (show 0 < z-a from sub_pos.mpr hz) (show 0 < z-s from sub_pos.mpr (hs.2.trans_lt hz))
      (sub_le_sub_left hs.2 z)) (norm_nonneg _)
  have hSplit (z : ℝ) (hz : a < z) : P z = J z+N z := by
    have hW : ContinuousOn w (Icc a z) := fun s hs =>
      (hw s (ha.trans_le hs.1)).continuousAt.continuousWithinAt
    obtain ⟨C,hC⟩ := isCompact_Icc.bddAbove_image hW.norm
    have hL := fractionalL_reflected_integrableOn_Ioc hα' (ha.trans hz).le
    have hNew : IntegrableOn (fun s => fractionalL α (z-s)*w s) (Ioc a z) := by
      refine ((hL.mono_set (Ioc_subset_Ioc_left ha.le)).norm.mul_const C).mono'
        (((fractionalL_measurable α).comp (measurable_const.sub measurable_id)).mul hm).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC ⟨s,Ioc_subset_Icc_self hs,rfl⟩) (norm_nonneg _)
    change (∫ s in Ioc (0:ℝ) z, fractionalL α (z-s)*w s) = _
    rw [← Ioc_union_Ioc_eq_Ioc ha.le hz.le,
      setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc (hInt z hz) hNew]
  have hJanti (x z : ℝ) (hx : a<x) (hxz : x≤z) : J z ≤ J x := by
    apply setIntegral_mono_on (hInt z (hx.trans_le hxz)) (hInt x hx) measurableSet_Ioc
    intro s hs
    have hxa : 0 < x-s := sub_pos.mpr (hs.2.trans_lt hx)
    have hza : 0 < z-s := hxa.trans_le (sub_le_sub_right hxz s)
    exact mul_le_mul_of_nonneg_right
      (fractionalL_antitone_pos_for_affine hα hα' hxa hza (sub_le_sub_right hxz s)) (hw₀ s hs)
  have hP := right_increment_quotient_tendsto_of_hasDerivAt hDeriv
  have hN := affine_recent_integral_lip_domination hα' ha hay hw
  refine le_of_tendsto_of_tendsto hP hN ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : 0 < h := hh
  have hyh : a < y+h := hay.trans (lt_add_of_pos_right y hh')
  change (P (y+h)-P y)/h ≤ (N (y+h)-N y)/h
  rw [hSplit (y+h) hyh,hSplit y hay]
  exact div_le_div_of_nonneg_right (by linarith [hJanti y (y+h) hay (le_add_of_nonneg_right hh'.le)]) hh'.le

/-- Exact separation of the differentiable recent convolution from
the old fractional Riccati history. -/
theorem affine_riccati_recent_coefficient_eq
    {α a y m : ℝ} {w : ℝ → ℝ}
    (hα : 0 < α) (hα' : α < 1) (ha : 0 < a) (hay : a < y)
    (hm : Measurable w) (hI : IntegrableOn w (Ioc 0 a))
    (hw : ∀ x > 0, ContDiffAt ℝ 1 w x)
    (hDeriv : HasDerivAt (volterraConvolution (fractionalL α) w) m y) :
    w a*fractionalL α (y-a) +
        (∫ r in Ioc (0 : ℝ) (y-a), fractionalL α r*deriv w (y-r)) =
      m + ∫ s in Ioc (0 : ℝ) a, fractionalHistoryDensity α (y-s)*w s := by
  let P (z : ℝ) := volterraConvolution (fractionalL α) w z
  let J (z : ℝ) := ∫ s in Ioc (0:ℝ) a, fractionalL α (z-s)*w s
  let N (z : ℝ) := ∫ s in Ioc a z, fractionalL α (z-s)*w s
  let ν := volume.restrict (Ioc (0:ℝ) a)
  let F (z s : ℝ) := fractionalL α (z-s)*w s
  let G (z s : ℝ) := -fractionalHistoryDensity α (z-s)*w s
  have hFm (z : ℝ) : Measurable (F z) :=
    ((fractionalL_measurable α).comp (measurable_const.sub measurable_id)).mul hm
  have hGm (z : ℝ) : Measurable (G z) := by
    have hHist : Measurable (fractionalHistoryDensity α) :=
      ((measurable_id.pow_const (-(1+α))).const_mul (α/Real.Gamma (1-α)))
    exact ((hHist.comp (measurable_const.sub measurable_id)).neg).mul hm
  have hInt (z : ℝ) (hz : a < z) : IntegrableOn (F z) (Ioc 0 a) := by
    refine (hI.norm.const_mul (fractionalL α (z-a))).mono' (hFm z).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    change ‖fractionalL α (z-s)*w s‖ ≤ _
    rw [norm_mul,Real.norm_of_nonneg (fractionalL_nonneg_for_affine hα' _)]
    exact mul_le_mul_of_nonneg_right (fractionalL_antitone_pos_for_affine hα hα'
      (show 0 < z-a from sub_pos.mpr hz) (show 0 < z-s from sub_pos.mpr (hs.2.trans_lt hz))
      (sub_le_sub_left hs.2 z)) (norm_nonneg _)
  have hSplit (z : ℝ) (hz : a < z) : P z = J z+N z := by
    have hW : ContinuousOn w (Icc a z) := fun s hs =>
      (hw s (ha.trans_le hs.1)).continuousAt.continuousWithinAt
    obtain ⟨C,hC⟩ := isCompact_Icc.bddAbove_image hW.norm
    have hL := fractionalL_reflected_integrableOn_Ioc hα' (ha.trans hz).le
    have hNew : IntegrableOn (F z) (Ioc a z) := by
      refine ((hL.mono_set (Ioc_subset_Ioc_left ha.le)).norm.mul_const C).mono'
        (hFm z).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      change ‖fractionalL α (z-s)*w s‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC ⟨s,Ioc_subset_Icc_self hs,rfl⟩) (norm_nonneg _)
    change (∫ s in Ioc (0:ℝ) z, F z s) = _
    rw [← Ioc_union_Ioc_eq_Ioc ha.le hz.le,
      setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc (hInt z hz) hNew]
  let c := (y-a)/2
  have hc : 0 < c := half_pos (sub_pos.mpr hay)
  have hRange : Ioi ((y+a)/2) ∈ 𝓝 y := Ioi_mem_nhds (by linarith)
  let B := fractionalHistoryDensity α c
  have hDerivBound : ∀ᵐ s ∂ν, ∀ z ∈ Ioi ((y+a)/2), ‖G z s‖ ≤ B*‖w s‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs z hz
    have hc' : c ≤ z-s := by dsimp [c]; linarith [hs.2,show (y+a)/2<z from hz]
    change ‖-fractionalHistoryDensity α (z-s)*w s‖ ≤ _
    rw [norm_mul,norm_neg,Real.norm_of_nonneg
      (fractionalHistoryDensity_nonneg hα.le hα' (hc.le.trans hc'))]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    dsimp [B,fractionalHistoryDensity]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hc hc' (by linarith))
      (div_nonneg hα.le (Real.Gamma_pos_of_pos (by linarith)).le)
  have hDerivFun : ∀ᵐ s ∂ν, ∀ z ∈ Ioi ((y+a)/2),
      HasDerivAt (fun x => F x s) (G z s) z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs z hz
    have hzs : 0 < z-s := by linarith [hs.2,show (y+a)/2<z from hz]
    have hh := ((hasDerivAt_fractionalL (α := α) hzs).comp z
      ((hasDerivAt_id z).sub_const s)).mul_const (w s)
    simpa only [F,G,Function.comp_apply,mul_one,id] using hh
  have hOld : HasDerivAt J (∫ s,G y s ∂ν) y :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le hRange
      (Eventually.of_forall fun z => (hFm z).aestronglyMeasurable)
      (hInt y hay) (hGm y).aestronglyMeasurable hDerivBound
      (hI.norm.const_mul B) hDerivFun).2
  have hQ := right_increment_quotient_tendsto_of_hasDerivAt hDeriv
  have hJ := right_increment_quotient_tendsto_of_hasDerivAt hOld
  have hN := affine_recent_integral_lip_domination hα' ha hay hw
  have hF := (hJ.add hN).congr' (show
      (fun h => (J (y+h)-J y)/h+(N (y+h)-N y)/h) =ᶠ[𝓝[>] (0:ℝ)]
        fun h => (P (y+h)-P y)/h from by
      filter_upwards [self_mem_nhdsWithin] with h hh
      have hh' : 0 < h := hh
      rw [hSplit (y+h) (hay.trans (lt_add_of_pos_right _ hh')),hSplit y hay]
      ring)
  have he := tendsto_nhds_unique hQ hF
  have hG : (∫ s,G y s ∂ν) = -(∫ s in Ioc (0:ℝ) a,fractionalHistoryDensity α (y-s)*w s) := by
    simp only [G,neg_mul,integral_neg]
    rfl
  rw [hG] at he
  linarith

#print axioms affine_riccati_primitive_deriv_le_recent
#print axioms affine_riccati_recent_coefficient_eq

end RoughHeston
