import AffinePreterminalBound

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RoughHeston

/-- A causal integrable kernel between a bounded outer time weight and
an integrable input gives an absolutely integrable Volterra triangle. -/
theorem affine_volterra_triangle_integrable
    {l k f : ℝ → ℝ} {t B : ℝ} (ht : 0 ≤ t) (hB : 0 ≤ B)
    (hl : Measurable l) (hk : Measurable k) (hf : Measurable f)
    (hk₀ : ∀ s ≤ 0, k s = 0)
    (hki : IntegrableOn k (Ioc 0 t)) (hfi : IntegrableOn f (Ioc 0 t))
    (hlB : ∀ s ∈ Icc 0 t, ‖l s‖ ≤ B) :
    Integrable (fun z : ℝ × ℝ => l (t-z.1)*k (z.1-z.2)*f z.2)
      ((volume.restrict (Ioc 0 t)).prod (volume.restrict (Ioc 0 t))) := by
  let ν := volume.restrict (Ioc (0:ℝ) t)
  let F (z : ℝ × ℝ) := l (t-z.1)*k (z.1-z.2)*f z.2
  have hFm : Measurable F := ((hl.comp (measurable_const.sub measurable_fst)).mul
    (hk.comp (measurable_fst.sub measurable_snd))).mul (hf.comp measurable_snd)
  have hShift (u : ℝ) (hu : u ∈ Ioc 0 t) :
      IntegrableOn (fun s => k (s-u)) (Ioc 0 t) := by
    have hOld : IntervalIntegrable k volume (-u) 0 := by
      apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (neg_nonpos.mpr hu.1.le)).mpr
      refine (integrable_zero _ _ _).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      simpa only [Pi.zero_apply] using (hk₀ s hs.2).symm
    have hNew : IntervalIntegrable k volume 0 (t-u) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (sub_nonneg.mpr hu.2)).mpr
        (hki.mono_set (Ioc_subset_Ioc_right (sub_le_self t hu.1.le)))
    have hi := (hOld.trans hNew).comp_sub_right u
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp (by
      simpa only [neg_add_cancel,sub_add_cancel] using hi)
  have hSec (u : ℝ) (hu : u ∈ Ioc 0 t) : Integrable (fun s => F (s,u)) ν := by
    have hMeas : Measurable (fun s => F (s,u)) :=
      hFm.comp (measurable_id.prodMk measurable_const)
    refine ((hShift u hu).norm.mul_const (B*‖f u‖)).mono' hMeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hL := hlB (t-s) ⟨sub_nonneg.mpr hs.2,sub_le_self t hs.1.le⟩
    change ‖l (t-s)*k (s-u)*f u‖ ≤ ‖k (s-u)‖*(B*‖f u‖)
    rw [norm_mul,norm_mul]
    calc
      _ ≤ (B*‖k (s-u)‖)*‖f u‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hL (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  let C := ∫ r in Ioc (0:ℝ) t, ‖k r‖
  have hShiftMass (u : ℝ) (hu : u ∈ Ioc 0 t) :
      (∫ s in Ioc (0:ℝ) t, ‖k (s-u)‖) ≤ C := by
    have hZero : ∀ r ≤ 0, ‖k r‖ = 0 := fun r hr => by rw [hk₀ r hr,norm_zero]
    have h := volterra_shifted_kernel_integral (l := fun _ => (1:ℝ)) hZero hu
    simp only [one_mul,volterraConvolution] at h
    rw [h]
    exact setIntegral_mono_set hki.norm (ae_of_all _ fun r => norm_nonneg (k r))
      (Ioc_subset_Ioc_right (sub_le_self t hu.1.le)).eventuallyLE
  refine (integrable_prod_iff' hFm.aestronglyMeasurable).mpr ⟨?_,?_⟩
  · exact (ae_restrict_mem measurableSet_Ioc).mono fun u hu => hSec u hu
  · refine (hfi.norm.const_mul (B*C)).mono_nonneg
      (hFm.stronglyMeasurable.norm.integral_prod_left' (μ := ν)).aestronglyMeasurable
      (ae_of_all _ fun _ => integral_nonneg fun _ => norm_nonneg _) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have h := setIntegral_mono_on (hSec u hu).norm
      ((hShift u hu).norm.mul_const (B*‖f u‖)) measurableSet_Ioc (fun s hs => by
        have hL := hlB (t-s) ⟨sub_nonneg.mpr hs.2,sub_le_self t hs.1.le⟩
        change ‖l (t-s)*k (s-u)*f u‖ ≤ ‖k (s-u)‖*(B*‖f u‖)
        rw [norm_mul,norm_mul]
        calc
          _ ≤ (B*‖k (s-u)‖)*‖f u‖ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hL (norm_nonneg _)) (norm_nonneg _)
          _ = _ := by ring)
    rw [integral_mul_const] at h
    exact h.trans ((mul_le_mul_of_nonneg_right (hShiftMass u hu)
      (mul_nonneg hB (norm_nonneg _))).trans_eq (by ring))

private theorem affine_history_density_antitone {α : ℝ} (hα : 0 < α) (hα' : α < 1) :
    AntitoneOn (fractionalHistoryDensity α) (Ioi 0) := by
  intro u hu v _ huv
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hu huv (by linarith))
    (div_nonneg hα.le (Real.Gamma_pos_of_pos (by linarith)).le)

/-- The history triangle for the preterminal affine transform is
integrable even at its singular corner. Only L¹ integrability is
needed near the initial Riccati charge. -/
theorem affine_history_triangle_integrable
    {α d t : ℝ} {w V : ℝ → ℝ} (hα : 0 < α) (hα' : α < 1) (hd : 0 < d) (ht : 0 ≤ t)
    (hw : Measurable w) (hwi : IntegrableOn w (Ioc 0 d))
    (hwc : ContinuousOn w (Icc (d/2) d)) (hV : Measurable V)
    (hVc : ContinuousOn V (Icc 0 t)) :
    Integrable (fun z : ℝ × ℝ =>
      fractionalHistoryDensity α (d+t-z.1-z.2)*w z.2*V z.1)
      ((volume.restrict (Ioc 0 t)).prod (volume.restrict (Ioc 0 d))) := by
  let ν := volume.restrict (Ioc (0:ℝ) t)
  let η := volume.restrict (Ioc (0:ℝ) d)
  let H := fractionalHistoryDensity α
  let L := fractionalL α
  let F (z : ℝ × ℝ) := H (d+t-z.1-z.2)*w z.2*V z.1
  have hH : Measurable H := (measurable_id.pow_const _).const_mul _
  have hFm : Measurable F := ((hH.comp
    ((measurable_const.sub measurable_fst).sub measurable_snd)).mul
      (hw.comp measurable_snd)).mul (hV.comp measurable_fst)
  obtain ⟨B₀,hB₀⟩ := isCompact_Icc.bddAbove_image hVc.norm
  let B := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hVb (r : ℝ) (hr : r∈Ioc 0 t) : ‖V r‖ ≤ B :=
    (hB₀ ⟨r,Ioc_subset_Icc_self hr,rfl⟩).trans (le_max_left _ _)
  obtain ⟨C₀,hC₀⟩ := isCompact_Icc.bddAbove_image hwc.norm
  let C := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hwb (u : ℝ) (hu : u∈Icc (d/2) d) : ‖w u‖ ≤ C :=
    (hC₀ ⟨u,hu,rfl⟩).trans (le_max_left _ _)
  have hHpos {x : ℝ} (hx : 0 < x) : 0 ≤ H x := fractionalHistoryDensity_nonneg hα.le hα' hx.le
  have hLpos {x : ℝ} (hx : 0 < x) : 0 ≤ L x := by
    change 0 ≤ fractionalL α x
    rw [fractionalL,ite_eq_right (not_le.mpr hx)]
    exact div_nonneg (Real.rpow_nonneg hx.le _) (Real.Gamma_pos_of_pos (by linarith)).le
  have hHanti : AntitoneOn H (Ioi 0) := affine_history_density_antitone hα hα'
  have hSections (u : ℝ) (hu : u∈Ioo 0 d) :
      IntegrableOn (fun r => H (d+t-r-u)) (Ioc 0 t) ∧
        (∫ r in Ioc (0:ℝ) t,H (d+t-r-u)) = L (d-u)-L (d-u+t) := by
    obtain ⟨hi,he⟩ := integral_fractionalHistoryDensity_shift (α := α) (sub_pos.mpr hu.2) ht
    have hcomp := hi.symm.comp_sub_left t
    have hi' : IntervalIntegrable (fun r => H (d+t-r-u)) volume 0 t := by
      convert hcomp using 1
      · funext r
        change H (d+t-r-u) = H (d-u+(t-r))
        congr 1
        ring
      · ring
      · ring
    refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp hi',?_⟩
    have hf (r : ℝ) : H (d+t-r-u) = H (d-u+(t-r)) := by congr 1; ring
    have hR := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := t)
      (fun r => H (d-u+r)) t
    rw [sub_self,sub_zero,intervalIntegral.integral_of_le ht,
      intervalIntegral.integral_of_le ht] at hR
    simp_rw [hf]
    exact hR.trans ((intervalIntegral.integral_of_le ht).symm.trans he)
  have hSec (u : ℝ) (hu : u∈Ioo 0 d) : Integrable (fun r => F (r,u)) ν := by
    have hm : Measurable (fun r => F (r,u)) := hFm.comp (measurable_id.prodMk measurable_const)
    refine (((hSections u hu).1.norm.mul_const (‖w u‖*B))).mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    change ‖H (d+t-r-u)*w u*V r‖ ≤ ‖H (d+t-r-u)‖*(‖w u‖*B)
    rw [norm_mul,norm_mul,mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hVb r hr) (norm_nonneg _)) (norm_nonneg _)
  let D₁ := B*(t*H (d/2))
  let D₂ := B*C
  have hD₁ : 0 ≤ D₁ := mul_nonneg hB (mul_nonneg ht (hHpos (half_pos hd)))
  have hD₂ : 0 ≤ D₂ := mul_nonneg hB hC
  have hLInt : IntegrableOn (fun u => L (d-u)) (Ioc 0 d) :=
    fractionalL_reflected_integrableOn_Ioc hα' hd.le
  have hStrict : ∀ᵐ u ∂η, u∈Ioo 0 d := by
    change ∀ᵐ u ∂volume.restrict (Ioc 0 d),u∈Ioo 0 d
    rw [← restrict_Ioo_eq_restrict_Ioc]
    exact ae_restrict_mem measurableSet_Ioo
  refine (integrable_prod_iff' hFm.aestronglyMeasurable).mpr ⟨?_,?_⟩
  · exact hStrict.mono hSec
  · refine ((hwi.norm.const_mul D₁).add (hLInt.const_mul D₂)).mono_nonneg
      (hFm.stronglyMeasurable.norm.integral_prod_left' (μ := ν)).aestronglyMeasurable
      (ae_of_all _ fun _ => integral_nonneg fun _ => norm_nonneg _) ?_
    filter_upwards [hStrict] with u hu
    let K (r : ℝ) := H (d+t-r-u)
    have hKn (r : ℝ) (hr : r∈Ioc 0 t) : 0 ≤ K r :=
      hHpos (by linarith [hu.2,hr.2])
    have h := setIntegral_mono_on (hSec u hu).norm
      ((hSections u hu).1.mul_const (‖w u‖*B)) measurableSet_Ioc (fun r hr => by
        change ‖K r*w u*V r‖ ≤ K r*(‖w u‖*B)
        rw [norm_mul,norm_mul,Real.norm_of_nonneg (hKn r hr),mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hVb r hr) (norm_nonneg _))
          (hKn r hr))
    rw [integral_mul_const] at h
    change (∫ r,‖F (r,u)‖ ∂ν) ≤ D₁*‖w u‖+D₂*L (d-u)
    by_cases hhalf : u ≤ d/2
    · have hMass : (∫ r in Ioc (0:ℝ) t,K r) ≤ t*H (d/2) := by
        have he := setIntegral_mono_on (hSections u hu).1
          (integrable_const (H (d/2))) measurableSet_Ioc (fun r hr => by
            have hll : d/2 ≤ d+t-r-u := by linarith [hr.2]
            exact hHanti (half_pos hd) ((half_pos hd).trans_le hll) hll)
        simpa only [setIntegral_const,smul_eq_mul,measureReal_def,Real.volume_Ioc,
          sub_zero,ENNReal.toReal_ofReal ht] using he
      exact h.trans (((mul_le_mul_of_nonneg_right hMass (mul_nonneg (norm_nonneg _) hB)).trans_eq
        (by dsimp [D₁]; ring)).trans (le_add_of_nonneg_right (mul_nonneg hD₂ (hLpos (sub_pos.mpr hu.2)))))
    · have hMass : (∫ r in Ioc (0:ℝ) t,K r) ≤ L (d-u) := by
        change (∫ r in Ioc (0:ℝ) t,H (d+t-r-u)) ≤ _
        rw [(hSections u hu).2]
        exact sub_le_self _ (hLpos (add_pos_of_pos_of_nonneg (sub_pos.mpr hu.2) ht))
      have hwu := hwb u ⟨le_of_not_ge hhalf,hu.2.le⟩
      have hBnd : (∫ r in Ioc (0:ℝ) t,K r)*(‖w u‖*B) ≤ D₂*L (d-u) := by
        refine (mul_le_mul hMass (mul_le_mul_of_nonneg_right hwu hB) (mul_nonneg (norm_nonneg _) hB)
          (hLpos (sub_pos.mpr hu.2))).trans_eq ?_
        dsimp [D₂]
        ring
      exact h.trans (hBnd.trans (le_add_of_nonneg_left (mul_nonneg hD₁ (norm_nonneg _))))

#print axioms affine_volterra_triangle_integrable
#print axioms affine_history_triangle_integrable

end RoughHeston
