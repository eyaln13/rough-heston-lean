import AffineKernelRecentDerivative

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RoughHeston

private theorem volterra_affine_outer_integrable
    {l k f : ℝ → ℝ} {t : ℝ}
    (hk : ∀ u ≤ 0, k u = 0)
    (hI : Integrable (fun z : ℝ × ℝ => l (t-z.1)*k (z.1-z.2)*f z.2)
      ((volume.restrict (Ioc 0 t)).prod (volume.restrict (Ioc 0 t)))) :
    IntegrableOn (fun s => l (t-s)*volterraConvolution k f s) (Ioc 0 t) ∧
      IntegrableOn (fun s => volterraConvolution l k (t-s)*f s) (Ioc 0 t) := by
  constructor
  · refine hI.integral_prod_left.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hsub : Ioc (0:ℝ) s ⊆ Ioc 0 t := Ioc_subset_Ioc_right hs.2
    have hZero (u : ℝ) (hu : u ∈ Ioc 0 t \ Ioc 0 s) :
        l (t-s)*k (s-u)*f u = 0 := by
      have hsu : s ≤ u := le_of_not_gt fun h => hu.2 ⟨hu.1.1,h.le⟩
      rw [hk (s-u) (sub_nonpos.mpr hsu),mul_zero,zero_mul]
    change (∫ u in Ioc (0:ℝ) t,l (t-s)*k (s-u)*f u) =
      l (t-s)*volterraConvolution k f s
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc hsub hZero,
      volterraConvolution,← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u _
    change l (t-s)*k (s-u)*f u = l (t-s)*(k (s-u)*f u)
    rw [mul_assoc]
  · refine hI.integral_prod_right.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    change (∫ s in Ioc (0:ℝ) t,l (t-s)*k (s-u)*f u) =
      volterraConvolution l k (t-u)*f u
    rw [integral_mul_const,volterra_shifted_kernel_integral hk hu]

private theorem affine_one_kernel_convolution {f : ℝ → ℝ} (s : ℝ) :
    volterraConvolution (fractionalK 1) f s = ∫ r in Ioc (0:ℝ) s,f r := by
  apply setIntegral_congr_ae measurableSet_Ioc
  filter_upwards [volume.ae_ne s] with r hn hr
  have hpos : 0 < s-r := sub_pos.mpr (lt_of_le_of_ne hr.2 hn)
  change fractionalK 1 (s-r)*f r = f r
  simp [fractionalK,not_le.mpr hpos,Real.Gamma_one]

theorem affine_recent_derivative_one_convolution
    {w : ℝ → ℝ} {d x : ℝ} (hd : 0 < d) (hx : 0 ≤ x)
    (hw : ∀ z > 0, ContDiffAt ℝ 1 w z) :
    volterraConvolution (fun y => deriv w (d+y)) (fractionalK 1) x =
      w (d+x)-w d := by
  let f (r : ℝ) := deriv w (d+r)
  have he : volterraConvolution f (fractionalK 1) x =
      ∫ r in Ioc (0:ℝ) x, f (x-r) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    change f (x-r)*fractionalK 1 r = f (x-r)
    simp [fractionalK,not_le.mpr hr.1,Real.Gamma_one]
  rw [he,← intervalIntegral.integral_of_le hx]
  have hR := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := x) f x
  rw [sub_self,sub_zero] at hR
  rw [hR]
  have hC : ContinuousOn (deriv w) (Ioi 0) := by
    have hw' : ContDiffOn ℝ 1 w (Ioi 0) := fun r hr => (hw r hr).contDiffWithinAt
    exact hw'.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
  have hfc : ContinuousOn f (Icc 0 x) := hC.comp
    (continuous_const.add continuous_id).continuousOn
    (fun r hr => add_pos_of_pos_of_nonneg hd hr.1)
  have hfi : IntervalIntegrable f volume 0 x := by
    apply hfc.intervalIntegrable_of_Icc hx
  have hFTC : (∫ r in 0..x, f r) = w (d+x)-w (d+0) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r hr => by
        have hr' : 0 ≤ r := (show r ∈ Icc 0 x by
          simpa only [uIcc_of_le hx] using hr).1
        have h := (hw (d+r) (add_pos_of_pos_of_nonneg hd hr')).differentiableAt
          one_ne_zero |>.hasDerivAt
        have h' := h.comp r ((hasDerivAt_id r).const_add d)
        change HasDerivAt (fun r : ℝ => w (d+r)) (deriv w (d+r)*1) r at h'
        simpa only [f,mul_one] using h') hfi
  simpa only [add_zero] using hFTC

private theorem affine_preterminal_inverse_exponent_expansion
    {α κ a d t : ℝ} {w V j M : ℝ → ℝ}
    (ht : 0 < t)
    (hInv : ∀ s ∈ Ioc 0 t, M s = volterraConvolution (fractionalL α) V s +
      ∫ r in Ioc (0:ℝ) s,κ*V r-j r)
    (hLV : IntegrableOn (fun r => fractionalL α (t-r)*V r) (Ioc 0 t))
    (hD : IntegrableOn (fun r => κ*V r-j r) (Ioc 0 t))
    (hWV : IntegrableOn (fun r => (w (d+t-r))^2*V r) (Ioc 0 t))
    (hTriL : Integrable (fun z : ℝ × ℝ =>
      deriv w (d+(t-z.1))*fractionalL α (z.1-z.2)*V z.2)
      ((volume.restrict (Ioc 0 t)).prod (volume.restrict (Ioc 0 t))))
    (hTriD : Integrable (fun z : ℝ × ℝ =>
      deriv w (d+(t-z.1))*fractionalK 1 (z.1-z.2)*(κ*V z.2-j z.2))
      ((volume.restrict (Ioc 0 t)).prod (volume.restrict (Ioc 0 t)))) :
    let q (y : ℝ) := deriv w (d+y)
    let D (r : ℝ) := κ*V r-j r
    let R (r : ℝ) := w d*(fractionalL α (t-r)*V r+D r)+
      (volterraConvolution q (fractionalL α) (t-r)*V r+
        volterraConvolution q (fractionalK 1) (t-r)*D r)+a*((w (d+t-r))^2*V r)
    IntegrableOn R (Ioc 0 t) ∧
      (∫ r in Ioc (0:ℝ) t,R r) = w d*M t + volterraConvolution q M t +
        a*(∫ r in Ioc (0:ℝ) t,(w (d+t-r))^2*V r) := by
  let q (y : ℝ) := deriv w (d+y)
  let D (r : ℝ) := κ*V r-j r
  let L := fractionalL α
  let C := fractionalK 1
  let ν := volume.restrict (Ioc (0:ℝ) t)
  have hLzero : ∀ r ≤ 0, L r = 0 := fun r hr => ite_eq_left hr
  have hCzero : ∀ r ≤ 0, C r = 0 := fun r hr => ite_eq_left hr
  obtain ⟨hL1,hL2⟩ := volterra_affine_outer_integrable (l := q) (f := V) (t := t) hLzero hTriL
  obtain ⟨hC1,hC2⟩ := volterra_affine_outer_integrable (l := q) (f := D) (t := t) hCzero hTriD
  have hM (s : ℝ) (hs : s ∈ Ioc 0 t) :
      M s = volterraConvolution L V s+volterraConvolution C D s :=
    (hInv s hs).trans (congrArg _ (affine_one_kernel_convolution (f := D) s).symm)
  have hOuter :
      volterraConvolution q M t =
      (∫ r, volterraConvolution q L (t-r)*V r ∂ν) +
      (∫ r, volterraConvolution q C (t-r)*D r ∂ν) := by
    have hSplit : volterraConvolution q M t =
        (∫ r,q (t-r)*volterraConvolution L V r ∂ν)+
        (∫ r,q (t-r)*volterraConvolution C D r ∂ν) := by
      calc
        _ = ∫ r,q (t-r)*volterraConvolution L V r + q (t-r)*volterraConvolution C D r ∂ν := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro r hr
          change q (t-r)*M r = q (t-r)*volterraConvolution L V r+q (t-r)*volterraConvolution C D r
          rw [hM r hr,mul_add]
        _ = _ := integral_add hL1 hC1
    rw [hSplit]
    exact congrArg₂ (·+·) (volterra_convolution_assoc (l := q) (f := V) (t := t) hLzero hTriL)
      (volterra_convolution_assoc (l := q) (f := D) (t := t) hCzero hTriD)
  let R (r : ℝ) := w d*(L (t-r)*V r+D r)+
    (volterraConvolution q L (t-r)*V r+volterraConvolution q C (t-r)*D r)+
    a*((w (d+t-r))^2*V r)
  have hRInt : Integrable R ν :=
    (((hLV.add hD).const_mul (w d)).add (hL2.add hC2)).add (hWV.const_mul a)
  have hsum : (∫ r,R r ∂ν) = w d*M t + volterraConvolution q M t+
      a*(∫ r in Ioc (0:ℝ) t,(w (d+t-r))^2*V r) := by
    calc
      _ = (∫ r,w d*(L (t-r)*V r+D r) ∂ν) +
          (∫ r,volterraConvolution q L (t-r)*V r+volterraConvolution q C (t-r)*D r ∂ν) +
          (∫ r,a*((w (d+t-r))^2*V r) ∂ν) := by
        refine (integral_add (((hLV.add hD).const_mul (w d)).add (hL2.add hC2))
          (hWV.const_mul a)).trans ?_
        have hS : (∫ r, w d*(L (t-r)*V r+D r)+
            (volterraConvolution q L (t-r)*V r+volterraConvolution q C (t-r)*D r) ∂ν) =
          (∫ r,w d*(L (t-r)*V r+D r) ∂ν) +
            (∫ r,volterraConvolution q L (t-r)*V r+volterraConvolution q C (t-r)*D r ∂ν) :=
          integral_add ((hLV.add hD).const_mul (w d)) (hL2.add hC2)
        exact congrArg (fun z : ℝ => z+(∫ r,a*((w (d+t-r))^2*V r) ∂ν)) hS
      _ = _ := by
        have hS : (∫ r,volterraConvolution q L (t-r)*V r+volterraConvolution q C (t-r)*D r ∂ν) =
            (∫ r,volterraConvolution q L (t-r)*V r ∂ν)+(∫ r,volterraConvolution q C (t-r)*D r ∂ν) :=
          integral_add hL2 hC2
        rw [integral_const_mul,hS,← hOuter,integral_const_mul]
        have hMD : (∫ r,L (t-r)*V r+D r ∂ν) = M t :=
          (integral_add hLV hD).trans (hInv t ⟨ht,le_rfl⟩).symm
        rw [hMD]
  exact ⟨hRInt,hsum⟩

/-- Pathwise exponent lower bound before the affine horizon. The first
two terms are deterministic integration by parts for the weighted
martingale integral. The inverse variance equation supplies the path M. -/
theorem affine_preterminal_inverse_exponent_lower
    {α κ a d t : ℝ} {w V j M f : ℝ → ℝ}
    (hα : 0 < α) (hα' : α < 1) (hd : 0 < d) (ht : 0 < t)
    (hwm : Measurable w) (hwI : IntegrableOn w (Ioc 0 d))
    (hw : ∀ y > 0, ContDiffAt ℝ 1 w y)
    (hw₀ : ∀ y ∈ Ioc 0 d, 0 ≤ w y)
    (hV₀ : ∀ r ∈ Ioc 0 t, 0 ≤ V r)
    (hf₀ : ∀ y ∈ Ioo d (d+t), 0 ≤ f y)
    (hDeriv : ∀ y ∈ Ioo d (d+t),
      HasDerivAt (volterraConvolution (fractionalL α) w) (f y-κ*w y-a*(w y)^2) y)
    (hInv : ∀ s ∈ Ioc 0 t, M s = volterraConvolution (fractionalL α) V s +
      ∫ r in Ioc (0:ℝ) s,κ*V r-j r)
    (hLV : IntegrableOn (fun r => fractionalL α (t-r)*V r) (Ioc 0 t))
    (hD : IntegrableOn (fun r => κ*V r-j r) (Ioc 0 t))
    (hWj : IntegrableOn (fun r => w (d+t-r)*j r) (Ioc 0 t))
    (hWV : IntegrableOn (fun r => (w (d+t-r))^2*V r) (Ioc 0 t))
    (hTriL : Integrable (fun z : ℝ × ℝ =>
      deriv w (d+(t-z.1))*fractionalL α (z.1-z.2)*V z.2)
      ((volume.restrict (Ioc 0 t)).prod (volume.restrict (Ioc 0 t))))
    (hTriD : Integrable (fun z : ℝ × ℝ =>
      deriv w (d+(t-z.1))*fractionalK 1 (z.1-z.2)*(κ*V z.2-j z.2))
      ((volume.restrict (Ioc 0 t)).prod (volume.restrict (Ioc 0 t)))) :
    -(∫ r in Ioc (0:ℝ) t,w (d+t-r)*j r) ≤
      w d*M t + volterraConvolution (fun y => deriv w (d+y)) M t +
        a*(∫ r in Ioc (0:ℝ) t,(w (d+t-r))^2*V r) := by
  let q (y : ℝ) := deriv w (d+y)
  let D (r : ℝ) := κ*V r-j r
  let L := fractionalL α
  let C := fractionalK 1
  let ν := volume.restrict (Ioc (0:ℝ) t)
  let R (r : ℝ) := w d*(L (t-r)*V r+D r)+
    (volterraConvolution q L (t-r)*V r+volterraConvolution q C (t-r)*D r)+
    a*((w (d+t-r))^2*V r)
  obtain ⟨hRInt,hsum⟩ := affine_preterminal_inverse_exponent_expansion (w := w) (d := d)
    (a := a) ht hInv hLV hD hWV hTriL hTriD
  change Integrable R ν at hRInt
  change (∫ r,R r ∂ν) = w d*M t+volterraConvolution q M t+
    a*(∫ r in Ioc (0:ℝ) t,(w (d+t-r))^2*V r) at hsum
  rw [← hsum,← integral_neg]
  apply integral_mono_ae hWj.neg hRInt
  have hStrict : ∀ᵐ r ∂ν, r ∈ Ioo 0 t := by
    change ∀ᵐ r ∂volume.restrict (Ioc 0 t), r ∈ Ioo 0 t
    rw [← restrict_Ioo_eq_restrict_Ioc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hStrict] with r hr
  have hyr : d+t-r ∈ Ioo d (d+t) := ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have hco := affine_riccati_primitive_deriv_le_recent hα hα' hd hyr.1 hwm hwI hw hw₀
    (hDeriv _ hyr)
  have hco' : f (d+t-r)-κ*w (d+t-r)-a*(w (d+t-r))^2 ≤
      w d*L (t-r)+volterraConvolution q L (t-r) := by
    have hEq : (∫ u in Ioc (0:ℝ) (d+t-r-d),L u*deriv w (d+t-r-u)) =
        volterraConvolution q L (t-r) := by
      rw [show d+t-r-d=t-r by ring]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro u _
      change L u*deriv w (d+t-r-u) = deriv w (d+(t-r-u))*L u
      rw [show d+t-r-u=d+(t-r-u) by ring,mul_comm]
    change _ ≤ w d*L (d+t-r-d)+∫ u in Ioc (0:ℝ) (d+t-r-d),L u*deriv w (d+t-r-u) at hco
    rw [hEq,show d+t-r-d=t-r by ring] at hco
    exact hco
  have hCder : volterraConvolution q C (t-r) = w (d+(t-r))-w d :=
    affine_recent_derivative_one_convolution hd (sub_nonneg.mpr hr.2.le) hw
  have hCoef : 0 ≤ w d*L (t-r)+volterraConvolution q L (t-r)+
      κ*w (d+t-r)+a*(w (d+t-r))^2 := by linarith [hf₀ _ hyr]
  have hpos := mul_nonneg hCoef (hV₀ r (Ioo_subset_Ioc_self hr))
  change -(w (d+t-r)*j r) ≤ R r
  dsimp only [R,D]
  rw [hCder,show d+(t-r)=d+t-r by ring]
  nlinarith only [hpos]

/-- Exact preterminal affine split. The future input consists of the
shifted original input and the fractional derivative of the known
variance history. All integrals are ordinary pathwise integrals. -/
theorem affine_preterminal_inverse_exponent_split
    {α κ a d t : ℝ} {w V j M f : ℝ → ℝ}
    (hα : 0 < α) (hα' : α < 1) (hd : 0 < d) (ht : 0 < t)
    (hwm : Measurable w) (hwI : IntegrableOn w (Ioc 0 d))
    (hw : ∀ y > 0, ContDiffAt ℝ 1 w y)
    (hDeriv : ∀ y ∈ Ioo d (d+t),
      HasDerivAt (volterraConvolution (fractionalL α) w) (f y-κ*w y-a*(w y)^2) y)
    (hInv : ∀ s ∈ Ioc 0 t, M s = volterraConvolution (fractionalL α) V s +
      ∫ r in Ioc (0:ℝ) s,κ*V r-j r)
    (hLV : IntegrableOn (fun r => fractionalL α (t-r)*V r) (Ioc 0 t))
    (hD : IntegrableOn (fun r => κ*V r-j r) (Ioc 0 t))
    (hWj : IntegrableOn (fun r => w (d+t-r)*j r) (Ioc 0 (d+t)))
    (hFV : IntegrableOn (fun r => f (d+t-r)*V r) (Ioc 0 t))
    (hWV : IntegrableOn (fun r => (w (d+t-r))^2*V r) (Ioc 0 t))
    (hTriL : Integrable (fun z : ℝ × ℝ =>
      deriv w (d+(t-z.1))*fractionalL α (z.1-z.2)*V z.2)
      ((volume.restrict (Ioc 0 t)).prod (volume.restrict (Ioc 0 t))))
    (hTriD : Integrable (fun z : ℝ × ℝ =>
      deriv w (d+(t-z.1))*fractionalK 1 (z.1-z.2)*(κ*V z.2-j z.2))
      ((volume.restrict (Ioc 0 t)).prod (volume.restrict (Ioc 0 t))))
    (hTriHist : Integrable (fun z : ℝ × ℝ =>
      fractionalHistoryDensity α (d+t-z.1-z.2)*w z.2*V z.1)
      ((volume.restrict (Ioc 0 t)).prod (volume.restrict (Ioc 0 d)))) :
    w d*M t + volterraConvolution (fun y => deriv w (d+y)) M t +
      a*(∫ r in Ioc (0:ℝ) t,(w (d+t-r))^2*V r) =
      (∫ r in Ioc (0:ℝ) t,f (d+t-r)*V r) -
        (∫ r in Ioc (0:ℝ) (d+t),w (d+t-r)*j r) +
        ∫ y in Ioc (0:ℝ) d,w (d-y)*
          (j (t+y)+∫ r in Ioc (0:ℝ) t,fractionalHistoryDensity α (t+y-r)*V r) := by
  let q (y : ℝ) := deriv w (d+y)
  let D (r : ℝ) := κ*V r-j r
  let L := fractionalL α
  let C := fractionalK 1
  let ν := volume.restrict (Ioc (0:ℝ) t)
  let η := volume.restrict (Ioc (0:ℝ) d)
  let R (r : ℝ) := w d*(L (t-r)*V r+D r)+
    (volterraConvolution q L (t-r)*V r+volterraConvolution q C (t-r)*D r)+
    a*((w (d+t-r))^2*V r)
  obtain ⟨_,hsum⟩ := affine_preterminal_inverse_exponent_expansion (w := w) (d := d)
    (a := a) ht hInv hLV hD hWV hTriL hTriD
  change (∫ r,R r ∂ν) = w d*M t+volterraConvolution q M t+
    a*(∫ r in Ioc (0:ℝ) t,(w (d+t-r))^2*V r) at hsum
  rw [← hsum]
  let H (r u : ℝ) := fractionalHistoryDensity α (d+t-r-u)
  let P (r : ℝ) := f (d+t-r)*V r
  let Q (r : ℝ) := w (d+t-r)*j r
  let Sr (r : ℝ) := (∫ u,H r u*w u ∂η)*V r
  let Su (u : ℝ) := w u*(∫ r,H r u*V r ∂ν)
  have hTri : Integrable (fun z : ℝ × ℝ => H z.1 z.2*w z.2*V z.1) (ν.prod η) := hTriHist
  have hSr : Integrable Sr ν := by
    refine hTri.integral_prod_left.congr (ae_of_all _ fun r => ?_)
    change (∫ u,H r u*w u*V r ∂η) = (∫ u,H r u*w u ∂η)*V r
    rw [integral_mul_const]
  have hSu : Integrable Su η := by
    refine hTri.integral_prod_right.congr (ae_of_all _ fun u => ?_)
    change (∫ r,H r u*w u*V r ∂ν) = w u*(∫ r,H r u*V r ∂ν)
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun r => by ring)
  have hHistSwap : (∫ r,Sr r ∂ν) = ∫ u,Su u ∂η := by
    calc
      _ = ∫ r,∫ u,H r u*w u*V r ∂η ∂ν := by
        apply integral_congr_ae
        exact ae_of_all _ fun r => (integral_mul_const _ _).symm
      _ = ∫ u,∫ r,H r u*w u*V r ∂ν ∂η := integral_integral_swap hTri
      _ = _ := by
        apply integral_congr_ae
        refine ae_of_all _ fun u => ?_
        change (∫ r,H r u*w u*V r ∂ν) = w u*(∫ r,H r u*V r ∂ν)
        rw [← integral_const_mul]
        exact integral_congr_ae (ae_of_all _ fun r => by ring)
  have hPoint : R =ᵐ[ν] fun r => P r-Q r+Sr r := by
    have hStrict : ∀ᵐ r ∂ν, r ∈ Ioo 0 t := by
      change ∀ᵐ r ∂volume.restrict (Ioc 0 t), r ∈ Ioo 0 t
      rw [← restrict_Ioo_eq_restrict_Ioc]
      exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [hStrict] with r hr
    have hyr : d+t-r ∈ Ioo d (d+t) := ⟨by linarith [hr.2],by linarith [hr.1]⟩
    have hco := affine_riccati_recent_coefficient_eq hα hα' hd hyr.1 hwm hwI hw (hDeriv _ hyr)
    have hco' : w d*L (t-r)+volterraConvolution q L (t-r) =
        f (d+t-r)-κ*w (d+t-r)-a*(w (d+t-r))^2 + ∫ u,H r u*w u ∂η := by
      have hEq : (∫ u in Ioc (0:ℝ) (d+t-r-d),L u*deriv w (d+t-r-u)) =
          volterraConvolution q L (t-r) := by
        rw [show d+t-r-d=t-r by ring]
        apply setIntegral_congr_fun measurableSet_Ioc
        intro u _
        change L u*deriv w (d+t-r-u) = deriv w (d+(t-r-u))*L u
        rw [show d+t-r-u=d+(t-r-u) by ring,mul_comm]
      change w d*L (d+t-r-d)+(∫ u in Ioc (0:ℝ) (d+t-r-d),L u*deriv w (d+t-r-u)) = _ at hco
      rw [hEq,show d+t-r-d=t-r by ring] at hco
      exact hco
    have hCder : volterraConvolution q C (t-r) = w (d+(t-r))-w d :=
      affine_recent_derivative_one_convolution hd (sub_nonneg.mpr hr.2.le) hw
    change R r = P r-Q r+Sr r
    dsimp only [R,D,P,Q,Sr]
    rw [hCder,show d+(t-r)=d+t-r by ring]
    linear_combination (V r)*hco'
  have hQpast : Integrable Q ν := hWj.mono_set (Ioc_subset_Ioc_right (by linarith))
  rw [integral_congr_ae hPoint]
  have hSplitInt : (∫ r,P r-Q r+Sr r ∂ν) =
      (∫ r,P r ∂ν)-(∫ r,Q r ∂ν)+(∫ r, Sr r ∂ν) :=
    (integral_add (hFV.sub hQpast) hSr).trans (congrArg (fun z => z+(∫ r,Sr r ∂ν))
      (integral_sub hFV hQpast))
  rw [hSplitInt,hHistSwap]
  have hSqj : IntervalIntegrable Q volume t (d+t) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_add_of_nonneg_left hd.le)).mpr
      (hWj.mono_set (Ioc_subset_Ioc_left ht.le))
  have hJIntegral : (∫ r in Ioc (0:ℝ) (d+t),Q r) =
      (∫ r,Q r ∂ν)+(∫ y in Ioc (0:ℝ) d,w (d-y)*j (t+y)) := by
    have hSplit : (∫ r in Ioc (0:ℝ) (d+t),Q r) =
        (∫ r,Q r ∂ν)+(∫ r in Ioc t (d+t),Q r) := by
      rw [← Ioc_union_Ioc_eq_Ioc ht.le (le_add_of_nonneg_left hd.le)]
      exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hQpast hSqj.1
    rw [hSplit]
    congr 1
    have hsh := intervalIntegral.integral_comp_add_right (a := (0:ℝ)) (b := d) Q t
    rw [zero_add,intervalIntegral.integral_of_le hd.le,
      intervalIntegral.integral_of_le (le_add_of_nonneg_left hd.le)] at hsh
    rw [← hsh]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro y _
    change w (d+t-(y+t))*j (y+t) = w (d-y)*j (t+y)
    rw [show d+t-(y+t)=d-y by ring,add_comm y t]
  have hJI : IntegrableOn (fun y => w (d-y)*j (t+y)) (Ioc 0 d) := by
    have hh : IntervalIntegrable (fun y : ℝ => Q (y+t)) volume 0 d := by
      have hi := hSqj.comp_add_right t
      simpa only [sub_self,add_sub_cancel_right] using hi
    refine hh.1.congr_fun ?_ measurableSet_Ioc
    intro y _
    change w (d+t-(y+t))*j (y+t) = w (d-y)*j (t+y)
    rw [show d+t-(y+t)=d-y by ring,add_comm y t]
  have hSI : IntegrableOn (fun y => Su (d-y)) (Ioc 0 d) := by
    have hi := ((intervalIntegrable_iff_integrableOn_Ioc_of_le hd.le).mpr (show IntegrableOn Su (Ioc 0 d) volume from hSu)).symm.comp_sub_left d
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hd.le).mp (by
      simpa only [sub_self,sub_zero] using hi)
  have hFutureHist (y : ℝ) :
      Su (d-y) = w (d-y)*(∫ r in Ioc (0:ℝ) t,fractionalHistoryDensity α (t+y-r)*V r) := by
    dsimp [Su]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun r => by
      dsimp [H]
      rw [show d+t-r-(d-y)=t+y-r by ring]
  have hHI : IntegrableOn (fun y => w (d-y)*
      (∫ r in Ioc (0:ℝ) t,fractionalHistoryDensity α (t+y-r)*V r)) (Ioc 0 d) :=
    hSI.congr (ae_of_all _ hFutureHist)
  have hHIntegral : (∫ u,Su u ∂η) =
      (∫ y in Ioc (0:ℝ) d,w (d-y)*
        (∫ r in Ioc (0:ℝ) t,fractionalHistoryDensity α (t+y-r)*V r)) := by
    have he := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := d) Su d
    rw [sub_self,sub_zero,intervalIntegral.integral_of_le hd.le,
      intervalIntegral.integral_of_le hd.le] at he
    change (∫ u in Ioc (0:ℝ) d,Su u) = _
    rw [← he]
    exact integral_congr_ae (ae_of_all _ hFutureHist)
  have hFuture :
      (∫ y in Ioc (0:ℝ) d,w (d-y)*
        (j (t+y)+∫ r in Ioc (0:ℝ) t,fractionalHistoryDensity α (t+y-r)*V r)) =
        (∫ y in Ioc (0:ℝ) d,w (d-y)*j (t+y))+(∫ u,Su u ∂η) := by
    rw [hHIntegral]
    simpa only [mul_add] using
      (integral_add hJI hHI : (∫ y in Ioc (0:ℝ) d, w (d-y)*j (t+y)+
        w (d-y)*(∫ r in Ioc (0:ℝ) t,fractionalHistoryDensity α (t+y-r)*V r)) = _)
  change (∫ r,f (d+t-r)*V r ∂ν)-(∫ r,Q r ∂ν)+(∫ u,Su u ∂η) =
    (∫ r,f (d+t-r)*V r ∂ν)-(∫ r in Ioc (0:ℝ) (d+t),Q r)+_
  rw [hJIntegral,hFuture]
  ring

#print axioms affine_preterminal_inverse_exponent_lower
#print axioms affine_preterminal_inverse_exponent_split

end RoughHeston
