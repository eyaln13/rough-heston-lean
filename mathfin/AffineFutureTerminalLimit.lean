import AffinePreterminalBound
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RoughHeston

/-- The future input after revealing the inverse variance history. -/
noncomputable def affineFutureInput (α t : ℝ) (j V : ℝ → ℝ) (y : ℝ) : ℝ :=
  j (t+y)+∫ r in Ioc (0:ℝ) t, fractionalHistoryDensity α (t+y-r)*V r

private theorem affineFutureInput_measurable {α t : ℝ} {j V : ℝ → ℝ}
    (hj : Measurable j) (hV : Measurable V) :
    Measurable (affineFutureInput α t j V) := by
  let F (z : ℝ × ℝ) := fractionalHistoryDensity α (t+z.1-z.2)*V z.2
  have hH : Measurable (fractionalHistoryDensity α) := (measurable_id.pow_const _).const_mul _
  have hF : Measurable F := (hH.comp
    ((measurable_const.add measurable_fst).sub measurable_snd)).mul
    (hV.comp measurable_snd)
  exact (hj.comp (measurable_const.add measurable_id)).add
    (hF.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc 0 t))).measurable

private theorem affine_terminal_L_nonneg {α u : ℝ} (hα' : α < 1) (hu : 0 < u) :
    0 ≤ fractionalL α u := by
  rw [fractionalL,ite_eq_right (not_le.mpr hu)]
  exact div_nonneg (Real.rpow_nonneg hu.le _) (Real.Gamma_pos_of_pos (by linarith)).le

private theorem affine_terminal_L_decreasing {α u v : ℝ}
    (hα : 0 < α) (hα' : α < 1) (hu : 0 < u) (huv : u ≤ v) :
    fractionalL α v ≤ fractionalL α u := by
  rw [fractionalL,fractionalL,ite_eq_right (not_le.mpr (hu.trans_le huv)),ite_eq_right (not_le.mpr hu)]
  exact div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hu huv (by linarith))
    (Real.Gamma_pos_of_pos (by linarith)).le

private theorem affine_terminal_history_decreasing {α u v : ℝ}
    (hα : 0 < α) (hα' : α < 1) (hu : 0 < u) (huv : u ≤ v) :
    fractionalHistoryDensity α v ≤ fractionalHistoryDensity α u :=
  mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hu huv (by linarith))
    (div_nonneg hα.le (Real.Gamma_pos_of_pos (by linarith)).le)

private theorem affine_terminal_history_mass {α t y : ℝ} (ht : 0 ≤ t) (hy : 0 < y) :
    IntegrableOn (fun r => fractionalHistoryDensity α (t+y-r)) (Ioc 0 t) ∧
      (∫ r in Ioc (0:ℝ) t,fractionalHistoryDensity α (t+y-r)) =
        fractionalL α y-fractionalL α (y+t) := by
  obtain ⟨hI,hMass⟩ := integral_fractionalHistoryDensity_shift (α := α) hy ht
  let F (r : ℝ) := fractionalHistoryDensity α (y+r)
  have he (r : ℝ) : fractionalHistoryDensity α (t+y-r) = F (t-r) := by
    dsimp [F]
    rw [show t+y-r = y+(t-r) by ring]
  have hRef := (hI.symm.comp_sub_left t)
  have hI' : IntervalIntegrable (fun r => F (t-r)) volume 0 t := by
    simpa only [F,sub_self,sub_zero] using hRef
  constructor
  · simpa only [he] using (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp hI'
  · simp_rw [he]
    rw [← intervalIntegral.integral_of_le ht,intervalIntegral.integral_comp_sub_left,
      sub_self,sub_zero]
    exact hMass

private theorem affine_future_terminal_pointwise
    {α T δ d y E Vmax Jmax : ℝ} {j V : ℝ → ℝ}
    (hα : 0 < α) (hα' : α < 1) (hT : 0 < T)
    (hδ : 0 < δ) (hd : 0 < d) (hdδ : d ≤ δ/2) (hdT : d ≤ T/2)
    (hy : y ∈ Ioc 0 d) (hE : 0 ≤ E) (hVmax : 0 ≤ Vmax)
    (hV : Continuous V) (hVb : ∀ r ∈ Icc 0 T, ‖V r‖ ≤ Vmax)
    (hclose : ∀ r ∈ Icc 0 T, T-r < δ → ‖V r-V T‖ ≤ E)
    (hjb : ∀ r ∈ Icc (T/2) T, ‖j r‖ ≤ Jmax) :
    ‖affineFutureInput α (T-d) j V y-V T*fractionalL α y‖ ≤
      E*fractionalL α y+
        (Jmax+(T*(2*Vmax*fractionalHistoryDensity α (δ/2)))+
            Vmax*fractionalL α (T/2)) := by
  let t := T-d
  let K (r : ℝ) := fractionalHistoryDensity α (t+y-r)
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ht₀ : 0 < t := by dsimp [t]; linarith
  have htT : t ≤ T := sub_le_self _ hd.le
  have hy₀ := hy.1
  obtain ⟨hK,hKmass⟩ := affine_terminal_history_mass (α := α) ht hy₀
  have hKn (r : ℝ) (hr : r∈Ioc 0 t) : 0 ≤ K r :=
    fractionalHistoryDensity_nonneg hα.le hα' (by linarith [hy.1,hr.2])
  have hVt : ‖V T‖ ≤ Vmax := hVb T ⟨hT.le,le_rfl⟩
  have hKV : IntegrableOn (fun r => K r*V r) (Ioc 0 t) := by
    have hKm : Measurable K := ((measurable_id.pow_const _).const_mul _).comp
      (measurable_const.sub measurable_id)
    refine (hK.norm.mul_const Vmax).mono' (hKm.mul hV.measurable).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    change ‖K r*V r‖ ≤ ‖K r‖*Vmax
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hVb r ⟨hr.1.le,hr.2.trans htT⟩) (norm_nonneg _)
  let D (r : ℝ) := K r*(V r-V T)
  have hDI : IntegrableOn D (Ioc 0 t) := by
    refine (hKV.sub (hK.mul_const (V T))).congr ?_
    exact ae_of_all _ fun r => (mul_sub (K r) _ _).symm
  let B := 2*Vmax*fractionalHistoryDensity α (δ/2)
  have hPoint (r : ℝ) (hr : r∈Ioc 0 t) : ‖D r‖ ≤ E*K r+B := by
    have hk := hKn r hr
    change ‖K r*(V r-V T)‖ ≤ E*K r+B
    rw [norm_mul,Real.norm_of_nonneg hk]
    have hrt : r∈Icc 0 T := ⟨hr.1.le,hr.2.trans htT⟩
    by_cases hnear : T-r<δ
    · have h := mul_le_mul_of_nonneg_left (hclose r hrt hnear) hk
      have h' : K r*‖V r-V T‖ ≤ E*K r := h.trans_eq (mul_comm _ _)
      have hB : 0 ≤ B := mul_nonneg (mul_nonneg (by norm_num) hVmax)
        (fractionalHistoryDensity_nonneg hα.le hα' (half_pos hδ).le)
      exact h'.trans (le_add_of_nonneg_right hB)
    · have hsep : δ/2 ≤ t+y-r := by
        dsimp [t]
        linarith [le_of_not_gt hnear,hy.1]
      have hVdiff : ‖V r-V T‖ ≤ 2*Vmax := by
        have h := (norm_sub_le _ _).trans (add_le_add (hVb r hrt) hVt)
        linarith
      have hK' : K r ≤ fractionalHistoryDensity α (δ/2) :=
        affine_terminal_history_decreasing hα hα' (half_pos hδ) hsep
      calc
        _ ≤ fractionalHistoryDensity α (δ/2)*(2*Vmax) :=
          mul_le_mul hK' hVdiff (norm_nonneg _)
            (fractionalHistoryDensity_nonneg hα.le hα' (half_pos hδ).le)
        _ = B := by dsimp [B]; ring
        _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hE hk)
  have hNorm : ‖∫ r in Ioc (0:ℝ) t,D r‖ ≤ E*fractionalL α y+T*B := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have h := setIntegral_mono_on hDI.norm ((hK.const_mul E).add (integrable_const B))
      measurableSet_Ioc hPoint
    have hS : (∫ r in Ioc (0:ℝ) t,E*K r+B) =
        (∫ r in Ioc (0:ℝ) t,E*K r)+(∫ _r in Ioc (0:ℝ) t,B) :=
      integral_add (hK.const_mul E) (integrable_const B)
    change (∫ r in Ioc (0:ℝ) t,‖D r‖) ≤ (∫ r in Ioc (0:ℝ) t,E*K r+B) at h
    have hm : (∫ r in Ioc (0:ℝ) t,K r) = fractionalL α y-fractionalL α (y+t) := hKmass
    rw [hS,integral_const_mul,setIntegral_const,smul_eq_mul,measureReal_def,
      Real.volume_Ioc,sub_zero,ENNReal.toReal_ofReal ht,hm] at h
    exact h.trans (add_le_add
      (mul_le_mul_of_nonneg_left (sub_le_self _ (affine_terminal_L_nonneg hα' (add_pos hy₀ ht₀))) hE)
      (mul_le_mul_of_nonneg_right htT (by
        dsimp [B]
        exact mul_nonneg (mul_nonneg (by norm_num) hVmax)
          (fractionalHistoryDensity_nonneg hα.le hα' (half_pos hδ).le))))
  have hEq : (∫ r in Ioc (0:ℝ) t,K r*V r)-V T*fractionalL α y =
      (∫ r in Ioc (0:ℝ) t,D r)-V T*fractionalL α (y+t) := by
    have hde : (∫ r in Ioc (0:ℝ) t,D r) =
        (∫ r in Ioc (0:ℝ) t,K r*V r) - (∫ r in Ioc (0:ℝ) t,K r*V T) := by
      simp_rw [D,mul_sub]
      exact integral_sub hKV (hK.mul_const _)
    rw [hde,integral_mul_const,hKmass]
    ring
  have hJ : ‖j (t+y)‖ ≤ Jmax := hjb _ ⟨by dsimp [t]; linarith [hy.1],
    by dsimp [t]; linarith [hy.2]⟩
  have hTail : ‖V T*fractionalL α (y+t)‖ ≤ Vmax*fractionalL α (T/2) := by
    rw [norm_mul,Real.norm_of_nonneg (affine_terminal_L_nonneg hα' (add_pos hy₀ ht₀))]
    exact mul_le_mul hVt (affine_terminal_L_decreasing hα hα' (half_pos hT)
      (by dsimp [t]; linarith [hy.1])) (affine_terminal_L_nonneg hα' (add_pos hy₀ ht₀)) hVmax
  change ‖j (t+y)+(∫ r in Ioc (0:ℝ) t,K r*V r)-V T*fractionalL α y‖ ≤ _
  rw [add_sub_assoc,hEq]
  have hh := (norm_add_le (j (t+y)) ((∫ r in Ioc (0:ℝ) t,D r)-V T*fractionalL α (y+t))).trans
    (add_le_add hJ ((norm_sub_le _ _).trans (add_le_add hNorm hTail)))
  convert hh using 1
  dsimp [B]
  ring

/-- The future term in the affine transform converges at the terminal
time. The point-charge contribution is q V(T); for density tests q=0.
The input j need only be bounded near the positive terminal time. -/
theorem affine_future_exponent_tendsto_terminal
    {α T q Jmax : ℝ} {w j V : ℝ → ℝ}
    (hα : 0 < α) (hα' : α < 1) (hT : 0 < T)
    (hwm : Measurable w) (hwi : IntegrableOn w (Ioc 0 T))
    (hw₀ : ∀ s ∈ Ioo 0 T, 0 ≤ w s)
    (hLwi : ∀ d ∈ Ioc 0 T, IntegrableOn (fun r => fractionalL α (d-r)*w r) (Ioc 0 d))
    (hq : Tendsto (volterraConvolution (fractionalL α) w) (𝓝[>] (0:ℝ)) (𝓝 q))
    (hjm : Measurable j) (hjb : ∀ r ∈ Icc (T/2) T, ‖j r‖ ≤ Jmax)
    (hV : Continuous V) :
    Tendsto (fun d => ∫ y in Ioc (0:ℝ) d, w (d-y)*affineFutureInput α (T-d) j V y)
      (𝓝[>] (0:ℝ)) (𝓝 (q*V T)) := by
  let Lw := volterraConvolution (fractionalL α) w
  let F (d : ℝ) := ∫ y in Ioc (0:ℝ) d, w (d-y)*affineFutureInput α (T-d) j V y
  let W (d : ℝ) := ∫ y in Ioc (0:ℝ) d, w y
  obtain ⟨B₀,hB₀⟩ := isCompact_Icc.bddAbove_image (K := Icc (0:ℝ) T) hV.norm.continuousOn
  let B := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hVb (r : ℝ) (hr : r∈Icc 0 T) : ‖V r‖ ≤ B :=
    (hB₀ ⟨r,hr,rfl⟩).trans (le_max_left _ _)
  have hJs : 0 ≤ Jmax := (norm_nonneg _).trans (hjb T ⟨by linarith,le_rfl⟩)
  have hW0 : Tendsto W (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr hwi
    have hCont : ContinuousWithinAt (fun s => ∫ y in (0:ℝ)..s,w y) (Icc 0 T) 0 :=
      intervalIntegral.continuousWithinAt_primitive (measure_singleton _) (by simpa [hT.le] using hi)
    have hNH : 𝓝[>] (0:ℝ) ≤ 𝓝[Icc 0 T] 0 := by
      refine le_inf nhdsWithin_le_nhds (le_principal_iff.mpr ?_)
      filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds hT)] with d hd ht
      exact ⟨(show 0<d from hd).le,(show d<T from ht).le⟩
    have hLim := hCont.tendsto.mono_left hNH
    simp only [intervalIntegral.integral_same] at hLim
    refine hLim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with d hd
    rw [intervalIntegral.integral_of_le (show 0<d from hd).le]
  have hError (E : ℝ) (hE : 0 < E) :
      ∃ K ≥ 0, ∀ᶠ d in 𝓝[>] (0:ℝ), ‖F d-V T*Lw d‖ ≤ E*Lw d+K*W d := by
    have hCont : Continuous (fun r : ℝ => ‖V r-V T‖) := (hV.sub continuous_const).norm
    have hHere : ‖V T-V T‖ < E := by simpa only [sub_self,norm_zero] using hE
    have hNear : ∀ᶠ r in 𝓝 T, ‖V r-V T‖ < E :=
      hCont.continuousAt.eventually_lt continuousAt_const hHere
    obtain ⟨δ,hδ,hclose⟩ := Metric.eventually_nhds_iff.mp hNear
    let K := Jmax+T*(2*B*fractionalHistoryDensity α (δ/2))+B*fractionalL α (T/2)
    have hK : 0 ≤ K := by
      dsimp [K]
      exact add_nonneg (add_nonneg hJs (mul_nonneg hT.le (mul_nonneg
        (mul_nonneg (by norm_num) hB) (fractionalHistoryDensity_nonneg hα.le hα' (half_pos hδ).le))))
        (mul_nonneg hB (affine_terminal_L_nonneg hα' (half_pos hT)))
    refine ⟨K,hK,?_⟩
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (lt_min (half_pos hδ) (half_pos hT)))] with d hd hδT
    have hd₀ : 0 < d := hd
    have hdδ : d ≤ δ/2 := (show d<min (δ/2) (T/2) from hδT).le.trans (min_le_left _ _)
    have hdT : d ≤ T/2 := (show d<min (δ/2) (T/2) from hδT).le.trans (min_le_right _ _)
    have hdT' : d < T := hdT.trans_lt (by linarith)
    let ν := volume.restrict (Ioc (0:ℝ) d)
    let g (y : ℝ) := w (d-y)
    let L := fractionalL α
    let p (y : ℝ) := affineFutureInput α (T-d) j V y
    have hg : Measurable g := hwm.comp (measurable_const.sub measurable_id)
    have hp : Measurable p := affineFutureInput_measurable hjm hV.measurable
    have hgi : Integrable g ν := by
      have hi := ((intervalIntegrable_iff_integrableOn_Ioc_of_le hd₀.le).mpr
        (hwi.mono_set (Ioc_subset_Ioc_right hdT'.le))).symm.comp_sub_left d
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hd₀.le).mp (by
        simpa only [g,sub_self,sub_zero] using hi)
    have hgl : Integrable (fun y => g y*L y) ν := by
      let l (r : ℝ) := L (d-r)*w r
      have hi := ((intervalIntegrable_iff_integrableOn_Ioc_of_le hd₀.le).mpr
        (hLwi d ⟨hd₀,hdT'.le⟩ : IntegrableOn l (Ioc 0 d) volume)).symm.comp_sub_left d
      have hi' : IntervalIntegrable (fun y => L y*g y) volume 0 d := by
        simpa only [l,sub_sub_cancel,sub_self,sub_zero,g] using hi
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hd₀.le).mp (by
        simpa only [mul_comm] using hi')
    have hgEq : (∫ y,g y ∂ν) = W d := by
      have h := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := d) w d
      simpa only [sub_self,sub_zero,intervalIntegral.integral_of_le hd₀.le] using h
    have hglEq : (∫ y,g y*L y ∂ν) = Lw d := by
      let l (r : ℝ) := L (d-r)*w r
      have h := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := d) l d
      simpa only [l,sub_self,sub_zero,sub_sub_cancel,intervalIntegral.integral_of_le hd₀.le,
        g,mul_comm,volterraConvolution,Lw,L] using h
    let err (y : ℝ) := g y*(p y-V T*L y)
    have hD : ∀ᵐ y ∂ν, ‖err y‖ ≤ E*(g y*L y)+K*g y := by
      have hY : ∀ᵐ y ∂ν,y∈Ioo 0 d := by
        change ∀ᵐ y ∂volume.restrict (Ioc 0 d),y∈Ioo 0 d
        rw [← restrict_Ioo_eq_restrict_Ioc]
        exact ae_restrict_mem measurableSet_Ioo
      filter_upwards [hY] with y hy
      have hgy : 0 ≤ g y := hw₀ (d-y) ⟨sub_pos.mpr hy.2,
        (sub_le_self d hy.1.le).trans_lt hdT'⟩
      have hPoint := affine_future_terminal_pointwise hα hα' hT hδ hd₀ hdδ hdT
        (Ioo_subset_Ioc_self hy) hE.le hB hV hVb (fun r hr hnear => by
          apply (hclose ?_).le
          rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hr.2)]
          linarith) hjb
      change ‖g y*(p y-V T*L y)‖ ≤ _
      rw [norm_mul,Real.norm_of_nonneg hgy]
      exact (mul_le_mul_of_nonneg_left hPoint hgy).trans_eq (by dsimp [K,L]; ring)
    have hDint : Integrable err ν := by
      have hm : Measurable err := hg.mul (hp.sub ((fractionalL_measurable α).const_mul (V T)))
      exact ((hgl.const_mul E).add (hgi.const_mul K)).mono' hm.aestronglyMeasurable hD
    have hFint : Integrable (fun y => g y*p y) ν := by
      refine (hDint.add (hgl.const_mul (V T))).congr ?_
      exact ae_of_all _ fun y => by dsimp [err]; ring
    have hEint : (∫ y,err y ∂ν) = F d-V T*Lw d := by
      have he (y : ℝ) : err y = g y*p y-V T*(g y*L y) := by dsimp [err]; ring
      simp_rw [he]
      rw [integral_sub hFint (hgl.const_mul _),integral_const_mul,hglEq]
    rw [← hEint]
    refine (norm_integral_le_integral_norm _).trans ?_
    have h := integral_mono_ae hDint.norm ((hgl.const_mul E).add (hgi.const_mul K)) hD
    have hL : (∫ y,E*(g y*L y)+K*g y ∂ν) =
        (∫ y,E*(g y*L y) ∂ν)+(∫ y,K*g y ∂ν) :=
      integral_add (hgl.const_mul E) (hgi.const_mul K)
    change (∫ y,‖err y‖ ∂ν) ≤ ∫ y,E*(g y*L y)+K*g y ∂ν at h
    rw [hL,integral_const_mul,integral_const_mul,hglEq,hgEq] at h
    exact h
  have hFinish : Tendsto (fun d => F d-V T*Lw d) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let E := ε/(2*(|q|+1))
    have hE : 0 < E := div_pos hε (by positivity)
    obtain ⟨K,_,hK⟩ := hError E hE
    have hqbound : q < |q|+1 := (le_abs_self q).trans_lt (lt_add_one _)
    have heQ := hq.eventually (Iio_mem_nhds hqbound)
    have heKW := ((hW0.const_mul K).congr' (Eventually.of_forall fun d => rfl))
    rw [mul_zero] at heKW
    have hsmall := heKW.eventually (Iio_mem_nhds (half_pos hε))
    filter_upwards [hK,heQ,hsmall] with d hb hq' hk
    rw [dist_zero_right]
    have hE' : E*(|q|+1)=ε/2 := by
      dsimp [E]
      field_simp
    exact hb.trans_lt (by
      have hh' : Lw d < |q|+1 := hq'
      have hh := mul_le_mul_of_nonneg_left hh'.le hE.le
      linarith)
  have hEnd := hFinish.add (hq.const_mul (V T))
  change Tendsto (fun d => F d-V T*Lw d+V T*Lw d) (𝓝[>] (0:ℝ)) (𝓝 (0+V T*q)) at hEnd
  simpa only [sub_add_cancel,zero_add,mul_comm (V T) q] using hEnd

#print axioms affine_future_exponent_tendsto_terminal

end RoughHeston
