import AffineTestInstantiation
import VolterraMomentBound
import BanachHestonInversion

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RoughHeston

private theorem affine_density_standard_form
    {α κ a q l T : ℝ} {w : ℝ → ℝ}
    (hα : 0<α) (hα' : α<1) (hT : 0<T) (hw : Continuous w)
    (hVol : ∀ t ∈ Ioc 0 T, w t = volterraConvolution (fractionalK α)
      (fun r => q+l*(fractionalL α r+κ)-κ*w r-a*(w r)^2) t) :
    ∀ t ∈ Icc 0 T, w t=l+volterraConvolution (fractionalK α)
      (fun r => q+κ*l-κ*w r-a*(w r)^2) t := by
  let G (u : ℝ) := q+κ*l-κ*w u-a*(w u)^2
  have hG : Continuous G := (continuous_const.sub (continuous_const.mul hw)).sub
    (continuous_const.mul (hw.pow 2))
  have hKLG (t : ℝ) (ht : t∈Ioc 0 T) :
      (volterraConvolution (fractionalK α)
        (fun r => q+l*(fractionalL α r+κ)-κ*w r-a*(w r)^2) t) =
        l+volterraConvolution (fractionalK α) G t := by
    let L (r : ℝ) := fractionalK α (t-r)*fractionalL α r
    let A (r : ℝ) := fractionalK α (t-r)*G r
    have hLk : fractionalL α = fractionalK (1-α) := by
      funext r
      simp only [fractionalL,fractionalK,show 1-α-1 = -α by ring]
    have hLi : IntegrableOn L (Ioc 0 t) := by
      have hi := (real_beta_weight_scaled (a := 1-α) (b := α) (sub_pos.mpr hα') hα ht.1).1
      refine (hi.div_const (Real.Gamma (1-α)*Real.Gamma α)).congr ?_
      rw [← restrict_Ioo_eq_restrict_Ioc]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      change r^(1-α-1)*(t-r)^(α-1)/(Real.Gamma (1-α)*Real.Gamma α) = L r
      unfold L
      rw [hLk,fractionalK,fractionalK,ite_eq_right (not_le.mpr (sub_pos.mpr hr.2)),
        ite_eq_right (not_le.mpr hr.1),div_mul_div_comm]
      ac_rfl
    have hAi : IntegrableOn A (Ioc 0 t) := density_conv_integrable hα (Ioc_subset_Icc_self ht) hG
    have hLm : (∫ r in Ioc (0:ℝ) t,L r)=1 := by
      change volterraConvolution (fractionalK α) (fractionalL α) t=1
      rw [hLk,fractionalK_convolution_add hα (sub_pos.mpr hα') ht.1,
        show α+(1-α)=1 by ring,fractionalK,ite_eq_right (not_le.mpr ht.1)]
      simp [Real.Gamma_one]
    unfold volterraConvolution
    have he (r : ℝ) : fractionalK α (t-r)*(q+l*(fractionalL α r+κ)-κ*w r-a*(w r)^2) =
      l*L r+A r := by
      dsimp [L,A,G]
      ring
    simp_rw [he]
    have hf := integral_add (hLi.const_mul l) hAi
    rw [hf,integral_const_mul,hLm,mul_one]
  have hContinuous : ContinuousOn (fun t => l+volterraConvolution (fractionalK α) G t) (Icc 0 T) :=
    continuousOn_const.add (continuousOn_volterra_forcing hT.le (fractionalK_measurable α)
      (fractionalK_integrableOn_Ioc hα T) hG.continuousOn)
  have hEq (t : ℝ) (ht : t∈Ioc 0 T) :
      w t=l+volterraConvolution (fractionalK α) G t := (hVol t ht).trans (hKLG t ht)
  intro t ht
  rcases eq_or_lt_of_le ht.1 with he | he
  · subst t
    have hNear : 𝓝[>] (0:ℝ) ≤ 𝓝[Icc (0:ℝ) T] 0 := by
      refine le_inf nhdsWithin_le_nhds (le_principal_iff.mpr ?_)
      filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds hT)] with r hr hrt
      exact ⟨(show 0<r from hr).le,(show r<T from hrt).le⟩
    have hwL : Tendsto w (𝓝[>] (0:ℝ)) (𝓝 (w 0)) :=
      hw.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hR := (hContinuous 0 ⟨le_rfl,hT.le⟩).mono_left hNear
    have hWe : w =ᶠ[𝓝[>] (0:ℝ)] (fun r => l+volterraConvolution (fractionalK α) G r) := by
      filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds hT)] with r hr hrt
      exact hEq r ⟨hr,(show r<T from hrt).le⟩
    exact tendsto_nhds_unique (hwL.congr' hWe) hR
  · exact hEq t ⟨he,ht.2⟩

/-- Any continuous solution of the density affine equation has the
same values on the finite horizon. -/
theorem density_affine_test_eqOn
    {α κ a q l T : ℝ} {v w : ℝ → ℝ}
    (hα : 0<α) (hα' : α<1) (hT : 0<T) (hv : Continuous v) (hw : Continuous w)
    (hV : ∀ t ∈ Ioc 0 T, v t = volterraConvolution (fractionalK α)
      (fun r => q+l*(fractionalL α r+κ)-κ*v r-a*(v r)^2) t)
    (hW : ∀ t ∈ Ioc 0 T, w t = volterraConvolution (fractionalK α)
      (fun r => q+l*(fractionalL α r+κ)-κ*w r-a*(w r)^2) t) :
    EqOn v w (Icc 0 T) := by
  have hV' := affine_density_standard_form hα hα' hT hv hV
  have hW' := affine_density_standard_form hα hα' hT hw hW
  let K := fractionalK α
  let R (s : ℝ) := -κ-a*(v s+w s)
  have hRc : Continuous R := continuous_const.sub (continuous_const.mul (hv.add hw))
  obtain ⟨B,hB⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_bound_of_continuousOn hRc.continuousOn
  have hB₀ : 0≤B := (norm_nonneg _).trans (hB 0 ⟨le_rfl,hT.le⟩)
  have hK₀ (s : ℝ) : 0≤K s := by
    by_cases hs : 0<s
    · dsimp [K]
      rw [fractionalK,ite_eq_right (not_le.mpr hs)]
      exact div_nonneg (Real.rpow_nonneg hs.le _) (Real.Gamma_pos_of_pos hα).le
    · simp [K,fractionalK,le_of_not_gt hs]
  let U (n : ℕ) (s : ℝ) := (n:ℝ)*‖v s-w s‖
  have hUc (n : ℕ) : Continuous (U n) := continuous_const.mul ((hv.sub hw).norm)
  have hU₀ (n : ℕ) (s : ℝ) (_ : s∈Icc 0 T) : 0≤U n s := mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have hIneq (n : ℕ) (t : ℝ) (ht : t∈Icc 0 T) : U n t≤B*(1+volterraConvolution K (U n) t) := by
    let V (s : ℝ) := q+κ*l-κ*v s-a*(v s)^2
    let W (s : ℝ) := q+κ*l-κ*w s-a*(w s)^2
    have hVc : Continuous V := (continuous_const.sub (continuous_const.mul hv)).sub
      (continuous_const.mul (hv.pow 2))
    have hWc : Continuous W := (continuous_const.sub (continuous_const.mul hw)).sub
      (continuous_const.mul (hw.pow 2))
    have hF (s : ℝ) : V s-W s=R s*(v s-w s) := by dsimp [V,W,R]; ring
    have hVi : IntegrableOn (fun r => K (t-r)*V r) (Ioc 0 t) := density_conv_integrable hα ht hVc
    have hWi : IntegrableOn (fun r => K (t-r)*W r) (Ioc 0 t) := density_conv_integrable hα ht hWc
    have he : v t-w t=∫ r in Ioc (0:ℝ) t,K (t-r)*(R r*(v r-w r)) := by
      rw [hV' t ht,hW' t ht,add_sub_add_left_eq_sub]
      change (∫ r in Ioc (0:ℝ) t,K (t-r)*V r)-(∫ r in Ioc (0:ℝ) t,K (t-r)*W r)=_
      rw [← integral_sub hVi hWi]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro r _
      change K (t-r)*V r-K (t-r)*W r=_
      rw [← mul_sub,hF]
    have ht1 : IntegrableOn (fun r => K (t-r)*(R r*(v r-w r))) (Ioc 0 t) :=
      density_conv_integrable hα ht (hRc.mul (hv.sub hw))
    have ht2 : IntegrableOn (fun r => B*(K (t-r)*‖v r-w r‖)) (Ioc 0 t) :=
      (density_conv_integrable hα ht ((hv.sub hw).norm)).const_mul B
    have hnorm : ‖v t-w t‖≤B*(∫ r in Ioc (0:ℝ) t,K (t-r)*‖v r-w r‖) := by
      rw [he,← integral_const_mul]
      refine (norm_integral_le_integral_norm _).trans (setIntegral_mono_on ht1.norm ht2 measurableSet_Ioc
        (fun r hr => ?_))
      rw [norm_mul,norm_mul,Real.norm_of_nonneg (hK₀ _)]
      have hRr := hB r ⟨hr.1.le,hr.2.trans ht.2⟩
      exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hRr (norm_nonneg _)) (hK₀ _)).trans_eq (by ring)
    have hscale : volterraConvolution K (U n) t =
      (n:ℝ)*(∫ r in Ioc (0:ℝ) t,K (t-r)*‖v r-w r‖) := by
      unfold volterraConvolution
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro r _
      dsimp [U]
      ring
    change (n:ℝ)*‖v t-w t‖≤_
    rw [hscale]
    have h := mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg n)
    linarith
  have hKi : IntervalIntegrable K volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr (fractionalK_integrableOn_Ioc hα T)
  obtain ⟨C,hC⟩ := uniform_volterra_moment_bound hT.le hB₀ hKi (fractionalK_measurable α)
    (fun s _ => hK₀ s) (fun n => (hUc n).measurable) hU₀
    (fun n => isCompact_Icc.bddAbove_image (hUc n).continuousOn) hIneq
  intro t ht
  by_contra hn
  have hp : 0<‖v t-w t‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hn)
  obtain ⟨n,hn⟩ := exists_nat_gt (C/‖v t-w t‖)
  exact (not_lt_of_ge (hC n t ht)) ((div_lt_iff₀ hp).mp hn)

#print axioms density_affine_test_eqOn

end RoughHeston
