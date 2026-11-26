import AffineMeanContinuity
import FractionalBoundaryHistory

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RoughHeston

/-- A conditional backward power bound gives a conditional first
moment bound for the future point-test exponent, uniformly in charge. -/
theorem affine_future_payoff_mean_bound
    {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {V : ℝ → Ω → ℝ} {j w : ℝ → ℝ} {α p t h C J W B : ℝ}
    (hα : 0<α) (hα' : α<1) (hp : 0<p) (hpα : p<α) (hη : 0 < p+1-2*α)
    (ht : 0≤t) (hh : 0<h) (hh₁ : h≤1) (hC : 0≤C) (hJ : 0≤J) (hW : 0≤W)
    (hVm : ∀ r,Measurable (V r)) (hVc : ∀ ω,Continuous fun r => V r ω)
    (hVnn : ∀ r ω,0≤V r ω) (hVi : ∀ r∈Ioc 0 t,Integrable (V r) Q)
    (hVB : ∀ r∈Ioc 0 t,(∫ ω,‖V r ω‖ ∂Q)≤B)
    (hBack : ∀ u∈Ioc (0:ℝ) t,(∫ ω,V (t-u) ω ∂Q)≤C*u^p)
    (hjm : Measurable j) (hjb : ∀ y∈Ioo 0 h,0≤j (t+y) ∧ j (t+y)≤J)
    (hwm : Measurable w) (hwb : ∀ y∈Ioo 0 h,0≤w y ∧ w y≤W*y^(-α)) :
    let K := α/Real.Gamma (1-α)
    let D := ∫ u in Ioi (0:ℝ),(1+u)^(-(1+α))*u^p
    let A := Real.Gamma (1+p-α)*Real.Gamma (1-α)/Real.Gamma (2+p-2*α)
    Integrable (fun ω => affineFuturePayoff α w j (fun r => V r ω) (t+h) t) Q ∧
      (∫ ω,affineFuturePayoff α w j (fun r => V r ω) (t+h) t ∂Q) ≤
        (2*W*(J+K*C*D)*A)*h^(p+1-2*α) := by
  let K := α/Real.Gamma (1-α)
  let D := ∫ u in Ioi (0:ℝ),(1+u)^(-(1+α))*u^p
  let A := Real.Gamma (1+p-α)*Real.Gamma (1-α)/Real.Gamma (2+p-2*α)
  let f (r : ℝ) := ∫ ω,V r ω ∂Q
  let H (y r : ℝ) := fractionalHistoryDensity α (t+y-r)
  let P (y : ℝ) (ω : Ω) := affineFutureInput α t j (fun r => V r ω) y
  let ν := volume.restrict (Ioo (0:ℝ) h)
  let F (z : ℝ × Ω) := w (h-z.1)*P z.1 z.2
  let G (y : ℝ) := ((h-y)^(-α))*y^(p-α)
  let E := 2*W*(J+K*C*D)
  have hK : 0≤K := div_nonneg hα.le (Real.Gamma_pos_of_pos (sub_pos.mpr hα')).le
  have hD : 0≤D := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (Real.rpow_nonneg (by linarith [show 0<u from hu]) _)
      (Real.rpow_nonneg (show 0≤u from (show 0<u from hu).le) _)
  have hE : 0≤E := by dsimp [E]; positivity
  have hVjoint : Measurable (Function.uncurry V) :=
    measurable_uncurry_of_continuous_of_measurable hVc hVm
  have hfM : Measurable f := measurable_affine_variance_mean hVm hVc
  have hfN (r : ℝ) : 0≤f r := integral_nonneg fun ω => hVnn r ω
  have hHistM : Measurable (fractionalHistoryDensity α) := (measurable_id.pow_const _).const_mul _
  have hHistM' (y : ℝ) : Measurable (H y) := hHistM.comp (measurable_const.sub measurable_id)
  have hPm : Measurable (Function.uncurry P) := by
    let G' (z : (ℝ × Ω) × ℝ) := H z.1.1 z.2*V z.2 z.1.2
    have hG' : Measurable G' := (hHistM.comp
      ((measurable_const.add (measurable_fst.comp measurable_fst)).sub measurable_snd)).mul
      (hVjoint.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
    exact (hjm.comp (measurable_const.add measurable_fst)).add
      (hG'.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc 0 t))).measurable
  have hFm : Measurable F := (hwm.comp (measurable_const.sub measurable_fst)).mul hPm
  have hPn (y : ℝ) (hy : y∈Ioo 0 h) (ω : Ω) : 0≤P y ω := by
    refine add_nonneg (hjb y hy).1 ?_
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact mul_nonneg (fractionalHistoryDensity_nonneg hα.le hα' (by linarith [hy.1,hr.2]))
      (hVnn r ω)
  have hReflect (y : ℝ) (hy : 0<y) :
      (∫ r in Ioc (0:ℝ) t,H y r*f r) ≤ K*C*D*y^(p-α) := by
    have hBack' : (∫ u in Ioc (0:ℝ) t,(y+u)^(-(1+α))*f (t-u))≤C*D*y^(p-α) :=
      conditionalHistory_power_bound hp hpα hy hC (hfM.comp (measurable_const.sub measurable_id))
        (fun u _ => hfN _) hBack
    have he : (∫ r in Ioc (0:ℝ) t,H y r*f r) =
        K*(∫ u in Ioc (0:ℝ) t,(y+u)^(-(1+α))*f (t-u)) := by
      unfold H fractionalHistoryDensity
      simp_rw [mul_assoc]
      rw [integral_const_mul]
      congr 1
      let G' (u : ℝ) := (y+u)^(-(1+α))*f (t-u)
      have hEq (r : ℝ) : (t+y-r)^(-(1+α))*f r=G' (t-r) := by
        dsimp [G']
        rw [show t-(t-r)=r by ring,show y+(t-r)=t+y-r by ring]
      simp_rw [hEq]
      rw [← intervalIntegral.integral_of_le ht,intervalIntegral.integral_comp_sub_left,
        sub_self,sub_zero,intervalIntegral.integral_of_le ht]
    rw [he]
    exact (mul_le_mul_of_nonneg_left hBack' hK).trans_eq (by ring)
  have hQ (y : ℝ) (hy : y∈Ioo 0 h) :
      Integrable (P y) Q ∧ (∫ ω,P y ω ∂Q)≤(J+K*C*D)*(1+y^(p-α)) := by
    have hci : IntegrableOn (H y) (Ioc 0 t) := by
      have hArg : ContinuousOn (fun r : ℝ => t+y-r) (Icc 0 t) :=
        (continuous_const.sub continuous_id).continuousOn
      have hc : ContinuousOn (H y) (Icc 0 t) := (hArg.rpow_const
        (p := -(1+α)) (fun r hr => Or.inl (ne_of_gt (by linarith [hy.1,hr.2])))).const_mul K
      exact (hc.intervalIntegrable_of_Icc ht).1
    have hFi := affine_weighted_mean_integral hVm hVc hVi hVB (hHistM' y) hci
    have hPInt : Integrable (P y) Q :=
      (integrable_const (j (t+y))).add hFi.1.integral_prod_right
    refine ⟨hPInt,?_⟩
    have hhI := integral_add (integrable_const (j (t+y))) hFi.1.integral_prod_right
    change (∫ ω,j (t+y)+(∫ r in Ioc (0:ℝ) t,H y r*V r ω) ∂Q)≤_
    rw [hhI,integral_const,probReal_univ,one_smul,hFi.2]
    have hyP : 0≤y^(p-α) := Real.rpow_nonneg hy.1.le _
    have hKK : 0≤K*C*D := by positivity
    have hhh := add_le_add (hjb y hy).2 (hReflect y hy.1)
    nlinarith [mul_nonneg hJ hyP]
  have hGData := real_beta_weight_scaled (a := 1+p-α) (b := 1-α)
    (by linarith : 0<1+p-α) (sub_pos.mpr hα') hh
  have hGi : Integrable G ν := by
    have hi := hGData.1
    simp only [show 1+p-α-1=p-α by ring,show 1-α-1=(-α) by ring] at hi
    refine (IntegrableOn.mono_set hi Ioo_subset_Ioc_self).congr ?_
    exact ae_of_all _ fun y => mul_comm _ _
  have hGe : (∫ y,G y ∂ν)=A*h^(p+1-2*α) := by
    dsimp [ν,G]
    rw [restrict_Ioo_eq_restrict_Ioc]
    have he := hGData.2
    simp only [show 1+p-α-1=p-α by ring,show 1-α-1=(-α) by ring,
      show 1+p-α+(1-α)=2+p-2*α by ring,
      show 2+p-2*α-1=p+1-2*α by ring] at he
    conv_lhs => enter [2,y]; rw [mul_comm]
    exact he.trans (mul_comm _ _)
  have hFbound (y : ℝ) (hy : y∈Ioo 0 h) :
      (∫ ω,‖F (y,ω)‖ ∂Q)≤E*G y := by
    have hwY := hwb (h-y) ⟨sub_pos.mpr hy.2,by linarith [hy.1]⟩
    have hEq : (∫ ω,‖F (y,ω)‖ ∂Q)=w (h-y)*(∫ ω,P y ω ∂Q) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with ω
      exact Real.norm_of_nonneg (mul_nonneg hwY.1 (hPn y hy ω))
    rw [hEq]
    have hV₀ : 0≤(∫ ω,P y ω ∂Q) := integral_nonneg (hPn y hy)
    have hBnd := mul_le_mul hwY.2 (hQ y hy).2 hV₀
      (mul_nonneg hW (Real.rpow_nonneg (sub_nonneg.mpr hy.2.le) _))
    refine hBnd.trans ?_
    have hyP : 1≤y^(p-α) := by simpa only [Real.one_rpow] using
      Real.rpow_le_rpow_of_nonpos hy.1 (hy.2.le.trans hh₁) (sub_nonpos.mpr hpα.le)
    dsimp [E,G]
    calc
      _ ≤ (W*(h-y)^(-α))*((J+K*C*D)*(2*y^(p-α))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
          (mul_nonneg hW (Real.rpow_nonneg (sub_nonneg.mpr hy.2.le) _))
      _ = _ := by ring
  have hFi : Integrable F (ν.prod Q) := by
    refine (integrable_prod_iff hFm.aestronglyMeasurable).mpr ⟨?_,?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
      exact (hQ y hy).1.const_mul (w (h-y))
    · refine (hGi.const_mul E).mono_nonneg
        (hFm.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
        (ae_of_all _ fun _ => integral_nonneg fun _ => norm_nonneg _) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
      exact hFbound y hy
  have hfe (ω : Ω) : affineFuturePayoff α w j (fun r => V r ω) (t+h) t =
      ∫ y,F (y,ω) ∂ν := by
    unfold affineFuturePayoff
    rw [add_sub_cancel_left,← restrict_Ioo_eq_restrict_Ioc]
  have hBi : Integrable (fun ω => affineFuturePayoff α w j (fun r => V r ω) (t+h) t) Q :=
    hFi.integral_prod_right.congr (ae_of_all _ fun ω => (hfe ω).symm)
  refine ⟨hBi,?_⟩
  simp_rw [hfe]
  rw [← integral_prod_symm F hFi,integral_prod F hFi]
  have hIn := hFi.integral_prod_left
  have hBnd : (∫ y,(∫ ω,F (y,ω) ∂Q) ∂ν)≤∫ y,E*G y ∂ν := by
    refine integral_mono_ae hIn (hGi.const_mul E) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    calc
      _ ≤ ‖∫ ω,F (y,ω) ∂Q‖ := le_abs_self _
      _ ≤ ∫ ω,‖F (y,ω)‖ ∂Q := norm_integral_le_integral_norm _
      _ ≤ _ := hFbound y hy
  exact hBnd.trans_eq (by rw [integral_const_mul,hGe]; dsimp [E]; ring)

#print axioms affine_future_payoff_mean_bound

end RoughHeston
