import AffinePathwiseTransform
import AffineVariancePreterminal
import AffineDensityMartingale
import AffineTerminalPassage

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal Interval

namespace RoughHeston

noncomputable def affinePreterminalCompensator {Ω : Type*}
    (T H : ℝ≥0) (w : ℝ → ℝ) (b : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  affineStoppedBracket H
    (fun r ω => (affinePreterminalWeight w ((T:ℝ)-(H:ℝ)) H r)^2*b r ω) t ω

theorem affinePreterminalCompensator_eq {Ω : Type*}
    (T H : ℝ≥0) (w : ℝ → ℝ) (b : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    affinePreterminalCompensator T H w b t ω =
      ∫ r in Ioc (0:ℝ) ((min t H:ℝ≥0):ℝ), (w ((T:ℝ)-r))^2*b r.toNNReal ω := by
  unfold affinePreterminalCompensator affineStoppedBracket
  rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg _)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r hr
  have hrN : r.toNNReal ≤ H := NNReal.coe_le_coe.mp (by
    rw [Real.coe_toNNReal r hr.1.le]
    exact hr.2.trans (NNReal.coe_le_coe.mpr (min_le_right _ _)))
  simp only [affinePreterminalWeight, min_eq_left hrN, Real.coe_toNNReal r hr.1.le]
  rw [show (T:ℝ)-(H:ℝ)+((H:ℝ)-r)=(T:ℝ)-r by ring]

theorem affinePreterminalCompensator_continuous {Ω : Type*}
    {T H : ℝ≥0} (hH : H<T) {w : ℝ → ℝ} (hw : ContinuousOn w (Ioi 0))
    {b : ℝ≥0 → Ω → ℝ} (hb : ∀ ω, Continuous fun t => b t ω) (ω : Ω) :
    Continuous (fun t => affinePreterminalCompensator T H w b t ω) := by
  have hArg : Continuous (fun t : ℝ≥0 => (T:ℝ)-(min t H:ℝ≥0)) :=
    continuous_const.sub (NNReal.continuous_coe.comp (continuous_id.min continuous_const))
  have hW : Continuous (fun t : ℝ≥0 => affinePreterminalWeight w ((T:ℝ)-(H:ℝ)) H t) := by
    convert hw.comp_continuous hArg (fun t =>
      sub_pos.mpr (NNReal.coe_lt_coe.mpr ((min_le_right t H).trans_lt hH))) using 1
    funext t
    unfold affinePreterminalWeight
    congr 1
    ring
  have hc : Continuous (fun r : ℝ =>
      (affinePreterminalWeight w ((T:ℝ)-(H:ℝ)) H r.toNNReal)^2*b r.toNNReal ω) :=
    ((hW.comp continuous_real_toNNReal).pow 2).mul ((hb ω).comp continuous_real_toNNReal)
  exact (intervalIntegral.continuous_primitive (fun a b => hc.intervalIntegrable a b) 0).comp
    (NNReal.continuous_coe.comp (continuous_id.min continuous_const))

theorem affinePreterminalVarianceMartingale_consistent {Ω : Type*}
    (T H : ℝ≥0) (w : ℝ → ℝ) (M : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) :
    affinePreterminalVarianceMartingale H ((T:ℝ)-(H:ℝ)) w M t =
    affinePreterminalVarianceMartingale (min t H) ((T:ℝ)-(min t H:ℝ≥0)) w M (min t H) := by
  funext ω
  simp only [affinePreterminalVarianceMartingale, sub_add_cancel, min_self]

/-- Stochastic exponential associated with the preterminal
Riccati-weighted variance martingale. -/
noncomputable def affinePreterminalDensity {Ω : Type*}
    (T H : ℝ≥0) (w : ℝ → ℝ) (M b : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (-affinePreterminalVarianceMartingale H ((T:ℝ)-(H:ℝ)) w M t ω -
    affinePreterminalCompensator T H w b t ω/2)

/-- The inverse variance equation and its ordinary bracket imply the
conditional affine Laplace transform for a mixed point and density
test. The Riccati equation is the only deterministic test input. -/
theorem heston_conditional_affine_transform
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} {M V C : ℝ≥0 → Ω → ℝ}
    {α κ a q : ℝ} {T s : ℝ≥0} {w f j : ℝ → ℝ}
    (hα : 0 < α) (hα' : α < 1) (ha : 0 ≤ a) (hs : s < T)
    (hw : AffineRiccatiTestOn α κ a q (T:ℝ) w f) (hj : AffineInputOn (T:ℝ) j)
    (hM : Martingale M 𝒢 μ) (hM₂ : ∀ t, MemLp (M t) 2 μ)
    (hMc : ∀ ω, Continuous fun t => M t ω)
    (hM0 : ∀ᵐ ω ∂μ, M 0 ω = 0)
    (hV : StronglyAdapted 𝒢 V) (hVc : ∀ ω, Continuous fun t => V t ω)
    (hVnn : ∀ t ω, 0 ≤ V t ω) {V₀ : ℝ} (hV₀ : ∀ ω, V 0 ω ≤ V₀)
    (hMC : Martingale (fun t => M t*M t-C t) 𝒢 μ)
    (hCi : ∀ t, Integrable (C t) μ)
    (hCmon : ∀ s t, s ≤ t → C s ≤ᵐ[μ] C t)
    (hC : ∀ t ≤ T, C t =ᵐ[μ] fun ω => ∫ r in (0:ℝ)..(t:ℝ), (2*a)*V r.toNNReal ω)
    (hInv : ∀ᵐ ω ∂μ, ∀ r ∈ Ioc (0:ℝ) (T:ℝ),
      M r.toNNReal ω = volterraConvolution (fractionalL α) (fun u => V u.toNNReal ω) r +
        ∫ u in Ioc (0:ℝ) r, κ*V u.toNNReal ω-j u) :
    μ[(fun ω => Real.exp (-(q*V T ω + affinePastPayoff f (fun r => V r.toNNReal ω) T T))) | 𝒢 s]
      =ᵐ[μ] fun ω => Real.exp (-(affinePastPayoff f (fun r => V r.toNNReal ω) T s +
        affineFuturePayoff α w j (fun r => V r.toNNReal ω) T s)) := by
  let _ : MeasurableSpace Ω := m
  let c := volterraConvolution w j (T:ℝ)
  let v (ω : Ω) (r : ℝ) := V r.toNNReal ω
  let b (t : ℝ≥0) (ω : Ω) := (2*a)*V t ω
  let N (H : ℝ≥0) := affinePreterminalVarianceMartingale H ((T:ℝ)-(H:ℝ)) w M
  let A (H : ℝ≥0) := affinePreterminalCompensator T H w b
  let E (H t : ℝ≥0) (ω : Ω) := Real.exp (-N H t ω-A H t ω/2)
  let F (t : ℝ≥0) (ω : Ω) :=
    affinePastPayoff f (v ω) T t+affineFuturePayoff α w j (v ω) T t
  let payoff (ω : Ω) := q*V T ω+affinePastPayoff f (v ω) T T
  let D (t : ℝ≥0) (ω : Ω) := if t<T then E t t ω else Real.exp (c-payoff ω)
  have hT : 0<T := zero_le.trans_lt hs
  have hTr : (0:ℝ)<T := NNReal.coe_pos.mpr hT
  have hbAd : StronglyAdapted 𝒢 b := fun t => (hV t).const_mul (2*a)
  have hbC (ω : Ω) : Continuous (fun t => b t ω) := continuous_const.mul (hVc ω)
  have hbNN (t : ℝ≥0) (ω : Ω) : 0 ≤ b t ω :=
    mul_nonneg (by positivity) (hVnn t ω)
  have hbStart (ω : Ω) : b 0 ω ≤ (2*a)*V₀ :=
    mul_le_mul_of_nonneg_left (hV₀ ω) (by positivity)
  have heCons (H t : ℝ≥0) (ω : Ω) : E H t ω = E (min t H) (min t H) ω := by
    have hN := congrFun (affinePreterminalVarianceMartingale_consistent T H w M t) ω
    have hA : A H t ω = A (min t H) (min t H) ω := by
      simp only [A, affinePreterminalCompensator_eq, min_self]
    dsimp only [E]
    rw [hA]
    exact congrArg (fun n => Real.exp (-n-A (min t H) (min t H) ω/2)) hN
  have hDE (H : ℝ≥0) (hH : H<T) (t : ℝ≥0) (ω : Ω) : D (min t H) ω = E H t ω := by
    simp only [D, ite_eq_left ((min_le_right t H).trans_lt hH), heCons H t ω]
  have hEdata (H : ℝ≥0) (hH : H<T) :
      StronglyAdapted 𝒢 (E H) ∧ IsLocalMartingale (E H) 𝒢 μ := by
    obtain ⟨hN,hNA,hE⟩ := affine_preterminal_variance_exponential
      (sub_pos.mpr (NNReal.coe_lt_coe.mpr hH)) H hw.solution_smooth
      hM hM₂ hMc hMC hCi hCmon (fun t ht => hC t (ht.trans hH.le)) hbAd hbC hbNN hbStart
    refine ⟨fun t => ?_, hE⟩
    have hAt : StronglyMeasurable[𝒢 t] (A H t) := by
      have hh := ((hN.stronglyAdapted t).pow 2).sub (hNA.stronglyAdapted t)
      convert hh using 1
      funext ω
      change A H t ω = N H t ω^2-(N H t ω^2-A H t ω)
      ring
    exact Real.continuous_exp.comp_stronglyMeasurable
      ((hN.stronglyAdapted t).neg.sub (hAt.mul_const (2:ℝ)⁻¹))
  have hEc (H : ℝ≥0) (hH : H<T) (ω : Ω) : Continuous (fun t => E H t ω) :=
    Real.continuous_exp.comp ((affinePreterminalVarianceMartingale_continuous H
      (sub_pos.mpr (NNReal.coe_lt_coe.mpr hH)) hw.solution_smooth hMc ω).neg.sub
        ((affinePreterminalCompensator_continuous hH hw.solution_continuous hbC ω).div_const 2))
  have hPayAd : StronglyMeasurable[𝒢 T] payoff := by
    have hP := weighted_time_primitive_stronglyMeasurable hV hVc
      (d := fun r => f ((T:ℝ)-r)) (hw.rate_measurable.comp (measurable_const.sub measurable_id)) T
    rw [show (fun ω => ∫ r in (0:ℝ)..(T:ℝ), f ((T:ℝ)-r)*V r.toNNReal ω) =
      (fun ω => affinePastPayoff f (v ω) T T) by
        funext ω
        exact intervalIntegral.integral_of_le (NNReal.coe_nonneg T)] at hP
    exact ((hV T).const_mul q).add hP
  have hDAd : StronglyAdapted 𝒢 D := by
    intro t
    by_cases ht : t<T
    · simpa only [D,ite_eq_left ht] using (hEdata t ht).1 t
    · have hl := Real.continuous_exp.comp_stronglyMeasurable
        ((stronglyMeasurable_const : StronglyMeasurable[𝒢 t] (fun _ : Ω => c)).sub
          (hPayAd.mono (𝒢.mono (le_of_not_gt ht))))
      simpa only [D,ite_eq_right ht,Pi.sub_apply] using hl
  have hPath (ω : Ω) (h0 : M 0 ω=0)
      (hi : ∀ r ∈ Ioc (0:ℝ) (T:ℝ), M r.toNNReal ω =
        volterraConvolution (fractionalL α) (v ω) r + ∫ u in Ioc (0:ℝ) r, κ*v ω u-j u)
      (t : ℝ≥0) (ht : t<T) : D t ω = Real.exp (c-F t ω) := by
    change (if t<T then E t t ω else Real.exp (c-payoff ω)) = _
    rw [ite_eq_left ht]
    rcases eq_or_lt_of_le (zero_le : 0≤t) with h | h
    · subst t
      simp [E,N,A,affinePreterminalVarianceMartingale,affinePreterminalCompensator_eq,F,c]
    have hTrt : (0:ℝ)<t := NNReal.coe_pos.mpr h
    have hrtT : (t:ℝ)<T := NNReal.coe_lt_coe.mpr ht
    have hSplit := affine_pathwise_exponent_split hα hα' ⟨hTrt,hrtT⟩ hw hj
      ((hVc ω).comp continuous_real_toNNReal)
      (fun r hr => hi r ⟨hr.1,hr.2.trans hrtT.le⟩)
    have hNv : N t t ω = w ((T:ℝ)-t)*M t ω +
        ∫ r in Ioc (0:ℝ) (t:ℝ), deriv w ((T:ℝ)-r)*M r.toNNReal ω := by
      simp only [N,affinePreterminalVarianceMartingale,sub_add_cancel,min_self,h0,mul_zero,sub_zero]
      rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t)]
    have hAv : A t t ω = (2*a)*(∫ r in Ioc (0:ℝ) (t:ℝ), (w ((T:ℝ)-r))^2*v ω r) := by
      change affinePreterminalCompensator T t w b t ω = _
      rw [affinePreterminalCompensator_eq,min_self,← integral_const_mul]
      congr 1
      funext r
      dsimp [b,v]
      ring
    rw [Real.toNNReal_coe] at hSplit
    change w ((T:ℝ)-↑t)*M t ω +
      (∫ r in Ioc (0:ℝ) (t:ℝ), deriv w ((T:ℝ)-r)*M r.toNNReal ω) +
      a*(∫ r in Ioc (0:ℝ) (t:ℝ), (w ((T:ℝ)-r))^2*v ω r) =
      affinePastPayoff f (v ω) T t-c+affineFuturePayoff α w j (v ω) T t at hSplit
    dsimp only [E,F]
    rw [hNv,hAv]
    congr 1
    linarith
  have hDPath : ∀ᵐ ω ∂μ, ∀ t<T, D t ω=Real.exp (c-F t ω) := by
    filter_upwards [hM0,hInv] with ω h0 hi
    exact hPath ω h0 hi
  have hDB (t : ℝ≥0) (ht : t<T) : ∀ᵐ ω ∂μ, ‖D t ω‖ ≤ Real.exp c := by
    filter_upwards [hDPath] with ω hω
    rw [hω t ht,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hP := affine_past_payoff_nonnegative (V := v ω) (NNReal.coe_lt_coe.mpr ht) hw
      (fun r _ => hVnn r.toNNReal ω)
    have hF := affine_future_payoff_nonnegative hα.le hα'
      (V := v ω) ⟨NNReal.coe_nonneg t, NNReal.coe_le_coe.mpr ht.le⟩ hw hj
      (fun r _ => hVnn r.toNNReal ω)
    change c-(affinePastPayoff f (v ω) T t+affineFuturePayoff α w j (v ω) T t) ≤ c
    linarith
  have hPre (H : ℝ≥0) (hH : H<T) : Martingale (fun t => D (min t H)) 𝒢 μ := by
    have hE := hEdata H hH
    have hb (t : ℝ≥0) : ∀ᵐ ω ∂μ, ‖E H t ω‖ ≤ Real.exp c := by
      simpa only [hDE H hH t] using hDB (min t H) ((min_le_right t H).trans_lt hH)
    have hEB := ae_uniform_bound_of_timewise_bound (ae_of_all _ (hEc H hH)) hb
    have hEM := martingale_of_bounded_localMartingale hE.1 hE.2 (Real.exp_pos c).le hEB
    exact hEM.congr (fun t => (hDAd (min t H)).mono (𝒢.mono (min_le_left _ _)))
      (fun t => ae_of_all _ fun ω => (hDE H hH t ω).symm)
  have hLeft : ∀ᵐ ω ∂μ, Tendsto (fun t => D t ω) (𝓝[<] T) (𝓝 (D T ω)) := by
    filter_upwards [hDPath] with ω hω
    have hCoe : Tendsto (fun r : ℝ≥0 => (r:ℝ)) (𝓝[<] T) (𝓝[<] (T:ℝ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact NNReal.continuous_coe.continuousAt.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact NNReal.coe_lt_coe.mpr (show r<T from hr)
    have hf := (affine_pathwise_payoffs_left_limit hα hα' hTr hw hj
      ((hVc ω).comp continuous_real_toNNReal)).comp hCoe
    have hf' : Tendsto (fun t => F t ω) (𝓝[<] T) (𝓝 (payoff ω)) := by
      simpa only [Function.comp_def,F,payoff,v,Real.toNNReal_coe] using hf
    have hExp := (Real.continuous_exp.tendsto (c-payoff ω)).comp (hf'.const_sub c)
    have hTval : D T ω=Real.exp (c-payoff ω) := by simp [D]
    rw [hTval]
    refine hExp.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hω t (show t<T from ht)).symm
  have hDM := affine_martingale_of_bounded_preterminal_of_left_limit hT hDAd
    (Real.exp_pos c).le hDB hLeft hPre
  have hPay : (fun ω => Real.exp (-payoff ω)) =ᵐ[μ] Real.exp (-c) • D T := by
    exact ae_of_all _ fun ω => by
      rw [Pi.smul_apply,smul_eq_mul,show D T ω = Real.exp (c-payoff ω) by simp [D],← Real.exp_add]
      rw [show -c+(c-payoff ω) = -payoff ω by ring]
  have hCE := hDM.condExp_ae_eq hs.le
  simp only [min_self,min_eq_left hs.le] at hCE
  change μ[(fun ω => Real.exp (-payoff ω)) | 𝒢 s] =ᵐ[μ] fun ω => Real.exp (-F s ω)
  refine ((condExp_congr_ae hPay).trans (condExp_smul (Real.exp (-c)) (D T) (𝒢 s))).trans ?_
  filter_upwards [hCE,hDPath] with ω hc hω
  rw [Pi.smul_apply,smul_eq_mul,hc,hω s hs,← Real.exp_add]
  rw [show -c+(c-F s ω) = -F s ω by ring]

#print axioms heston_conditional_affine_transform

end RoughHeston
