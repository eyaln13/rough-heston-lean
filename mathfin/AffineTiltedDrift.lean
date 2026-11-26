import HestonConditionalAffine
import AffinePerturbationDerivative

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal Interval

namespace RoughHeston

noncomputable def affineWeightedDrift {Ω : Type*}
    (T H : ℝ≥0) (w : ℝ → ℝ) (b : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ r in Ioc (0:ℝ) ((min t H:ℝ≥0):ℝ), w ((T:ℝ)-r)*b r.toNNReal ω

theorem affinePreterminalDensity_martingale_of_bound
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} {M C b : ℝ≥0 → Ω → ℝ}
    {T H : ℝ≥0} (hH : H<T) {w : ℝ → ℝ}
    (hw : ∀ s > 0, ContDiffAt ℝ 1 w s)
    (hM : Martingale M 𝒢 μ) (hM₂ : ∀ t, MemLp (M t) 2 μ)
    (hMc : ∀ ω, Continuous fun t => M t ω)
    (hMC : Martingale (fun t => M t*M t-C t) 𝒢 μ)
    (hCi : ∀ t, Integrable (C t) μ)
    (hCmon : ∀ s t, s ≤ t → C s ≤ᵐ[μ] C t)
    (hC : ∀ t ≤ H, C t =ᵐ[μ] fun ω => ∫ r in (0:ℝ)..(t:ℝ), b r.toNNReal ω)
    (hbAd : StronglyAdapted 𝒢 b) (hbC : ∀ ω, Continuous fun t => b t ω)
    (hbNN : ∀ t ω, 0 ≤ b t ω) {L B : ℝ} (hbStart : ∀ ω, b 0 ω ≤ L)
    (hB : 0 ≤ B) (hBdd : ∀ t, ∀ᵐ ω ∂μ, ‖affinePreterminalDensity T H w M b t ω‖ ≤ B) :
    Martingale (affinePreterminalDensity T H w M b) 𝒢 μ := by
  have hd : 0 < (T:ℝ)-(H:ℝ) := sub_pos.mpr (NNReal.coe_lt_coe.mpr hH)
  obtain ⟨hN,hNA,hE⟩ := affine_preterminal_variance_exponential hd H hw
    hM hM₂ hMc hMC hCi hCmon hC hbAd hbC hbNN hbStart
  let N := affinePreterminalVarianceMartingale H ((T:ℝ)-(H:ℝ)) w M
  let A := affinePreterminalCompensator T H w b
  have hAd : StronglyAdapted 𝒢 (affinePreterminalDensity T H w M b) := by
    intro t
    have hAt : StronglyMeasurable[𝒢 t] (A t) := by
      have hh := ((hN.stronglyAdapted t).pow 2).sub (hNA.stronglyAdapted t)
      convert hh using 1
      funext ω
      change A t ω = N t ω^2-(N t ω^2-A t ω)
      ring
    exact Real.continuous_exp.comp_stronglyMeasurable
      ((hN.stronglyAdapted t).neg.sub (hAt.mul_const (2:ℝ)⁻¹))
  have hCont (ω : Ω) : Continuous (fun t => affinePreterminalDensity T H w M b t ω) :=
    Real.continuous_exp.comp ((affinePreterminalVarianceMartingale_continuous H hd hw hMc ω).neg.sub
      ((affinePreterminalCompensator_continuous hH
        (fun r hr => (hw r hr).continuousAt.continuousWithinAt) hbC ω).div_const 2))
  exact martingale_of_bounded_localMartingale hAd hE hB
    (ae_uniform_bound_of_timewise_bound (ae_of_all _ hCont) hBdd)

private theorem affine_preterminal_perturbation_expand
    {Ω : Type*} {T H : ℝ≥0} (hH : H<T)
    {w : ℝ → ℝ} (hw : ContinuousOn w (Ioi 0))
    {M b : ℝ≥0 → Ω → ℝ} (hb : ∀ ω, Continuous (fun t => b t ω))
    (ε : ℝ) (t : ℝ≥0) (ω : Ω) :
    affinePreterminalDensity T H (fun x => w x+ε) M b t ω =
      affinePreterminalDensity T H w M b t ω *
        Real.exp (-ε*(M (min t H) ω-M 0 ω+affineWeightedDrift T H w b t ω)-
          ε^2*(∫ r in Ioc (0:ℝ) ((min t H:ℝ≥0):ℝ), b r.toNNReal ω)/2) := by
  let U := ((min t H:ℝ≥0):ℝ)
  let W (r : ℝ) := w ((T:ℝ)-r)
  let f (r : ℝ) := b r.toNNReal ω
  have hU : 0≤U := NNReal.coe_nonneg _
  have hFc : Continuous f := (hb ω).comp continuous_real_toNNReal
  have hWc : ContinuousOn W (Icc 0 U) :=
    hw.comp (continuous_const.sub continuous_id).continuousOn (fun r hr =>
      sub_pos.mpr (hr.2.trans_lt (NNReal.coe_lt_coe.mpr ((min_le_right t H).trans_lt hH))))
  have hf : IntegrableOn f (Ioc 0 U) := (hFc.intervalIntegrable 0 U).1
  have h1 : IntegrableOn (fun r => W r*f r) (Ioc 0 U) :=
    ((hWc.mul hFc.continuousOn).intervalIntegrable_of_Icc hU).1
  have h2 : IntegrableOn (fun r => (W r)^2*f r) (Ioc 0 U) :=
    (((hWc.pow 2).mul hFc.continuousOn).intervalIntegrable_of_Icc hU).1
  have hC : affinePreterminalCompensator T H (fun x => w x+ε) b t ω =
      affinePreterminalCompensator T H w b t ω + 2*ε*affineWeightedDrift T H w b t ω +
        ε^2*(∫ r in Ioc (0:ℝ) U,f r) := by
    rw [affinePreterminalCompensator_eq,affinePreterminalCompensator_eq,affineWeightedDrift]
    change (∫ r in Ioc (0:ℝ) U,(W r+ε)^2*f r) =
      (∫ r in Ioc (0:ℝ) U,(W r)^2*f r)+2*ε*(∫ r in Ioc (0:ℝ) U,W r*f r) +
        ε^2*(∫ r in Ioc (0:ℝ) U,f r)
    have he (r : ℝ) : (W r+ε)^2*f r = ((W r)^2*f r+2*ε*(W r*f r))+ε^2*f r := by ring
    simp_rw [he]
    have he1 := integral_add h2 (h1.const_mul (2*ε))
    have he2 := integral_add (h2.add (h1.const_mul (2*ε))) (hf.const_mul (ε^2))
    simp only [Pi.add_apply] at he1 he2
    rw [he2,he1,integral_const_mul,integral_const_mul]
  have hN : affinePreterminalVarianceMartingale H ((T:ℝ)-(H:ℝ)) (fun x => w x+ε) M t ω =
      affinePreterminalVarianceMartingale H ((T:ℝ)-(H:ℝ)) w M t ω + ε*(M (min t H) ω-M 0 ω) := by
    simp only [affinePreterminalVarianceMartingale,deriv_add_const]
    ring
  rw [affinePreterminalDensity,hC,hN,affinePreterminalDensity,← Real.exp_add]
  congr 1
  ring

/-- An affine density gives the expected preterminal drift under the
tilt. The covariance correction is derived by perturbing the weighted
exponential, with all martingales in the supplied filtration. -/
theorem affine_preterminal_density_weighted_drift
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} {M C b : ℝ≥0 → Ω → ℝ}
    {T H : ℝ≥0} (hH : H<T) {w : ℝ → ℝ}
    (hwm : Measurable w) (hw : ∀ s > 0, ContDiffAt ℝ 1 w s)
    (hwn : ∀ r ∈ Icc ((T:ℝ)-(H:ℝ)) (T:ℝ),0≤w r)
    (hM : Martingale M 𝒢 μ) (hM₂ : ∀ t, MemLp (M t) 2 μ)
    (hMc : ∀ ω, Continuous fun t => M t ω)
    (hM0 : ∀ᵐ ω ∂μ, M 0 ω=0)
    (hMC : Martingale (fun t => M t*M t-C t) 𝒢 μ)
    (hCi : ∀ t, Integrable (C t) μ)
    (hCmon : ∀ s t, s ≤ t → C s ≤ᵐ[μ] C t)
    (hC : ∀ t ≤ H, C t =ᵐ[μ] fun ω => ∫ r in (0:ℝ)..(t:ℝ), b r.toNNReal ω)
    (hbAd : StronglyAdapted 𝒢 b) (hbC : ∀ ω, Continuous fun t => b t ω)
    (hbNN : ∀ t ω, 0 ≤ b t ω) {L B K : ℝ} (hbStart : ∀ ω, b 0 ω ≤ L)
    (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hDbd : ∀ t, ∀ᵐ ω ∂μ, ‖affinePreterminalDensity T H w M b t ω‖ ≤ B)
    (hMlo : ∀ t ≤ H, ∀ᵐ ω ∂μ, -K≤M t ω) :
    let D := affinePreterminalDensity T H w M b H
    (∫ ω, D ω*(M H ω+affineWeightedDrift T H w b H ω) ∂μ) = 0 := by
  let E := affinePreterminalDensity T H w M b
  let J := affineWeightedDrift T H w b
  let P (t : ℝ≥0) (ω : Ω) := ∫ r in Ioc (0:ℝ) ((min t H:ℝ≥0):ℝ), b r.toNNReal ω
  have hWc : ContinuousOn w (Ioi 0) := fun r hr => (hw r hr).continuousAt.continuousWithinAt
  have hd : 0 < (T:ℝ)-(H:ℝ) := sub_pos.mpr (NNReal.coe_lt_coe.mpr hH)
  have hRange (t : ℝ≥0) (r : ℝ) (hr : r∈Ioc (0:ℝ) ((min t H:ℝ≥0):ℝ)) :
      (T:ℝ)-r ∈ Icc ((T:ℝ)-(H:ℝ)) (T:ℝ) :=
    ⟨sub_le_sub_left (hr.2.trans (NNReal.coe_le_coe.mpr (min_le_right t H))) _, sub_le_self _ hr.1.le⟩
  have hJn (t : ℝ≥0) (ω : Ω) : 0≤J t ω := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact mul_nonneg (hwn _ (hRange t r hr)) (hbNN _ _)
  have hPn (t : ℝ≥0) (ω : Ω) : 0≤P t ω := integral_nonneg fun r => hbNN _ _
  have hPi : Integrable (P H) μ := by
    refine (hCi H).congr ?_
    filter_upwards [hC H le_rfl] with ω he
    rw [he,intervalIntegral.integral_of_le (NNReal.coe_nonneg H)]
    simp [P]
  have hJi : Integrable (J H) μ := by
    obtain ⟨B',hB'⟩ := isCompact_Icc.bddAbove_image
      ((hWc.mono (show Icc ((T:ℝ)-(H:ℝ)) (T:ℝ) ⊆ Ioi 0 from fun r hr => hd.trans_le hr.1)).norm)
    let S := max B' 0
    have hSm : StronglyMeasurable[𝒢 H] (J H) := by
      have hh := weighted_time_primitive_stronglyMeasurable hbAd hbC
        (d := fun r => w ((T:ℝ)-r)) (hwm.comp (measurable_const.sub measurable_id)) H
      have he : (fun ω => ∫ r in (0:ℝ)..(H:ℝ), w ((T:ℝ)-r)*b r.toNNReal ω) = J H := by
        funext ω
        rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg H)]
        simp [J,affineWeightedDrift]
      rwa [he] at hh
    refine (hPi.const_mul S).mono' (hSm.mono (𝒢.le H)).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_of_nonneg (hJn H ω)]
    have he : S*P H ω = (∫ r in Ioc (0:ℝ) (H:ℝ), S*b r.toNNReal ω) := by
      simp [P,integral_const_mul]
    change J H ω ≤ S*P H ω
    rw [he]
    change (∫ r in Ioc (0:ℝ) ((min H H:ℝ≥0):ℝ), w ((T:ℝ)-r)*b r.toNNReal ω) ≤ _
    rw [min_self]
    have hb := (hbC ω).comp continuous_real_toNNReal
    have hw' : ContinuousOn (fun r : ℝ => w ((T:ℝ)-r)) (Icc 0 (H:ℝ)) :=
      hWc.comp (continuous_const.sub continuous_id).continuousOn
        (fun r hr => sub_pos.mpr (hr.2.trans_lt (NNReal.coe_lt_coe.mpr hH)))
    apply setIntegral_mono_on
      ((hw'.mul hb.continuousOn).intervalIntegrable_of_Icc (NNReal.coe_nonneg H)).1
      ((hb.intervalIntegrable 0 (H:ℝ)).1.const_mul S) measurableSet_Ioc
    intro r hr
    have hle := hB' ⟨(T:ℝ)-r,hRange H r (by simpa only [min_self] using hr),rfl⟩
    exact mul_le_mul_of_nonneg_right (((le_abs_self (w ((T:ℝ)-r))).trans hle).trans (le_max_left _ _))
      (hbNN _ _)
  have hXm : ∀ t, ∀ᵐ ω ∂μ, -K ≤ M (min t H) ω-M 0 ω+J t ω := by
    intro t
    filter_upwards [hMlo (min t H) (min_le_right _ _),hM0] with ω hm h0
    linarith [hJn t ω]
  have hDM := affinePreterminalDensity_martingale_of_bound hH hw hM hM₂ hMc hMC hCi hCmon hC
    hbAd hbC hbNN hbStart hB hDbd
  have hEm (ε : ℝ) (hε : ε∈Icc (0:ℝ) 1) :
      Martingale (affinePreterminalDensity T H (fun r => w r+ε) M b) 𝒢 μ := by
    refine affinePreterminalDensity_martingale_of_bound hH
      (fun s hs => (hw s hs).add contDiffAt_const) hM hM₂ hMc hMC hCi hCmon hC hbAd hbC hbNN hbStart
      (mul_nonneg hB (Real.exp_pos K).le) ?_
    intro t
    filter_upwards [hDbd t,hXm t] with ω hE hX
    rw [affine_preterminal_perturbation_expand hH hWc hbC, norm_mul,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    apply mul_le_mul hE _ (Real.exp_pos _).le hB
    apply Real.exp_le_exp.mpr
    have hpos : 0≤ε^2*P t ω/2 :=
      div_nonneg (mul_nonneg (sq_nonneg ε) (hPn t ω)) (by norm_num)
    have hlo := mul_le_mul_of_nonneg_left (neg_le_neg hX) hε.1
    have hhi := mul_le_mul_of_nonneg_right hε.2 hK
    change -ε*(M (min t H) ω-M 0 ω+J t ω)-ε^2*P t ω/2 ≤ K
    linarith only [show ε*(-(M (min t H) ω-M 0 ω+J t ω))≤ε*K by
      simpa only [neg_neg] using hlo,hhi,hpos]
  have hmean {v : ℝ → ℝ} (hv : Martingale (affinePreterminalDensity T H v M b) 𝒢 μ) :
      (∫ ω,affinePreterminalDensity T H v M b H ω ∂μ)=1 := by
    have he := hv.setIntegral_eq (show (0:ℝ≥0)≤H from zero_le) MeasurableSet.univ
    simpa [affinePreterminalDensity,affinePreterminalVarianceMartingale,
      affinePreterminalCompensator,affineStoppedBracket] using he.symm
  have hLo : ∀ᵐ ω ∂μ, -K≤M H ω+J H ω := by
    filter_upwards [hXm H,hM0] with ω hX h0
    simpa only [min_self,h0,sub_zero] using hX
  change (∫ ω,E H ω*(M H ω+J H ω) ∂μ)=0
  refine integral_mul_eq_zero_of_affine_exp_perturbation hK
    ((hDM.stronglyMeasurable H).mono (𝒢.le H)).aestronglyMeasurable (hDbd H)
    ((hM.integrable H).add hJi) hPi hLo (ae_of_all _ (hPn H)) ?_
  intro ε hε
  rw [hmean hDM,← hmean (hEm ε hε)]
  apply integral_congr_ae
  filter_upwards [hM0] with ω h0
  rw [affine_preterminal_perturbation_expand hH hWc hbC]
  simp only [P,min_self,h0,sub_zero]
  rfl

#print axioms affine_preterminal_density_weighted_drift

end RoughHeston
