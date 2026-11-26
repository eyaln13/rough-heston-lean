import HestonConditionalAffine

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal Interval

namespace RoughHeston

/-- The inverse equation has a deterministic lower bound on its
driving martingale, since variance and immigration are nonnegative. -/
theorem inverse_variance_martingale_lower
    {α κ T t : ℝ} {j V : ℝ → ℝ} {M : ℝ}
    (hα' : α < 1) (hκ : 0 ≤ κ) (ht : t∈Ioc 0 T) (hj : AffineInputOn T j)
    (hV : Continuous V) (hVn : ∀ r, 0≤V r)
    (hInv : M = volterraConvolution (fractionalL α) V t +
      ∫ r in Ioc (0:ℝ) t, κ*V r-j r) :
    -(∫ r in Ioc (0:ℝ) T, j r) ≤ M := by
  have hL : 0 ≤ volterraConvolution (fractionalL α) V t := by
    unfold volterraConvolution
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    refine mul_nonneg ?_ (hVn r)
    by_cases hr' : r=t
    · simp [hr', fractionalL]
    · have h : 0 < t-r := sub_pos.mpr (lt_of_le_of_ne hr.2 hr')
      rw [fractionalL,ite_eq_right (not_le.mpr h)]
      exact div_nonneg (Real.rpow_nonneg h.le _) (Real.Gamma_pos_of_pos (sub_pos.mpr hα')).le
  have hVint : IntegrableOn V (Ioc 0 t) := (hV.intervalIntegrable 0 t).1
  have hjI := hj.integrable.mono_set (Ioc_subset_Ioc_right ht.2)
  have hVI : 0 ≤ ∫ r in Ioc (0:ℝ) t, κ*V r := integral_nonneg fun r => mul_nonneg hκ (hVn r)
  have hJ := setIntegral_mono_set hj.integrable
    (ae_restrict_mem measurableSet_Ioc |>.mono fun r hr => hj.nonnegative r hr)
    (Eventually.of_forall (Ioc_subset_Ioc_right ht.2))
  rw [hInv,integral_sub (hVint.const_mul κ) hjI]
  linarith

theorem affinePreterminalDensity_eq_exp_payoffs
    {Ω : Type*} {M V : ℝ≥0 → Ω → ℝ}
    {α κ a q : ℝ} {T H : ℝ≥0} {w f j : ℝ → ℝ}
    (hα : 0 < α) (hα' : α < 1) (hH : H<T)
    (hw : AffineRiccatiTestOn α κ a q (T:ℝ) w f) (hj : AffineInputOn (T:ℝ) j) (ω : Ω)
    (hV : Continuous fun t => V t ω) (hM0 : M 0 ω=0)
    (hInv : ∀ r ∈ Ioc (0:ℝ) (T:ℝ), M r.toNNReal ω =
      volterraConvolution (fractionalL α) (fun u => V u.toNNReal ω) r +
        ∫ u in Ioc (0:ℝ) r, κ*V u.toNNReal ω-j u)
    (t : ℝ≥0) :
    affinePreterminalDensity T H w M (fun r ω => (2*a)*V r ω) t ω =
      Real.exp (volterraConvolution w j T - (affinePastPayoff f (fun r => V r.toNNReal ω) T
        (min t H:ℝ≥0)+affineFuturePayoff α w j (fun r => V r.toNNReal ω) T (min t H:ℝ≥0))) := by
  let b (r : ℝ≥0) (ω : Ω) := (2*a)*V r ω
  let u := min t H
  let v (r : ℝ) := V r.toNNReal ω
  have hu : u<T := (min_le_right _ _).trans_lt hH
  have hAr : affinePreterminalCompensator T H w b t ω =
      (2*a)*(∫ r in Ioc (0:ℝ) (u:ℝ), (w ((T:ℝ)-r))^2*v r) := by
    rw [affinePreterminalCompensator_eq,← integral_const_mul]
    congr 1
    funext r
    dsimp [b,v]
    ring
  rw [affinePreterminalDensity,affinePreterminalVarianceMartingale_consistent, hAr]
  change Real.exp (-affinePreterminalVarianceMartingale u ((T:ℝ)-(u:ℝ)) w M u ω -
    (2*a*(∫ r in Ioc (0:ℝ) (u:ℝ), (w ((T:ℝ)-r))^2*v r))/2) =
      Real.exp (volterraConvolution w j T - (affinePastPayoff f v T u+affineFuturePayoff α w j v T u))
  rcases eq_or_lt_of_le (zero_le : 0≤u) with hz | hz
  · have h0 : u=0 := hz.symm
    simp [h0,affinePreterminalVarianceMartingale]
  have hrt : (0:ℝ)<u := NNReal.coe_pos.mpr hz
  have hur : (u:ℝ)<T := NNReal.coe_lt_coe.mpr hu
  have he := affine_pathwise_exponent_split hα hα' ⟨hrt,hur⟩ hw hj
      (hV.comp continuous_real_toNNReal)
      (fun r hr => hInv r ⟨hr.1,hr.2.trans hur.le⟩)
  rw [Real.toNNReal_coe] at he
  change w ((T:ℝ)-↑u)*M u ω +
    (∫ r in Ioc (0:ℝ) (u:ℝ), deriv w ((T:ℝ)-r)*M r.toNNReal ω) +
    a*(∫ r in Ioc (0:ℝ) (u:ℝ), (w ((T:ℝ)-r))^2*v r) =
    affinePastPayoff f v T u-volterraConvolution w j T+affineFuturePayoff α w j v T u at he
  simp only [affinePreterminalVarianceMartingale,min_self,sub_add_cancel,hM0,mul_zero,sub_zero]
  rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg u)]
  congr 1
  linarith

/-- The actual point-test preterminal exponential is the conditional
density process of the point tilt in the original filtration. -/
theorem heston_point_preterminal_conditional_density
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} {M V C : ℝ≥0 → Ω → ℝ}
    {α κ a q : ℝ} {T H : ℝ≥0} {w j : ℝ → ℝ}
    (hα : 0 < α) (hα' : α < 1) (ha : 0 ≤ a) (hH : H<T)
    (hw : AffineRiccatiTestOn α κ a q (T:ℝ) w (fun _ => 0)) (hj : AffineInputOn (T:ℝ) j)
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
        ∫ u in Ioc (0:ℝ) r, κ*V u.toNNReal ω-j u) (t : ℝ≥0) :
    let c := volterraConvolution w j T
    let E := affinePreterminalDensity T H w M (fun r ω => (2*a)*V r ω)
    (μ[(fun ω => Real.exp (c-q*V T ω)) | 𝒢 (min t H)] =ᵐ[μ] E t) ∧
      ∀ᵐ ω ∂μ, ‖E t ω‖≤Real.exp c := by
  let _ : MeasurableSpace Ω := m
  let u := min t H
  let E := affinePreterminalDensity T H w M (fun r ω => (2*a)*V r ω)
  let c := volterraConvolution w j T
  let F (ω : Ω) := affineFuturePayoff α w j (fun r => V r.toNNReal ω) T u
  have hu : u<T := (min_le_right _ _).trans_lt hH
  have hCond := heston_conditional_affine_transform hα hα' ha hu hw hj hM hM₂ hMc hM0
    hV hVc hVnn hV₀ hMC hCi hCmon hC hInv
  simp only [affinePastPayoff,zero_mul,integral_zero,add_zero,zero_add] at hCond
  have hPath : E t =ᵐ[μ] fun ω => Real.exp (c-F ω) := by
    filter_upwards [hM0,hInv] with ω h0 hi
    simpa only [E,c,F,affinePastPayoff,zero_mul,integral_zero,zero_add] using
      affinePreterminalDensity_eq_exp_payoffs hα hα' hH hw hj ω (hVc ω) h0 hi t
  constructor
  · have hE : (fun ω => Real.exp (c-q*V T ω)) = Real.exp c • (fun ω => Real.exp (-(q*V T ω))) := by
      funext ω
      rw [Pi.smul_apply,smul_eq_mul,← Real.exp_add]
      rfl
    rw [hE]
    refine (condExp_smul (Real.exp c) (fun ω => Real.exp (-(q*V T ω))) (𝒢 u)).trans ?_
    filter_upwards [hPath,hCond] with ω hp hc
    change _ = E t ω
    rw [Pi.smul_apply,smul_eq_mul,hc,hp,← Real.exp_add]
    rfl
  · filter_upwards [hPath] with ω hp
    change ‖E t ω‖≤Real.exp c
    rw [hp,Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    exact sub_le_self _ (affine_future_payoff_nonnegative hα.le hα'
      (V := fun r => V r.toNNReal ω) ⟨NNReal.coe_nonneg u,NNReal.coe_le_coe.mpr hu.le⟩
      hw hj (fun r _ => hVnn _ _))

#print axioms inverse_variance_martingale_lower
#print axioms heston_point_preterminal_conditional_density

end RoughHeston
