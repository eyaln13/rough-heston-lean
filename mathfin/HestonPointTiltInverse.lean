import AffineTestInstantiation
import AffineTiltedDrift
import AffineMeanFubini

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal Interval ENNReal

namespace RoughHeston

/-- The normalized terminal point test is written using the affine
normalizer to expose its uniformly bounded density. -/
noncomputable def affinePointTiltDensity {Ω : Type*}
    (q c : ℝ) (X : Ω → ℝ) (ω : Ω) : ℝ :=
  Real.exp (c-q*X ω)

/-- The genuine tilted mean satisfies the inverse variance equation
with the Riccati drift. The proof uses the preterminal weighted
stochastic exponential and then ordinary Fubini. -/
theorem heston_point_tilt_inverse_mean
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} {M V C : ℝ≥0 → Ω → ℝ}
    {α κ a q : ℝ} {T : ℝ≥0} {w j : ℝ → ℝ}
    (hα : 0 < α) (hα' : α < 1) (hκ : 0 ≤ κ) (ha : 0 ≤ a) (hq : 0 ≤ q) (hT : 0<T)
    (hw : AffineRiccatiTestOn α κ a q (T:ℝ) w (fun _ => 0)) (hj : AffineInputOn (T:ℝ) j)
    (hwPos : ∀ t > 0, 0 ≤ w t)
    (hM : Martingale M 𝒢 μ) (hM₂ : ∀ t, MemLp (M t) 2 μ)
    (hMc : ∀ ω, Continuous fun t => M t ω) (hM0 : ∀ᵐ ω ∂μ, M 0 ω = 0)
    (hV : StronglyAdapted 𝒢 V) (hVc : ∀ ω, Continuous fun t => V t ω) (hVnn : ∀ t ω, 0 ≤ V t ω)
    {V₀ B : ℝ} (hV₀ : ∀ ω, V 0 ω ≤ V₀) (hVi : ∀ t ≤ T, Integrable (V t) μ)
    (hVB : ∀ t ≤ T, (∫ ω, ‖V t ω‖ ∂μ) ≤ B)
    (hMC : Martingale (fun t => M t*M t-C t) 𝒢 μ)
    (hCi : ∀ t, Integrable (C t) μ)
    (hCmon : ∀ s t, s ≤ t → C s ≤ᵐ[μ] C t)
    (hC : ∀ t ≤ T, C t =ᵐ[μ] fun ω => ∫ r in (0:ℝ)..(t:ℝ), (2*a)*V r.toNNReal ω)
    (hInv : ∀ᵐ ω ∂μ, ∀ r ∈ Ioc (0:ℝ) (T:ℝ),
      M r.toNNReal ω = volterraConvolution (fractionalL α) (fun u => V u.toNNReal ω) r +
        ∫ u in Ioc (0:ℝ) r, κ*V u.toNNReal ω-j u) :
    let D := affinePointTiltDensity q (volterraConvolution w j T) (V T)
    let Q := @affineTiltMeasure Ω m μ D
    let f (r : ℝ) := ∫ ω,V r.toNNReal ω ∂Q
    (IsProbabilityMeasure Q) ∧
    (∫ ω, Real.exp (-(q*V T ω)) ∂μ) = Real.exp (-(volterraConvolution w j T)) ∧
    ∀ s ∈ Ioo (0:ℝ) (T:ℝ), volterraConvolution (fractionalL α) f s =
      ∫ r in Ioc (0:ℝ) s, j r-(κ+2*a*w ((T:ℝ)-r))*f r := by
  let _ : MeasurableSpace Ω := m
  let v (r : ℝ) (ω : Ω) := V r.toNNReal ω
  let b (t : ℝ≥0) (ω : Ω) := (2*a)*V t ω
  let c := volterraConvolution w j T
  let D := affinePointTiltDensity q c (V T)
  let Q := affineTiltMeasure μ D
  let f (r : ℝ) := ∫ ω,v r ω ∂Q
  have hDm : Measurable D := by
    exact (( (hV T).mono (𝒢.le T)).measurable.const_mul q |>.const_sub c).exp
  have hDn (ω : Ω) : 0≤D ω := (Real.exp_pos _).le
  have hDb (ω : Ω) : ‖D ω‖≤Real.exp c := by
    rw [Real.norm_of_nonneg (hDn ω)]
    exact Real.exp_le_exp.mpr (sub_le_self _ (mul_nonneg hq (hVnn _ _)))
  have hDba : ∀ᵐ ω ∂μ, ‖D ω‖≤Real.exp c := ae_of_all _ hDb
  have hDi : Integrable D μ := (integrable_const _).mono' hDm.aestronglyMeasurable hDba
  have hsetup (H : ℝ≥0) (hH : H<T) (t : ℝ≥0) :
      (μ[D | 𝒢 (min t H)] =ᵐ[μ] affinePreterminalDensity T H w M b t) ∧
      ∀ᵐ ω ∂μ, ‖affinePreterminalDensity T H w M b t ω‖≤Real.exp c :=
    heston_point_preterminal_conditional_density hα hα' ha hH hw hj hM hM₂ hMc hM0
      hV hVc hVnn hV₀ hMC hCi hCmon hC hInv t
  have hDint : (∫ ω,D ω ∂μ)=1 := by
    calc
      _ = ∫ ω, μ[D | 𝒢 (0:ℝ≥0)] ω ∂μ := (integral_condExp (𝒢.le 0)).symm
      _ = ∫ ω, affinePreterminalDensity T 0 w M b 0 ω ∂μ :=
        integral_congr_ae (by simpa only [min_self] using (hsetup 0 hT 0).1)
      _ = _ := by
        simp [affinePreterminalDensity,affinePreterminalVarianceMartingale,
          affinePreterminalCompensator,affineStoppedBracket]
  let : IsProbabilityMeasure Q := affineTiltMeasure_isProbability hDi hDn hDint
  refine ⟨inferInstance,?_,?_⟩
  · calc
      _ = ∫ ω, Real.exp (-c)*D ω ∂μ := by
        apply integral_congr_ae
        exact ae_of_all _ fun ω => by
          change Real.exp (-(q*V T ω))=Real.exp (-c)*Real.exp (c-q*V T ω)
          rw [← Real.exp_add,show -c+(c-q*V T ω) = -(q*V T ω) by ring]
      _ = _ := by rw [integral_const_mul,hDint,mul_one]
  intro s hs
  let H := s.toNNReal
  have hHr : (H:ℝ)=s := Real.coe_toNNReal s hs.1.le
  have hH : H<T := NNReal.coe_lt_coe.mp (by simpa only [hHr] using hs.2)
  let K := ∫ r in Ioc (0:ℝ) (T:ℝ), j r
  have hK : 0 ≤ K := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact hj.nonnegative r hr
  have hMlo (t : ℝ≥0) (ht : t≤H) : ∀ᵐ ω ∂μ, -K≤M t ω := by
    rcases eq_or_lt_of_le (zero_le : 0≤t) with ht₀ | ht₀
    · rw [← ht₀]
      filter_upwards [hM0] with ω h0
      linarith
    · filter_upwards [hInv] with ω hi
      have htr : (t:ℝ)∈Ioc (0:ℝ) (T:ℝ) :=
        ⟨NNReal.coe_pos.mpr ht₀,NNReal.coe_le_coe.mpr (ht.trans hH.le)⟩
      exact inverse_variance_martingale_lower hα' hκ htr hj ((hVc ω).comp continuous_real_toNNReal)
        (fun _ => hVnn _ _) (by simpa only [Real.toNNReal_coe,Function.comp_def] using hi t htr)
  have hbAd : StronglyAdapted 𝒢 b := fun t => (hV t).const_mul (2*a)
  have hbC (ω : Ω) : Continuous (fun t => b t ω) := continuous_const.mul (hVc ω)
  have hbNN (t : ℝ≥0) (ω : Ω) : 0≤b t ω := mul_nonneg (by positivity) (hVnn _ _)
  have hbStart (ω : Ω) : b 0 ω≤(2*a)*V₀ := mul_le_mul_of_nonneg_left (hV₀ ω) (by positivity)
  have hWpos (r : ℝ) (hr : r∈Icc ((T:ℝ)-(H:ℝ)) (T:ℝ)) : 0≤w r :=
    hwPos r ((sub_pos.mpr (NNReal.coe_lt_coe.mpr hH)).trans_le hr.1)
  have hDrift := affine_preterminal_density_weighted_drift hH
    hw.solution_measurable hw.solution_smooth hWpos hM hM₂ hMc hM0 hMC hCi hCmon (fun t ht => hC t (ht.trans hH.le))
    hbAd hbC hbNN hbStart (Real.exp_pos c).le hK (fun t => (hsetup H hH t).2) hMlo
  let J := affineWeightedDrift T H w b H
  have hJAd : StronglyMeasurable[𝒢 H] J := by
    have hh := weighted_time_primitive_stronglyMeasurable hbAd hbC
      (d := fun r => w ((T:ℝ)-r)) (hw.solution_measurable.comp (measurable_const.sub measurable_id)) H
    have he : (fun ω => ∫ r in (0:ℝ)..(H:ℝ),w ((T:ℝ)-r)*b r.toNNReal ω)=J := by
      funext ω
      rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg H)]
      simp [J,affineWeightedDrift]
    rwa [he] at hh
  have hvM (r : ℝ) : Measurable (v r) := ((hV r.toNNReal).mono (𝒢.le _)).measurable
  have hvC (ω : Ω) : Continuous (fun r => v r ω) := (hVc ω).comp continuous_real_toNNReal
  have hvt (r : ℝ) (hr : r∈Ioc (0:ℝ) s) : r.toNNReal≤T :=
    NNReal.coe_le_coe.mp (by simpa only [Real.coe_toNNReal r hr.1.le] using hr.2.trans hs.2.le)
  have hvmI (r : ℝ) (hr : r∈Ioc 0 s) : Integrable (v r) μ := hVi _ (hvt r hr)
  have hvmB (r : ℝ) (hr : r∈Ioc 0 s) : (∫ ω,‖v r ω‖ ∂μ)≤B := hVB _ (hvt r hr)
  let g (r : ℝ) := (2*a)*w ((T:ℝ)-r)
  have hgm : Measurable g := (hw.solution_measurable.comp (measurable_const.sub measurable_id)).const_mul _
  have hgi : IntegrableOn g (Ioc 0 s) := by
    have hh : ContinuousOn (fun r : ℝ => w ((T:ℝ)-r)) (Icc 0 s) :=
      hw.solution_continuous.comp (continuous_const.sub continuous_id).continuousOn
        (fun r hr => sub_pos.mpr (hr.2.trans_lt hs.2))
    exact (((hh.const_mul _).intervalIntegrable_of_Icc hs.1.le).1)
  have hJe (ω : Ω) : J ω = ∫ r in Ioc (0:ℝ) s,g r*v r ω := by
    simp only [J,affineWeightedDrift,min_self,hHr]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r _
    dsimp [g,b,v]
    ring
  have hJint : Integrable J μ := by
    have hi := (affine_weighted_mean_integral hvM hvC hvmI hvmB hgm hgi).1.integral_prod_right
    exact hi.congr (ae_of_all _ fun ω => (hJe ω).symm)
  have hQDrift : (∫ ω, M H ω+J ω ∂Q)=0 := by
    have hA := (hM.stronglyAdapted H).add hJAd
    have hI := (hM.integrable H).add hJint
    have hCE : μ[D | 𝒢 H] =ᵐ[μ] affinePreterminalDensity T H w M b H := by
      simpa only [min_self] using (hsetup H hH H).1
    have hh := affineTiltMeasure_condExp_test (𝒢.le H) hDm hDn hDba hCE hA hI
    simp only [Pi.add_apply] at hh
    exact hh.trans hDrift
  have hQv (r : ℝ) (hr : r∈Ioc 0 s) : Integrable (v r) Q :=
    affineTiltMeasure_integrable hDm hDn hDba (hvmI r hr)
  have hQVB (r : ℝ) (hr : r∈Ioc 0 s) : (∫ ω, ‖v r ω‖ ∂Q) ≤ Real.exp c*B :=
    (affineTiltMeasure_integral_norm_le hDm hDn hDba (hvmI r hr)).trans
      (mul_le_mul_of_nonneg_left (hvmB r hr) (Real.exp_pos c).le)
  let k (r : ℝ) := κ+g r
  have hkm : Measurable k := hgm.const_add κ
  have hki : IntegrableOn k (Ioc 0 s) :=
    (integrableOn_const (C := κ) (by simp : volume (Ioc (0:ℝ) s) ≠ ∞)).add hgi
  let l (r : ℝ) := fractionalL α (s-r)
  have hlm : Measurable l := (fractionalL_measurable α).comp (measurable_const.sub measurable_id)
  have hli : IntegrableOn l (Ioc 0 s) := fractionalL_reflected_integrableOn_Ioc hα' hs.1.le
  have hL := affine_weighted_mean_integral hvM hvC hQv hQVB hlm hli
  have hK' := affine_weighted_mean_integral hvM hvC hQv hQVB hkm hki
  have hJj : IntegrableOn j (Ioc 0 s) := hj.integrable.mono_set (Ioc_subset_Ioc_right hs.2.le)
  have hh : (∫ ω, M H ω+J ω ∂Q) =
      ∫ ω, (∫ r in Ioc (0:ℝ) s,l r*v r ω)+((∫ r in Ioc (0:ℝ) s,k r*v r ω)-∫ r in Ioc (0:ℝ) s,j r) ∂Q := by
    apply integral_congr_ae
    have hQμ : Q ≪ μ := withDensity_absolutelyContinuous μ _
    filter_upwards [hQμ.ae_le hInv] with ω hi
    have he := hi s ⟨hs.1,hs.2.le⟩
    change M H ω = _ at he
    rw [he,hJe]
    unfold volterraConvolution
    change (∫ r in Ioc (0:ℝ) s,l r*v r ω)+(∫ r in Ioc (0:ℝ) s,κ*v r ω-j r)+
      (∫ r in Ioc (0:ℝ) s,g r*v r ω) = _
    have hVi : IntegrableOn (fun r => v r ω) (Ioc 0 s) := ((hvC ω).intervalIntegrable 0 s).1
    have hGi : IntegrableOn (fun r => g r*v r ω) (Ioc 0 s) := by
      have hgc : ContinuousOn g (Icc 0 s) :=
        (hw.solution_continuous.comp (continuous_const.sub continuous_id).continuousOn
          (fun r (hr : r∈Icc (0:ℝ) s) => sub_pos.mpr (hr.2.trans_lt hs.2))).const_mul (2*a)
      exact ((hgc.mul (hvC ω).continuousOn).intervalIntegrable_of_Icc hs.1.le).1
    have he' : (∫ r in Ioc (0:ℝ) s,k r*v r ω) =
        (∫ r in Ioc (0:ℝ) s,κ*v r ω)+(∫ r in Ioc (0:ℝ) s,g r*v r ω) := by
      have hi' := integral_add (hVi.const_mul κ) hGi
      simpa only [k,add_mul] using hi'
    rw [integral_sub (hVi.const_mul κ) hJj,he']
    ring
  have ha₁ := integral_add hL.1.integral_prod_right
    (hK'.1.integral_prod_right.sub (integrable_const (∫ r in Ioc (0:ℝ) s,j r)))
  have ha₂ := integral_sub hK'.1.integral_prod_right (integrable_const (∫ r in Ioc (0:ℝ) s,j r))
  simp only [Pi.sub_apply] at ha₁ ha₂
  rw [ha₁,ha₂,integral_const,probReal_univ,one_smul,hL.2,hK'.2,hQDrift] at hh
  change (∫ r in Ioc (0:ℝ) s,l r*f r) = _
  have hki' : IntegrableOn (fun r => k r*f r) (Ioc 0 s) := by
    refine hK'.1.integral_prod_left.congr (ae_of_all _ fun r => ?_)
    change (∫ ω,k r*v r ω ∂Q) = k r*f r
    exact integral_const_mul _ _
  rw [integral_sub hJj hki']
  change (∫ r in Ioc (0:ℝ) s,l r*f r) = (∫ r in Ioc (0:ℝ) s,j r)-(∫ r in Ioc (0:ℝ) s,k r*f r)
  linarith

#print axioms heston_point_tilt_inverse_mean

end RoughHeston
