import AffineTestInstantiation
import HestonPointTiltInverse
import AffineMeanVolterra
import AffineMeanContinuity
import LaplaceBoundary

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal Interval ENNReal

namespace RoughHeston

/-- The inverse variance model on a fixed horizon with deterministic
constant immigration. The martingale and filtration are the supplied
ones, and the moments concern only the indicated finite horizon. -/
structure HestonBoundaryProcess {Ω : Type*} {m : MeasurableSpace Ω}
    (μ : Measure Ω) (𝒢 : Filtration ℝ≥0 m) (U : ℝ≥0)
    (α κ a b v₀ : ℝ) (M V C : ℝ≥0 → Ω → ℝ) : Prop where
  martingale : Martingale M 𝒢 μ
  martingale_memLp : ∀ t, MemLp (M t) 2 μ
  martingale_continuous : ∀ ω, Continuous fun t => M t ω
  martingale_zero : ∀ᵐ ω ∂μ, M 0 ω=0
  variance_adapted : StronglyAdapted 𝒢 V
  variance_continuous : ∀ ω, Continuous fun t => V t ω
  variance_nonnegative : ∀ t ω, 0≤V t ω
  variance_initial_bound : ∀ ω, V 0 ω≤v₀
  variance_initial : ∀ᵐ ω ∂μ, V 0 ω=v₀
  variance_integrable : ∀ t≤U, Integrable (V t) μ
  variance_second_integrable : ∀ t≤U, Integrable (fun ω => (V t ω)^2) μ
  variance_mean_bound : ∃ B : ℝ, 0≤B ∧ ∀ t≤U, (∫ ω,V t ω ∂μ)≤B
  variance_second_bound : ∃ B : ℝ, 0≤B ∧ ∀ t≤U, (∫ ω,(V t ω)^2 ∂μ)≤B
  compensated_square : Martingale (fun t => M t*M t-C t) 𝒢 μ
  compensator_integrable : ∀ t, Integrable (C t) μ
  compensator_monotone : ∀ s t, s ≤ t → C s ≤ᵐ[μ] C t
  compensator : ∀ t ≤ U, C t =ᵐ[μ] fun ω => ∫ r in (0:ℝ)..(t:ℝ), (2*a)*V r.toNNReal ω
  inverse : ∀ᵐ ω ∂μ, ∀ r ∈ Ioc (0:ℝ) (U:ℝ),
    M r.toNNReal ω = volterraConvolution (fractionalL α) (fun u => V u.toNNReal ω) r +
      ∫ u in Ioc (0:ℝ) r,κ*V u.toNNReal ω-(b+v₀*fractionalL α u)

theorem exists_boundary_point_test_family {α κ a : ℝ}
    (hα : 1/2<α) (hα' : α<1) (hκ : 0≤κ) (ha : 0≤a) :
    ∃ w : ℕ → ℝ → ℝ, (∀ (n : ℕ) (T : ℝ), PointChargeRiccatiOn α (n:ℝ) (-κ) (-a) T (w n)) ∧
      ∀ n t, 0<t → 0≤w n t := by
  have hex (n : ℕ) :
      ∃ w : ℝ → ℝ, (∀ T, PointChargeRiccatiOn α (n:ℝ) (-κ) (-a) T w) ∧
        ∀ t, 0<t → 0≤w t := by
    rcases Nat.eq_zero_or_pos n with he|hn
    · subst n
      refine ⟨fun _ => 0,fun T => ⟨measurable_const,(fun _ _ => contDiffAt_const),?_,?_⟩,
        fun _ _ => le_rfl⟩
      · intro t ht
        simp [volterraConvolution]
      · simpa only [Nat.cast_zero,zero_div,mul_zero] using
          (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0:ℝ)) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)))
    · obtain ⟨w,hw,hW⟩ := exists_global_fractional_riccati_point_charge hα hα'
        (show 0<(n:ℝ) from Nat.cast_pos.mpr hn) (neg_nonpos.mpr hκ) (neg_nonpos.mpr ha)
      exact ⟨w,hw,fun t ht => (hW t ht).1.le⟩
  choose w hw hn using hex
  exact ⟨w,hw,hn⟩

/-- The point transform at a future observation, in the original
filtration of the inverse variance process. -/
theorem heston_boundary_conditional_point_test
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} {M V C : ℝ≥0 → Ω → ℝ}
    {α κ a b v₀ q : ℝ} {U T s : ℝ≥0} {w : ℝ → ℝ}
    (hα : 1/2<α) (hα' : α<1) (ha : 0≤a) (hb : 0≤b) (hv₀ : 0≤v₀)
    (hT : T≤U) (hs : s<T) (hP : HestonBoundaryProcess μ 𝒢 U α κ a b v₀ M V C)
    (hw : PointChargeRiccatiOn α q (-κ) (-a) (T:ℝ) w) (hwn : ∀ t>0,0≤w t) :
    μ[(fun ω => Real.exp (-(q*V T ω))) | 𝒢 s] =ᵐ[μ] fun ω =>
      Real.exp (-affineFuturePayoff α w (fun r => b+v₀*fractionalL α r)
        (fun r => V r.toNNReal ω) T s) := by
  have hTr : 0<(T:ℝ) := NNReal.coe_pos.mpr (zero_le.trans_lt hs)
  have hα₀ : 0<α := by linarith
  let j (r : ℝ) := b+v₀*fractionalL α r
  have hj : AffineInputOn (T:ℝ) j := affine_input_on_of_initial_and_bounded_rate
    hα₀ hα' hTr hv₀ measurable_const (fun _ _ => hb) (C := ‖b‖) (fun _ _ => le_rfl)
  have he := heston_conditional_affine_transform hα₀ hα' ha hs
    (hw.affine_test hα hTr (fun t ht => hwn t ht.1)) hj
    hP.martingale hP.martingale_memLp hP.martingale_continuous hP.martingale_zero
    hP.variance_adapted hP.variance_continuous hP.variance_nonnegative hP.variance_initial_bound
    hP.compensated_square hP.compensator_integrable hP.compensator_monotone
    (fun t ht => hP.compensator t (ht.trans hT))
    (hP.inverse.mono fun ω ho r hr => ho r ⟨hr.1,hr.2.trans (NNReal.coe_le_coe.mpr hT)⟩)
  simpa only [j,affinePastPayoff,zero_mul,integral_zero,zero_add,add_zero] using he

/-- The normalized integer point tilt of the actual inverse model has
the continuous Volterra mean required by the backward comparison. -/
theorem heston_boundary_tilt_mean
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} {M V C : ℝ≥0 → Ω → ℝ}
    {α κ a b v₀ : ℝ} {U T : ℝ≥0} {n : ℕ} {w : ℝ → ℝ}
    (hα : 1/2<α) (hα' : α<1) (hκ : 0≤κ) (ha : 0≤a) (hb : 0≤b) (hv₀ : 0≤v₀)
    (hT₀ : 0<T) (hT : T≤U) (hP : HestonBoundaryProcess μ 𝒢 U α κ a b v₀ M V C)
    (hw : PointChargeRiccatiOn α (n:ℝ) (-κ) (-a) (T:ℝ) w) (hwn : ∀ t>0,0≤w t) :
    let j (r : ℝ) := b+v₀*fractionalL α r
    let f (r : ℝ) := ∫ ω,V r.toNNReal ω ∂@laplaceBoundaryTilt Ω m μ (V T) n
    (∫ ω,@laplaceBoundaryWeight Ω (V T) n ω ∂μ)=Real.exp (-(volterraConvolution w j T)) ∧
      ContinuousOn f (Ico (0:ℝ) (T:ℝ)) ∧
      ∀ s ∈ Ioo (0:ℝ) (T:ℝ), f s=f 0+
        volterraConvolution (fractionalK α) (fun r => b-(κ+2*a*w ((T:ℝ)-r))*f r) s := by
  let _ : MeasurableSpace Ω := m
  let j (r : ℝ) := b+v₀*fractionalL α r
  let v (r : ℝ) := V r.toNNReal
  let c := volterraConvolution w j T
  let D := affinePointTiltDensity (n:ℝ) c (V T)
  let Q := affineTiltMeasure μ D
  let f (r : ℝ) := ∫ ω,v r ω ∂Q
  let k (r : ℝ) := κ+2*a*w ((T:ℝ)-r)
  have hTr : 0<(T:ℝ) := NNReal.coe_pos.mpr hT₀
  have hα₀ : 0<α := by linarith
  have hj : AffineInputOn (T:ℝ) j := affine_input_on_of_initial_and_bounded_rate
    hα₀ hα' hTr hv₀ measurable_const (fun _ _ => hb) (C := ‖b‖) (fun _ _ => le_rfl)
  obtain ⟨B,hB,hVB⟩ := hP.variance_mean_bound
  obtain ⟨B',hB',hVB'⟩ := hP.variance_second_bound
  have hInv' : ∀ᵐ ω ∂μ, ∀ r ∈ Ioc (0:ℝ) (T:ℝ),
      M r.toNNReal ω = volterraConvolution (fractionalL α) (fun u => V u.toNNReal ω) r +
        ∫ u in Ioc (0:ℝ) r, κ*V u.toNNReal ω-j u :=
    hP.inverse.mono fun ω ho r hr => ho r ⟨hr.1,hr.2.trans (NNReal.coe_le_coe.mpr hT)⟩
  obtain ⟨hPQ,hNorm,hI⟩ := heston_point_tilt_inverse_mean hα₀ hα' hκ ha
    (Nat.cast_nonneg n) hT₀ (hw.affine_test hα hTr (fun t ht => hwn t ht.1)) hj hwn
    hP.martingale hP.martingale_memLp hP.martingale_continuous hP.martingale_zero
    hP.variance_adapted hP.variance_continuous hP.variance_nonnegative hP.variance_initial_bound
    (fun t ht => hP.variance_integrable t (ht.trans hT))
    (fun t ht => by simpa only [Real.norm_of_nonneg (hP.variance_nonnegative t _)] using hVB t (ht.trans hT))
    hP.compensated_square hP.compensator_integrable hP.compensator_monotone
    (fun t ht => hP.compensator t (ht.trans hT)) hInv'
  let : IsProbabilityMeasure Q := hPQ
  have hvM (t : ℝ) : Measurable (v t) := ((hP.variance_adapted t.toNNReal).mono (𝒢.le _)).measurable
  have hvC (ω : Ω) : Continuous (fun r => v r ω) := (hP.variance_continuous ω).comp continuous_real_toNNReal
  have hDm : Measurable D := (((hP.variance_adapted T).mono (𝒢.le _)).measurable.const_mul (n:ℝ) |>.const_sub c |>.exp)
  have hDn (ω : Ω) : 0≤D ω := (Real.exp_pos _).le
  have hDb (ω : Ω) : ‖D ω‖≤Real.exp c := by
    rw [Real.norm_of_nonneg (hDn ω)]
    exact Real.exp_le_exp.mpr (sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) (hP.variance_nonnegative _ _)))
  have hDba : ∀ᵐ ω ∂μ, ‖D ω‖≤Real.exp c := ae_of_all _ hDb
  have hfEq (r : ℝ) : (∫ ω,v r ω ∂laplaceBoundaryTilt μ (V T) n)=f r := by
    have hXT : Measurable (V T) := ((hP.variance_adapted T).mono (𝒢.le _)).measurable
    change _=(∫ ω,v r ω ∂affineTiltMeasure μ D)
    rw [laplaceBoundaryTilt_integral _ _ hXT,affineTiltMeasure_integral hDm hDn]
    have hN : (∫ ω,laplaceBoundaryWeight (V T) n ω ∂μ)=Real.exp (-c) := by
      simpa only [laplaceBoundaryWeight,neg_mul] using hNorm
    rw [hN,div_eq_mul_inv,← Real.exp_neg,neg_neg,mul_comm]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with ω
    change Real.exp c*(Real.exp (-(n:ℝ)*V T ω)*v r ω)=Real.exp (c-(n:ℝ)*V T ω)*v r ω
    rw [← mul_assoc,← Real.exp_add]
    congr 2
    ring
  have hfM : Measurable f := measurable_affine_variance_mean hvM hvC
  have hfC : ContinuousOn f (Ico (0:ℝ) (T:ℝ)) := by
    have hvU (r : ℝ) (hr : r∈Ico (0:ℝ) (T:ℝ)) : r.toNNReal≤U :=
      (NNReal.coe_le_coe.mp (by simpa only [Real.coe_toNNReal r hr.1] using hr.2.le : (r.toNNReal:ℝ)≤T)).trans hT
    refine continuousOn_affine_variance_mean (B := Real.exp c*B') hvM hvC (fun r ω => hP.variance_nonnegative _ _)
      (fun r hr => affineTiltMeasure_integrable hDm hDn hDba (hP.variance_integrable _ (hvU r hr)))
      (fun r hr => affineTiltMeasure_integrable hDm hDn hDba
        (hP.variance_second_integrable _ (hvU r hr))) (mul_nonneg (Real.exp_pos _).le hB') ?_
    intro r hr
    have hh := affineTiltMeasure_integral_norm_le hDm hDn hDba
      (hP.variance_second_integrable _ (hvU r hr))
    simp only [Real.norm_of_nonneg (sq_nonneg _)] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (hVB' _ (hvU r hr)) (Real.exp_pos c).le)
  have hkM : Measurable k :=
    ((hw.measurable.comp (measurable_const.sub measurable_id)).const_mul (2*a)).const_add κ
  have hkC : ContinuousOn k (Ico (0:ℝ) (T:ℝ)) :=
    continuousOn_const.add ((hw.continuousOn_pos.comp (continuous_const.sub continuous_id).continuousOn
      (fun r (hr : r∈Ico (0:ℝ) (T:ℝ)) => sub_pos.mpr hr.2)).const_mul (2*a))
  have hEp : ∀ s ∈ Ioo (0:ℝ) (T:ℝ), f s=v₀+
      volterraConvolution (fractionalK α) (fun r => b-k r*f r) s :=
    affine_mean_volterra_of_inverse hα₀ hα' hfM hkM hfC hkC hI
  have hf₀ : f 0=v₀ := by
    have hQμ : Q ≪ μ := withDensity_absolutelyContinuous μ _
    change (∫ ω,V (0:ℝ).toNNReal ω ∂Q)=v₀
    simp only [Real.toNNReal_zero]
    rw [integral_congr_ae (hQμ.ae_le hP.variance_initial),integral_const,probReal_univ,one_smul]
  let L (r : ℝ) := ∫ ω,V r.toNNReal ω ∂laplaceBoundaryTilt μ (V T) n
  have hfe : L=f := funext hfEq
  change _ ∧ ContinuousOn L (Ico (0:ℝ) (T:ℝ)) ∧
    (∀ s ∈ Ioo (0:ℝ) (T:ℝ), L s=L 0+volterraConvolution (fractionalK α) (fun r => b-k r*L r) s)
  rw [hfe]
  exact ⟨by simpa only [laplaceBoundaryWeight,neg_mul] using hNorm,hfC,fun s hs => by
    rw [hf₀]
    exact hEp s hs⟩

#print axioms heston_boundary_conditional_point_test
#print axioms heston_boundary_tilt_mean

end RoughHeston
