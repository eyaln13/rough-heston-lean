import DensityAffineTestUniqueness
import HestonConditionalAffine
import AffinePointPreterminal

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal Interval ENNReal

namespace RoughHeston

/-- An actual fractional pulse process in the supplied filtration. The
probability measure can be the original law conditioned at birth. -/
structure FractionalPulseProcess {Ω : Type*} {m : MeasurableSpace Ω}
    (μ : Measure Ω) (𝒢 : Filtration ℝ≥0 m) (H : ℝ≥0)
    (α κ a ε d : ℝ) (M U C : ℝ≥0 → Ω → ℝ) : Prop where
  martingale : Martingale M 𝒢 μ
  martingale_memLp : ∀ t, MemLp (M t) 2 μ
  martingale_continuous : ∀ ω, Continuous fun t => M t ω
  martingale_zero : ∀ᵐ ω ∂μ, M 0 ω=0
  variance_adapted : StronglyAdapted 𝒢 U
  variance_continuous : ∀ ω, Continuous fun t => U t ω
  variance_nonnegative : ∀ t ω, 0≤U t ω
  variance_zero : ∀ ω, U 0 ω=0
  compensated_square : Martingale (fun t => M t*M t-C t) 𝒢 μ
  compensator_integrable : ∀ t, Integrable (C t) μ
  compensator_monotone : ∀ s t, s≤t → C s≤ᵐ[μ] C t
  compensator : ∀ t ≤ H, C t =ᵐ[μ] fun ω => ∫ r in (0:ℝ)..(t:ℝ), (2*a)*U r.toNNReal ω
  inverse : ∀ᵐ ω ∂μ, ∀ r ∈ Ioc (0:ℝ) (H:ℝ),
    M r.toNNReal ω = volterraConvolution (fractionalL α) (fun u => U u.toNNReal ω) r +
      ∫ u in Ioc (0:ℝ) r,κ*U u.toNNReal ω-rectangularPulseRate ε d u

noncomputable def fractionalPulseMass {Ω : Type*} (ε : ℝ)
    (M : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ := ε+M t ω

/-- Conservation of total prospective mass, including the deterministic
remainder of the still-arriving rectangular pulse. -/
theorem fractional_pulse_mass_identity
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} {M U C : ℝ≥0 → Ω → ℝ}
    {α κ a ε d : ℝ} {H : ℝ≥0}
    (hα : 0<α) (hα' : α<1) (hε : 0≤ε) (hd : 0<d)
    (hP : FractionalPulseProcess μ 𝒢 H α κ a ε d M U C) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0:ℝ) (H:ℝ),
      fractionalPulseMass ε M t.toNNReal ω =
        ε-(ε/d)*min t d+
          volterraConvolution (fractionalL α) (fun u => U u.toNNReal ω) t+
          κ*clusterAccumulatedVariance (fun u => U u.toNNReal) t ω := by
  filter_upwards [hP.martingale_zero,hP.inverse] with ω h0 hInv
  intro t ht
  rcases eq_or_lt_of_le ht.1 with he|he
  · subst t
    simp [fractionalPulseMass,h0,volterraConvolution,clusterAccumulatedVariance,min_eq_left hd.le]
  have hj := affine_input_on_rectangular_pulse hα hα' he hε hd
  have hUi : IntegrableOn (fun u => U u.toNNReal ω) (Ioc 0 t) :=
    (((hP.variance_continuous ω).comp continuous_real_toNNReal).intervalIntegrable 0 t).1
  have heq := hInv t ⟨he,ht.2⟩
  rw [integral_sub (hUi.const_mul κ) hj.integrable,integral_const_mul,
    rectangularPulse_accumulatedMass_eq_real_univ hε hd,
    rectangularPulseMeasure_real_univ hε hd ht.1] at heq
  change ε+M t.toNNReal ω = ε-(ε/d)*min t d+
    volterraConvolution (fractionalL α) (fun u => U u.toNNReal ω) t+
    κ*(∫ u in Ioc (0:ℝ) t,U u.toNNReal ω)
  rw [min_comm d t] at heq
  linarith

theorem fractional_pulse_mass_data
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} {M U C : ℝ≥0 → Ω → ℝ}
    {α κ a ε d : ℝ} {H s : ℝ≥0}
    (hα : 0<α) (hα' : α<1) (hκ : 0≤κ) (hε : 0<ε) (hd : 0<d)
    (hs : s≤H) (hP : FractionalPulseProcess μ 𝒢 H α κ a ε d M U C) :
    let Z := fractionalPulseMass ε M s
    Measurable[m] Z ∧ (∀ᵐ ω ∂μ, 0≤Z ω) ∧ Integrable Z μ ∧
      (∫ ω,Z ω ∂μ)=ε ∧ MemLp Z 2 μ := by
  let _ : MeasurableSpace Ω := m
  let Z := fractionalPulseMass ε M s
  have hMeas : Measurable Z := (((hP.martingale.stronglyAdapted s).mono (𝒢.le s)).measurable.const_add ε)
  have hInt : Integrable Z μ := (integrable_const ε).add (hP.martingale.integrable s)
  have hMmean : (∫ ω,M s ω ∂μ)=0 := by
    have h := hP.martingale.setIntegral_eq (show (0:ℝ≥0)≤s from zero_le) MeasurableSet.univ
    rw [Measure.restrict_univ,integral_congr_ae hP.martingale_zero,integral_zero] at h
    exact h.symm
  have hMean : (∫ ω,Z ω ∂μ)=ε := by
    have he := integral_add (integrable_const ε) (hP.martingale.integrable s)
    simp only [integral_const,probReal_univ,one_smul,hMmean,add_zero] at he
    exact he
  have hNN : ∀ᵐ ω ∂μ, 0≤Z ω := by
    filter_upwards [fractional_pulse_mass_identity hα hα' hε.le hd hP] with ω hω
    specialize hω (s:ℝ) ⟨NNReal.coe_nonneg s, NNReal.coe_le_coe.mpr hs⟩
    rw [Real.toNNReal_coe] at hω
    change 0≤fractionalPulseMass ε M s ω
    rw [hω]
    have hRem : 0≤ε-(ε/d)*min (s:ℝ) d := by
      have hB := mul_le_mul_of_nonneg_left (min_le_right (s:ℝ) d) (div_nonneg hε.le hd.le)
      rwa [div_mul_cancel₀ _ hd.ne',← sub_nonneg] at hB
    have hL : 0≤volterraConvolution (fractionalL α) (fun u => U u.toNNReal ω) (s:ℝ) := by
      unfold volterraConvolution
      apply integral_nonneg
      intro u
      change 0≤fractionalL α ((s:ℝ)-u)*U u.toNNReal ω
      by_cases hu : 0<(s:ℝ)-u
      · rw [fractionalL,ite_eq_right (not_le.mpr hu)]
        exact mul_nonneg (div_nonneg (Real.rpow_nonneg hu.le _)
          (Real.Gamma_pos_of_pos (sub_pos.mpr hα')).le) (hP.variance_nonnegative _ _)
      · simp [fractionalL,le_of_not_gt hu]
    have hJ : 0≤clusterAccumulatedVariance (fun u => U u.toNNReal) (s:ℝ) ω :=
      integral_nonneg fun u => hP.variance_nonnegative _ _
    positivity
  exact ⟨hMeas,hNN,hInt,hMean,(memLp_const ε).add (hP.martingale_memLp s)⟩

theorem fractional_pulse_accumulated_measurable
    {Ω : Type*} {m : MeasurableSpace Ω} {𝒢 : Filtration ℝ≥0 m} {U : ℝ≥0 → Ω → ℝ}
    (hU : StronglyAdapted 𝒢 U) (hc : ∀ ω,Continuous fun t => U t ω) (s : ℝ≥0) :
    Measurable[m] (clusterAccumulatedVariance (fun u => U u.toNNReal) (s:ℝ)) := by
  have h := (weighted_time_primitive_stronglyMeasurable hU hc
    (d := fun _ => (1:ℝ)) measurable_const s).mono (𝒢.le s)
  change Measurable[m] (fun ω => ∫ r in Ioc (0:ℝ) (s:ℝ),U r.toNNReal ω)
  simpa only [one_mul,intervalIntegral.integral_of_le (NNReal.coe_nonneg s)] using h.measurable

/-- The density-test affine transform of the actual rectangular pulse
law, including the mixed test used for the size-biased denominator. -/
theorem fractional_pulse_density_affine_transform
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} {M U C : ℝ≥0 → Ω → ℝ}
    {α κ a ε d q l : ℝ} {w : ℝ → ℝ} {H s : ℝ≥0}
    (hα : 1/2<α) (hα' : α<1) (hκ : 0≤κ) (ha : 0<a)
    (hε : 0<ε) (hd : 0<d) (hs₀ : 0<s) (hs : s≤H) (hq : 0<q) (hl : 0≤l)
    (hP : FractionalPulseProcess μ 𝒢 H α κ a ε d M U C)
    (hw : Continuous w)
    (hW : ∀ t∈Ioc 0 (s:ℝ), w t = volterraConvolution (fractionalK α)
      (fun u => q+l*(fractionalL α u+κ)-κ*w u-a*(w u)^2) t) :
    (∫ ω,Real.exp (-(volterraConvolution (fun u => q+l*(fractionalL α u+κ))
      (fun u => U u.toNNReal ω) (s:ℝ))) ∂μ) =
        Real.exp (-(volterraConvolution w (rectangularPulseRate ε d) (s:ℝ))) := by
  let _ : MeasurableSpace Ω := m
  have hα₀ : 0<α := by linarith
  have hsr : 0<(s:ℝ) := NNReal.coe_pos.mpr hs₀
  obtain ⟨v,hv,_,hvA,hvE⟩ := exists_affine_cluster_density_test hα hα' hκ ha hsr hq hl
  have he := density_affine_test_eqOn hα₀ hα' hsr hw hv hW (fun t ht => by
    simpa only [zero_mul,zero_add] using hvA.volterra t ht)
  let j := rectangularPulseRate ε d
  have hj := affine_input_on_rectangular_pulse hα₀ hα' hsr hε.le hd
  have hInv : ∀ᵐ ω ∂μ, ∀ r∈Ioc (0:ℝ) (s:ℝ), M r.toNNReal ω =
      volterraConvolution (fractionalL α) (fun u => U u.toNNReal ω) r +
      ∫ u in Ioc (0:ℝ) r,κ*U u.toNNReal ω-j u :=
    hP.inverse.mono (fun ω hω r hr => hω r ⟨hr.1,hr.2.trans (NNReal.coe_le_coe.mpr hs)⟩)
  have hT := heston_conditional_affine_transform hα₀ hα' ha.le hs₀ hvA hj
    hP.martingale hP.martingale_memLp hP.martingale_continuous hP.martingale_zero
    hP.variance_adapted hP.variance_continuous hP.variance_nonnegative
    (fun ω => (hP.variance_zero ω).le) hP.compensated_square hP.compensator_integrable
    hP.compensator_monotone (fun t ht => hP.compensator t (ht.trans hs)) hInv
  simp only [zero_mul,zero_add,NNReal.coe_zero,affine_past_payoff_zero,affine_future_payoff_zero] at hT
  have hwv : volterraConvolution v j s=volterraConvolution w j s := by
    unfold volterraConvolution
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    have hr' : (s:ℝ)-r∈Icc 0 (s:ℝ) := ⟨sub_nonneg.mpr hr.2,sub_le_self _ hr.1.le⟩
    change v ((s:ℝ)-r)*j r=w ((s:ℝ)-r)*j r
    rw [he hr']
  change (∫ ω,Real.exp (-(affinePastPayoff (fun u => q+l*(fractionalL α u+κ))
    (fun u => U u.toNNReal ω) (s:ℝ) (s:ℝ))) ∂μ)=Real.exp (-(volterraConvolution w j s))
  rw [← integral_condExp (𝒢.le (0:ℝ≥0)),integral_congr_ae hT,integral_const,
    probReal_univ,one_smul,hwv]

#print axioms fractional_pulse_mass_identity
#print axioms fractional_pulse_mass_data
#print axioms fractional_pulse_density_affine_transform

end RoughHeston
