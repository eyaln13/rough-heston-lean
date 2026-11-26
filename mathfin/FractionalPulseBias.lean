import ActualFractionalPulse

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal Interval ENNReal

namespace RoughHeston

theorem fractional_pulse_accumulated_adapted
    {Ω : Type*} {m : MeasurableSpace Ω} {𝒢 : Filtration ℝ≥0 m} {U : ℝ≥0 → Ω → ℝ}
    (hU : StronglyAdapted 𝒢 U) (hc : ∀ ω,Continuous fun t => U t ω) (s : ℝ≥0) :
    StronglyMeasurable[𝒢 s] (clusterAccumulatedVariance (fun u => U u.toNNReal) (s:ℝ)) := by
  have h := weighted_time_primitive_stronglyMeasurable hU hc
    (d := fun _ => (1:ℝ)) measurable_const s
  change StronglyMeasurable[𝒢 s] (fun ω => ∫ r in Ioc (0:ℝ) (s:ℝ),U r.toNNReal ω)
  simpa only [one_mul,intervalIntegral.integral_of_le (NNReal.coe_nonneg s)] using h

/-- The terminal size bias has the same restriction to the past as
bias at that past time by its current martingale mass. -/
theorem fractional_pulse_bias_agrees_on_past
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} {M U C : ℝ≥0 → Ω → ℝ}
    {α κ a ε d : ℝ} {H s r : ℝ≥0} {A : Set Ω}
    (hα : 0<α) (hα' : α<1) (hκ : 0≤κ) (hε : 0<ε) (hd : 0<d)
    (hsr : s≤r) (hr : r≤H) (hP : FractionalPulseProcess μ 𝒢 H α κ a ε d M U C)
    (hA : MeasurableSet[𝒢 s] A) :
    (@sizeBiasedLaw Ω m μ (fractionalPulseMass ε M r) ε).real A =
      (@sizeBiasedLaw Ω m μ (fractionalPulseMass ε M s) ε).real A := by
  let _ : MeasurableSpace Ω := m
  have hAm : MeasurableSet A := (𝒢.le s) _ hA
  let Z := fractionalPulseMass ε M
  let I := A.indicator (fun _ : Ω => (1:ℝ))
  have hI (t : ℝ≥0) (ht : t≤H) :
      (sizeBiasedLaw μ (Z t) ε).real A = (∫ ω in A,Z t ω ∂μ)/ε := by
    obtain ⟨hZm,hZ₀,hZi,hZmean,_⟩ := fractional_pulse_mass_data hα hα' hκ hε hd ht hP
    have hleft : (∫ ω,I ω ∂sizeBiasedLaw μ (Z t) ε)=(sizeBiasedLaw μ (Z t) ε).real A := by
      change (∫ ω,A.indicator (fun _ : Ω => (1:ℝ)) ω ∂sizeBiasedLaw μ (Z t) ε)=_
      rw [integral_indicator hAm,setIntegral_const,smul_eq_mul,mul_one]
    have hright : (∫ ω,Z t ω*I ω ∂μ) = ∫ ω in A,Z t ω ∂μ := by
      rw [← integral_indicator hAm]
      apply integral_congr_ae
      filter_upwards with ω
      by_cases h : ω∈A
      · simp [I,indicator_of_mem h]
      · simp [I,indicator_of_notMem h]
    rw [← hleft,integral_sizeBiasedLaw_eq hε hZm hZ₀,hright]
  have hS (t : ℝ≥0) : (∫ ω in A,Z t ω ∂μ)=ε*(μ.real A)+(∫ ω in A,M t ω ∂μ) := by
    have hi : Integrable (fun _ : Ω => ε) (μ.restrict A) := integrable_const _
    have hh := integral_add hi (hP.martingale.integrable t).restrict
    simp only [integral_const,smul_eq_mul] at hh
    exact hh.trans (by rw [measureReal_restrict_apply_univ,mul_comm (μ.real A) ε])
  rw [hI r hr,hI s (hsr.trans hr),hS r,hS s,hP.martingale.setIntegral_eq hsr hA]

/-- Once the pulse has arrived, the mixed q+λ(L+κ) density payoff
equals q times accumulated variance plus λ times the mass martingale. -/
theorem fractional_pulse_postpulse_affine_payoff
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} {M U C : ℝ≥0 → Ω → ℝ}
    {α κ a ε d q l : ℝ} {H s : ℝ≥0}
    (hα : 0<α) (hα' : α<1) (hε : 0≤ε) (hd : 0<d)
    (hds : d≤(s:ℝ)) (hs : s≤H) (hP : FractionalPulseProcess μ 𝒢 H α κ a ε d M U C) :
    ∀ᵐ ω ∂μ,
      volterraConvolution (fun u => q+l*(fractionalL α u+κ)) (fun u => U u.toNNReal ω) (s:ℝ) =
      q*clusterAccumulatedVariance (fun u => U u.toNNReal) (s:ℝ) ω+l*fractionalPulseMass ε M s ω := by
  filter_upwards [fractional_pulse_mass_identity hα hα' hε hd hP] with ω he
  specialize he (s:ℝ) ⟨NNReal.coe_nonneg s, NNReal.coe_le_coe.mpr hs⟩
  rw [Real.toNNReal_coe,min_eq_right hds,div_mul_cancel₀ _ hd.ne',sub_self,zero_add] at he
  rw [he]
  let v (u : ℝ) := U u.toNNReal ω
  obtain ⟨hV,hLV⟩ := cluster_affine_payoff_integrability_of_continuous hα' (NNReal.coe_nonneg s)
    ((hP.variance_continuous ω).comp continuous_real_toNNReal)
  change IntegrableOn v (Ioc 0 (s:ℝ)) at hV
  change IntegrableOn (fun r => fractionalL α ((s:ℝ)-r)*v r) (Ioc 0 (s:ℝ)) at hLV
  unfold volterraConvolution clusterAccumulatedVariance
  change (∫ u in Ioc (0:ℝ) (s:ℝ),
      (q+l*(fractionalL α ((s:ℝ)-u)+κ))*v u) =
      q*(∫ u in Ioc (0:ℝ) (s:ℝ),v u) +
        l*((∫ u in Ioc (0:ℝ) (s:ℝ),fractionalL α ((s:ℝ)-u)*v u)+
          κ*(∫ u in Ioc (0:ℝ) (s:ℝ),v u))
  have hEq (u : ℝ) :
      (q+l*(fractionalL α ((s:ℝ)-u)+κ))*v u =
        q*v u+l*(fractionalL α ((s:ℝ)-u)*v u+κ*v u) := by ring
  simp_rw [hEq]
  have hA := integral_add (hV.const_mul q) ((hLV.add (hV.const_mul κ)).const_mul l)
  have hB := integral_add hLV (hV.const_mul κ)
  try simp only [Pi.add_apply] at hA hB
  rw [hA,integral_const_mul,integral_const_mul,hB,integral_const_mul]

#print axioms fractional_pulse_bias_agrees_on_past
#print axioms fractional_pulse_postpulse_affine_payoff

end RoughHeston
