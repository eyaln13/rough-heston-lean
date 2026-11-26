import ActualPulseSeparationWithMeans
import UniformBoundaryAcrossLaws

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace RoughHeston

universe u

private theorem integrable_continuous_age_test
    {Ξ : Type*} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsFiniteMeasure ν]
    {age : Ξ → ℝ} {T : ℝ} {f : ℝ → ℝ} (hf : Continuous f) (ha : Measurable age)
    (haT : ∀ᵐ v ∂ν, age v ∈ Icc 0 T) :
    Integrable (fun v => f (age v)) ν := by
  obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image (K := Icc (0 : ℝ) T) hf.norm.continuousOn
  refine (integrable_const B).mono' (hf.measurable.comp ha).aestronglyMeasurable ?_
  filter_upwards [haT] with v hv
  exact hB ⟨age v,hv,rfl⟩

/-- The post-pulse square-root lower-tail constant is chosen before
the measure, process, age, and pulse mass. -/
theorem uniform_cluster_postpulse_mass_tail_over_sample_spaces
    {Ξ : Type*} [MeasurableSpace Ξ]
    {α κ a H : ℝ} (hα : 1/2 < α) (hα' : α < 1) (hκ : 0 ≤ κ) (ha : 0 < a) (hH : 0<H) :
    ∃ D : ℝ, 0<D ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (ν : Measure Ξ) [IsFiniteMeasure ν]
      {J Z : Ω → ℝ} {age : Ξ → ℝ} {s ε : ℝ},
      0<s → s≤H → 0<ε →
      Measurable J → Measurable Z → (∀ᵐ ω ∂μ,0≤J ω) →
      (∀ᵐ ω ∂μ,0≤Z ω) → Integrable Z μ → (∫ ω,Z ω ∂μ)=ε →
      Measurable age → (∀ᵐ v ∂ν,age v∈Icc (s/2) s) → ν.real univ=ε →
      (∀ q > 0, ∀ l ∈ Icc (0 : ℝ) 1, ∀ w : ℝ → ℝ, Continuous w →
        (∀ t ∈ Icc 0 s, w t = l+
          volterraConvolution (fractionalK α) (fun u => q+κ*l-κ*w u-a*(w u)^2) t) →
        (∫ ω,Real.exp (-q*J ω-l*Z ω) ∂μ)=Real.exp (-(∫ v,w (age v) ∂ν))) →
      ∀ x, 0<x → x≤1 →
        (sizeBiasedLaw μ Z ε).real {ω | J ω≤x*s^(2*α)}≤D*Real.sqrt x := by
  have hα₀ : 0<α := by linarith
  let A := max (H^(2*α)) ((2:ℝ)^(2*α))
  have hA : 0<A := (Real.rpow_pos_of_pos hH _).trans_le (le_max_left _ _)
  obtain ⟨D,hD,hDec⟩ := exists_cluster_riccati_sensitivity_decay hα hα' hκ ha hH
  let C := D*(2:ℝ)^α
  have hC : 0<C := mul_pos hD (by positivity)
  refine ⟨Real.exp A*C/Real.sqrt A,by positivity,?_⟩
  intro Ω _ μ _ ν _ J Z age s ε hs hsH hε hJ hZ hJ₀ hZ₀ hZi hZmean hage hageSupport hmass htransform x hx hx₁
  let T := s+1
  have hsT : s < T := lt_add_one s
  have hT : 0 < T := hs.trans hsT
  have hsα : 0 < s^α := Real.rpow_pos_of_pos hs _
  have hTwo : 0 < (2:ℝ)^α := by positivity
  have hageS : ∀ᵐ v ∂ν, age v ∈ Icc (0 : ℝ) s := hageSupport.mono fun _ hv =>
    ⟨(half_pos hs).le.trans hv.1,hv.2⟩
  have hageT : ∀ᵐ v ∂ν, age v ∈ Icc (0 : ℝ) T := hageS.mono fun _ hv =>
    ⟨hv.1,hv.2.trans hsT.le⟩
  have hLap (q : ℝ) (hq : A/s^(2*α) ≤ q) :
      (∫ ω, Real.exp (-q*J ω) ∂sizeBiasedLaw μ Z ε) ≤ C/(Real.sqrt q*s^α) := by
    have hq₁ := (cluster_sensitivity_charge_threshold hα₀ hH hs hsH
      (show s ∈ Icc (s/2) s from ⟨by linarith,le_rfl⟩) hq).1
    have hq₀ := zero_lt_one.trans_le hq₁
    have hsqrt : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq₀
    obtain ⟨w,k,hk,hw,hwV,hkV,hwPos,⟨E,hE,hSlope⟩,hkB⟩ :=
      exists_cluster_density_riccati_with_sensitivity_data hα hα' hq₀ hκ ha hT.le
    have hlZero : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl,zero_le_one⟩
    have hw₀ : w 0 0 = 0 := by simpa [volterraConvolution] using hwV 0 hlZero 0 ⟨le_rfl,hT.le⟩
    have hWVol : ∀ u ∈ Icc 0 T, w 0 u = w 0 0+
        volterraConvolution (fractionalK α) (fun v => q+(-κ)*w 0 v+(-a)*(w 0 v)^2) u := by
      simpa only [hw₀, mul_zero, add_zero, neg_mul, sub_eq_add_neg] using hwV 0 hlZero
    let B := C/(Real.sqrt q*s^α)
    have hB : 0 ≤ B := div_nonneg hC.le (mul_nonneg hsqrt.le hsα.le)
    have hAgeK : ∀ᵐ v ∂ν, k (age v) ≤ B := by
      filter_upwards [hageSupport] with z hz
      let u := age z
      have hu : 0 < u := (half_pos hs).trans_le hz.1
      have huT : u < T := hz.2.trans_lt hsT
      have huH : u ≤ H := hz.2.trans hsH
      have hqs := (cluster_sensitivity_charge_threshold hα₀ hH hs hsH hz hq).2
      have hK := hDec hq₁ hu huH huT hqs (hw 0 hlZero) hw₀
        (fun v hv => hwPos v ⟨hv.1.le,hv.2.trans huT.le⟩) hWVol hk
        (fun v hv => (hkB v ⟨hv.1,hv.2.trans huT.le⟩).1.2) hkV
      have hPow : (s/2)^α ≤ u^α := Real.rpow_le_rpow (half_pos hs).le hz.1 hα₀.le
      calc
        k (age z) ≤ D/(Real.sqrt q*u^α) := hK
        _ ≤ D/(Real.sqrt q*(s/2)^α) := div_le_div_of_nonneg_left hD.le
          (mul_pos hsqrt (Real.rpow_pos_of_pos (half_pos hs) _))
          (mul_le_mul_of_nonneg_left hPow hsqrt.le)
        _ = B := by
          rw [Real.div_rpow hs.le (by norm_num : (0:ℝ) ≤ 2)]
          dsimp [B,C]
          field_simp
    have hKInt : (∫ v,k (age v) ∂ν) ≤ ε*B := by
      have h := integral_mono_ae (integrable_continuous_age_test hk hage hageT)
        (integrable_const B) hAgeK
      rwa [integral_const, smul_eq_mul, hmass] at h
    have hExp : Real.exp (-(∫ v,w 0 (age v) ∂ν)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      apply neg_nonpos.mpr
      apply integral_nonneg_of_ae
      exact hageT.mono fun v hv => hwPos (age v) hv
    have htr (l : ℝ) (hl : l ∈ Icc 0 1) :
        (∫ ω,Real.exp (-q*J ω-l*Z ω) ∂μ) = Real.exp (-(∫ v,w l (age v) ∂ν)) :=
      htransform q hq₀ l hl (w l) (hw l hl) (fun u hu => hwV l hl u ⟨hu.1,hu.2.trans hsT.le⟩)
    rw [sizeBiased_laplace_eq_density_sensitivity hq₀.le hε hJ hZ hJ₀ hZ₀ hZi
      hage hageT hw hk hE hSlope htr]
    apply (div_le_iff₀ hε).mpr
    exact (mul_le_mul_of_nonneg_left hKInt (Real.exp_pos _).le).trans
      ((mul_le_of_le_one_left (mul_nonneg hε.le hB) hExp).trans_eq (mul_comm _ _))
  let Q := sizeBiasedLaw μ Z ε
  let hQ : IsProbabilityMeasure Q := sizeBiasedLaw_isProbabilityMeasure hε hZi hZ₀ hZmean
  have hJQ : ∀ᵐ ω ∂Q, 0 ≤ J ω :=
    (withDensity_absolutelyContinuous μ _).ae_le hJ₀
  exact cluster_mass_lower_tail_of_laplace hJ hJQ hA hs hx hx₁ hLap

/-- The early-pulse square-root lower-tail constant is chosen before
the measure, process, age, and pulse mass. -/
theorem uniform_cluster_earlypulse_mass_tail_over_sample_spaces
    {Ξ : Type*} [MeasurableSpace Ξ]
    {α κ a H C₀ η : ℝ} (hα : 1/2 < α) (hα' : α < 1) (hκ : 0 ≤ κ) (ha : 0 < a)
    (hH : 0<H) (hC₀ : 0<C₀) (hη : 0<η) :
    ∃ D : ℝ, 0<D ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (ν : Measure Ξ) [IsFiniteMeasure ν]
      {J Z : Ω → ℝ} {age : Ξ → ℝ} {s ε : ℝ},
      0<s → s≤H → 0<ε →
      Measurable J → Measurable Z → (∀ᵐ ω ∂μ,0≤J ω) →
      (∀ᵐ ω ∂μ,0≤Z ω) → Integrable Z μ → (∫ ω,Z ω ∂μ)=ε →
      MemLp Z 2 μ → (∫ ω,(Z ω)^2 ∂μ)≤C₀*ε^2 →
      Measurable age → (∀ᵐ v ∂ν,age v∈Icc 0 s) → η*s^α≤ν.real {v | s/2≤age v} →
      (∀ q > 0, ∀ w : ℝ → ℝ, Continuous w →
        (∀ t ∈ Icc 0 s, w t =
          volterraConvolution (fractionalK α) (fun u => q+(-κ)*w u+(-a)*(w u)^2) t) →
        (∫ ω,Real.exp (-q*J ω) ∂μ)=Real.exp (-(∫ v,w (age v) ∂ν))) →
      ∀ x, 0<x → x≤1 →
        (sizeBiasedLaw μ Z ε).real {ω | J ω≤x*s^(2*α)}≤D*Real.sqrt x := by
  have hα₀ : 0<α := by linarith
  let A := max (H^(2*α)) ((2:ℝ)^(2*α))
  have hA : 0<A := (Real.rpow_pos_of_pos hH _).trans_le (le_max_left _ _)
  obtain ⟨c,hc,hLower⟩ := exists_cluster_riccati_lower_constant hα hα' hκ ha.le
  let ρ := c*η/2
  have hρ : 0<ρ := half_pos (mul_pos hc hη)
  refine ⟨Real.exp A*(Real.sqrt C₀/ρ)/Real.sqrt A,by positivity,?_⟩
  intro Ω _ μ _ ν _ J Z age s ε hs hsH hε hJ hZ hJ₀ hZ₀ hZi hZmean hZL2 hZ2 hage hageSupport hMass htransform x hx hx₁
  let T := s+1
  have hsT : s < T := lt_add_one s
  have hT : 0 < T := hs.trans hsT
  have hsα : 0 < s^α := Real.rpow_pos_of_pos hs _
  have hageT : ∀ᵐ v ∂ν, age v ∈ Icc (0 : ℝ) T := hageSupport.mono fun _ hv =>
    ⟨hv.1,hv.2.trans hsT.le⟩
  let E : Set Ξ := {v | s/2 ≤ age v}
  have hE : MeasurableSet E := measurableSet_le measurable_const hage
  have hLaw (q : ℝ) (hq : A/s^(2*α) ≤ q) :
      (∫ ω,Real.exp (-q*J ω) ∂μ) ≤ Real.exp (-(c*η*Real.sqrt q*s^α)) := by
    have ⟨hq₁,hqScale⟩ := cluster_sensitivity_charge_threshold hα₀ hH hs hsH
      (show s ∈ Icc (s/2) s from ⟨by linarith,le_rfl⟩) hq
    have hq₀ := zero_lt_one.trans_le hq₁
    obtain ⟨w,_,_,hw,hwV,_,hwPos,_,_⟩ :=
      exists_cluster_density_riccati_with_sensitivity_data hα hα' hq₀ hκ ha hT.le
    have hlZero : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl,zero_le_one⟩
    have hw₀ : w 0 0 = 0 := by simpa [volterraConvolution] using hwV 0 hlZero 0 ⟨le_rfl,hT.le⟩
    have hWVol : ∀ u ∈ Icc 0 T, w 0 u = w 0 0+
        volterraConvolution (fractionalK α) (fun v => q+(-κ)*w 0 v+(-a)*(w 0 v)^2) u := by
      simpa only [hw₀, mul_zero, add_zero, neg_mul, sub_eq_add_neg] using hwV 0 hlZero
    have htr := htransform q hq₀ (w 0) (hw 0 hlZero) (fun t ht => by
      simpa only [hw₀,zero_add] using hWVol t ⟨ht.1,ht.2.trans hsT.le⟩)
    rw [htr]
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    have hWInt : Integrable (fun v => w 0 (age v)) ν := by
      obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image (K := Icc (0 : ℝ) T)
        (hw 0 hlZero).norm.continuousOn
      refine (integrable_const B).mono' (((hw 0 hlZero).measurable.comp hage).aestronglyMeasurable) ?_
      filter_upwards [hageT] with v hv
      exact hB ⟨age v,hv,rfl⟩
    have hDom : ∀ᵐ v ∂ν, E.indicator (fun _ => c*Real.sqrt q) v ≤ w 0 (age v) := by
      filter_upwards [hageSupport] with v hv
      by_cases hve : v ∈ E
      · rw [indicator_of_mem hve]
        exact hLower hq₁ hs hsT hqScale (hw 0 hlZero) hw₀
          (fun u hu => hwPos u ⟨hu.1.le,hu.2.trans hsT.le⟩) hWVol (age v) ⟨hve,hv.2⟩
      · rw [indicator_of_notMem hve]
        exact hwPos (age v) ⟨hv.1,hv.2.trans hsT.le⟩
    have hInt := integral_mono_ae ((integrable_const (c*Real.sqrt q)).indicator hE) hWInt hDom
    rw [integral_indicator hE,setIntegral_const,smul_eq_mul] at hInt
    calc
      _ = (η*s^α)*(c*Real.sqrt q) := by ring
      _ ≤ ν.real E*(c*Real.sqrt q) := mul_le_mul_of_nonneg_right hMass
        (mul_nonneg hc.le (Real.sqrt_nonneg _))
      _ ≤ _ := hInt
  have hLap (q : ℝ) (hq : A/s^(2*α) ≤ q) :
      (∫ ω,Real.exp (-q*J ω) ∂sizeBiasedLaw μ Z ε) ≤
        Real.sqrt C₀*Real.exp (-(ρ*Real.sqrt q*s^α)) := by
    have hq₀ := (div_pos hA (Real.rpow_pos_of_pos hs _)).trans_le hq
    let f (ω : Ω) := Real.exp (-q*J ω)
    have hf : Measurable f := (hJ.const_mul (-q)).exp
    have hf₀ (ω : Ω) : 0 ≤ f ω := (Real.exp_pos _).le
    have hf₂ : MemLp f 2 μ := by
      apply MemLp.of_bound hf.aestronglyMeasurable 1
      filter_upwards [hJ₀] with ω hw
      rw [Real.norm_of_nonneg (hf₀ ω)]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq₀.le) hw)
    have hpq : (2:ℝ).HolderConjugate 2 := by
      rw [Real.holderConjugate_iff]
      norm_num
    have hcs : (∫ ω,Z ω*f ω ∂μ) ≤
        Real.sqrt (∫ ω,(Z ω)^2 ∂μ)*Real.sqrt (∫ ω,(f ω)^2 ∂μ) := by
      have he := integral_mul_le_Lp_mul_Lq_of_nonneg hpq hZ₀ (Eventually.of_forall hf₀)
        (by simpa only [ENNReal.ofReal_ofNat] using hZL2)
        (by simpa only [ENNReal.ofReal_ofNat] using hf₂)
      simpa only [Real.rpow_two,Real.sqrt_eq_rpow] using he
    have hSQZ : Real.sqrt (∫ ω,(Z ω)^2 ∂μ) ≤ Real.sqrt C₀*ε := by
      have hh := Real.sqrt_le_sqrt hZ2
      rwa [Real.sqrt_mul hC₀.le,Real.sqrt_sq hε.le] at hh
    have hq₂ : A/s^(2*α) ≤ 2*q := hq.trans (by linarith)
    have hSqInt : (∫ ω,(f ω)^2 ∂μ) = (∫ ω,Real.exp (-(2*q)*J ω) ∂μ) := by
      apply integral_congr_ae
      refine ae_of_all _ fun ω => ?_
      simp only [f,pow_two,← Real.exp_add]
      congr 1
      ring
    have hFInt : Real.sqrt (∫ ω,(f ω)^2 ∂μ) ≤
        Real.exp (-(ρ*Real.sqrt q*s^α)) := by
      rw [hSqInt]
      have hSqrtQ : Real.sqrt q ≤ Real.sqrt (2*q) := Real.sqrt_le_sqrt (by linarith)
      have hExp : Real.exp (-(c*η*Real.sqrt (2*q)*s^α)) ≤ Real.exp (-(c*η*Real.sqrt q*s^α)) := by
        apply Real.exp_le_exp.mpr
        exact neg_le_neg (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hSqrtQ (mul_nonneg hc.le hη.le)) hsα.le)
      refine (Real.sqrt_le_sqrt ((hLaw (2*q) hq₂).trans hExp)).trans_eq ?_
      rw [Real.sqrt_eq_rpow,← Real.exp_mul]
      congr 1
      dsimp [ρ]
      ring
    rw [integral_sizeBiasedLaw_eq hε hZ hZ₀]
    apply (div_le_iff₀ hε).mpr
    exact hcs.trans ((mul_le_mul hSQZ hFInt (Real.sqrt_nonneg _) (mul_nonneg
      (Real.sqrt_nonneg _) hε.le)).trans_eq (by ring))
  let Q := sizeBiasedLaw μ Z ε
  let hQ : IsProbabilityMeasure Q := sizeBiasedLaw_isProbabilityMeasure hε hZi hZ₀ hZmean
  have hJQ : ∀ᵐ ω ∂Q, 0 ≤ J ω := (withDensity_absolutelyContinuous μ _).ae_le hJ₀
  apply cluster_mass_lower_tail_of_laplace hJ hJQ hA hs hx hx₁
  intro q hq
  have hq₀ := (div_pos hA (Real.rpow_pos_of_pos hs _)).trans_le hq
  let z := ρ*Real.sqrt q*s^α
  have hz : 0 < z := mul_pos (mul_pos hρ (Real.sqrt_pos.mpr hq₀)) hsα
  have hExp : Real.exp (-z) ≤ 1/z := by
    apply (le_div_iff₀ hz).mpr
    have h := Real.add_one_le_exp z
    calc
      Real.exp (-z)*z ≤ Real.exp (-z)*Real.exp z :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
  exact (hLap q hq).trans ((mul_le_mul_of_nonneg_left hExp (Real.sqrt_nonneg _)).trans_eq (by
    dsimp [z]
    rw [mul_assoc,one_div,mul_inv,div_eq_mul_inv,div_eq_mul_inv]
    ring))

theorem uniform_focal_envelope_of_block_estimates_over_sample_spaces
    {α γ K D p σ : ℝ} (hα : 0 < α) (hα' : α < 1) (hγ : 0 < γ)
    (hK : 0 ≤ K) (hD : 0 ≤ D) (hp : 0 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q] (r : ℝ≥0)
      (d ε κ : ℝ) (U Z : ℝ≥0 → Ω → ℝ),
      0 < d → 4*d ≤ (r:ℝ) → ε = d^α → 0 ≤ κ →
      (∀ ω, Continuous (fun t => U t ω)) →
      (∀ t ≤ r, ∀ ω, 0 ≤ U t ω) →
      (∀ t ≤ r, ∀ ω, Z t ω = ε-ε/d*min (t:ℝ) d+
        volterraConvolution (fractionalL α) (fun s => U s.toNNReal ω) t+
        κ*clusterAccumulatedVariance (fun s => U s.toNNReal) t ω) →
      FocalBlockEstimate Q (fun t => U t.toNNReal) 0 (4*d) (d/4) d α K D →
      (∀ j, let s := clusterDyadicAge (r:ℝ) j
        2*d ≤ s → FocalBlockEstimate Q (fun t => U t.toNNReal) s (2*s) s s α K D) →
      Q.real {ω | envelopeStop r (C*(r:ℝ)^(3*γ))
        (clusterEnvelopeValue 0 σ (1+3*γ) U Z) ω < r} ≤ p := by
  let q := (1/2:ℝ)^(γ/2)
  have hq : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by positivity)
  obtain ⟨c,M,hc,hc1,hM,hcost⟩ := choose_focal_envelope_thresholds hK hD hq1 hp
  let m₁ := min (3/4) ((4:ℝ)^(-α)/Real.Gamma (1-α)*c/(4:ℝ)^(2*α))
  let m₂ := (2:ℝ)^(-α)/Real.Gamma (1-α)*c
  let m := min m₁ m₂
  have hG := Real.Gamma_pos_of_pos (sub_pos.mpr hα')
  have hm : 0 < m := by dsimp [m,m₁,m₂]; positivity
  refine ⟨4^(1+3*γ)*σ^2*M/m^2,by positivity,?_⟩
  intro Ω _ Q hQ r d ε κ U Z hd hd4 hε hκ huc hn hz early late
  let U' (t : ℝ) := U t.toNNReal
  let Z' (t : ℝ) := Z t.toNNReal
  let A (t : ℝ) := ε/d*min t d
  have hdr : d ≤ (r:ℝ) := by linarith
  have hr : 0 < (r:ℝ) := hd.trans_le hdr
  have heps : 0 < ε := hε ▸ Real.rpow_pos_of_pos hd _
  have hU (ω : Ω) : Continuous (fun t => U' t ω) := (huc ω).comp continuous_real_toNNReal
  have hN (t : ℝ) (ht : t ∈ Icc (0:ℝ) (r:ℝ)) (ω : Ω) : 0 ≤ U' t ω :=
    hn t.toNNReal (Real.toNNReal_le_iff_le_coe.mpr ht.2) ω
  have hZ (t : ℝ) (ht : t ∈ Icc (0:ℝ) (r:ℝ)) (ω : Ω) : Z' t ω = ε - A t +
      volterraConvolution (fractionalL α) (fun v => U' v ω) t + κ*clusterAccumulatedVariance U' t ω := by
    simpa [U',Z',A,Real.coe_toNNReal t ht.1] using hz t.toNNReal (Real.toNNReal_le_iff_le_coe.mpr ht.2) ω
  have hA (t : ℝ) (_ : t ∈ Icc (0:ℝ) (r:ℝ)) : A t ≤ ε := by
    calc _ ≤ ε/d*d := mul_le_mul_of_nonneg_left (min_le_right ..) (div_nonneg heps.le hd.le)
         _ = ε := div_mul_cancel₀ _ hd.ne'
  obtain ⟨E,he,hfirst⟩ := focal_early_pulse_block (U := U') (Z := Z') hd hdr hα hα' hκ hε hγ.le hc hc1 hM hU
    (fun t ht => hN t ⟨ht.1,ht.2.trans hd4⟩)
    (fun t ht => hZ t ⟨ht.1,ht.2.trans hd4⟩)
    early.dominates early.integrable early.nonnegative early.mean early.tail
  let B := K/M+D*Real.sqrt c
  have hB : 0 ≤ B := add_nonneg (div_nonneg hK hM.le) (mul_nonneg hD (Real.sqrt_nonneg _))
  have hP (j : ℕ) : ∃ E : Set Ω, Q.real E ≤ B*q^j ∧
      ∀ ω ∉ E, ∀ t ∈ Ioc (0:ℝ≥0) r,
        let s := clusterDyadicAge (r:ℝ) j
        2*d ≤ s → (t:ℝ) ∈ Icc s (2*s) →
        U t ω ≤ M*s^(2*α-1)*((r:ℝ)/s)^γ ∧ m*s^α*(s/(r:ℝ))^γ ≤ Z t ω := by
    let s := clusterDyadicAge (r:ℝ) j
    have hs : 0 < s := by dsimp [s,clusterDyadicAge]; positivity
    by_cases hds : 2*d ≤ s
    · let data := late j hds
      obtain ⟨E,hprob,hgood⟩ := focal_postpulse_block (U := U') (Z := Z') hr hα hα' hκ hγ hc hc1 hM hD hK j
        hU hN hA hZ data.dominates data.integrable data.nonnegative data.mean data.tail
      refine ⟨E,hprob,?_⟩
      intro ω hω t ht
      dsimp only
      intro _ hts
      obtain ⟨h₁,h₂⟩ := hgood ω hω t ⟨ht.1,ht.2⟩ hts
      have h₂' : m₂*s^α*(s/(r:ℝ))^γ ≤ Z t ω := by simpa [m₂,s,Z'] using h₂
      refine ⟨by simpa [U',s] using h₁, le_trans ?_ h₂'⟩
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_right m₁ m₂)
        (Real.rpow_nonneg hs.le _)) (Real.rpow_nonneg (div_nonneg hs.le hr.le) _)
    · exact ⟨∅, by simp [mul_nonneg hB (pow_nonneg hq.le j)], by intro ω _ t ht; dsimp only; intro h; exact (hds h).elim⟩
  choose bad hbad hgood using hP
  apply (focal_envelope_failure_probability (Q := Q) (r := r) hr hd hγ.le hm hM.le
    hB hq.le hq1 hn E bad he hbad ?_ (fun j hds ω hω t ht hts => hgood j ω hω t ht hds hts)).trans hcost
  intro ω hω t ht htd
  obtain ⟨h₁,h₂⟩ := hfirst ω hω t ⟨t.coe_nonneg,htd⟩
  have h₂' : m₁*d^α*(d/(r:ℝ))^γ ≤ Z t ω := by simpa [m₁,Z'] using h₂
  exact ⟨by simpa [U'] using h₁,(mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (min_le_left m₁ m₂) (Real.rpow_nonneg hd.le _))
    (Real.rpow_nonneg (div_nonneg hd.le hr.le) _)).trans h₂'⟩

theorem uniform_actual_fractional_pulse_mass_tails_over_sample_spaces
    {α κ a C₀ : ℝ} {H : ℝ≥0}
    (hα : 1/2<α) (hα' : α<1) (hκ : 0≤κ) (ha : 0<a) (hH : 0<H) (hC₀ : 0<C₀) :
    ∃ D : ℝ, 0<D ∧ ∀ {Ω : Type u} {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
      (𝒢 : Filtration ℝ≥0 m) (r : ℝ≥0) (ε : ℝ) (M U C : ℝ≥0 → Ω → ℝ),
      let d := ε^(1/α)
      let s₀ := d/4
      let J := clusterAccumulatedVariance (fun s => U s.toNNReal)
      let Z := fractionalPulseMass ε M
      let Q := @sizeBiasedLaw Ω m μ (Z r) ε
      0<ε → r≤H → s₀≤(r:ℝ) →
      FractionalPulseProcess μ 𝒢 H α κ a ε d M U C →
      (∫ ω,(Z s₀.toNNReal ω)^2 ∂μ)≤C₀*ε^2 →
      (∀ x, 0<x → x≤1 → Q.real {ω | J s₀ ω≤x*s₀^(2*α)}≤D*Real.sqrt x) ∧
      (∀ s : ℝ≥0, 2*d≤(s:ℝ) → s≤r → ∀ x,0<x → x≤1 →
        Q.real {ω | J s ω≤x*(s:ℝ)^(2*α)}≤D*Real.sqrt x) := by
  have hα₀ : 0<α := by linarith
  have hHr : 0<(H:ℝ) := NNReal.coe_pos.mpr hH
  obtain ⟨De,hDe,hEarly⟩ := uniform_cluster_earlypulse_mass_tail_over_sample_spaces (Ξ := ℝ)
    hα hα' hκ ha hHr hC₀ (by norm_num : (0:ℝ)<1/8)
  obtain ⟨Dp,hDp,hPost⟩ := uniform_cluster_postpulse_mass_tail_over_sample_spaces (Ξ := ℝ)
    hα hα' hκ ha hHr
  let D := max De Dp
  refine ⟨D,hDe.trans_le (le_max_left _ _),?_⟩
  intro Ω m μ _ 𝒢 r ε M U C
  let _ : MeasurableSpace Ω := m
  dsimp only
  intro hε hr hs₀ hP hZ₂
  let d := ε^(1/α)
  let s₀ : ℝ := d/4
  let J := clusterAccumulatedVariance (fun s => U s.toNNReal)
  let Z := fractionalPulseMass ε M
  let Q := sizeBiasedLaw μ (Z r) ε
  have hd : 0<d := Real.rpow_pos_of_pos hε _
  have hs₀p : 0<s₀ := div_pos hd (by norm_num)
  have hs₀r : s₀.toNNReal≤r := Real.toNNReal_le_iff_le_coe.mpr hs₀
  have hs₀c : (s₀.toNNReal:ℝ)=s₀ := Real.coe_toNNReal s₀ hs₀p.le
  have hJad (s : ℝ≥0) : StronglyMeasurable[𝒢 s] (J s) :=
    fractional_pulse_accumulated_adapted hP.variance_adapted hP.variance_continuous s
  have hJm (s : ℝ≥0) : Measurable (J s) := ((hJad s).mono (𝒢.le s)).measurable
  have hJn (s : ℝ) (ω : Ω) : 0≤J s ω := integral_nonneg fun _ => hP.variance_nonnegative _ _
  have hAt (s : ℝ≥0) (hs : s≤r) (x : ℝ) :
      Q.real {ω | J s ω≤x*(s:ℝ)^(2*α)} =
        (sizeBiasedLaw μ (Z s) ε).real {ω | J s ω≤x*(s:ℝ)^(2*α)} :=
    fractional_pulse_bias_agrees_on_past hα₀ hα' hκ hε hd hs hr hP
      (measurableSet_le (hJad s).measurable measurable_const)
  refine ⟨?_,?_⟩
  · intro x hx hx₁
    let t := s₀.toNNReal
    let ν := rectangularPulseMeasure ε d s₀
    let : IsFiniteMeasure ν := rectangularPulseMeasure_isFiniteMeasure ε d s₀
    obtain ⟨hZm,hZn,hZi,hZmean,hZLp⟩ := fractional_pulse_mass_data hα₀ hα' hκ hε hd
      (hs₀r.trans hr) hP
    have hJmeas : Measurable (J s₀) := by
      have hJt : Measurable (J (t:ℝ)) := hJm t
      rw [show (t:ℝ)=s₀ from hs₀c] at hJt
      exact hJt
    have hMass : (1/8:ℝ)*s₀^α≤ν.real {v | s₀/2≤s₀-v} := by
      have h := rectangularPulseMeasure_earlypulse_scaled hε hα₀
      change s₀^α/8≤_ at h
      linarith
    have hTransform (q : ℝ) (hq : 0<q) (w : ℝ→ℝ) (hw : Continuous w)
        (he : ∀ s∈Icc 0 s₀, w s=volterraConvolution (fractionalK α)
          (fun u => q+(-κ)*w u+(-a)*(w u)^2) s) :
        (∫ ω,Real.exp (-q*J s₀ ω) ∂μ)=Real.exp (-(∫ v,w (s₀-v) ∂ν)) := by
      have he' (s : ℝ) (hs : s∈Ioc 0 (t:ℝ)) :
          w s=volterraConvolution (fractionalK α)
            (fun u => q+(0:ℝ)*(fractionalL α u+κ)-κ*w u-a*(w u)^2) s := by
        rw [hs₀c] at hs
        simpa only [zero_mul,add_zero,neg_mul,sub_eq_add_neg] using he s (Ioc_subset_Icc_self hs)
      have hA := fractional_pulse_density_affine_transform hα hα' hκ ha hε hd
        (Real.toNNReal_pos.mpr hs₀p) (hs₀r.trans hr) hq (show 0≤(0:ℝ) from le_rfl) hP hw he'
      rw [rectangularPulseMeasure_integral_eq_convolution hε.le hd]
      calc
        _ = ∫ ω,Real.exp (-(volterraConvolution (fun _ => q) (fun u => U u.toNNReal ω) s₀)) ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          change Real.exp (-q*J s₀ ω)=Real.exp (-(volterraConvolution (fun _ => q) (fun u => U u.toNNReal ω) s₀))
          unfold J clusterAccumulatedVariance volterraConvolution
          rw [integral_const_mul,neg_mul]
        _ = _ := by simpa only [zero_mul,add_zero,hs₀c] using hA
    have hTail := hEarly (Ω := Ω) μ ν (age := fun v => s₀-v) hs₀p
      (hs₀.trans (NNReal.coe_le_coe.mpr hr)) hε hJmeas hZm (ae_of_all _ (hJn s₀)) hZn hZi
      hZmean hZLp hZ₂ (measurable_const.sub measurable_id)
      (rectangularPulseMeasure_ae_age hs₀p.le) hMass hTransform x hx hx₁
    have he := hAt t hs₀r x
    rw [show ((t:ℝ))=s₀ from hs₀c] at he
    change Q.real {ω | J s₀ ω≤x*s₀^(2*α)}≤D*Real.sqrt x
    rw [he]
    exact hTail.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
  · intro s hds hsr x hx hx₁
    have hsr₀ : 0<(s:ℝ) := (show 0<2*d by positivity).trans_le hds
    have hs : s≤H := hsr.trans hr
    let ν := rectangularPulseMeasure ε d (s:ℝ)
    let : IsFiniteMeasure ν := rectangularPulseMeasure_isFiniteMeasure ε d (s:ℝ)
    obtain ⟨hZm,hZn,hZi,hZmean,_⟩ := fractional_pulse_mass_data hα₀ hα' hκ hε hd hs hP
    obtain ⟨hνmass,hνage⟩ := rectangularPulseMeasure_postpulse hε.le hd hds
    have hTransform (q : ℝ) (hq : 0<q) (l : ℝ) (hl : l∈Icc (0:ℝ) 1) (w : ℝ→ℝ)
        (hw : Continuous w)
        (he : ∀ t∈Icc 0 (s:ℝ), w t=l+volterraConvolution (fractionalK α)
          (fun u => q+κ*l-κ*w u-a*(w u)^2) t) :
        (∫ ω,Real.exp (-q*J s ω-l*Z s ω) ∂μ)=Real.exp (-(∫ v,w ((s:ℝ)-v) ∂ν)) := by
      have he' (t : ℝ) (ht : t∈Ioc 0 (s:ℝ)) := density_riccati_affine_convolution hα₀ hα' ht hw he
      have hA := fractional_pulse_density_affine_transform hα hα' hκ ha hε hd
        (NNReal.coe_pos.mp hsr₀) hs hq hl.1 hP hw he'
      change (∫ ω,Real.exp (-q*J s ω-l*Z s ω) ∂μ)=
        Real.exp (-(∫ v,w ((s:ℝ)-v) ∂rectangularPulseMeasure ε d (s:ℝ)))
      rw [rectangularPulseMeasure_integral_eq_convolution hε.le hd]
      refine (integral_congr_ae ?_).trans hA
      filter_upwards [fractional_pulse_postpulse_affine_payoff (q := q) (l := l)
        hα₀ hα' hε.le hd (show d≤(s:ℝ) by linarith) hs hP] with ω hω
      rw [hω]
      congr 1
      ring
    have hTail := hPost (Ω := Ω) μ ν (age := fun v => (s:ℝ)-v) hsr₀ (NNReal.coe_le_coe.mpr hs) hε
      (hJm s) hZm (ae_of_all _ (hJn s)) hZn hZi hZmean
      (measurable_const.sub measurable_id) hνage hνmass hTransform x hx hx₁
    change Q.real {ω | J s ω≤x*(s:ℝ)^(2*α)}≤D*Real.sqrt x
    rw [hAt s hsr x]
    exact hTail.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _))

private theorem envelopeStop_congr_path {Ω : Type*} {E F : ℝ≥0 → Ω → ℝ}
    (r : ℝ≥0) (c : ℝ) (ω : Ω) (h : ∀ t, E t ω=F t ω) :
    envelopeStop r c E ω=envelopeStop r c F ω := by
  have hS : {t : ℝ≥0 | ⊥≤t ∧ E t ω∈Ioi c}={t : ℝ≥0 | ⊥≤t ∧ F t ω∈Ioi c} := by
    ext t
    simp only [mem_ofPred_eq,h]
  have hE : (∃ t : ℝ≥0, ⊥≤t ∧ E t ω∈Ioi c) ↔ (∃ t : ℝ≥0, ⊥≤t ∧ F t ω∈Ioi c) := by
    constructor
    · rintro ⟨t,ht,he⟩
      exact ⟨t,ht,(h t) ▸ he⟩
    · rintro ⟨t,ht,he⟩
      exact ⟨t,ht,(h t).symm ▸ he⟩
  unfold envelopeStop leastGT hittingAfter
  by_cases he : ∃ t : ℝ≥0, ⊥≤t ∧ E t ω∈Ioi c
  · rw [ite_eq_left he,ite_eq_left (hE.mp he),hS]
  · rw [ite_eq_right he,ite_eq_right (he ∘ hE.mpr)]

/-- Denominator tails from the genuine pulse affine transform give
the uniform envelope. The coefficient precedes the law, filtration,
observation age, mesh mass, and block data. -/
theorem uniform_actual_pulse_envelope_over_sample_spaces
    {α κ a C₀ γ K p σ : ℝ} {H : ℝ≥0}
    (hα : 1/2<α) (hα' : α<1) (hκ : 0≤κ) (ha : 0<a) (hH : 0<H) (hC₀ : 0<C₀)
    (hγ : 0<γ) (hK : 0≤K) (hp : 0<p) :
    ∃ Cenv : ℝ, 0≤Cenv ∧ ∀ {Ω : Type u} {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
      (𝒢 : Filtration ℝ≥0 m) (r : ℝ≥0) (ε : ℝ) (M U C : ℝ≥0 → Ω → ℝ),
      let d := ε^(1/α)
      let Z := fractionalPulseMass ε M
      let Q := @sizeBiasedLaw Ω m μ (Z r) ε
      0<ε → r≤H → 4*d≤(r:ℝ) →
      FractionalPulseProcess μ 𝒢 H α κ a ε d M U C →
      (∫ ω,(Z (d/4).toNNReal ω)^2 ∂μ)≤C₀*ε^2 →
      Nonempty (@PulseBlockUpperMean Ω m Q (fun t => U t.toNNReal) 0 (4*d) d α K) →
      (∀ j, let s := clusterDyadicAge (r:ℝ) j
        2*d≤s → Nonempty (@PulseBlockUpperMean Ω m Q (fun t => U t.toNNReal) s (2*s) s α K)) →
      Q.real {ω | envelopeStop r (Cenv*(r:ℝ)^(3*γ))
        (clusterEnvelopeValue 0 σ (1+3*γ) U Z) ω<r}≤p := by
  have hα₀ : 0<α := by linarith
  obtain ⟨D,hD,hTail⟩ := uniform_actual_fractional_pulse_mass_tails_over_sample_spaces
    hα hα' hκ ha hH hC₀
  obtain ⟨Cenv,hCenv,hEnvelope⟩ := uniform_focal_envelope_of_block_estimates_over_sample_spaces
    (σ := σ) hα₀ hα' hγ hK hD.le hp
  refine ⟨Cenv,hCenv,?_⟩
  intro Ω m μ _ 𝒢 r ε M U C
  let _ : MeasurableSpace Ω := m
  dsimp only
  intro hε hr hd4 hP hZ2 hEarly hLate
  let d := ε^(1/α)
  let Z := fractionalPulseMass ε M
  let Q := sizeBiasedLaw μ (Z r) ε
  have hd : 0<d := Real.rpow_pos_of_pos hε _
  have hεd : ε=d^α := by
    dsimp [d]
    rw [← Real.rpow_mul hε.le,one_div,inv_mul_cancel₀ hα₀.ne',Real.rpow_one]
  obtain ⟨hZm,hZn,hZi,hZmean,_⟩ := fractional_pulse_mass_data hα₀ hα' hκ hε hd hr hP
  let : IsProbabilityMeasure Q := sizeBiasedLaw_isProbabilityMeasure hε hZi hZn hZmean
  have hQμ : Q ≪ μ := withDensity_absolutelyContinuous μ _
  let good (ω : Ω) : Prop := ∀ s∈Icc (0:ℝ) (H:ℝ),
    Z s.toNNReal ω=ε-(ε/d)*min s d+volterraConvolution (fractionalL α)
      (fun u => U u.toNNReal ω) s+κ*clusterAccumulatedVariance (fun u => U u.toNNReal) s ω
  have hGood : ∀ᵐ ω ∂Q, good ω :=
    hQμ.ae_le (fractional_pulse_mass_identity hα₀ hα' hε.le hd hP)
  classical
  let U' (s : ℝ≥0) (ω : Ω) := if good ω then U s ω else 0
  let Z' (s : ℝ≥0) (ω : Ω) := if good ω then Z s ω else ε-(ε/d)*min (s:ℝ) d
  have hU'c (ω : Ω) : Continuous (fun t => U' t ω) := by
    by_cases hw : good ω
    · simpa only [U',ite_eq_left hw] using hP.variance_continuous ω
    · simpa only [U',ite_eq_right hw] using (continuous_const : Continuous (fun _ : ℝ≥0 => (0:ℝ)))
  have hU'n (s : ℝ≥0) (_ : s≤r) (ω : Ω) : 0≤U' s ω := by
    by_cases hw : good ω
    · simpa only [U',ite_eq_left hw] using hP.variance_nonnegative s ω
    · simp [U',hw]
  have hZ' (s : ℝ≥0) (hs : s≤r) (ω : Ω) :
      Z' s ω=ε-(ε/d)*min (s:ℝ) d+
        volterraConvolution (fractionalL α) (fun u => U' u.toNNReal ω) (s:ℝ)+
        κ*clusterAccumulatedVariance (fun u => U' u.toNNReal) (s:ℝ) ω := by
    by_cases hw : good ω
    · simpa only [U',Z',ite_eq_left hw,Real.toNNReal_coe,clusterAccumulatedVariance] using
        hw (s:ℝ) ⟨NNReal.coe_nonneg _, NNReal.coe_le_coe.mpr (hs.trans hr)⟩
    · simp [U',Z',hw,volterraConvolution,clusterAccumulatedVariance]
  have hMassTail := hTail (Ω := Ω) μ 𝒢 r ε M U C hε hr (by linarith [hd4,hd]) hP hZ2
  have hBuild {lo hi massAge age : ℝ}
      (hSup : PulseBlockUpperMean Q (fun t => U t.toNNReal) lo hi age α K)
      (hMtail : ∀ x,0<x → x≤1 →
        Q.real {ω | clusterAccumulatedVariance (fun t => U t.toNNReal) massAge ω≤x*massAge^(2*α)}
          ≤D*Real.sqrt x) :
      FocalBlockEstimate Q (fun t => U' t.toNNReal) lo hi massAge age α K D := by
    let S (ω : Ω) := max (hSup.supU ω) 0
    have hSeq : hSup.supU =ᵐ[Q] S := hSup.nonnegative.mono fun ω hw =>
      (max_eq_left hw).symm
    refine ⟨S,?_,hSup.integrable.congr hSeq,ae_of_all _ (fun _ => le_max_right _ _),?_,?_⟩
    · intro t ht ω
      by_cases hw : good ω
      · have hh : U' t.toNNReal ω≤hSup.supU ω := by
          simpa only [U',ite_eq_left hw] using hSup.dominates t ht ω
        exact hh.trans (le_max_left _ _)
      · simp only [U',ite_eq_right hw]
        exact le_max_right _ _
    · rw [← integral_congr_ae hSeq]
      exact hSup.mean
    · intro x hx hx₁
      have hSets : {ω | clusterAccumulatedVariance (fun t => U' t.toNNReal) massAge ω≤x*massAge^(2*α)}
          =ᵐ[Q] {ω | clusterAccumulatedVariance (fun t => U t.toNNReal) massAge ω≤x*massAge^(2*α)} := by
        filter_upwards [hGood] with ω hw
        have hh : (fun t : ℝ => U' t.toNNReal ω)=(fun t : ℝ => U t.toNNReal ω) := by
          funext t
          simp [U',hw]
        change ((∫ t in Ioc 0 massAge,U' t.toNNReal ω)≤x*massAge^(2*α)) =
          ((∫ t in Ioc 0 massAge,U t.toNNReal ω)≤x*massAge^(2*α))
        rw [hh]
      exact (measureReal_congr hSets).trans_le (hMtail x hx hx₁)
  obtain ⟨hEarly⟩ := hEarly
  have he := hBuild hEarly hMassTail.1
  have hl (j : ℕ) (hds : 2*d≤clusterDyadicAge (r:ℝ) j) :
      let s := clusterDyadicAge (r:ℝ) j
      FocalBlockEstimate Q (fun t => U' t.toNNReal) s (2*s) s s α K D := by
    let s := clusterDyadicAge (r:ℝ) j
    have hs₀ : 0≤s := by dsimp [s,clusterDyadicAge]; positivity
    have hsr : s≤(r:ℝ) := by
      dsimp [s,clusterDyadicAge]
      exact mul_le_of_le_one_right (NNReal.coe_nonneg _) (pow_le_one₀ (by norm_num) (by norm_num))
    have hs : s.toNNReal≤r := Real.toNNReal_le_iff_le_coe.mpr hsr
    have hsc : (s.toNNReal:ℝ)=s := Real.coe_toNNReal s hs₀
    let hUpper := Classical.choice (hLate j hds)
    apply hBuild hUpper
    intro x hx hx₁
    have hds' : 2*d≤(s.toNNReal:ℝ) := by simpa only [hsc] using hds
    have hh := hMassTail.2 s.toNNReal hds' hs x hx hx₁
    rw [hsc] at hh
    exact hh
  have hEnvelopeBound := hEnvelope (Ω := Ω) Q r d ε κ U' Z' hd hd4 hεd hκ hU'c hU'n hZ' he
    (fun j hj => hl j hj)
  have heq : {ω | envelopeStop r (Cenv*(r:ℝ)^(3*γ))
      (clusterEnvelopeValue 0 σ (1+3*γ) U Z) ω<r} =ᵐ[Q]
      {ω | envelopeStop r (Cenv*(r:ℝ)^(3*γ))
      (clusterEnvelopeValue 0 σ (1+3*γ) U' Z') ω<r} := by
    filter_upwards [hGood] with ω hw
    have hh := envelopeStop_congr_path (E := clusterEnvelopeValue 0 σ (1+3*γ) U Z)
      (F := clusterEnvelopeValue 0 σ (1+3*γ) U' Z') r (Cenv*(r:ℝ)^(3*γ)) ω
        (fun t => by simp [clusterEnvelopeValue,U',Z',hw])
    change (_<r) = (_<r)
    rw [hh]
  exact (measureReal_congr heq).trans_le hEnvelopeBound

theorem uniform_actual_pulse_stopped_separation_over_sample_spaces
    {α κ a σ C₀ γ K p cU cZ cB η rCap : ℝ} {H : ℝ≥0}
    (hα : 1/2<α) (hα' : α<1) (hκ : 0≤κ) (ha : 0<a) (hH : 0<H) (hC₀ : 0<C₀)
    (hγ : 0<γ) (hK : 0≤K) (hp : 0<p) (_hcU : 0<cU) (hcZ : 0<cZ) (hcB : 0<cB)
    (hη : 0<η) (hrCap : 0<rCap) :
    ∃ Cenv : ℝ, 0≤Cenv ∧ ∀ Cenergy Cocc : ℝ,
      ∃ (r : ℝ≥0) (ε₀ c : ℝ), 0<r ∧ r≤H ∧ (r:ℝ)<rCap ∧ 0<ε₀ ∧ ε₀=((r:ℝ)/8)^α ∧ 0<c ∧
      ∀ {Ω : Type u} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝒢 : Filtration ℝ≥0 m)
        (birth : Set Ω) (ε : ℝ) (M U C : ℝ≥0 → Ω → ℝ) (Y : Ω → ℝ),
        let μ := @boundaryConditionedMeasure Ω m P birth
        let d := ε^(1/α)
        let Z := fractionalPulseMass ε M
        let Q := @sizeBiasedLaw Ω m μ (Z r) ε
        let env := envelopeStop r (Cenv*(r:ℝ)^(3*γ)) (clusterEnvelopeValue 0 σ (1+3*γ) U Z)
        let δ := (r:ℝ)^(2*η/3)
        0<ε → ε≤ε₀ → cB≤P.real birth →
        FractionalPulseProcess μ 𝒢 H α κ a ε d M U C →
        (∫ ω,(Z (d/4).toNNReal ω)^2 ∂μ)≤C₀*ε^2 →
        Nonempty (@PulseBlockUpperMean Ω m Q (fun t => U t.toNNReal) 0 (4*d) d α K) →
        (∀ j, let s := clusterDyadicAge (r:ℝ) j
          2*d≤s → Nonempty (@PulseBlockUpperMean Ω m Q (fun t => U t.toNNReal) s (2*s) s α K)) →
        Measurable[m] Y → (∀ ω,0≤Y ω) →
        p≤Q.real {ω | cU*(r:ℝ)^(2*α-1)≤U r ω ∧ Z r ω≤cZ*(r:ℝ)^α} →
        (∀ (R : Measure Ω) [IsProbabilityMeasure R],
          @PulseStoppedLaw Ω m Q R r δ (Cenergy*(r:ℝ)^η) (Cocc*(r:ℝ)^η) env Y →
          c*ε≤P.real ({ω | cU*(r:ℝ)^(2*α-1)≤U r ω ∧ Y ω=0} ∩ birth)) := by
  have hα₀ : 0<α := by linarith
  have hp4 : 0<p/4 := by positivity
  obtain ⟨Cenv,hCenv,hEnv⟩ := uniform_actual_pulse_envelope_over_sample_spaces (σ := σ)
    (γ := γ) hα hα' hκ ha hH hC₀ hγ hK hp4
  refine ⟨Cenv,hCenv,?_⟩
  intro Cenergy Cocc
  have hHr : 0<(H:ℝ) := NNReal.coe_pos.mpr hH
  have hNear : ∀ᶠ r in 𝓝[>] (0:ℝ), 0<r ∧ r<min (H:ℝ) rCap ∧
      p/2≤p-p/4-Cenergy*r^η/r^(2*η/3)-Cocc*r^η-Real.sqrt (r^(2*η/3))/2 := by
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds (lt_min hHr hrCap)),
      eventually_small_age_separation hη hp Cenergy Cocc] with r hr hl hs
    exact ⟨hr,hl,hs⟩
  obtain ⟨u,hu,huH,huSep⟩ := hNear.exists
  let r := u.toNNReal
  have hru : (r:ℝ)=u := Real.coe_toNNReal u hu.le
  have hr : 0<r := NNReal.coe_pos.mp (by simpa only [hru] using hu)
  have hrH : r≤H := NNReal.coe_le_coe.mp (by rw [hru]; exact huH.le.trans (min_le_left _ _))
  have hrC : (r:ℝ)<rCap := by rw [hru]; exact huH.trans_le (min_le_right _ _)
  let ε₀ := (u/8)^α
  let cap := cZ*(r:ℝ)^α
  have hcap : 0<cap := mul_pos hcZ (Real.rpow_pos_of_pos (NNReal.coe_pos.mpr hr) _)
  let c := cB*(p/2)/cap
  have hc : 0<c := div_pos (mul_pos hcB (by positivity)) hcap
  refine ⟨r,ε₀,c,hr,hrH,hrC,Real.rpow_pos_of_pos (by positivity) _,?_,hc,?_⟩
  · change (u/8)^α=((r:ℝ)/8)^α
    rw [hru]
  intro Ω m P _ 𝒢 birth ε M U C Y
  let _ : MeasurableSpace Ω := m
  dsimp only
  intro hε hε₀ hBirth hP hZ₂ hEarly hLate hYm hY₀ hBurst R _ stopped
  let μ := boundaryConditionedMeasure P birth
  let Z := fractionalPulseMass ε M
  let Q := sizeBiasedLaw μ (Z r) ε
  let d := ε^(1/α)
  let δ := (r:ℝ)^(2*η/3)
  let env := envelopeStop r (Cenv*(r:ℝ)^(3*γ)) (clusterEnvelopeValue 0 σ (1+3*γ) U Z)
  have hB : 0<P birth := (ENNReal.toReal_pos_iff.mp (hcB.trans_le hBirth)).1
  let : IsProbabilityMeasure μ := boundaryConditionedMeasure_isProbability hB
  have hd : 0<d := Real.rpow_pos_of_pos hε _
  have hdR : d≤u/8 := by
    have hv := Real.rpow_le_rpow hε.le hε₀ (by positivity : 0≤1/α)
    dsimp [ε₀] at hv
    rw [← Real.rpow_mul (by positivity : 0≤u/8),one_div,mul_inv_cancel₀ hα₀.ne',
      Real.rpow_one] at hv
    simpa only [d,one_div] using hv
  have hd4 : 4*d≤(r:ℝ) := by rw [hru]; linarith
  have hδ : 0<δ := Real.rpow_pos_of_pos (NNReal.coe_pos.mpr hr) _
  obtain ⟨hZm,hZn,hZi,hZmean,_⟩ := fractional_pulse_mass_data hα₀ hα' hκ hε hd hrH hP
  let : IsProbabilityMeasure Q := sizeBiasedLaw_isProbabilityMeasure hε hZi hZn hZmean
  have hEnvelope : Q.real {ω | env ω<r}≤p/4 :=
    hEnv (Ω := Ω) μ 𝒢 r ε M U C hε hrH hd4 hP hZ₂ hEarly hLate
  have hSep := stopped_burst_with_zero_probability hδ stopped.stop_measurable hYm hY₀
    stopped.energy_measurable stopped.energy_nonnegative stopped.energy_integrable
    stopped.energy_mean stopped.exit hEnvelope stopped.stopped_occupation stopped.total_variation hBurst
  have hSep' : p/2≤Q.real
      ({ω | cU*(r:ℝ)^(2*α-1)≤U r ω ∧ Z r ω≤cap} ∩ {ω | Y ω=0}) := by
    refine le_trans ?_ hSep
    simpa only [δ,hru] using huSep
  have hUm : Measurable (U r) := ((hP.variance_adapted r).mono (𝒢.le r)).measurable
  exact original_single_birth_burst hB hBirth hε hcap (by positivity) hUm hYm hZm hSep'

theorem uniform_actual_pulse_separation_of_resolvent_mean_over_sample_spaces
    {α κ a σ γ K p cU cZ cB η rCap : ℝ} {H : ℝ≥0} {L : ℝ → ℝ}
    (hα : 1/2<α) (hα' : α<1) (hκ : 0≤κ) (ha : 0<a) (hH : 0<H)
    (hγ : 0<γ) (hK : 0≤K) (hp : 0<p) (hcU : 0<cU) (hcZ : 0<cZ) (hcB : 0<cB)
    (hη : 0<η) (hrCap : 0<rCap)
    (hLm : Measurable L) (hL : ∀ t∈Ioc (0:ℝ) (H:ℝ),0≤L t ∧ L t≤2*fractionalK α t) :
    ∃ Cenv : ℝ, 0≤Cenv ∧ ∀ Cenergy Cocc : ℝ,
      ∃ (r : ℝ≥0) (ε₀ c : ℝ), 0<r ∧ r≤H ∧ (r:ℝ)<rCap ∧ 0<ε₀ ∧ ε₀=((r:ℝ)/8)^α ∧ 0<c ∧
      ∀ {Ω : Type u} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝒢 : Filtration ℝ≥0 m)
        (birth : Set Ω) (ε : ℝ) (M U C : ℝ≥0 → Ω → ℝ) (Y : Ω → ℝ),
        let μ := @boundaryConditionedMeasure Ω m P birth
        let d := ε^(1/α)
        let Z := fractionalPulseMass ε M
        let Q := @sizeBiasedLaw Ω m μ (Z r) ε
        let env := envelopeStop r (Cenv*(r:ℝ)^(3*γ)) (clusterEnvelopeValue 0 σ (1+3*γ) U Z)
        let δ := (r:ℝ)^(2*η/3)
        0<ε → ε≤ε₀ → cB≤P.real birth →
        FractionalPulseProcess μ 𝒢 H α κ a ε d M U C →
        (∀ t≤H, Integrable (U t) μ) →
        (∀ t∈Ioc (0:ℝ) (H:ℝ), (∫ ω,U t.toNNReal ω ∂μ)=
          volterraConvolution L (rectangularPulseRate ε d) t) →
        (∀ s, d≤s → 2*s≤(r:ℝ) →
          Nonempty (@PulseBlockUpperMean Ω m Q (fun t => U t.toNNReal) 0 (2*s) s α K)) →
        Measurable[m] Y → (∀ ω,0≤Y ω) →
        p≤Q.real {ω | cU*(r:ℝ)^(2*α-1)≤U r ω ∧ Z r ω≤cZ*(r:ℝ)^α} →
        (∀ (R : Measure Ω) [IsProbabilityMeasure R],
          @PulseStoppedLaw Ω m Q R r δ (Cenergy*(r:ℝ)^η) (Cocc*(r:ℝ)^η) env Y →
          c*ε≤P.real ({ω | cU*(r:ℝ)^(2*α-1)≤U r ω ∧ Y ω=0} ∩ birth)) := by
  have hα₀ : 0<α := by linarith
  let K' := K*(2:ℝ)^(2*α-1)
  have hK' : 0≤K' := mul_nonneg hK (by positivity)
  let C₀ := 1+(2*a)*(4/(Real.Gamma α*α))/4
  have hC₀ : 0<C₀ := by
    dsimp [C₀]
    exact add_pos_of_pos_of_nonneg zero_lt_one (by positivity)
  obtain ⟨Cenv,hCenv,hSep⟩ := uniform_actual_pulse_stopped_separation_over_sample_spaces
    (σ := σ) hα hα' hκ ha hH hC₀ hγ hK' hp hcU hcZ hcB hη hrCap
  refine ⟨Cenv,hCenv,?_⟩
  intro Cenergy Cocc
  obtain ⟨r,ε₀,c,hr,hrH,hrCap,hε₀,hε₀Eq,hc,hData⟩ := hSep Cenergy Cocc
  refine ⟨r,ε₀,c,hr,hrH,hrCap,hε₀,hε₀Eq,hc,?_⟩
  intro Ω m P _ 𝒢 birth ε M U C Y
  let _ : MeasurableSpace Ω := m
  dsimp only
  intro hε hcut hBirth hP hUi hMean hFull hYm hYn hBurst
  let d := ε^(1/α)
  have hd : 0<d := Real.rpow_pos_of_pos hε _
  have hεd : ε=d^α := by
    dsimp [d]
    rw [← Real.rpow_mul hε.le,one_div,inv_mul_cancel₀ hα₀.ne',Real.rpow_one]
  have hSmall : d≤(r:ℝ)/8 := by
    rw [hε₀Eq] at hcut
    have he := Real.rpow_le_rpow hε.le hcut (by positivity : 0≤1/α)
    rw [← Real.rpow_mul (by positivity : 0≤(r:ℝ)/8),one_div,
      mul_inv_cancel₀ hα₀.ne',Real.rpow_one] at he
    simpa only [d,one_div] using he
  have hd4 : 4*d≤(r:ℝ) := by linarith [NNReal.coe_nonneg r]
  have hdH : d/4≤(H:ℝ) := by
    linarith [NNReal.coe_le_coe.mpr hrH]
  let μ := boundaryConditionedMeasure P birth
  have hpos : 0<P birth := (ENNReal.toReal_pos_iff.mp (hcB.trans_le hBirth)).1
  let : IsProbabilityMeasure μ := boundaryConditionedMeasure_isProbability hpos
  have hZ₂ := actual_pulse_early_mass_second_of_resolvent_mean hα₀ hα' ha.le hd hεd hdH
    hP hUi hLm hL hMean
  obtain ⟨_,hEarly,hLate⟩ := actual_pulse_block_means_of_full hα hK hd hd4 hFull
  exact hData (Ω := Ω) P 𝒢 birth ε M U C Y hε hcut hBirth hP hZ₂ hEarly hLate hYm hYn hBurst

theorem uniform_affine_boundary_backward_mean_over_sample_spaces
    {α κ a lo hi b B D : ℝ}
    (hα : 1/2<α) (hα' : α<1) (hκ : 0≤κ) (ha : 0<a)
    (hlo : 0<lo) (hB : 0≤B) :
    ∃ p ∈ Ioo (2*α-1) α, ∃ C : ℝ, 0<C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {V : ℝ → Ω → ℝ} {w : ℕ → ℝ → ℝ},
        (∀ t, Measurable (V t)) → (∀ t ω,0≤V t ω) →
        (∀ t∈Icc 0 hi, Integrable (V t) μ) →
        (∀ t∈Icc 0 hi, (∫ ω,V t ω ∂μ)≤B) →
        (∀ (n : ℕ) (t : ℝ), PointChargeRiccatiOn α (n:ℝ) (-κ) (-a) t (w n)) →
        (∀ t∈Icc lo hi, ∀ n, Real.exp (-D) ≤ (∫ ω,laplaceBoundaryWeight (V t) n ω ∂μ)) →
        (∀ t∈Icc lo hi, ∀ n,
          let f (r : ℝ) := ∫ ω,V r ω ∂laplaceBoundaryTilt μ (V t) n
          ContinuousOn f (Ico 0 t) ∧
          ∀ s ∈ Ioo (0:ℝ) t, f s = f 0+
            volterraConvolution (fractionalK α) (fun r => b-(κ+2*a*w n (t-r))*f r) s) →
        ∀ t ∈ Icc lo hi, ∀ u ∈ Ioc (0:ℝ) t,
          (∫ ω,V (t-u) ω ∂boundaryConditionedMeasure μ {ω | V t ω=0})≤C*u^p := by
  obtain ⟨p,hp,hpg⟩ := exists_backwardPowerCoefficient_gap hα hα' ha
  have hp₀ : 0<p := (show 0<2*α-1 by linarith).trans hp.1
  have hpc : caputoCoefficient α p < boundaryCoefficient α := by
    rw [← two_mul_singularRiccatiCoefficient hα' ha]
    exact hpg
  obtain ⟨c,hc,d,hd,N,hN,hR⟩ :=
    exists_global_riccati_uniform_boundary_lower hα hα' ha hκ (half_pos hlo) hpc
  let K := B/Real.exp (-D)
  have hK : 0≤K := div_nonneg hB (Real.exp_pos _).le
  obtain ⟨A,hA,hComp⟩ := caputo_mean_le_backwardPower_of_volterra (b := b) hα hα' hp₀ hp.2 hc hK hd.1
  let C := max A (K/d^p)
  have hC : 0<C := hA.trans_le (le_max_left _ _)
  refine ⟨p,hp,C,hC,?_⟩
  intro Ω _ μ _ V w hVm hVnn hVi hVB hw hAff hMean t ht u hu
  let f (n : ℕ) (r : ℝ) := ∫ ω,V r ω ∂laplaceBoundaryTilt μ (V t) n
  have hdt : d<t := hd.2.trans_lt ((half_lt_self hlo).trans_le ht.1)
  have ht₀ : 0<t := hlo.trans_le ht.1
  have hKf (n : ℕ) (r : ℝ) (hr : r ∈ Icc 0 t) : f n r ≤ K := by
    have hr' : r∈Icc 0 hi := ⟨hr.1,hr.2.trans ht.2⟩
    let P := laplaceBoundaryWeight (V t) n
    have hPm : Measurable P := ((hVm t).const_mul (-(n:ℝ))).exp
    have hP0 (ω : Ω) : 0≤P ω := (Real.exp_pos _).le
    have hP1 (ω : Ω) : P ω≤1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (hVnn _ _))
    have hInt : Integrable (fun ω => P ω*V r ω) μ :=
      (hVi r hr').bdd_mul hPm.aestronglyMeasurable
        (ae_of_all _ fun ω => by simpa only [Real.norm_of_nonneg (hP0 ω)] using hP1 ω)
    have hNum : (∫ ω,P ω*V r ω ∂μ)≤B :=
      (integral_mono hInt (hVi r hr') (fun ω => mul_le_of_le_one_left (hVnn _ _) (hP1 ω))).trans
        (hVB r hr')
    have hPos : 0<(∫ ω,P ω ∂μ) := (Real.exp_pos _).trans_le (hAff t ht n)
    change (∫ ω,V r ω ∂laplaceBoundaryTilt μ (V t) n)≤K
    rw [laplaceBoundaryTilt_integral _ _ (hVm t)]
    exact (div_le_div_of_nonneg_right hNum hPos.le).trans
      (div_le_div_of_nonneg_left hB (Real.exp_pos _) (hAff t ht n))
  have hAtom : 0<μ {ω | V t ω=0} := by
    have hh := ge_of_tendsto (tendsto_laplaceBoundary_atom (hVm t) (ae_of_all _ (hVnn t)))
      (Eventually.of_forall (hAff t ht))
    exact (ENNReal.toReal_pos_iff.mp ((Real.exp_pos _).trans_le hh)).1
  have htu : t-u∈Icc (0:ℝ) t := ⟨sub_nonneg.mpr hu.2,sub_le_self _ hu.1.le⟩
  apply boundaryConditionalMean_le_of_laplaceTilt (hVm t) (ae_of_all _ (hVnn t))
    (hVi (t-u) ⟨htu.1,htu.2.trans ht.2⟩) hAtom
  by_cases hud : d≤u
  · exact Eventually.of_forall fun n => (hKf n (t-u) htu).trans (by
      have hdPow : 0<d^p := Real.rpow_pos_of_pos hd.1 _
      have hPow : d^p≤u^p := Real.rpow_le_rpow hd.1.le hud hp₀.le
      calc
        K = (K/d^p)*d^p := (div_mul_cancel₀ _ hdPow.ne').symm
        _ ≤ C*d^p := mul_le_mul_of_nonneg_right (le_max_right _ _) hdPow.le
        _ ≤ C*u^p := mul_le_mul_of_nonneg_left hPow hC.le)
  · have hPow : 0<u^(2*α-1) := Real.rpow_pos_of_pos hu.1 _
    obtain ⟨n₀,hn₀⟩ := exists_nat_ge ((N:ℝ)/u^(2*α-1))
    filter_upwards [eventually_ge_atTop n₀] with n hn
    have hnR : (N:ℝ)≤(n:ℝ)*u^(2*α-1) :=
      (div_le_iff₀ hPow).mp (hn₀.trans (Nat.cast_le.mpr hn))
    let k (r : ℝ) := κ+2*a*w n (t-r)
    have hkc (r : ℝ) (hr : r∈Ico 0 t) : ContDiffAt ℝ 1 k r :=
      contDiffAt_const.add (contDiffAt_const.mul ((hw n t).contDiffAt_pos _ (sub_pos.mpr hr.2)
        |>.comp r (contDiffAt_const.sub contDiffAt_id)))
    have hkC : ContinuousOn k (Ico 0 t) := fun r hr => (hkc r hr).continuousAt.continuousWithinAt
    have hkl (r : ℝ) (hr : r ∈ Icc (t-d) (t-u)) : c*(t-r)^(-α)≤k r := by
      have h₁ : u≤t-r := by linarith [hr.2]
      have h₂ : t-r≤d := by linarith [hr.1]
      have hh := hR hu.1 h₁ h₂ hnR (hw n (t-r))
      dsimp [k]
      linarith
    have hmean := hMean t ht n
    have hh := hComp (T := t) (S := t-u) hdt (sub_lt_self _ hu.1)
      hmean.1 hkC (fun r hr => hkc r ⟨hr.1.le,hr.2⟩)
      (fun r hr => hKf n r ⟨hr.1,hr.2.trans (sub_le_self _ hd.1.le)⟩)
      hkl hmean.2 (t-u) ⟨sub_le_sub_left (le_of_not_ge hud) _,le_rfl⟩
    have hh' : f n (t-u) < A*u^p := by
      simpa only [sub_sub_cancel] using hh
    exact hh'.le.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg hu.1.le _))

/-- The boundary constants are chosen before the probability law and
filtration when the variance has a common second-moment bound. -/
theorem uniform_heston_zero_boundary_over_laws_over_sample_spaces
    {α κ a b v₀ lo hi B₂ : ℝ} {U : ℝ≥0}
    (hα : 1/2<α) (hα' : α<1) (hκ : 0≤κ) (ha : 0<a) (hb : 0≤b) (hv₀ : 0≤v₀)
    (hlo : 0<lo) (hhi : hi<(U:ℝ)) (hB₂ : 0≤B₂) :
    ∃ c C₁ η h₀ : ℝ, 0<c ∧ 0<C₁ ∧ 0<η ∧ 0<h₀ ∧
      ∀ {Ω : Type u} {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ] (𝒢 : Filtration ℝ≥0 m)
        {M V C : ℝ≥0 → Ω → ℝ},
        HestonBoundaryProcess μ 𝒢 U α κ a b v₀ M V C →
        (∀ t≤U, (∫ ω,(V t ω)^2 ∂μ)≤B₂) →
        ∀ t∈Icc lo hi,
          c≤μ.real {ω | V t.toNNReal ω=0} ∧
          ∀ h∈Ioc (0:ℝ) h₀,
            (@boundaryConditionedMeasure Ω m μ {ω | V t.toNNReal ω=0}).real
              {ω | 0<V (t+h).toNNReal ω}≤C₁*h^η := by
  let j (r : ℝ) := b+v₀*fractionalL α r
  let W := singularRiccatiCoefficient α a
  let D := W*Real.Gamma (1-α)*
    (b*(hi^(1-α)/Real.Gamma (2-α))+v₀*(lo^(1-2*α)/Real.Gamma (2-2*α)))
  let c := Real.exp (-D)
  let h₀ := min 1 ((U:ℝ)-hi)
  have hα₀ : 0<α := by linarith
  have hW : 0<W := singularRiccatiCoefficient_pos hα hα' ha
  have hc : 0<c := Real.exp_pos _
  have hh₀ : 0<h₀ := lt_min zero_lt_one (sub_pos.mpr hhi)
  obtain ⟨w,hw,hwn⟩ := exists_boundary_point_test_family hα hα' hκ ha.le
  have hjm : Measurable j := ((fractionalL_measurable α).const_mul v₀).const_add b
  let B := 1+B₂
  have hB : 0≤B := add_nonneg zero_le_one hB₂
  obtain ⟨p,hp,C₀,hC₀,hBackAll⟩ := uniform_affine_boundary_backward_mean_over_sample_spaces
    (hi := hi) (b := b) (D := D) hα hα' hκ ha hlo hB
  let η := p+1-2*α
  have hη : 0<η := by dsimp [η]; linarith [hp.1]
  have hp₀ : 0<p := by linarith [hp.1]
  let J := j lo
  have hJb {r : ℝ} (hr : lo≤r) : 0≤j r ∧ j r≤J := by
    have hr₀ : 0<r := hlo.trans_le hr
    have hΓ : 0<Real.Gamma (1-α) := Real.Gamma_pos_of_pos (sub_pos.mpr hα')
    have hL₀ : 0≤fractionalL α r := by
      rw [fractionalL,ite_eq_right (not_le.mpr hr₀)]
      exact div_nonneg (Real.rpow_nonneg hr₀.le _) hΓ.le
    have hL : fractionalL α r≤fractionalL α lo := by
      rw [fractionalL,fractionalL,ite_eq_right (not_le.mpr hr₀),ite_eq_right (not_le.mpr hlo)]
      exact div_le_div_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hlo hr (neg_nonpos.mpr hα₀.le)) hΓ.le
    exact ⟨add_nonneg hb (mul_nonneg hv₀ hL₀),
      add_le_add (le_refl b) (mul_le_mul_of_nonneg_left hL hv₀)⟩
  have hJ : 0≤J := (hJb (le_refl lo)).1
  let K := α/Real.Gamma (1-α)
  let E := ∫ u in Ioi (0:ℝ),(1+u)^(-(1+α))*u^p
  let F := Real.Gamma (1+p-α)*Real.Gamma (1-α)/Real.Gamma (2+p-2*α)
  let C₁ := max 1 (2*W*(J+K*C₀*E)*F)
  have hC₁ : 0<C₁ := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨c,C₁,η,h₀,hc,hC₁,hη,hh₀,?_⟩
  intro Ω m μ _ 𝒢 M V C hP hSecond
  let _ : MeasurableSpace Ω := m
  let v (t : ℝ) := V t.toNNReal
  have hVm (r : ℝ) : Measurable (v r) := ((hP.variance_adapted r.toNNReal).mono (𝒢.le _)).measurable
  have hVn (r : ℝ) (ω : Ω) : 0≤v r ω := hP.variance_nonnegative _ _
  have hVc (ω : Ω) : Continuous (fun r => v r ω) :=
    (hP.variance_continuous ω).comp continuous_real_toNNReal
  have hvTime (r : ℝ) (hr : r∈Icc (0:ℝ) hi) : r.toNNReal≤U :=
    NNReal.coe_le_coe.mp (by simpa only [Real.coe_toNNReal r hr.1] using hr.2.trans hhi.le)
  have hvInt (r : ℝ) (hr : r∈Icc (0:ℝ) hi) : Integrable (v r) μ :=
    hP.variance_integrable _ (hvTime r hr)
  have hvB (r : ℝ) (hr : r∈Icc (0:ℝ) hi) : (∫ ω,v r ω ∂μ)≤B := by
    have hSq := hP.variance_second_integrable _ (hvTime r hr)
    have hi : Integrable (fun _ : Ω => (1:ℝ)) μ := integrable_const _
    have he := integral_mono (hvInt r hr) (hi.add hSq) (fun ω => by
      change v r ω≤1+(v r ω)^2
      nlinarith [sq_nonneg (v r ω-1)])
    have hAdd := integral_add hi hSq
    simp only [Pi.add_apply] at he
    rw [hAdd,integral_const,probReal_univ,one_smul] at he
    exact he.trans (add_le_add (le_refl 1) (hSecond _ (hvTime r hr)))
  have hMeanNorm (t : ℝ) (ht : t∈Icc lo hi) (n : ℕ) :
      (∫ ω,laplaceBoundaryWeight (v t) n ω ∂μ)=Real.exp (-(volterraConvolution (w n) j t)) ∧
      (let f (r : ℝ) := ∫ ω,v r ω ∂laplaceBoundaryTilt μ (v t) n
       ContinuousOn f (Ico (0:ℝ) t) ∧ ∀ s∈Ioo (0:ℝ) t, f s=f 0+
         volterraConvolution (fractionalK α) (fun r => b-(κ+2*a*w n (t-r))*f r) s) := by
    have ht₀ : 0<t := hlo.trans_le ht.1
    have he := heston_boundary_tilt_mean hα hα' hκ ha.le hb hv₀
      (Real.toNNReal_pos.mpr ht₀) (hvTime t ⟨ht₀.le,ht.2⟩) hP
      (by simpa only [Real.coe_toNNReal t ht₀.le] using hw n t) (hwn n)
    simpa only [v,j,Real.coe_toNNReal t ht₀.le] using he
  have hUpper (t : ℝ) (ht : t∈Icc lo hi) (n : ℕ) : volterraConvolution (w n) j t ≤ D :=
    point_riccati_input_convolution_uniform hα hα' hκ ha hlo ht hb hv₀ (hw n t)
  have hAff (t : ℝ) (ht : t∈Icc lo hi) (n : ℕ) :
      Real.exp (-D)≤(∫ ω,laplaceBoundaryWeight (v t) n ω ∂μ) := by
    rw [(hMeanNorm t ht n).1]
    exact Real.exp_le_exp.mpr (neg_le_neg (hUpper t ht n))
  have hBack := hBackAll (Ω := Ω) μ hVm hVn hvInt hvB hw hAff (fun t ht n => (hMeanNorm t ht n).2)
  intro t ht
  have ht₀ : 0<t := hlo.trans_le ht.1
  let Z := {ω | v t ω=0}
  obtain ⟨hCZ,hZ⟩ := laplaceBoundary_atom_of_affine_bound (hVm t) (ae_of_all _ (hVn t))
    (fun n => (hMeanNorm t ht n).1) (hUpper t ht)
  refine ⟨hCZ,?_⟩
  intro h hh
  have h₁ : h≤1 := hh.2.trans (min_le_left _ _)
  have hth : t+h≤(U:ℝ) := by
    linarith [ht.2,hh.2.trans (min_le_right 1 ((U:ℝ)-hi))]
  have hTh : 0<t+h := add_pos ht₀ hh.1
  let H := (t+h).toNNReal
  let S := t.toNNReal
  have hH : H≤U := NNReal.coe_le_coe.mp (by simpa only [H,Real.coe_toNNReal _ hTh.le] using hth)
  have hSH : S<H := NNReal.coe_lt_coe.mp (by
    simpa only [H,S,Real.coe_toNNReal _ hTh.le,Real.coe_toNNReal _ ht₀.le] using lt_add_of_pos_right t hh.1)
  let Q := boundaryConditionedMeasure μ Z
  let : IsProbabilityMeasure Q := boundaryConditionedMeasure_isProbability hZ
  have hZmeas : MeasurableSet[𝒢 S] Z := measurableSet_eq_fun (hP.variance_adapted S).measurable measurable_const
  have hZreal : 0<μ.real Z := hc.trans_le hCZ
  have hQvi (r : ℝ) (hr : r∈Ioc (0:ℝ) t) : Integrable (v r) Q :=
    ((hvInt r ⟨hr.1.le,hr.2.trans ht.2⟩).restrict).smul_measure (ENNReal.inv_ne_top.mpr hZ.ne')
  have hQvb (r : ℝ) (hr : r∈Ioc (0:ℝ) t) : (∫ ω,‖v r ω‖ ∂Q)≤B/c := by
    simp_rw [Real.norm_of_nonneg (hVn r _)]
    rw [integral_boundaryConditionedMeasure]
    have hN := setIntegral_le_integral (s := Z) (hvInt r ⟨hr.1.le,hr.2.trans ht.2⟩) (ae_of_all _ (hVn r))
    exact (div_le_div_of_nonneg_right (hN.trans (hvB r ⟨hr.1.le,hr.2.trans ht.2⟩)) hZreal.le).trans
      (div_le_div_of_nonneg_left hB hc hCZ)
  let Ψ (n : ℕ) (ω : Ω) := affineFuturePayoff α (w n) j (fun r => v r ω) (t+h) t
  have hΨ (n : ℕ) : Integrable (Ψ n) Q ∧ (∫ ω,Ψ n ω ∂Q)≤C₁*h^η := by
    have hwp (r : ℝ) (hr : r∈Ioo (0:ℝ) h) : 0≤w n r ∧ w n r≤W*r^(-α) := by
      refine ⟨hwn n r hr.1,?_⟩
      let u := hw n (t+h)
      have hrT : r∈Ioc (0:ℝ) (t+h) := ⟨hr.1,by linarith [hr.2]⟩
      have hC := point_charge_riccati_lt_singular_profile hα hα' hκ ha hTh
        u.measurable u.contDiffAt_pos u.volterra u.asymptotic r hrT
      rw [singularRiccatiProfile,ite_eq_left hr.1] at hC
      exact hC.le
    obtain ⟨hi,he⟩ := affine_future_payoff_mean_bound hα₀ hα' hp₀ hp.2 hη ht₀.le hh.1 h₁
      hC₀.le hJ hW.le hVm hVc hVn hQvi hQvb (hBack t ht) hjm
      (fun y hy => hJb (by linarith [ht.1,hy.1])) (hw n (t+h)).measurable hwp
    refine ⟨hi,he.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hh.1.le _)
  have hA (n : ℕ) : μ[laplaceBoundaryWeight (V H) n | 𝒢 S] =ᵐ[μ] fun ω => Real.exp (-Ψ n ω) := by
    have hh' := heston_boundary_conditional_point_test hα hα' ha.le hb hv₀ hH hSH hP
      (by simpa only [H,Real.coe_toNNReal _ hTh.le] using hw n (t+h)) (hwn n)
    have hLap : laplaceBoundaryWeight (V H) n = fun ω => Real.exp (-((n:ℝ)*V H ω)) := by
      funext ω
      simp only [laplaceBoundaryWeight,neg_mul]
    rw [hLap]
    simpa only [Ψ,v,j,H,S,Real.coe_toNNReal _ ht₀.le,
      Real.coe_toNNReal _ hTh.le] using hh'
  have hΨi (n : ℕ) : Integrable (Ψ n) (μ.restrict Z) :=
    (integrable_smul_measure (ENNReal.inv_ne_zero.mpr (measure_ne_top μ Z))
      (ENNReal.inv_ne_top.mpr hZ.ne')).mp (hΨ n).1
  have hΨb (n : ℕ) : (∫ ω in Z,Ψ n ω ∂μ) ≤ (C₁*h^η)*μ.real Z := by
    have hh' := (hΨ n).2
    change (∫ ω,Ψ n ω ∂boundaryConditionedMeasure μ Z)≤_ at hh'
    rw [integral_boundaryConditionedMeasure] at hh'
    exact (div_le_iff₀ hZreal).mp hh'
  exact boundaryConditionalPositive_le_of_affine_bound (𝒢.le S) hZmeas hZ (hVm (t+h))
    (ae_of_all _ (hVn (t+h))) hA hΨi hΨb

#print axioms uniform_cluster_postpulse_mass_tail_over_sample_spaces
#print axioms uniform_cluster_earlypulse_mass_tail_over_sample_spaces
#print axioms uniform_focal_envelope_of_block_estimates_over_sample_spaces
#print axioms uniform_actual_fractional_pulse_mass_tails_over_sample_spaces
#print axioms uniform_actual_pulse_envelope_over_sample_spaces
#print axioms uniform_actual_pulse_stopped_separation_over_sample_spaces
#print axioms uniform_actual_pulse_separation_of_resolvent_mean_over_sample_spaces
#print axioms uniform_affine_boundary_backward_mean_over_sample_spaces
#print axioms uniform_heston_zero_boundary_over_laws_over_sample_spaces

end RoughHeston
