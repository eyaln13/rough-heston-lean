import ClusterSensitivityDecay
import ClusterLaplaceDerivative
import ClusterMassLowerTail

open MeasureTheory Set Filter
open scoped Topology

namespace RoughHeston

private theorem integrable_continuous_age_test
    {Ξ : Type*} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsFiniteMeasure ν]
    {age : Ξ → ℝ} {T : ℝ} {f : ℝ → ℝ} (hf : Continuous f) (ha : Measurable age)
    (haT : ∀ᵐ v ∂ν, age v ∈ Icc 0 T) :
    Integrable (fun v => f (age v)) ν := by
  obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image (K := Icc (0 : ℝ) T) hf.norm.continuousOn
  refine (integrable_const B).mono' (hf.measurable.comp ha).aestronglyMeasurable ?_
  filter_upwards [haT] with v hv
  exact hB ⟨age v,hv,rfl⟩

/-- The post-pulse affine transform gives the cluster's size-biased
Laplace bound and its lower-tail bound at exponent one half. The
deterministic age measure has total initial mass and support in the
last half of the observation interval. -/
theorem cluster_postpulse_sizeBiased_lower_tail_of_affine_transform
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ν : Measure Ξ} [IsFiniteMeasure ν]
    {J Z : Ω → ℝ} {age : Ξ → ℝ} {α κ a H s ε : ℝ}
    (hα : 1/2 < α) (hα' : α < 1) (hκ : 0 ≤ κ) (ha : 0 < a)
    (hs : 0 < s) (hsH : s ≤ H) (hε : 0 < ε)
    (hJ : Measurable J) (hZ : Measurable Z) (hJ₀ : ∀ᵐ ω ∂μ, 0 ≤ J ω)
    (hZ₀ : ∀ᵐ ω ∂μ, 0 ≤ Z ω) (hZi : Integrable Z μ) (hZmean : (∫ ω,Z ω ∂μ) = ε)
    (hage : Measurable age) (hageSupport : ∀ᵐ v ∂ν, age v ∈ Icc (s/2) s)
    (hmass : ν.real univ = ε)
    (htransform : ∀ q > 0, ∀ l ∈ Icc (0 : ℝ) 1, ∀ w : ℝ → ℝ, Continuous w →
      (∀ t ∈ Icc 0 s, w t = l+
        volterraConvolution (fractionalK α) (fun u => q+κ*l-κ*w u-a*(w u)^2) t) →
      (∫ ω, Real.exp (-q*J ω-l*Z ω) ∂μ) = Real.exp (-(∫ v, w (age v) ∂ν))) :
    ∃ A C : ℝ, 0 < A ∧ 0 < C ∧
      (∀ q ≥ A/s^(2*α),
        (∫ ω, Real.exp (-q*J ω) ∂sizeBiasedLaw μ Z ε) ≤ C/(Real.sqrt q*s^α)) ∧
      ∀ x, 0 < x → x ≤ 1 →
        (sizeBiasedLaw μ Z ε).real {ω | J ω ≤ x*s^(2*α)} ≤
          (Real.exp A*C/Real.sqrt A)*Real.sqrt x := by
  have hα₀ : 0 < α := by linarith
  have hH := hs.trans_le hsH
  let A := max (H^(2*α)) ((2:ℝ)^(2*α))
  have hA : 0 < A := (Real.rpow_pos_of_pos hH _).trans_le (le_max_left _ _)
  obtain ⟨D,hD,hDec⟩ := exists_cluster_riccati_sensitivity_decay hα hα' hκ ha hH
  let C := D*(2:ℝ)^α
  have hC : 0 < C := mul_pos hD (by positivity)
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
  refine ⟨A,C,hA,hC,hLap,?_⟩
  intro x hx hx₁
  let Q := sizeBiasedLaw μ Z ε
  let hQ : IsProbabilityMeasure Q := sizeBiasedLaw_isProbabilityMeasure hε hZi hZ₀ hZmean
  have hJQ : ∀ᵐ ω ∂Q, 0 ≤ J ω :=
    (withDensity_absolutelyContinuous μ _).ae_le hJ₀
  exact cluster_mass_lower_tail_of_laplace hJ hJQ hA hs hx hx₁ hLap

#print axioms cluster_postpulse_sizeBiased_lower_tail_of_affine_transform

end RoughHeston
