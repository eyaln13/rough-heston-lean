import ClusterSizeBiasedLowerTail

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace RoughHeston

/-- At an early pulse age only a positive fraction of the deterministic
input must lie in the second-half age set. A second-moment bound for
the size-bias density then yields exponential large-charge decay. -/
theorem cluster_earlypulse_sizeBiased_lower_tail_of_affine_transform
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ν : Measure Ξ} [IsFiniteMeasure ν]
    {J Z : Ω → ℝ} {age : Ξ → ℝ} {α κ a H s ε C₀ η : ℝ}
    (hα : 1/2 < α) (hα' : α < 1) (hκ : 0 ≤ κ) (ha : 0 < a)
    (hs : 0 < s) (hsH : s ≤ H) (hε : 0 < ε) (hC₀ : 0 < C₀) (hη : 0 < η)
    (hJ : Measurable J) (hZ : Measurable Z) (hJ₀ : ∀ᵐ ω ∂μ, 0 ≤ J ω)
    (hZ₀ : ∀ᵐ ω ∂μ, 0 ≤ Z ω) (hZi : Integrable Z μ) (hZmean : (∫ ω,Z ω ∂μ) = ε)
    (hZL2 : MemLp Z 2 μ) (hZ2 : (∫ ω,(Z ω)^2 ∂μ) ≤ C₀*ε^2)
    (hage : Measurable age) (hageSupport : ∀ᵐ v ∂ν, age v ∈ Icc 0 s)
    (hMass : η*s^α ≤ ν.real {v | s/2 ≤ age v})
    (htransform : ∀ q > 0, ∀ w : ℝ → ℝ, Continuous w →
      (∀ t ∈ Icc 0 s, w t =
        volterraConvolution (fractionalK α) (fun u => q+(-κ)*w u+(-a)*(w u)^2) t) →
      (∫ ω, Real.exp (-q*J ω) ∂μ) = Real.exp (-(∫ v, w (age v) ∂ν))) :
    ∃ A ρ : ℝ, 0 < A ∧ 0 < ρ ∧
      (∀ q ≥ A/s^(2*α), (∫ ω, Real.exp (-q*J ω) ∂sizeBiasedLaw μ Z ε) ≤
        Real.sqrt C₀ * Real.exp (-(ρ*Real.sqrt q*s^α))) ∧
      ∀ x, 0 < x → x ≤ 1 →
        (sizeBiasedLaw μ Z ε).real {ω | J ω ≤ x*s^(2*α)} ≤
          (Real.exp A*(Real.sqrt C₀/ρ)/Real.sqrt A)*Real.sqrt x := by
  have hα₀ : 0 < α := by linarith
  have hH := hs.trans_le hsH
  let A := max (H^(2*α)) ((2:ℝ)^(2*α))
  have hA : 0 < A := (Real.rpow_pos_of_pos hH _).trans_le (le_max_left _ _)
  obtain ⟨c,hc,hLower⟩ := exists_cluster_riccati_lower_constant hα hα' hκ ha.le
  let ρ := c*η/2
  have hρ : 0 < ρ := half_pos (mul_pos hc hη)
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
  refine ⟨A,ρ,hA,hρ,hLap,?_⟩
  intro x hx hx₁
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

#print axioms cluster_earlypulse_sizeBiased_lower_tail_of_affine_transform

end RoughHeston
