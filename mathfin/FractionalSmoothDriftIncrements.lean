import FractionalSmoothNoiseIncrements
import WeightedDriftPowerMoment
import FractionalSmoothUniformVariancePowers

/-! Uniform moments of the deterministic drift increments in the
actual smooth fractional variance approximations. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

set_option maxHeartbeats 1300000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {T : ℝ≥0} {α κ σ : ℝ} {n : ℕ} {v : Option ι → ℝ} {β : Option ι → ℝ≥0 → ℝ}

namespace FractionalCoupledSmoothLaw

noncomputable def driftInput (L : FractionalCoupledSmoothLaw T α n κ σ v β) (i : Option ι)
    (r : ℝ) (p : CanonicalPath T (FractionalCoupledSmoothState ι n)) : ℝ :=
  β i r.toNNReal - κ*L.variance i r.toNNReal p

noncomputable def driftConvolution (L : FractionalCoupledSmoothLaw T α n κ σ v β) (i : Option ι)
    (t : ℝ≥0) (p : CanonicalPath T (FractionalCoupledSmoothState ι n)) : ℝ :=
  ∫ r in (0:ℝ)..(t:ℝ), fractionalExponentialApproximation α n ((t:ℝ)-r)*L.driftInput i r p

theorem measurable_driftInput (L : FractionalCoupledSmoothLaw T α n κ σ v β) (i : Option ι)
    {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B) :
    Measurable (Function.uncurry (L.driftInput i)) := by
  have hβr : Measurable (fun r : ℝ => β i r.toNNReal) := (hβ i).comp continuous_real_toNNReal.measurable
  have hc (p : CanonicalPath T (FractionalCoupledSmoothState ι n)) :
      Continuous (fun r : ℝ => L.variance i r.toNNReal p) :=
    (L.variance_continuous_time i hB hβ hβB p).comp continuous_real_toNNReal
  have hm (r : ℝ) : Measurable (L.variance i r.toNNReal) := by
    have h : StronglyMeasurable[canonicalPathNaturalFiltration T r.toNNReal] (L.variance i r.toNNReal) :=
      L.variance_stronglyAdapted i r.toNNReal
    exact h.measurable.mono ((canonicalPathNaturalFiltration (E := FractionalCoupledSmoothState ι n) T).le _) le_rfl
  exact (hβr.comp measurable_fst).sub
    (measurable_const.mul (measurable_uncurry_of_continuous_of_measurable hc hm))

theorem driftInput_intervalIntegrable (L : FractionalCoupledSmoothLaw T α n κ σ v β) (i : Option ι)
    {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B)
    (p : CanonicalPath T (FractionalCoupledSmoothState ι n)) (a b : ℝ) :
    IntervalIntegrable (fun r => L.driftInput i r p) volume a b := by
  have hβi : IntervalIntegrable (fun r : ℝ => β i r.toNNReal) volume a b := by
    rw [intervalIntegrable_iff]
    have hconst : IntervalIntegrable (fun _ : ℝ => B) volume a b := intervalIntegrable_const
    rw [intervalIntegrable_iff] at hconst
    exact hconst.mono' ((hβ i).comp continuous_real_toNNReal.measurable).stronglyMeasurable.aestronglyMeasurable
      (Eventually.of_forall fun r => hβB i r.toNNReal)
  exact hβi.sub (((L.variance_continuous_time i hB hβ hβB p).comp
    continuous_real_toNNReal).intervalIntegrable a b |>.const_mul κ)

/-- The drift increment estimate for any available uniform power
bound on the input. -/
theorem driftConvolution_increment_moment_le
    (L : FractionalCoupledSmoothLaw T α n κ σ v β)
    (hα : 0 < α) (hα' : α < 1) (i : Option ι)
    {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B)
    {s t : ℝ≥0} (hst : s ≤ t) (ht : t ≤ T) (p : ℕ) (hp : 1 ≤ p) {C : ℝ≥0∞}
    (hF : ∀ r ∈ Icc (0:ℝ) (T:ℝ), (∫⁻ q, ‖L.driftInput i r q‖ₑ^p ∂(L.law : Measure _)) ≤ C) :
    let e := (2/(Real.Gamma α*α))*((t:ℝ)-(s:ℝ))^α
    (∫⁻ q, ‖L.driftConvolution i t q-L.driftConvolution i s q‖ₑ^p ∂(L.law : Measure _)) ≤
      (2:ℝ≥0∞)^p*(ENNReal.ofReal e^p*C+ENNReal.ofReal e^p*C) := by
  dsimp only
  let Ω := CanonicalPath T (FractionalCoupledSmoothState ι n)
  let μ : Measure Ω := L.law
  let K := fractionalExponentialApproximation α n
  let f (r : ℝ) := K ((t:ℝ)-r)-K ((s:ℝ)-r)
  let g (r : ℝ) := K ((t:ℝ)-r)
  let F := L.driftInput i
  let e := (2/(Real.Gamma α*α))*((t:ℝ)-(s:ℝ))^α
  let ν₀ := volume.restrict (Ioc (0:ℝ) (s:ℝ))
  let ν₁ := volume.restrict (Ioc (s:ℝ) (t:ℝ))
  let D₀ (q : Ω) := ∫ r, f r*F r q ∂ν₀
  let D₁ (q : Ω) := ∫ r, g r*F r q ∂ν₁
  have hTm : (t:ℝ) ≤ T := NNReal.coe_le_coe.mpr ht
  have hst' : (s:ℝ) ≤ t := NNReal.coe_le_coe.mpr hst
  have hK := (fractionalExponentialApproximation_properties hα hα' n).1
  have hg : Continuous g := hK.comp (continuous_const.sub continuous_id)
  have hsK : Continuous (fun r : ℝ => K ((s:ℝ)-r)) := hK.comp (continuous_const.sub continuous_id)
  have hf : Continuous f := hg.sub hsK
  have hFi (q : Ω) (a b : ℝ) := L.driftInput_intervalIntegrable i hB hβ hβB q a b
  have hFm : Measurable (Function.uncurry F) := L.measurable_driftInput i hB hβ hβB
  have hν₀ : ∀ᵐ r ∂ν₀, (∫⁻ q, ‖F r q‖ₑ^p ∂μ) ≤ C :=
    (ae_restrict_mem measurableSet_Ioc).mono fun r hr => hF r ⟨hr.1.le, hr.2.trans (hst'.trans hTm)⟩
  have hν₁ : ∀ᵐ r ∂ν₁, (∫⁻ q, ‖F r q‖ₑ^p ∂μ) ≤ C :=
    (ae_restrict_mem measurableSet_Ioc).mono fun r hr =>
      hF r ⟨s.coe_nonneg.trans hr.1.le, hr.2.trans hTm⟩
  have hD₀ := lintegral_weighted_drift_power_le (μ := μ) (ν := ν₀) hf.measurable
    (hf.intervalIntegrable (μ := volume) 0 s).1 hFm
    (Eventually.of_forall fun q => ((hFi q 0 s).continuousOn_mul hf.continuousOn).1) p hp hν₀
  have hD₁ := lintegral_weighted_drift_power_le (μ := μ) (ν := ν₁) hg.measurable
    (hg.intervalIntegrable (μ := volume) s t).1 hFm
    (Eventually.of_forall fun q => ((hFi q s t).continuousOn_mul hg.continuousOn).1) p hp hν₁
  have hSum :=
    fractionalSmooth_increment_mass_le hα hα' s.coe_nonneg hst' n
  have hSum' : (∫ r, ‖f r‖ ∂ν₀) + (∫ r, ‖g r‖ ∂ν₁) ≤ e := by
    simpa only [ν₀, ν₁, f, g, K, e, Real.norm_eq_abs, intervalIntegral.integral_of_le s.coe_nonneg,
      intervalIntegral.integral_of_le hst'] using hSum
  have h0 : (∫ r, ‖f r‖ ∂ν₀) ≤ e :=
    (le_add_of_nonneg_right (integral_nonneg fun _ => norm_nonneg _)).trans hSum'
  have h1 : (∫ r, ‖g r‖ ∂ν₁) ≤ e :=
    (le_add_of_nonneg_left (integral_nonneg fun _ => norm_nonneg _)).trans hSum'
  have hD₀' : (∫⁻ q, ‖D₀ q‖ₑ^p ∂μ) ≤ ENNReal.ofReal e^p*C := by
    apply hD₀.trans
    gcongr
  have hD₁' : (∫⁻ q, ‖D₁ q‖ₑ^p ∂μ) ≤ ENNReal.ofReal e^p*C := by
    apply hD₁.trans
    gcongr
  have hEq (q : Ω) : L.driftConvolution i t q-L.driftConvolution i s q = D₀ q+D₁ q := by
    have he := intervalIntegral.integral_add_adjacent_intervals
      ((hFi q 0 s).continuousOn_mul hg.continuousOn) ((hFi q s t).continuousOn_mul hg.continuousOn)
    change L.driftConvolution i t q-L.driftConvolution i s q = D₀ q+D₁ q
    have he' :
        (∫ r in (0:ℝ)..(s:ℝ), f r*F r q) =
          (∫ r in (0:ℝ)..(s:ℝ), g r*F r q) -
            ∫ r in (0:ℝ)..(s:ℝ), K ((s:ℝ)-r)*F r q := by
      simp only [f, sub_mul]
      exact intervalIntegral.integral_sub ((hFi q 0 s).continuousOn_mul hg.continuousOn)
        ((hFi q 0 s).continuousOn_mul hsK.continuousOn)
    unfold D₀ D₁ driftConvolution
    rw [← intervalIntegral.integral_of_le s.coe_nonneg, ← intervalIntegral.integral_of_le hst',
      he', ← he]
    ring
  have hD₀m : Measurable D₀ := by
    have h : StronglyMeasurable (fun z : ℝ × Ω => f z.1*F z.1 z.2) :=
      ((hf.measurable.comp measurable_fst).mul hFm).stronglyMeasurable
    exact (h.integral_prod_left' (μ := ν₀)).measurable
  have hi : (∫⁻ q, ‖L.driftConvolution i t q-L.driftConvolution i s q‖ₑ^p ∂μ) ≤
      ∫⁻ q, (2:ℝ≥0∞)^p*(‖D₀ q‖ₑ^p+‖D₁ q‖ₑ^p) ∂μ :=
    lintegral_mono fun q => hEq q ▸ enorm_add_pow_le p
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofNat_ne_top),
    lintegral_add_left ((hD₀m.enorm).pow_const p)] at hi
  apply hi.trans
  gcongr

end FractionalCoupledSmoothLaw

#print axioms RoughHeston.FractionalCoupledSmoothLaw.driftConvolution_increment_moment_le

end RoughHeston
