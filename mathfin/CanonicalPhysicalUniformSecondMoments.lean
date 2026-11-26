import FractionalCoupledFixedMeshLimit
import FractionalSmoothVarianceIncrementRate
import PhysicalCovarianceDensityBound

/-! Uniform timewise second moments of observable canonical martingales
and their compensated products. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston

open MathFin.ItoIntegralCLM

set_option maxHeartbeats 1500000

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
local notation "J" => CoupledPhysicalState ι
local notation "Ω" => CanonicalPath T J

private theorem real_memLp_two_and_integral_sq_of_bound {μ : Measure Ω} {X : Ω → ℝ}
    (hX : Measurable X) {D : ℝ≥0∞} (hD : D ≠ ⊤)
    (h : (∫⁻ p, ‖X p‖ₑ^2 ∂μ) ≤ D) :
    MemLp X 2 μ ∧ (∫ p, (X p)^2 ∂μ) ≤ D.toReal := by
  have hh : (∫⁻ p, ENNReal.ofReal (‖X p‖^2) ∂μ) ≤ ENNReal.ofReal D.toReal := by
    simpa only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.ofReal_toReal hD] using h
  have hm := memLp_and_integral_norm_pow_of_lintegral (p := 2) (by decide) hX ENNReal.toReal_nonneg hh
  simpa only [Nat.cast_ofNat, sq_abs, Real.norm_eq_abs] using hm

private theorem enorm_sq_le_one_add_fourth (a : ℝ) : ‖a‖ₑ^2 ≤ 1+‖a‖ₑ^4 := by
  have h : ‖a‖^2 ≤ 1+‖a‖^4 := by nlinarith [sq_nonneg (‖a‖^2-1/2)]
  have hh := ENNReal.ofReal_le_ofReal h
  rwa [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
    ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] at hh

private theorem enorm_sq_mul_le_fourth (a b : ℝ) : ‖a*b‖ₑ^2 ≤ ‖a‖ₑ^4+‖b‖ₑ^4 := by
  have h : ‖a*b‖^2 ≤ ‖a‖^4+‖b‖^4 := by
    rw [norm_mul]
    nlinarith [sq_nonneg (‖a‖^2-‖b‖^2), sq_nonneg (‖a‖*‖b‖)]
  have hh := ENNReal.ofReal_le_ofReal h
  rwa [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
    ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ofReal_norm,
    ofReal_norm] at hh

theorem canonicalPhysical_compensator_second_bound
    (P : ProbabilityMeasure Ω) (σ : ℝ) (i j : Option ι) (t : ℝ≥0)
    {CV : ℝ≥0∞}
    (hV : ∀ k u, u ≤ T →
      (∫⁻ p, ENNReal.ofReal (max (canonicalPhysicalVariance T k u p) 0)^2 ∂(P : Measure Ω)) ≤ CV) :
    (∫⁻ p, ‖canonicalPhysicalCompensator T σ i j t p‖ₑ^2 ∂(P : Measure Ω)) ≤
      ENNReal.ofReal (T:ℝ)^2*(ENNReal.ofReal (σ^2/2)^2*(2:ℝ≥0∞)^2*(CV+CV)) := by
  let μ := (P : Measure Ω)
  let ν := timeMeasureHorizon (min t T)
  let F := fun r (p : Ω) => physicalCouplingDensity σ i j (canonicalPathEval T r p).1
  have hFcont (p : Ω) : Continuous (fun r => F r p) :=
    ((continuous_physicalCouplingDensity σ i j).comp continuous_fst).comp
      (p.continuous.comp ((continuous_id.min continuous_const).subtype_mk _))
  have hFmeas (r : ℝ≥0) : Measurable (F r) :=
    (((continuous_physicalCouplingDensity σ i j).comp continuous_fst).comp
      (continuous_canonicalPathEval T r)).measurable
  have hFM : Measurable (Function.uncurry F) :=
    measurable_uncurry_of_continuous_of_measurable hFcont hFmeas
  have hFI : ∀ᵐ p ∂μ, Integrable (fun r => (1:ℝ)*F r p) ν := by
    apply Eventually.of_forall
    intro p
    simp only [one_mul, ν, timeMeasureHorizon]
    exact ((hFcont p).continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hP : ∀ᵐ r ∂ν, (∫⁻ p, ‖F r p‖ₑ^2 ∂μ) ≤
      ENNReal.ofReal (σ^2/2)^2*(2:ℝ≥0∞)^2*(CV+CV) := by
    have hr : ∀ᵐ r ∂ν, r ∈ Ioc 0 (min t T) := ae_restrict_mem measurableSet_Ioc
    filter_upwards [hr] with r hr
    let X := fun p => max (canonicalPhysicalVariance T i r p) 0
    let Y := fun p => max (canonicalPhysicalVariance T j r p) 0
    have hVc : Continuous (canonicalPhysicalVariance T i r) :=
      ((continuous_apply i).comp continuous_fst).comp (continuous_canonicalPathEval T r)
    have hX : Measurable X := hVc.measurable.max measurable_const
    have hCert (p : Ω) : ‖F r p‖ₑ^2 ≤
        ENNReal.ofReal (σ^2/2)^2*((2:ℝ≥0∞)^2*(ENNReal.ofReal (X p)^2+ENNReal.ofReal (Y p)^2)) := by
      rw [← ofReal_norm]
      have hf := norm_physicalCouplingDensity_le σ i j (canonicalPathEval T r p).1
      change ‖F r p‖ ≤ (σ^2/2)*(X p+Y p) at hf
      refine (pow_le_pow_left' (ENNReal.ofReal_le_ofReal hf) 2).trans ?_
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ σ^2/2), mul_pow]
      apply mul_right_mono
      have hX₀ : 0 ≤ X p := le_max_right _ _
      have hY₀ : 0 ≤ Y p := le_max_right _ _
      simpa only [← ofReal_norm, Real.norm_of_nonneg hX₀, Real.norm_of_nonneg hY₀,
        Real.norm_of_nonneg (add_nonneg hX₀ hY₀)] using
        (enorm_add_pow_le (a := X p) (b := Y p) 2)
    have hh := lintegral_mono (μ := μ) hCert
    simp_rw [← mul_assoc] at hh
    rw [lintegral_const_mul' _ _ (by finiteness),
      lintegral_add_left ((hX.ennreal_ofReal).pow_const _)] at hh
    exact hh.trans (mul_right_mono (add_le_add (hV i r (hr.2.trans (min_le_right _ _)))
      (hV j r (hr.2.trans (min_le_right _ _)))))
  have h := lintegral_weighted_drift_power_le (μ := μ) (ν := ν) (w := fun _ => 1)
    measurable_const (integrable_const _) hFM hFI 2 (by decide) hP
  simp only [one_mul, norm_one, integral_const, smul_eq_mul, mul_one] at h
  change (∫⁻ p, ‖∫ r, F r p ∂ν‖ₑ^2 ∂μ) ≤ _
  rw [euler_timeMeasureHorizon_mass] at h
  exact h.trans (mul_left_mono (pow_le_pow_left'
    (ENNReal.ofReal_le_ofReal (NNReal.coe_le_coe.mpr (min_le_right t T))) 2))

/-- Second moments needed to pass the joint compensated-product identities
follow from uniform variance second moments and residual fourth moments. -/
theorem uniformPhysicalSecondMoment_of_row_powers
    (Pn : ℕ → ProbabilityMeasure Ω) (σ : ℝ) {CV CM : ℝ≥0∞}
    (hCV : CV ≠ ⊤) (hCM : CM ≠ ⊤)
    (hV : ∀ n i u, u ≤ T →
      (∫⁻ p, ENNReal.ofReal (max (canonicalPhysicalVariance T i u p) 0)^2 ∂(Pn n : Measure Ω)) ≤ CV)
    (hM : ∀ n i t,
      (∫⁻ p, ‖canonicalPhysicalResidual T i t p‖ₑ^4 ∂(Pn n : Measure Ω)) ≤ CM) :
    (∀ i, uniformPhysicalSecondMoment Pn (canonicalPhysicalResidual T i)) ∧
    (∀ i j, uniformPhysicalSecondMoment Pn (canonicalPhysicalCompensatedProduct T σ i j)) := by
  constructor
  · intro i t
    let D := 1+CM
    refine ⟨D.toReal, fun n => ?_⟩
    have h := lintegral_mono (μ := (Pn n : Measure Ω))
      (fun p => enorm_sq_le_one_add_fourth (canonicalPhysicalResidual T i t p))
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one] at h
    exact real_memLp_two_and_integral_sq_of_bound
      (continuous_canonicalPhysicalResidual T i t).measurable (by dsimp [D]; finiteness)
      (h.trans (add_le_add_right (hM n i t) 1))
  · intro i j t
    let CA := ENNReal.ofReal (T:ℝ)^2*(ENNReal.ofReal (σ^2/2)^2*(2:ℝ≥0∞)^2*(CV+CV))
    let D := (2:ℝ≥0∞)^2*(CM+CM+CA)
    refine ⟨D.toReal, fun n => ?_⟩
    let X := fun p => canonicalPhysicalResidual T i t p*canonicalPhysicalResidual T j t p
    let Y := fun p => -canonicalPhysicalCompensator T σ i j t p
    have hi := (continuous_canonicalPhysicalResidual T i t).measurable
    have hj := (continuous_canonicalPhysicalResidual T j t).measurable
    have hX (p : Ω) : ‖X p‖ₑ^2 ≤
        ‖canonicalPhysicalResidual T i t p‖ₑ^4+‖canonicalPhysicalResidual T j t p‖ₑ^4 :=
      enorm_sq_mul_le_fourth _ _
    have hx := lintegral_mono (μ := (Pn n : Measure Ω)) hX
    rw [lintegral_add_left (hi.enorm.pow_const _)] at hx
    have hx' := hx.trans (add_le_add (hM n i t) (hM n j t))
    have hy : (∫⁻ p, ‖Y p‖ₑ^2 ∂(Pn n : Measure Ω)) ≤ CA := by
      simpa only [Y, enorm_neg] using canonicalPhysical_compensator_second_bound (Pn n) σ i j t (hV n)
    apply real_memLp_two_and_integral_sq_of_bound
      (continuous_canonicalPhysicalCompensatedProduct T σ i j t).measurable (by dsimp [D, CA]; finiteness)
    exact (lintegral_enorm_add_pow_le (X := X) (Y := Y) (hi.mul hj) 2).trans
      (mul_right_mono (add_le_add hx' hy))

#print axioms RoughHeston.canonicalPhysical_compensator_second_bound
#print axioms RoughHeston.uniformPhysicalSecondMoment_of_row_powers

end RoughHeston
