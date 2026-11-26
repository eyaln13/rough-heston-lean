import CanonicalApproximationProof
import FractionalSmoothVarianceIncrementRate
import WeightedDriftPowerMoment

/-! Fourth moments of the variance coordinates suffice for all five
uniform second-moment requirements in the canonical mesh limit. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

set_option maxHeartbeats 1600000

variable {T : ℝ≥0}
local notation "Ω" => CanonicalPath T (ℝ × ℝ)

private theorem integrable_weighted_pairPath_period {u : ℝ} {k : ℝ → ℝ}
    (hk : IntegrableOn k (Ioc 0 u)) (f : C(ℝ × ℝ, ℝ)) (p : Ω) :
    IntegrableOn (fun s => k s*f (p (realTimeOnHorizon T s))) (Ioc 0 u) := by
  obtain ⟨A,hA⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f.continuous.comp (p.continuous.comp (realTimeOnHorizon T).continuous)).continuousOn
      (s := Icc (0:ℝ) u)
  have hM : Continuous (fun s => f (p (realTimeOnHorizon T s))) :=
    f.continuous.comp (p.continuous.comp (realTimeOnHorizon T).continuous)
  refine (hk.norm.mul_const A).mono' (hk.aestronglyMeasurable.mul hM.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hA s (Ioc_subset_Icc_self hs)) (norm_nonneg _)

private theorem canonicalPairPath_weighted_moment_bound
    (Pn : ℕ → ProbabilityMeasure Ω) (n : ℕ)
    (f : C(ℝ × ℝ, ℝ)) {k : ℝ → ℝ} (hkm : Measurable k)
    {u : ℝ} (hu : u ≤ T) (hki : IntegrableOn k (Ioc 0 u)) (q : ℕ) (hq : 1 ≤ q) {C : ℝ≥0∞}
    (hMom : ∀ t ≤ T, (∫⁻ p, ‖f (canonicalPathEval T t p)‖ₑ^q ∂(Pn n : Measure Ω)) ≤ C) :
    (∫⁻ p, ‖∫ r in Ioc (0:ℝ) u, k r*f (p (realTimeOnHorizon T r))‖ₑ^q ∂(Pn n : Measure Ω)) ≤
      ENNReal.ofReal (∫ r in Ioc (0:ℝ) u, ‖k r‖)^q*C := by
  let F := fun r (p : Ω) => f (p (realTimeOnHorizon T r))
  have hFc (p : Ω) : Continuous (fun r : ℝ => F r p) :=
    f.continuous.comp (p.continuous.comp (realTimeOnHorizon T).continuous)
  have hFm (r : ℝ) : Measurable (F r) := (f.continuous.comp (continuous_eval_const _)).measurable
  have hF : Measurable (Function.uncurry F) := measurable_uncurry_of_continuous_of_measurable hFc hFm
  have hFI : ∀ᵐ p ∂(Pn n : Measure Ω), IntegrableOn (fun r => k r*F r p) (Ioc 0 u) :=
    Eventually.of_forall fun p => integrable_weighted_pairPath_period hki f p
  have hMoment : ∀ᵐ r ∂volume.restrict (Ioc 0 u),
      (∫⁻ p, ‖F r p‖ₑ^q ∂(Pn n : Measure Ω)) ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have ht : r.toNNReal ≤ T := NNReal.coe_le_coe.mp ((Real.coe_toNNReal r hr.1.le).trans_le (hr.2.trans hu))
    exact hMom r.toNNReal ht
  exact lintegral_weighted_drift_power_le hkm hki hF hFI q hq hMoment

private theorem real_memLp_two_and_sq_le {μ : Measure Ω} {X : Ω → ℝ}
    (hX : Measurable X) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (h : (∫⁻ p, ‖X p‖ₑ^2 ∂μ) ≤ C) :
    MemLp X 2 μ ∧ (∫ p, (X p)^2 ∂μ) ≤ C.toReal := by
  have hh : (∫⁻ p, ENNReal.ofReal (‖X p‖^2) ∂μ) ≤ ENNReal.ofReal C.toReal := by
    simpa only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.ofReal_toReal hC] using h
  have hm := memLp_and_integral_norm_pow_of_lintegral (p := 2) (by decide) hX ENNReal.toReal_nonneg hh
  simpa only [Nat.cast_ofNat, sq_abs, Real.norm_eq_abs] using hm

private theorem enorm_sq_le_one_plus_fourth (x : ℝ) : ‖x‖ₑ^2 ≤ 1+‖x‖ₑ^4 := by
  have h : ‖x‖^2 ≤ 1+‖x‖^4 := by nlinarith [sq_nonneg (‖x‖^2-1/2)]
  have hh := ENNReal.ofReal_le_ofReal h
  rwa [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
    ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] at hh

private theorem enorm_sq_product_le_fourth_sum (x y : ℝ) : ‖x*y‖ₑ^2 ≤ ‖x‖ₑ^4+‖y‖ₑ^4 := by
  have h : ‖x*y‖^2 ≤ ‖x‖^4+‖y‖^4 := by
    rw [norm_mul]
    nlinarith [sq_nonneg (‖x‖^2-‖y‖^2), sq_nonneg (‖x‖*‖y‖)]
  have hh := ENNReal.ofReal_le_ofReal h
  rwa [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
    ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ofReal_norm,
    ofReal_norm] at hh

theorem canonicalVarianceMartingale_fourth_bound
    {α v₀ κ θ : ℝ} (hα' : α < 1) (Pn : ℕ → ProbabilityMeasure Ω) (f : C(ℝ × ℝ, ℝ))
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hMom : ∀ n t, t ≤ T → (∫⁻ p, ‖f (canonicalPathEval T t p)‖ₑ^4 ∂(Pn n : Measure Ω)) ≤ C)
    (t : ℝ≥0) : ∃ A : ℝ≥0∞, A ≠ ⊤ ∧ ∀ n,
      (∫⁻ p, ‖canonicalVarianceMartingale T α v₀ κ θ f t p‖ₑ^4 ∂(Pn n : Measure Ω)) ≤ A := by
  let u := min t T
  let k (r : ℝ) := fractionalL α ((u:ℝ)-r)+κ
  let K (r : ℝ) := fractionalL α ((u:ℝ)-r)
  let d := -v₀*(∫ r in Ioc (0:ℝ) (u:ℝ), K r)-κ*θ*(u:ℝ)
  let A := (2:ℝ≥0∞)^4*(‖d‖ₑ^4 + ENNReal.ofReal (∫ r in Ioc (0:ℝ) (u:ℝ), ‖k r‖)^4*C)
  have hA : A ≠ ⊤ := by dsimp [A]; finiteness
  refine ⟨A,hA,?_⟩
  intro n
  let μ := (Pn n : Measure Ω)
  let ν := volume.restrict (Ioc (0:ℝ) (u:ℝ))
  have hK : Integrable K ν := fractionalL_reflected_integrableOn_Ioc hα' u.coe_nonneg
  have hk : Integrable k ν := hK.add (integrable_const κ)
  have hkm : Measurable k := ((fractionalL_measurable α).comp (measurable_const.sub measurable_id)).add_const _
  let X (p : Ω) := ∫ r, k r*f (p (realTimeOnHorizon T r)) ∂ν
  have he (p : Ω) : canonicalVarianceMartingale T α v₀ κ θ f t p = d+X p := by
    let V (r : ℝ) := f (p (realTimeOnHorizon T r))
    have hKint : Integrable (fun r => K r*V r) ν := integrable_weighted_pairPath_period hK f p
    have hVint : Integrable V ν := by
      simpa only [one_mul, V, ν, IntegrableOn] using integrable_weighted_pairPath_period (k := fun _ => 1)
        (integrable_const 1) f p
    have hdint := hK.mul_const v₀
    have hκint := hVint.const_mul κ
    have hDist : (∫ r, k r*V r ∂ν) = (∫ r, K r*V r ∂ν)+κ*(∫ r, V r ∂ν) := by
      simp only [k, add_mul]
      rw [integral_add hKint hκint, integral_const_mul]
    have hDiff : (∫ r, K r*(V r-v₀) ∂ν) = (∫ r, K r*V r ∂ν)-(∫ r, K r ∂ν)*v₀ := by
      simp only [mul_sub]
      rw [integral_sub hKint hdint, integral_mul_const]
    unfold canonicalVarianceMartingale recoveredVarianceMartingale
    change (∫ r, K r*(V r-v₀) ∂ν) -κ*θ*(u:ℝ)+κ*(∫ r, V r ∂ν) = d+∫ r, k r*V r ∂ν
    rw [hDiff,hDist]
    dsimp [d]
    ring
  have hMoment := canonicalPairPath_weighted_moment_bound Pn n f hkm
    (NNReal.coe_le_coe.mpr (min_le_right t T)) hk 4 (by decide) (hMom n)
  have hEq : (∫⁻ p, ‖canonicalVarianceMartingale T α v₀ κ θ f t p‖ₑ^4 ∂μ) =
      ∫⁻ p, ‖d+X p‖ₑ^4 ∂μ := lintegral_congr fun p => by rw [he p]
  change (∫⁻ p, ‖canonicalVarianceMartingale T α v₀ κ θ f t p‖ₑ^4 ∂μ) ≤ A
  rw [hEq]
  refine (lintegral_enorm_add_pow_le (μ := μ) (X := fun _ => d) (Y := X) measurable_const 4).trans ?_
  rw [lintegral_const, measure_univ, mul_one]
  exact mul_right_mono (add_le_add_right hMoment _)

theorem norm_canonicalVarianceCovariance_sq_bound
    (σ : ℝ) (f g : C(ℝ × ℝ, ℝ)) (hf : ∀ z, 0 ≤ f z) (hg : ∀ z, 0 ≤ g z) (z : ℝ × ℝ) :
    ‖canonicalVarianceCovariance σ f g z‖^2 ≤ σ^4*(1+‖f z‖^4+‖g z‖^4) := by
  rw [Real.norm_eq_abs, sq_abs]
  change ((σ*Real.sqrt (f z))*(σ*Real.sqrt (g z)))^2 ≤ _
  rw [mul_pow,mul_pow,mul_pow, Real.sq_sqrt (hf z), Real.sq_sqrt (hg z)]
  have h : f z*g z ≤ 1+‖f z‖^4+‖g z‖^4 := by
    rw [Real.norm_of_nonneg (hf z), Real.norm_of_nonneg (hg z)]
    nlinarith [sq_nonneg (f z-g z), sq_nonneg ((f z)^2-1/2), sq_nonneg ((g z)^2-1/2)]
  calc
    _ = σ^4*(f z*g z) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)

theorem canonicalVarianceCompensator_second_moment_bound
    (Pn : ℕ → ProbabilityMeasure Ω) (σ : ℝ) (f g : C(ℝ × ℝ, ℝ))
    (hf : ∀ z, 0 ≤ f z) (hg : ∀ z, 0 ≤ g z) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hF : ∀ n t, t ≤ T → (∫⁻ p, ‖f (canonicalPathEval T t p)‖ₑ^4 ∂(Pn n : Measure Ω)) ≤ C)
    (hG : ∀ n t, t ≤ T → (∫⁻ p, ‖g (canonicalPathEval T t p)‖ₑ^4 ∂(Pn n : Measure Ω)) ≤ C)
    (t : ℝ≥0) : ∃ A : ℝ≥0∞, A ≠ ⊤ ∧ ∀ n,
      (∫⁻ p, ‖canonicalVarianceCompensator T (canonicalVarianceCovariance σ f g) t p‖ₑ^2 ∂(Pn n : Measure Ω)) ≤ A := by
  let u := min t T
  let k : ℝ → ℝ := fun _ => 1
  let C' := ENNReal.ofReal (σ^4)*(1+C+C)
  let A := ENNReal.ofReal (∫ r in Ioc (0:ℝ) (u:ℝ), ‖k r‖)^2*C'
  have hA : A ≠ ⊤ := by dsimp [A,C']; finiteness
  refine ⟨A,hA,?_⟩
  intro n
  have hCov (t : ℝ≥0) (ht : t ≤ T) :
      (∫⁻ p, ‖canonicalVarianceCovariance σ f g (canonicalPathEval T t p)‖ₑ^2 ∂(Pn n : Measure Ω)) ≤ C' := by
    let z := canonicalPathEval (E := ℝ × ℝ) T t
    have hMeasF : Measurable (fun p : Ω => ‖f (z p)‖ₑ^4) :=
      ((f.continuous.comp (continuous_canonicalPathEval T t)).measurable.enorm).pow_const _
    have hPoint (p : Ω) : ‖canonicalVarianceCovariance σ f g (z p)‖ₑ^2 ≤
        ENNReal.ofReal (σ^4)*(1+‖f (z p)‖ₑ^4+‖g (z p)‖ₑ^4) := by
      have h := ENNReal.ofReal_le_ofReal (norm_canonicalVarianceCovariance_sq_bound σ f g hf hg (z p))
      simpa only [ENNReal.ofReal_mul (by positivity : 0 ≤ σ^4),
        ENNReal.ofReal_add (by positivity : 0 ≤ (1:ℝ)+‖f (z p)‖^4) (by positivity : 0 ≤ ‖g (z p)‖^4),
        ENNReal.ofReal_add zero_le_one (by positivity : 0 ≤ ‖f (z p)‖^4), ENNReal.ofReal_one,
        ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] using h
    have h := lintegral_mono (μ := (Pn n : Measure Ω)) hPoint
    have hf1 : Measurable (fun p : Ω => (1:ℝ≥0∞)+‖f (z p)‖ₑ^4) := measurable_const.add hMeasF
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_add_left hf1, lintegral_add_left measurable_const,
      lintegral_const, measure_univ, mul_one] at h
    exact h.trans (mul_right_mono (add_le_add (add_le_add_right (hF n t ht) 1) (hG n t ht)))
  have h := canonicalPairPath_weighted_moment_bound Pn n (canonicalVarianceCovariance σ f g)
    (k := k) measurable_const (NNReal.coe_le_coe.mpr (min_le_right t T)) (integrable_const 1) 2 (by decide) hCov
  simpa only [k, one_mul, A, canonicalVarianceCompensator] using h

/-- The two inverse martingale coordinates have the uniform tests
required by weak convergence. -/
theorem uniformCanonicalSecondMoment_varianceMartingale_of_variance_fourth
    {α v₀ κ θ : ℝ} (hα' : α < 1) (Pn : ℕ → ProbabilityMeasure Ω) (f : C(ℝ × ℝ, ℝ))
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hMom : ∀ n t, t ≤ T → (∫⁻ p, ‖f (canonicalPathEval T t p)‖ₑ^4 ∂(Pn n : Measure Ω)) ≤ C) :
    uniformCanonicalSecondMoment Pn (canonicalVarianceMartingale T α v₀ κ θ f) := by
  intro t
  let M := canonicalVarianceMartingale T α v₀ κ θ f t
  obtain ⟨A,hA,hBound⟩ := canonicalVarianceMartingale_fourth_bound (v₀ := v₀) (κ := κ) (θ := θ)
    hα' Pn f hC hMom t
  have hC : 1+A ≠ ⊤ := by finiteness
  refine ⟨(1+A).toReal,?_⟩
  intro n
  have h := lintegral_mono (μ := (Pn n : Measure Ω)) (fun p => enorm_sq_le_one_plus_fourth (M p))
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ,mul_one] at h
  have hm : Continuous M := (continuous_recoveredVarianceMartingale T hα' v₀ κ θ (min t T).prop).comp
    (ContinuousMap.continuous_postcomp f)
  exact real_memLp_two_and_sq_le hm.measurable hC (h.trans (add_le_add_right (hBound n) 1))

/-- Fourth variance moments control the same uniform tests for all
three compensated products. -/
theorem uniformCanonicalSecondMoment_compensatedProduct_of_variance_fourth
    {α v₀ κ θ σ : ℝ} (hα' : α < 1) (Pn : ℕ → ProbabilityMeasure Ω) (f g : C(ℝ × ℝ, ℝ))
    (hf : ∀ z, 0 ≤ f z) (hg : ∀ z, 0 ≤ g z) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hF : ∀ n t, t ≤ T → (∫⁻ p, ‖f (canonicalPathEval T t p)‖ₑ^4 ∂(Pn n : Measure Ω)) ≤ C)
    (hG : ∀ n t, t ≤ T → (∫⁻ p, ‖g (canonicalPathEval T t p)‖ₑ^4 ∂(Pn n : Measure Ω)) ≤ C) :
    uniformCanonicalSecondMoment Pn (fun t p => canonicalVarianceMartingale T α v₀ κ θ f t p *
      canonicalVarianceMartingale T α v₀ κ θ g t p-
      canonicalVarianceCompensator T (canonicalVarianceCovariance σ f g) t p) := by
  intro t
  let M := canonicalVarianceMartingale T α v₀ κ θ f t
  let N := canonicalVarianceMartingale T α v₀ κ θ g t
  let Q := canonicalVarianceCompensator T (canonicalVarianceCovariance σ f g) t
  obtain ⟨A,hA,hMB⟩ := canonicalVarianceMartingale_fourth_bound (v₀ := v₀) (κ := κ) (θ := θ) hα' Pn f hC hF t
  obtain ⟨D,hD,hNB⟩ := canonicalVarianceMartingale_fourth_bound (v₀ := v₀) (κ := κ) (θ := θ) hα' Pn g hC hG t
  obtain ⟨E,hE,hQB⟩ := canonicalVarianceCompensator_second_moment_bound Pn σ f g hf hg hC hF hG t
  let G := (2:ℝ≥0∞)^2*(A+D+E)
  have hG : G ≠ ⊤ := by dsimp [G]; finiteness
  refine ⟨G.toReal,?_⟩
  intro n
  have hMC : Continuous M := (continuous_recoveredVarianceMartingale T hα' v₀ κ θ (min t T).prop).comp
    (ContinuousMap.continuous_postcomp f)
  have hNC : Continuous N := (continuous_recoveredVarianceMartingale T hα' v₀ κ θ (min t T).prop).comp
    (ContinuousMap.continuous_postcomp g)
  have hQC : Continuous Q := continuous_pair_path_time_integral T (min t T : ℝ≥0) (canonicalVarianceCovariance σ f g)
  have h := lintegral_mono (μ := (Pn n : Measure Ω)) (fun p => enorm_sq_product_le_fourth_sum (M p) (N p))
  rw [lintegral_add_left (hMC.measurable.enorm.pow_const _)] at h
  have hMN := h.trans (add_le_add (hMB n) (hNB n))
  have hQ : (∫⁻ p, ‖-Q p‖ₑ^2 ∂(Pn n : Measure Ω)) ≤ E := by simpa only [enorm_neg] using hQB n
  have hX : Continuous (fun p => M p*N p-Q p) := (hMC.mul hNC).sub hQC
  apply real_memLp_two_and_sq_le hX.measurable hG
  exact (lintegral_enorm_add_pow_le (X := fun p => M p*N p) (Y := fun p => -Q p)
    (hMC.mul hNC).measurable 2).trans (mul_right_mono (add_le_add hMN hQ))

#print axioms RoughHeston.canonicalVarianceMartingale_fourth_bound
#print axioms RoughHeston.canonicalVarianceCompensator_second_moment_bound
#print axioms RoughHeston.uniformCanonicalSecondMoment_varianceMartingale_of_variance_fourth
#print axioms RoughHeston.uniformCanonicalSecondMoment_compensatedProduct_of_variance_fourth

end RoughHeston
