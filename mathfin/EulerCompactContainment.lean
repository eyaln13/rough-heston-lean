import EulerLinearGrowthEnergy
import ContinuousDoobRealEnvelope

/-! Canonical path sup-moment estimates under a common linear-growth constant. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston

open MathFin.ItoIntegralCLM

private theorem continuous_canonicalCoefficientIntegral_time {ι : Type*} [Fintype ι]
    (T : ℝ≥0) {c : ℝ≥0 → (ι → ℝ) → ℝ} (hc : Continuous (Function.uncurry c))
    (p : CanonicalPath T (ι → ℝ)) :
    Continuous (fun t => canonicalCoefficientIntegral T c t p) := by
  have hEvalT : Continuous (canonicalEvalTime T) :=
    (continuous_id.min continuous_const).subtype_mk _
  let f (r : ℝ≥0) := c r (canonicalPathEval T r p)
  have hf : Continuous f := hc.comp (continuous_id.prodMk (p.continuous.comp hEvalT))
  have hF : Continuous (fun r : ℝ => f r.toNNReal) := hf.comp continuous_real_toNNReal
  have hI := (intervalIntegral.differentiable_integral_of_continuous (a := 0) hF).continuous
  have hMap (t : ℝ≥0) : canonicalCoefficientIntegral T c t p =
      ∫ r in (0 : ℝ)..(↑(min t T) : ℝ), f r.toNNReal :=
    integral_timeMeasureHorizon_eq_intervalIntegral hf.measurable _
  simp_rw [hMap]
  exact hI.comp (NNReal.continuous_coe.comp (continuous_id.min continuous_const))

private theorem norm_canonicalCoefficientIntegral_le_absTerminal {ι : Type*} [Fintype ι]
    (T : ℝ≥0) {c : ℝ≥0 → (ι → ℝ) → ℝ} (hc : Continuous (Function.uncurry c))
    {B : ℝ} (hB : ∀ r y, ‖c r y‖ ≤ B) (p : CanonicalPath T (ι → ℝ)) (t : ℝ≥0) :
    ‖canonicalCoefficientIntegral T c t p‖ ≤
        canonicalCoefficientIntegral T (fun r y => ‖c r y‖) T p := by
  let f (s : ℝ≥0) := ‖c s (canonicalPathEval T s p)‖
  have hEvalT : Continuous (canonicalEvalTime T) :=
    (continuous_id.min continuous_const).subtype_mk _
  have hf : Continuous f := (hc.comp (continuous_id.prodMk (p.continuous.comp hEvalT))).norm
  have hi : Integrable f (timeMeasureHorizon T) :=
    (integrable_const B).mono' hf.stronglyMeasurable.aestronglyMeasurable
      (Eventually.of_forall fun r => by rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hB _ _)
  have hle : timeMeasureHorizon (min t T) ≤ timeMeasureHorizon T := by
    unfold timeMeasureHorizon
    exact Measure.restrict_mono (Ioc_subset_Ioc_right (min_le_right _ _)) le_rfl
  calc
    _ ≤ ∫ r, f r ∂timeMeasureHorizon (min t T) := norm_integral_le_integral_norm _
    _ ≤ ∫ r, f r ∂timeMeasureHorizon T :=
      integral_mono_measure hle (Eventually.of_forall fun _ => norm_nonneg _) hi
    _ = _ := by simp [canonicalCoefficientIntegral, f]

private theorem expected_canonicalCoefficientIntegral_le_of_energy {ι : Type*} [Fintype ι]
    (T : ℝ≥0) {c : ℝ≥0 → (ι → ℝ) → ℝ} (hc : Continuous (Function.uncurry c))
    {B Q H : ℝ} (hB : ∀ r y, ‖c r y‖ ≤ B) (hQ : 0 ≤ Q)
    (hGrowth : ∀ r y, c r y ≤ Q * (1 + ∑ i, (y i)^2))
    (μ : Measure (CanonicalPath T (ι → ℝ))) [IsProbabilityMeasure μ]
    (h2 : ∀ r i, Integrable (fun p : CanonicalPath T (ι → ℝ) => (canonicalPathEval T r p i)^2) μ)
    (hE : ∀ r ≤ T, canonicalEulerStateSecondMoment T μ r ≤ H) :
    (∫ p, canonicalCoefficientIntegral T c T p ∂μ) ≤ Q * (T : ℝ) * (1 + H) := by
  let P := CanonicalPath T (ι → ℝ)
  let F (r : ℝ≥0) (p : P) := c r (canonicalPathEval T r p)
  let Z (r : ℝ≥0) (p : P) := ∑ i, (canonicalPathEval T r p i)^2
  let mean (r : ℝ≥0) := ∫ p, F r p ∂μ
  let ν := timeMeasureHorizon T
  have hFc : Continuous (Function.uncurry F) := hc.comp (continuous_fst.prodMk (continuous_joint_pathEval T))
  have hMeanI : Integrable mean ν := (integrable_const B).mono'
    hFc.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    (Eventually.of_forall fun r => by
      have h := norm_integral_le_of_norm_le_const (μ := μ) (f := F r)
        (Eventually.of_forall fun p => hB r (canonicalPathEval T r p))
      simpa [mean, measureReal_def] using h)
  have hExpected (r : ℝ≥0) (hr : r ≤ T) : mean r ≤ Q * (1+H) := by
    have hI : Integrable (F r) μ := (integrable_const B).mono'
      (hFc.comp (continuous_const.prodMk continuous_id)).stronglyMeasurable.aestronglyMeasurable
      (Eventually.of_forall fun p => hB r (canonicalPathEval T r p))
    have hZ : Integrable (Z r) μ := integrable_finsetSum _ fun i _ => h2 r i
    have h1 : Integrable (fun p => 1 + Z r p) μ := (integrable_const _).add hZ
    have he : (∫ p, Z r p ∂μ) = canonicalEulerStateSecondMoment T μ r := by
      dsimp only [Z, canonicalEulerStateSecondMoment]
      rw [integral_finsetSum _ (fun i _ => h2 r i)]
    calc
      _ ≤ ∫ p : P, Q * (1 + Z r p) ∂μ :=
        integral_mono hI (h1.const_mul _) (fun p => hGrowth r (canonicalPathEval T r p))
      _ = Q * (1 + canonicalEulerStateSecondMoment T μ r) := by
        rw [integral_const_mul, integral_add (integrable_const (1 : ℝ)) hZ, integral_const, he]
        simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl (hE r hr)) hQ
  rw [integral_canonicalCoefficientIntegral_eq_integral_mean T T hc hB, min_self]
  change (∫ r, mean r ∂ν) ≤ _
  have hτ : ∀ᵐ r ∂ν, r ∈ Ioc 0 T := ae_restrict_mem measurableSet_Ioc
  calc
    _ ≤ ∫ _r, Q * (1+H) ∂ν :=
      integral_mono_ae hMeanI (integrable_const _) (hτ.mono fun r hr => hExpected r hr.2)
    _ = _ := by rw [integral_const, smul_eq_mul, euler_timeMeasureHorizon_mass]; ring

/-- A uniform, radius-independent bound for the squared canonical
supremum norm follows from the drift, covariance and martingale problem.
In particular, truncated laws with a common linear-growth coefficient
satisfy compact containment. -/
theorem canonicalEulerPath_sq_norm_le_linear_growth
    {ι κ : Type*} [Fintype ι] [Fintype κ] {T : ℝ≥0}
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    {x : ι → ℝ} {μ : Measure (CanonicalPath T (ι → ℝ))} [IsProbabilityMeasure μ]
    (hInit : μ {p | canonicalPathEval T 0 p = x} = 1)
    (hb : ∀ i, Continuous (fun z : ℝ≥0 × (ι → ℝ) => b z.1 z.2 i))
    (hσ : ∀ i j, Continuous (fun z : ℝ≥0 × (ι → ℝ) => σ z.1 z.2 i j))
    {B C L : ℝ} (hB₀ : 0 ≤ B) (hC₀ : 0 ≤ C) (hL : 0 ≤ L)
    (hB : ∀ r y i, ‖b r y i‖ ≤ B) (hC : ∀ r y i j, ‖σ r y i j‖ ≤ C)
    (hBG : ∀ r y i, ‖b r y i‖ ≤ L * (1 + ‖y‖))
    (hCG : ∀ r y i j, ‖σ r y i j‖ ≤ L * (1 + ‖y‖))
    (hM : ∀ i, Martingale (canonicalEulerMartingaleCoordinate T b x i)
      (canonicalPathNaturalFiltration T) μ)
    (hQ : ∀ i, Martingale (canonicalEulerCompensatedProduct T b σ x i i)
      (canonicalPathNaturalFiltration T) μ) :
    let K := 6 * (Fintype.card ι : ℝ) * ((T : ℝ) + Fintype.card κ) * L^2
    let H := 2 * (3 * (∑ i, (x i)^2) + K * (T : ℝ)) * Real.exp ((2*K+1) * (T : ℝ))
    Integrable (fun p : CanonicalPath T (ι → ℝ) => ‖p‖^2) μ ∧
      (∫ p : CanonicalPath T (ι → ℝ), ‖p‖^2 ∂μ) ≤
        3 * (∑ i, (x i)^2) + 6 * (Fintype.card ι : ℝ) * L^2 *
          (T : ℝ) * ((T : ℝ) + 4 * Fintype.card κ) * (1 + H) := by
  dsimp only
  let P := CanonicalPath T (ι → ℝ)
  let K := 6 * (Fintype.card ι : ℝ) * ((T : ℝ) + Fintype.card κ) * L^2
  let H := 2 * (3 * (∑ i, (x i)^2) + K * (T : ℝ)) * Real.exp ((2*K+1) * (T : ℝ))
  let M := canonicalEulerMartingaleCoordinate T b x
  let A (i : ι) := canonicalCoefficientIntegral T (fun r y => ‖b r y i‖) T
  let Kb := 2 * L^2 * (T : ℝ) ^ 2 * (1 + H)
  let Kc := (Fintype.card κ : ℝ) * (2 * L^2) * (T : ℝ) * (1 + H)
  have h2 (r : ℝ≥0) (i : ι) : Integrable (fun p : P => (canonicalPathEval T r p i)^2) μ :=
    (integral_sq_canonicalEulerState_le_energy hInit hb hσ hB hC₀ hC i (hQ i) r).1
  have hE (r : ℝ≥0) (hr : r ≤ T) : canonicalEulerStateSecondMoment T μ r ≤ H :=
    (canonicalEulerStateSecondMoment_le_linear_growth_energy hInit hb hσ hB₀ hC₀ hL hB hC
      hBG hCG hQ hr).2
  have hBtop (i : ι) : Continuous (Function.uncurry (fun r y => ‖b r y i‖)) := (hb i).norm
  have hA (i : ι) : Integrable (fun p : P => (A i p)^2) μ := by
    have hm := continuous_canonicalCoefficientIntegral T T (hBtop i)
      (fun r y => by rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hB r y i)
    refine (integrable_const ((B*(T:ℝ))^2)).mono' (hm.pow 2).stronglyMeasurable.aestronglyMeasurable ?_
    exact Eventually.of_forall fun p => by
      rw [norm_pow]
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      simpa only [min_self] using norm_canonicalCoefficientIntegral_le T T
        (b := fun r y => ‖b r y i‖)
        (fun r y => by rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hB r y i) p
  have hAm (i : ι) : (∫ p : P, (A i p)^2 ∂μ) ≤ Kb := by
    have hbSq (r : ℝ≥0) (y : ι → ℝ) : ‖‖b r y i‖^2‖ ≤ B^2 := by
      rw [norm_pow, Real.norm_of_nonneg (norm_nonneg (b r y i))]
      exact pow_le_pow_left₀ (norm_nonneg _) (hB r y i) 2
    have hbGr (r : ℝ≥0) (y : ι → ℝ) : ‖b r y i‖^2 ≤ (2*L^2) * (1+∑ i, (y i)^2) := by
      rw [Real.norm_eq_abs, sq_abs]
      exact growth_sq_le hL (hBG r y i)
    have hmean := expected_canonicalCoefficientIntegral_le_of_energy T ((hBtop i).pow 2)
      hbSq (by positivity : 0 ≤ 2*L^2) hbGr μ h2 hE
    rw [integral_canonicalCoefficientIntegral_eq_integral_mean T T ((hBtop i).pow 2) hbSq, min_self] at hmean
    have hJ := integral_sq_canonicalCoefficientIntegral_le T T (hBtop i)
      (fun r y => by rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hB r y i) μ
    rw [min_self] at hJ
    refine hJ.trans ?_
    have h := mul_le_mul_of_nonneg_left hmean T.coe_nonneg
    exact h.trans_eq (by dsimp [Kb]; ring)
  have hMo (i : ι) := canonicalEulerMartingaleCoordinate_sq_eq_covariance hInit hσ hC₀ hC i (hQ i) T
  have hM2 (i : ι) : (∫ p : P, (M i T p)^2 ∂μ) ≤ Kc := by
    have hGr (r : ℝ≥0) (y : ι → ℝ) :
        eulerCovarianceCoefficient σ i i r y ≤
          ((Fintype.card κ : ℝ)*(2*L^2)) * (1+∑ i, (y i)^2) := by
      unfold eulerCovarianceCoefficient
      simp_rw [← pow_two]
      calc
        _ ≤ ∑ _j : κ, (2*L^2) * (1+∑ i, (y i)^2) :=
          Finset.sum_le_sum fun j _ => growth_sq_le hL (hCG r y i j)
        _ = _ := by simp [mul_assoc]
    calc
      _ = ∫ p : P, canonicalCoefficientIntegral T (eulerCovarianceCoefficient σ i i) T p ∂μ :=
        (hMo i).2
      _ ≤ _ := expected_canonicalCoefficientIntegral_le_of_energy T
        (continuous_eulerCovarianceCoefficient hσ i i) (norm_eulerCovarianceCoefficient_le hC₀ hC i i)
        (by positivity) hGr μ h2 hE
  have hMCont (i : ι) (p : P) : Continuous (fun t => M i t p) := by
    have hTime : Continuous (canonicalEvalTime T) :=
      (continuous_id.min continuous_const).subtype_mk _
    exact (((continuous_apply i).comp (p.continuous.comp hTime)).sub continuous_const).sub
      (continuous_canonicalCoefficientIntegral_time T (hb i) p)
  have hEn (i : ι) := exists_continuous_martingale_real_norm_envelope_sq (hM i) T
    (Eventually.of_forall fun p => (hMCont i p).continuousOn) (hMo i).1
  choose S hSm hSi hSdom hSb using hEn
  let U (p : P) := 3 * (∑ i, ((x i)^2 + (A i p)^2 + (S i p)^2))
  have hU : Integrable U μ :=
    (integrable_finsetSum _ fun i _ =>
      (((integrable_const _).add (hA i)).add (hSi i))).const_mul _
  have hDom : ∀ᵐ p ∂μ, ‖p‖^2 ≤ U p := by
    have hall : ∀ᵐ p ∂μ, ∀ i, ∀ t ≤ T, ‖M i t p‖ ≤ S i p := ae_all_iff.2 hSdom
    filter_upwards [hall] with p hp
    have hU0 : 0 ≤ U p := by
      dsimp only [U]
      exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => by positivity)
    have hEach (t : CanonicalPathTime T) : ‖p t‖ ≤ Real.sqrt (U p) := by
      apply le_of_pow_le_pow_left₀ (n := 2) (by decide) (Real.sqrt_nonneg _)
      rw [Real.sq_sqrt hU0]
      refine (norm_sq_pi_real_le_sum (p t)).trans ?_
      dsimp only [U]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      let D := canonicalCoefficientIntegral T (fun r y => b r y i) t.val p
      let N := M i t.val p
      have hv : canonicalPathEval T t.val p = p t := by
        exact congrArg p (Subtype.ext (min_eq_left t.property.2))
      have hEq : p t i = x i + D + N := by
        rw [← hv]
        dsimp [D, N, M, canonicalEulerMartingaleCoordinate]
        ring
      have hDr : |D| ≤ A i p := norm_canonicalCoefficientIntegral_le_absTerminal T
        (hb i) (fun r y => hB r y i) p t.val
      have hNr : |N| ≤ S i p := hp i t.val t.property.2
      have hDs := pow_le_pow_left₀ (abs_nonneg _) hDr 2
      have hNs := pow_le_pow_left₀ (abs_nonneg _) hNr 2
      rw [sq_abs] at hDs hNs
      rw [hEq]
      nlinarith [sq_nonneg (x i - D), sq_nonneg (x i - N), sq_nonneg (D-N)]
    let : Nonempty (CanonicalPathTime T) := ⟨canonicalEvalTime T 0⟩
    have hp' : ‖p‖ ≤ Real.sqrt (U p) := (ContinuousMap.norm_le_of_nonempty p).2 hEach
    exact (pow_le_pow_left₀ (norm_nonneg _) hp' 2).trans_eq (Real.sq_sqrt hU0)
  have hPI : Integrable (fun p : P => ‖p‖^2) μ := hU.mono' (continuous_norm.pow 2).stronglyMeasurable.aestronglyMeasurable
    (hDom.mono fun p hp => by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hp)
  refine ⟨hPI, (integral_mono_ae hPI hU hDom).trans ?_⟩
  have hBound (i : ι) : (∫ p : P, (x i)^2 + (A i p)^2 + (S i p)^2 ∂μ) ≤
      (x i)^2 + Kb + 4*Kc := by
    have hI : Integrable (fun p : P => (x i)^2 + (A i p)^2) μ :=
      (integrable_const _).add (hA i)
    rw [integral_add hI (hSi i), integral_add (integrable_const _) (hA i)]
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
    exact add_le_add (add_le_add le_rfl (hAm i))
      ((hSb i).trans (mul_le_mul_of_nonneg_left (hM2 i) (by norm_num)))
  have hSummand (i : ι) : Integrable (fun p : P => (x i)^2 + (A i p)^2 + (S i p)^2) μ :=
    (((integrable_const _).add (hA i)).add (hSi i))
  dsimp only [U]
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hSummand i)]
  refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hBound i) (by norm_num)).trans_eq ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]
  dsimp only [Kb, Kc, H, K]
  ring

#print axioms RoughHeston.canonicalEulerPath_sq_norm_le_linear_growth

end RoughHeston
