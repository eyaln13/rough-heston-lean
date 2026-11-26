import EulerSecondMomentEnergy
import BoundedMeasurableGronwall
import ProductKernelEnergy

/-! Radius-independent linear-growth bounds for the canonical cutoff laws. -/

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston

open MathFin.ItoIntegralCLM

theorem norm_sq_pi_real_le_sum {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    ‖x‖^2 ≤ ∑ i, (x i)^2 := by
  let S := ∑ i, (x i)^2
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  have h : dist x (0 : ι → ℝ) ≤ Real.sqrt S :=
    (dist_pi_le_iff (Real.sqrt_nonneg S)).2 (fun i => by
      rw [Pi.zero_apply, dist_zero_right]
      apply le_of_pow_le_pow_left₀ (n := 2) (by decide) (Real.sqrt_nonneg _)
      rw [Real.norm_eq_abs, sq_abs, Real.sq_sqrt hS]
      exact Finset.single_le_sum (f := fun j => (x j)^2) (fun _ _ => by positivity) (Finset.mem_univ i))
  rw [dist_zero_right] at h
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq (Real.sq_sqrt hS)

theorem growth_sq_le {ι : Type*} [Fintype ι] {B v : ℝ}
    (hB : 0 ≤ B) {x : ι → ℝ} (h : ‖v‖ ≤ B * (1 + ‖x‖)) :
    v^2 ≤ 2 * B^2 * (1 + ∑ i, (x i)^2) := by
  have hp := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [Real.norm_eq_abs, sq_abs, mul_pow] at hp
  have hn : (1 + ‖x‖)^2 ≤ 2 * (1 + ‖x‖^2) := by nlinarith [sq_nonneg (‖x‖ - 1)]
  calc
    _ ≤ B^2 * (1 + ‖x‖)^2 := hp
    _ ≤ B^2 * (2 * (1 + ‖x‖^2)) := mul_le_mul_of_nonneg_left hn (sq_nonneg _)
    _ = 2 * B^2 * (1 + ‖x‖^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl (norm_sq_pi_real_le_sum x)) (by positivity)

theorem euler_timeMeasureHorizon_mass (t : ℝ≥0) : (timeMeasureHorizon t).real univ = (t : ℝ) := by
  rw [measureReal_def, timeMeasureHorizon, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, MathFin.ItoIntegralL2.timeMeasure_Ioc, NNReal.coe_zero, sub_zero,
    ENNReal.toReal_ofReal t.coe_nonneg]

theorem continuous_joint_pathEval {ι : Type*} [Fintype ι] (T : ℝ≥0) :
    Continuous (fun z : ℝ≥0 × CanonicalPath T (ι → ℝ) => canonicalPathEval T z.1 z.2) := by
  have h : Continuous (canonicalEvalTime T) :=
    (continuous_id.min continuous_const).subtype_mk _
  exact continuous_eval.comp (continuous_snd.prodMk (h.comp continuous_fst))

/-- Expected coefficient time integrals may be computed by integrating
the timewise means, even when the path law is unrelated to the Euler construction. -/
theorem integral_canonicalCoefficientIntegral_eq_integral_mean {ι : Type*} [Fintype ι]
    (T t : ℝ≥0) {c : ℝ≥0 → (ι → ℝ) → ℝ} (hc : Continuous (Function.uncurry c))
    {B : ℝ} (hB : ∀ r y, ‖c r y‖ ≤ B)
    (μ : Measure (CanonicalPath T (ι → ℝ))) [IsProbabilityMeasure μ] :
    (∫ p, canonicalCoefficientIntegral T c t p ∂μ) =
      ∫ r, ∫ p, c r (canonicalPathEval T r p) ∂μ ∂timeMeasureHorizon (min t T) := by
  let H (r : ℝ≥0) (p : CanonicalPath T (ι → ℝ)) := c r (canonicalPathEval T r p)
  let ν := timeMeasureHorizon (min t T)
  have hH : Continuous (Function.uncurry H) :=
    hc.comp (continuous_fst.prodMk (continuous_joint_pathEval T))
  have hI : Integrable (Function.uncurry H) (ν.prod μ) :=
    (integrable_const B).mono' hH.stronglyMeasurable.aestronglyMeasurable
      (Eventually.of_forall fun z => hB _ _)
  exact integral_integral_swap hI |>.symm

/-- The sum of the coordinate second moments of a canonical law. -/
noncomputable def canonicalEulerStateSecondMoment {ι : Type*} [Fintype ι]
    (T : ℝ≥0) (μ : Measure (CanonicalPath T (ι → ℝ))) (t : ℝ≥0) : ℝ :=
  ∑ i, ∫ p, (canonicalPathEval T t p i)^2 ∂μ

theorem measurable_canonicalEulerStateSecondMoment {ι : Type*} [Fintype ι]
    (T : ℝ≥0) (μ : Measure (CanonicalPath T (ι → ℝ))) [IsProbabilityMeasure μ] :
    Measurable (canonicalEulerStateSecondMoment T μ) := by
  unfold canonicalEulerStateSecondMoment
  apply Finset.measurable_sum
  intro i _
  have h : Continuous (fun z : ℝ≥0 × CanonicalPath T (ι → ℝ) =>
      (canonicalPathEval T z.1 z.2 i)^2) :=
    ((continuous_apply i).comp (continuous_joint_pathEval T)).pow 2
  exact h.stronglyMeasurable.integral_prod_right'.measurable

theorem integral_timeMeasureHorizon_eq_intervalIntegral {f : ℝ≥0 → ℝ} (hf : Measurable f) (t : ℝ≥0) :
    (∫ s, f s ∂timeMeasureHorizon t) = ∫ r in (0 : ℝ)..(t : ℝ), f r.toNNReal := by
  rw [← hestonTimeMeasure_eq_horizon, hestonTimeMeasure,
    integral_map continuous_real_toNNReal.measurable.aemeasurable hf.stronglyMeasurable.aestronglyMeasurable,
    intervalIntegral.integral_of_le t.coe_nonneg, restrict_Ioo_eq_restrict_Ioc]

/-- The scalar second moment of any bounded law with common linear-growth
constant satisfies a radius-independent integral inequality. -/
theorem canonicalEulerStateSecondMoment_le_linear_growth_energy
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
    (hQ : ∀ i, Martingale (canonicalEulerCompensatedProduct T b σ x i i)
      (canonicalPathNaturalFiltration T) μ)
    {t : ℝ≥0} (ht : t ≤ T) :
    let G := canonicalEulerStateSecondMoment T μ
    let K := 6 * (Fintype.card ι : ℝ) * ((T : ℝ) + Fintype.card κ) * L^2
    let A := 3 * (∑ i, (x i)^2) + K * (T : ℝ)
    (G t ≤ A + K * (∫ r in (0 : ℝ)..(t : ℝ), G r.toNNReal)) ∧
      G t ≤ 2 * A * Real.exp ((2*K+1) * (T : ℝ)) := by
  dsimp only
  let P := CanonicalPath T (ι → ℝ)
  let G := canonicalEulerStateSecondMoment T μ
  let Q := (2 * L^2)
  let D := (Fintype.card κ : ℝ)
  let K := 6 * (Fintype.card ι : ℝ) * ((T : ℝ) + Fintype.card κ) * L^2
  have hSt (r : ℝ≥0) (i : ι) := integral_sq_canonicalEulerState_le_energy hInit hb hσ hB hC₀ hC i (hQ i) r
  let hA (r : ℝ≥0) (p : P) := ∑ i, (canonicalPathEval T r p i)^2
  have hMass : μ.real univ = 1 := by simp [measureReal_def]
  let X (r : ℝ≥0) (p : P) := 1 + hA r p
  have hXI (r : ℝ≥0) : Integrable (X r) μ :=
    (integrable_const (1 : ℝ)).add (integrable_finsetSum _ fun i _ => (hSt r i).1)
  have hXMean (r : ℝ≥0) : (∫ p, X r p ∂μ) = 1 + G r := by
    have hi : Integrable (fun p => hA r p) μ :=
      integrable_finsetSum _ fun i _ => (hSt r i).1
    change (∫ p, 1 + hA r p ∂μ) = _
    rw [integral_add (integrable_const (1 : ℝ)) hi]
    simp only [integral_const, hMass, smul_eq_mul, one_mul]
    dsimp only [hA, G, canonicalEulerStateSecondMoment]
    rw [integral_finsetSum _ (fun i _ => (hSt r i).1)]
  have hJointB (i : ι) : Continuous (fun z : ℝ≥0 × P =>
      (b z.1 (canonicalPathEval T z.1 z.2) i)^2) :=
    ((hb i).comp (continuous_fst.prodMk (continuous_joint_pathEval T))).pow 2
  have hJointC (i : ι) : Continuous (fun z : ℝ≥0 × P =>
      eulerCovarianceCoefficient σ i i z.1 (canonicalPathEval T z.1 z.2)) :=
    (continuous_eulerCovarianceCoefficient hσ i i).comp
      (continuous_fst.prodMk (continuous_joint_pathEval T))
  let bMean (i : ι) (r : ℝ≥0) := ∫ p : P, (b r (canonicalPathEval T r p) i)^2 ∂μ
  let cMean (i : ι) (r : ℝ≥0) := ∫ p : P, eulerCovarianceCoefficient σ i i r (canonicalPathEval T r p) ∂μ
  have hbSm (i : ι) : StronglyMeasurable (bMean i) := (hJointB i).stronglyMeasurable.integral_prod_right'
  have hcSm (i : ι) : StronglyMeasurable (cMean i) := (hJointC i).stronglyMeasurable.integral_prod_right'
  have hBMeanBound (i : ι) (r : ℝ≥0) : ‖bMean i r‖ ≤ B^2 := by
    have hi := norm_integral_le_of_norm_le_const (μ := μ) (C := B^2)
      (f := fun p : P => (b r (canonicalPathEval T r p) i)^2)
      (Eventually.of_forall fun p => by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hB _ _ _) 2)
    simpa only [hMass, mul_one] using hi
  have hCMeanBound (i : ι) (r : ℝ≥0) : ‖cMean i r‖ ≤ D * C^2 := by
    have hi := norm_integral_le_of_norm_le_const (μ := μ)
      (Eventually.of_forall fun p : P => norm_eulerCovarianceCoefficient_le hC₀ hC i i r (canonicalPathEval T r p))
    simpa only [hMass, mul_one] using hi
  have hbI (i : ι) (s : ℝ≥0) : Integrable (bMean i) (timeMeasureHorizon s) :=
    (integrable_const _).mono' (hbSm i).aestronglyMeasurable (Eventually.of_forall (hBMeanBound i))
  have hcI (i : ι) (s : ℝ≥0) : Integrable (cMean i) (timeMeasureHorizon s) :=
    (integrable_const _).mono' (hcSm i).aestronglyMeasurable (Eventually.of_forall (hCMeanBound i))
  have hSt' (r : ℝ≥0) (i : ι) :
      (∫ p : P, (canonicalPathEval T r p i)^2 ∂μ) ≤ 3 * (x i)^2 +
        3 * (↑(min r T) : ℝ) * (∫ s, bMean i s ∂timeMeasureHorizon (min r T)) +
        3 * (∫ s, cMean i s ∂timeMeasureHorizon (min r T)) := by
    have h := (hSt r i).2
    rw [integral_canonicalCoefficientIntegral_eq_integral_mean T r
      (continuous_eulerCovarianceCoefficient hσ i i) (norm_eulerCovarianceCoefficient_le hC₀ hC i i)] at h
    exact h
  have hBounded (r : ℝ≥0) (i : ι) :
      (∫ p : P, (canonicalPathEval T r p i)^2 ∂μ) ≤
        3 * (x i)^2 + 3 * (T : ℝ) * (B^2 * (T : ℝ)) + 3 * (D * C^2 * (T : ℝ)) := by
    have hb' : (∫ s, bMean i s ∂timeMeasureHorizon (min r T)) ≤ B^2 * (T : ℝ) := by
      have h := norm_integral_le_of_norm_le_const (μ := timeMeasureHorizon (min r T))
        (Eventually.of_forall (hBMeanBound i))
      rw [euler_timeMeasureHorizon_mass] at h
      exact (le_abs_self _).trans (h.trans
        (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr (min_le_right _ _)) (sq_nonneg _)))
    have hc' : (∫ s, cMean i s ∂timeMeasureHorizon (min r T)) ≤ D * C^2 * (T : ℝ) := by
      have h := norm_integral_le_of_norm_le_const (μ := timeMeasureHorizon (min r T))
        (Eventually.of_forall (hCMeanBound i))
      rw [euler_timeMeasureHorizon_mass] at h
      exact (le_abs_self _).trans (h.trans
        (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr (min_le_right _ _)) (by dsimp [D]; positivity)))
    refine (hSt' r i).trans ?_
    have hD := mul_le_mul (NNReal.coe_le_coe.mpr (min_le_right r T)) hb'
      (integral_nonneg fun s => integral_nonneg fun _ => sq_nonneg _) T.coe_nonneg
    linarith
  let Fbound := ∑ i : ι, (3 * (x i)^2 + 3 * (T : ℝ) * (B^2 * (T : ℝ)) + 3 * (D * C^2 * (T : ℝ)))
  have hG₀ (r : ℝ≥0) : 0 ≤ G r := Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
  have hGB (r : ℝ≥0) : G r ≤ Fbound := Finset.sum_le_sum fun i _ => hBounded r i
  let A := 3 * (∑ i, (x i)^2) + K * (T : ℝ)
  have hLe (t : ℝ≥0) (ht : t ≤ T) :
      G t ≤ A + K * (∫ r in (0 : ℝ)..(t : ℝ), G r.toNNReal) := by
    let ν := timeMeasureHorizon t
    have hGI : Integrable G ν := (integrable_const Fbound).mono'
      (measurable_canonicalEulerStateSecondMoment T μ).stronglyMeasurable.aestronglyMeasurable
      (Eventually.of_forall fun r => by rw [Real.norm_of_nonneg (hG₀ r)]; exact hGB r)
    have hR (i : ι) (r : ℝ≥0) : bMean i r ≤ Q * (1 + G r) := by
      have hi : Integrable (fun p : P => (b r (canonicalPathEval T r p) i)^2) μ :=
        (integrable_const (B^2)).mono'
          (((hb i).comp (continuous_const.prodMk (continuous_canonicalPathEval T r))).pow 2).stronglyMeasurable.aestronglyMeasurable
          (Eventually.of_forall fun _ => by rw [norm_pow]; gcongr; exact hB _ _ _)
      calc
        _ ≤ ∫ p : P, Q * X r p ∂μ :=
          integral_mono hi ((hXI r).const_mul _) (fun p => growth_sq_le hL (hBG r (canonicalPathEval T r p) i))
        _ = _ := by rw [integral_const_mul, hXMean]
    have hS (i : ι) (r : ℝ≥0) : cMean i r ≤ D * Q * (1 + G r) := by
      have hi : Integrable (fun p : P => eulerCovarianceCoefficient σ i i r (canonicalPathEval T r p)) μ :=
        (integrable_const (D * C^2)).mono'
          (((continuous_eulerCovarianceCoefficient hσ i i).comp
            (continuous_const.prodMk (continuous_canonicalPathEval T r))).stronglyMeasurable.aestronglyMeasurable)
          (Eventually.of_forall fun _ => norm_eulerCovarianceCoefficient_le hC₀ hC _ _ _ _)
      calc
        _ ≤ ∫ p : P, D * Q * X r p ∂μ := by
          apply integral_mono hi ((hXI r).const_mul _)
          intro p
          change (∑ j, σ r (canonicalPathEval T r p) i j * σ r (canonicalPathEval T r p) i j) ≤ D * Q * X r p
          simp_rw [← pow_two]
          calc
            _ ≤ ∑ _j : κ, Q * X r p :=
              Finset.sum_le_sum fun j _ => growth_sq_le hL (hCG r (canonicalPathEval T r p) i j)
            _ = _ := by simp [D, mul_assoc]
        _ = _ := by rw [integral_const_mul, hXMean]
    have hInt (s : ℝ) (i : ι) (U : ℝ≥0 → ℝ) (hUi : Integrable U ν)
        (hsBound : ∀ r, U r ≤ s * (1 + G r)) :
        (∫ r, U r ∂ν) ≤ s * ((t : ℝ) + ∫ r, G r ∂ν) := by
      calc
        _ ≤ ∫ r, s * (1 + G r) ∂ν := integral_mono hUi
          (((integrable_const (1 : ℝ)).add hGI).const_mul s) hsBound
        _ = _ := by
          rw [integral_const_mul, integral_add (integrable_const (1 : ℝ)) hGI,
            integral_const, smul_eq_mul, mul_one, euler_timeMeasureHorizon_mass]
    have hGInt : 0 ≤ ∫ r, G r ∂ν := integral_nonneg hG₀
    have hSum (i : ι) : (∫ p : P, (canonicalPathEval T t p i)^2 ∂μ) ≤
        3 * (x i)^2 + 3 * ((T : ℝ) + D) * Q * ((t : ℝ) + ∫ r, G r ∂ν) := by
      have hb' := hInt Q i (bMean i) (hbI i t) (hR i)
      have hc' := hInt (D * Q) i (cMean i) (hcI i t) (hS i)
      have hi := hSt' t i
      rw [min_eq_left ht] at hi
      refine hi.trans ?_
      have ht' := NNReal.coe_le_coe.mpr ht
      have hP := mul_le_mul ht' hb'
        (integral_nonneg fun r => integral_nonneg fun _ => sq_nonneg _) T.coe_nonneg
      nlinarith [hc']
    have hFinal :
        G t ≤ 3 * (∑ i, (x i)^2) + K * ((t : ℝ) + ∫ r, G r ∂ν) := by
      unfold G canonicalEulerStateSecondMoment
      calc
        _ ≤ ∑ i, (3 * (x i)^2 + 3 * ((T : ℝ) + D) * Q * ((t : ℝ) + ∫ r, G r ∂ν)) :=
          Finset.sum_le_sum fun i _ => hSum i
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          dsimp only [K, D, Q, G, canonicalEulerStateSecondMoment]
          ring
    have hK : 0 ≤ K := by dsimp [K]; positivity
    rw [show (∫ r, G r ∂ν) = ∫ r in (0 : ℝ)..(t : ℝ), G r.toNNReal from
      integral_timeMeasureHorizon_eq_intervalIntegral (measurable_canonicalEulerStateSecondMoment T μ) t] at hFinal
    refine hFinal.trans ?_
    dsimp only [A]
    have hs := mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr ht) hK
    linarith
  refine ⟨hLe t ht, ?_⟩
  let f (r : ℝ) := G r.toNNReal
  have hf : Measurable f := (measurable_canonicalEulerStateSecondMoment T μ).comp
    continuous_real_toNNReal.measurable
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    exact add_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
      (mul_nonneg hK T.coe_nonneg)
  have hCont (r : ℝ) (hr : r ∈ Icc (0 : ℝ) (T : ℝ)) :
      f r ≤ A + K * (∫ q in (0 : ℝ)..r, f q) := by
    have hrT : r.toNNReal ≤ T := by
      apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal _ hr.1]
      exact hr.2
    have h := hLe r.toNNReal hrT
    rw [Real.coe_toNNReal _ hr.1] at h
    exact h
  have hU := le_uniform_exp_of_bounded_measurable_integral_inequality hf hA0 hK T.coe_nonneg
    (fun r _ => ⟨hG₀ r.toNNReal, hGB r.toNNReal⟩) hCont (t : ℝ)
    ⟨t.coe_nonneg, NNReal.coe_le_coe.mpr ht⟩
  simpa only [f, Real.toNNReal_coe] using hU

#print axioms RoughHeston.integral_canonicalCoefficientIntegral_eq_integral_mean
#print axioms RoughHeston.canonicalEulerStateSecondMoment_le_linear_growth_energy

end RoughHeston
