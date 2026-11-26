import EulerProblemMoments
import MovingMartingaleTestLimits
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! Identification of the bounded continuous Euler weak limit. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BoundedContinuousFunction

namespace RoughHeston

private theorem canonicalStoppedPath_clip_eq {ι : Type*} {T : ℝ≥0}
    (s : ℝ≥0) (p : CanonicalPath T (ι → ℝ)) :
    canonicalStoppedPath T (min s T) p = canonicalStoppedPath T s p := by
  ext u i
  change p (canonicalStopTime T (min s T) u) i = p (canonicalStopTime T s u) i
  apply congrArg (fun v : CanonicalPathTime T => p v i)
  apply Subtype.ext
  change min u.val (min s T) = min u.val s
  rw [← min_assoc, min_eq_left ((min_le_left _ _).trans u.property.2)]

/-- Every weak subsequential limit of the actual bounded dyadic Euler
laws solves the coordinate and product martingale problem. -/
theorem eulerDyadicLaw_weak_limit_martingale_problem {Ω ι κ : Type*}
    {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    [Fintype ι] [Fintype κ] [DecidableEq κ] {𝒢 : Filtration ℝ≥0 m}
    {T : ℝ≥0} (hT : 0 < T)
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    {W : κ → ℝ≥0 → Ω → ℝ} (x : ι → ℝ)
    (hb : ∀ i, Continuous (fun z : ℝ≥0 × (ι → ℝ) => b z.1 z.2 i))
    (hσ : ∀ i j, Continuous (fun z : ℝ≥0 × (ι → ℝ) => σ z.1 z.2 i j))
    (hW : ∀ j, Martingale (W j) 𝒢 μ) (hW₂ : ∀ j t, MemLp (W j t) 2 μ)
    {B C : ℝ} (hB₀ : 0 ≤ B) (hC₀ : 0 ≤ C)
    (hB : ∀ t y i, ‖b t y i‖ ≤ B) (hC : ∀ t y i j, ‖σ t y i j‖ ≤ C)
    (hGaussian : ∀ j k a, HasLaw
      (W a (((uniformDyadicGrids T).grid j) (k+1)) - W a (((uniformDyadicGrids T).grid j) k))
      (gaussianReal 0 (((uniformDyadicGrids T).grid j) (k+1) - ((uniformDyadicGrids T).grid j) k)) μ)
    (hCov : ∀ j k a a', μ[(W a (((uniformDyadicGrids T).grid j) (k+1)) -
      W a (((uniformDyadicGrids T).grid j) k)) * (W a' (((uniformDyadicGrids T).grid j) (k+1)) -
      W a' (((uniformDyadicGrids T).grid j) k)) | 𝒢 (((uniformDyadicGrids T).grid j) k)] =ᵐ[μ]
      fun _ => if a = a' then ((((uniformDyadicGrids T).grid j) (k+1) : ℝ) -
        (((uniformDyadicGrids T).grid j) k : ℝ)) else 0)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {P : ProbabilityMeasure (CanonicalPath T (ι → ℝ))}
    (hweak : Tendsto (fun n => eulerDyadicLaw (μ := μ) T (φ n) b σ W x) atTop (𝓝 P)) :
    (P : Measure (CanonicalPath T (ι → ℝ))) {p | canonicalPathEval T 0 p = x} = 1 ∧
    (∀ i, Martingale (canonicalEulerMartingaleCoordinate T b x i)
      (canonicalPathNaturalFiltration T) (P : Measure _)) ∧
    (∀ i l, Martingale (canonicalEulerCompensatedProduct T b σ x i l)
      (canonicalPathNaturalFiltration T) (P : Measure _)) := by
  let Path := CanonicalPath T (ι → ℝ)
  let g (j : ℕ) := (uniformDyadicGrids T).grid j
  let a (j : ℕ) (t : ℝ≥0) := eulerDyadicCeiling T j t
  let u (j : ℕ) (t : ℝ≥0) := g j (a j t)
  let Pn (n : ℕ) := eulerDyadicLaw (μ := μ) T (φ n) b σ W x
  let F := canonicalPathNaturalFiltration (E := ι → ℝ) T
  have hgm (j : ℕ) : ∀ k < 2^j, g j k < g j (k+1) :=
    fun k _ => uniformDyadicGrid_strictMono hT j k.lt_succ_self
  have hau (j : ℕ) (t : ℝ≥0) : a j t ≤ 2^j := eulerDyadicCeiling_le_terminal T j t
  have huT (j : ℕ) (t : ℝ≥0) : u j t ≤ T :=
    ((g j).monotone (hau j t)).trans_eq (uniform_dyadic_terminal_vertex T j)
  have hbmeas (r : ℝ≥0) (i : ι) : Measurable (fun y => b r y i) :=
    ((hb i).comp (continuous_const.prodMk continuous_id)).measurable
  have hσmeas (r : ℝ≥0) (i : ι) (k : κ) : Measurable (fun y => σ r y i k) :=
    ((hσ i k).comp (continuous_const.prodMk continuous_id)).measurable
  let M (i : ι) (t : ℝ≥0) : C(Path, ℝ) :=
    ⟨canonicalEulerMartingaleCoordinate T b x i t,
      continuous_canonicalEulerMartingaleCoordinate T t x i (hb i) (fun r y => hB r y i)⟩
  let Mn (i : ι) (j : ℕ) (t : ℝ≥0) : C(Path, ℝ) :=
    ⟨canonicalGridEulerNoise T (g j) b x i (a j t),
      continuous_canonicalGridEulerNoise T (g j) x i (a j t) (hb i)⟩
  let Q (i l : ι) (t : ℝ≥0) : C(Path, ℝ) :=
    ⟨canonicalEulerCompensatedProduct T b σ x i l t,
      continuous_canonicalEulerCompensatedProduct T t x i l hb hσ hB hC₀ hC⟩
  let Qn (i l : ι) (j : ℕ) (t : ℝ≥0) : C(Path, ℝ) :=
    ⟨canonicalGridEulerCompensatedProduct T (g j) b σ x i l (a j t),
      continuous_canonicalGridEulerCompensatedProduct T (g j) x i l (a j t) hb hσ⟩
  let D := 81 * boundedEulerGridFourthConstant κ B C T * (T : ℝ)^2
  let L := 8 * (D + (B * (T : ℝ))^4)
  let J := (Fintype.card κ : ℝ) * C^2 * (T : ℝ)
  have hD : 0 ≤ D := by
    dsimp [D]
    have := boundedEulerGridFourthConstant_nonneg κ B C T
    positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hCoord (i : ι) (t : ℝ≥0) (n : ℕ) :=
    eulerDyadicLaw_coordinate_fourth_moment hT (φ n) x i hbmeas hσmeas hW hW₂
      hB₀ hC₀ hB hC (hGaussian (φ n)) (hCov (φ n)) t
  have hMfour (i : ι) (t : ℝ≥0) (n : ℕ) : MemLp (M i t) 4 (Pn n : Measure Path) ∧
      (∫ p, (M i t p)^4 ∂(Pn n : Measure Path)) ≤ L := by
    let A := canonicalCoefficientIntegral T (fun r y => b r y i) t
    have hA : AEStronglyMeasurable A (Pn n : Measure Path) :=
      (continuous_canonicalCoefficientIntegral T t (hb i) (fun r y => hB r y i)).stronglyMeasurable.aestronglyMeasurable
    have hAb (p : Path) : ‖A p‖ ≤ B * (T : ℝ) :=
      (norm_canonicalCoefficientIntegral_le T t (fun r y => hB r y i) p).trans
        (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr (min_le_right t T)) hB₀)
    have h := memLp_and_integral_pow_four_sub_le_of_bound (hCoord i t n).1 hA hAb
    exact ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_left
      (add_le_add (hCoord i t n).2 le_rfl) (by norm_num))⟩
  have hMnfour (i : ι) (t : ℝ≥0) (n : ℕ) : MemLp (Mn i (φ n) t) 4 (Pn n : Measure Path) ∧
      (∫ p, (Mn i (φ n) t p)^4 ∂(Pn n : Measure Path)) ≤ L := by
    let j := φ n
    let A := canonicalGridCoefficientSum T (g j) (fun r y => b r y i) (a j t)
    have hA : AEStronglyMeasurable A (Pn n : Measure Path) :=
      (continuous_canonicalGridCoefficientSum T (g j) (hb i) (a j t)).stronglyMeasurable.aestronglyMeasurable
    have hAb (p : Path) : ‖A p‖ ≤ B * (T : ℝ) := by
      have h := norm_canonicalGridCoefficientSum_le T (g j) (fun r y => hB r y i) (a j t) p
      rw [show g j 0 = 0 from uniform_dyadic_first_vertex T j, NNReal.coe_zero, sub_zero] at h
      exact h.trans (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr (huT j t)) hB₀)
    have h := memLp_and_integral_pow_four_sub_le_of_bound (hCoord i (u j t) n).1 hA hAb
    exact ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_left
      (add_le_add (hCoord i (u j t) n).2 le_rfl) (by norm_num))⟩
  have hQsq (i l : ι) (t : ℝ≥0) (n : ℕ) : MemLp (Q i l t) 2 (Pn n : Measure Path) ∧
      (∫ p, (Q i l t p)^2 ∂(Pn n : Measure Path)) ≤ 2 * (L + J^2) := by
    let A := canonicalCoefficientIntegral T (eulerCovarianceCoefficient σ i l) t
    have hcovB := norm_eulerCovarianceCoefficient_le hC₀ hC i l
    have hA : AEStronglyMeasurable A (Pn n : Measure Path) :=
      (continuous_canonicalCoefficientIntegral T t
        (continuous_eulerCovarianceCoefficient hσ i l) hcovB).stronglyMeasurable.aestronglyMeasurable
    have hAb (p : Path) : ‖A p‖ ≤ J :=
      (norm_canonicalCoefficientIntegral_le T t hcovB p).trans
        (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr (min_le_right t T)) (by positivity))
    have hh := integral_sq_mul_le_of_four (hMfour i t n).1 (hMfour l t n).1
    have h := memLp_and_integral_sq_sub_le_of_bound hh.1 hA hAb
    refine ⟨h.1, h.2.trans ?_⟩
    have hp := hh.2.trans (mul_le_mul_of_nonneg_left
      (add_le_add (hMfour i t n).2 (hMfour l t n).2) (show (0 : ℝ) ≤ 1/2 by norm_num))
    simp only [Pi.mul_apply]
    linarith
  have hQnsq (i l : ι) (t : ℝ≥0) (n : ℕ) : MemLp (Qn i l (φ n) t) 2 (Pn n : Measure Path) ∧
      (∫ p, (Qn i l (φ n) t p)^2 ∂(Pn n : Measure Path)) ≤ 2 * (L + J^2) := by
    let j := φ n
    let A := canonicalGridCoefficientSum T (g j) (eulerCovarianceCoefficient σ i l) (a j t)
    have hcovB := norm_eulerCovarianceCoefficient_le hC₀ hC i l
    have hA : AEStronglyMeasurable A (Pn n : Measure Path) :=
      (continuous_canonicalGridCoefficientSum T (g j) (continuous_eulerCovarianceCoefficient hσ i l)
        (a j t)).stronglyMeasurable.aestronglyMeasurable
    have hAb (p : Path) : ‖A p‖ ≤ J := by
      have h := norm_canonicalGridCoefficientSum_le T (g j) hcovB (a j t) p
      rw [show g j 0 = 0 from uniform_dyadic_first_vertex T j, NNReal.coe_zero, sub_zero] at h
      exact h.trans (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr (huT j t)) (by positivity))
    have hh := integral_sq_mul_le_of_four (hMnfour i t n).1 (hMnfour l t n).1
    have h := memLp_and_integral_sq_sub_le_of_bound hh.1 hA hAb
    refine ⟨h.1, h.2.trans ?_⟩
    have hp := hh.2.trans (mul_le_mul_of_nonneg_left
      (add_le_add (hMnfour i t n).2 (hMnfour l t n).2) (show (0 : ℝ) ≤ 1/2 by norm_num))
    simp only [Pi.mul_apply]
    linarith
  have hInit : (P : Measure Path) {p | canonicalPathEval T 0 p = x} = 1 := by
    let S : Set Path := {p | canonicalPathEval T 0 p = x}
    have hS : IsClosed S := isClosed_eq (continuous_canonicalPathEval T 0) continuous_const
    have hEach (n : ℕ) : (Pn n : Measure Path) S = 1 := by
      let I := eulerDyadicInterpolant T (φ n) b σ W x
      have hm := measurable_eulerDyadicInterpolant (𝒢 := 𝒢) T (φ n) x hbmeas hσmeas
        (fun k => (hW k).stronglyAdapted)
      change μ.map I S = 1
      rw [Measure.map_apply hm hS.measurableSet]
      have hPre : I ⁻¹' S = univ := by
        ext ω
        simp only [S, mem_preimage, mem_univ, iff_true]
        exact eulerDyadicInterpolant_at_zero hT (φ n) b σ W x ω
      rw [hPre, measure_univ]
    have hLim := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hweak hS
    change Filter.limsup (fun n => (Pn n : Measure Path) S) atTop ≤ (P : Measure Path) S at hLim
    simp only [hEach, Filter.limsup_const] at hLim
    exact le_antisymm prob_le_one hLim
  refine ⟨hInit, ?_, ?_⟩
  · intro i
    refine martingale_of_exact_moving_continuous_tests hweak (M := M i)
      (Mn := fun n => Mn i (φ n))
      (stronglyAdapted_canonicalEulerMartingaleCoordinate T x i (hb i) (fun r y => hB r y i))
      (continuous_canonicalStoppedPath T) (canonicalPathNaturalFiltration_eq_comap_stopped T)
      (fun t => (tendsto_canonicalGridEulerNoise_ceiling T t x i (hb i) (fun r y => hB r y i)).comp hφ.tendsto_atTop)
      ?_ ?_ ?_
    · intro s t hst f n
      let j := φ n
      have h := eulerCanonicalGridNoise_past_test T (g j) (hgm j)
        (uniform_dyadic_terminal_vertex T j).le
        (eulerDyadicCeiling_monotone T j hst) (hau j t) (eulerDyadicCeiling_spec T j s)
        x i hbmeas hσmeas hW hW₂ hC f
      simp_rw [canonicalStoppedPath_clip_eq] at h
      exact h
    · intro t
      refine ⟨1 + L, by positivity, fun n => ?_⟩
      have h := integral_sq_le_one_add_integral_pow_four (hMfour i t n).1
      exact ⟨h.1, h.2.trans (add_le_add le_rfl (hMfour i t n).2)⟩
    · intro t
      refine ⟨1 + L, by positivity, fun n => ?_⟩
      have h := integral_sq_le_one_add_integral_pow_four (hMnfour i t n).1
      exact ⟨h.1, h.2.trans (add_le_add le_rfl (hMnfour i t n).2)⟩
  · intro i l
    refine martingale_of_exact_moving_continuous_tests hweak (M := Q i l)
      (Mn := fun n => Qn i l (φ n))
      (stronglyAdapted_canonicalEulerCompensatedProduct T x i l hb hσ hB hC₀ hC)
      (continuous_canonicalStoppedPath T) (canonicalPathNaturalFiltration_eq_comap_stopped T)
      (fun t => (tendsto_canonicalGridEulerCompensatedProduct_ceiling T t x i l hb hσ hB hC₀ hC).comp
        hφ.tendsto_atTop) ?_ ?_ ?_
    · intro s t hst f n
      let j := φ n
      have h := eulerCanonicalGridCompensatedProduct_past_test T (g j) (hgm j)
        (uniform_dyadic_terminal_vertex T j).le
        (eulerDyadicCeiling_monotone T j hst) (hau j t) (eulerDyadicCeiling_spec T j s)
        x i l hbmeas hσmeas hW hW₂ hC (hCov j) f
      simp_rw [canonicalStoppedPath_clip_eq] at h
      exact h
    · intro t
      exact ⟨2 * (L + J^2), by positivity, hQsq i l t⟩
    · intro t
      exact ⟨2 * (L + J^2), by positivity, hQnsq i l t⟩

#print axioms RoughHeston.eulerDyadicLaw_weak_limit_martingale_problem

end RoughHeston
