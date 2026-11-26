import EulerCoefficientIntervalMoments

/-! Fourth moments for the actual canonical Euler martingale-problem law. -/

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston

theorem memLp_four_of_integrable_pow_four {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    (hInt : Integrable (fun ω => f ω ^ 4) μ) : MemLp f 4 μ := by
  refine (integrable_norm_rpow_iff (p := 4) hf (by norm_num) (by simp)).1 ?_
  have he : (fun ω => ‖f ω‖ ^ (4 : ℝ≥0∞).toReal) = fun ω => f ω ^ 4 := by
    funext ω
    rw [ENNReal.toReal_ofNat, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity : 0 ≤ f ω^4)]
  rwa [he]

private theorem continuous_canonicalCoeff_time {ι : Type*} [Fintype ι]
    (T : ℝ≥0) {c : ℝ≥0 → (ι → ℝ) → ℝ} (hc : Continuous (Function.uncurry c))
    (p : CanonicalPath T (ι → ℝ)) :
    Continuous (fun t => canonicalCoefficientIntegral T c t p) := by
  let f (r : ℝ≥0) := c r (canonicalPathEval T r p)
  have hf : Continuous f := hc.comp
    (continuous_id.prodMk ((continuous_joint_pathEval T).comp (continuous_id.prodMk continuous_const)))
  have hF : Continuous (fun r : ℝ => f r.toNNReal) := hf.comp continuous_real_toNNReal
  have he (t : ℝ≥0) : canonicalCoefficientIntegral T c t p =
      ∫ r in (0 : ℝ)..(↑(min t T) : ℝ), f r.toNNReal :=
    integral_timeMeasureHorizon_eq_intervalIntegral hf.measurable _
  simp_rw [he]
  exact (intervalIntegral.differentiable_integral_of_continuous (a := 0) hF).continuous.comp
    (NNReal.continuous_coe.comp (continuous_id.min continuous_const))

/-- A canonical state increment is bounded in fourth moment by the
time-averaged fourth power of the drift and squared diagonal covariance. -/
theorem integral_fourth_canonicalEulerState_sub_le_energy
    {ι κ : Type*} [Fintype ι] [Fintype κ] {T : ℝ≥0}
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    {x : ι → ℝ} {μ : Measure (CanonicalPath T (ι → ℝ))} [IsProbabilityMeasure μ]
    (hInit : μ {p | canonicalPathEval T 0 p = x} = 1)
    (hb : ∀ i, Continuous (fun z : ℝ≥0 × (ι → ℝ) => b z.1 z.2 i))
    (hσ : ∀ i j, Continuous (fun z : ℝ≥0 × (ι → ℝ) => σ z.1 z.2 i j))
    {B C : ℝ} (hB : ∀ r y i, ‖b r y i‖ ≤ B)
    (hC₀ : 0 ≤ C) (hC : ∀ r y i j, ‖σ r y i j‖ ≤ C)
    (i : ι)
    (hM : Martingale (canonicalEulerMartingaleCoordinate T b x i)
      (canonicalPathNaturalFiltration T) μ)
    (hQ : Martingale (canonicalEulerCompensatedProduct T b σ x i i)
      (canonicalPathNaturalFiltration T) μ) {s t : ℝ≥0} (hst : s ≤ t) :
    let P := CanonicalPath T (ι → ℝ)
    let Δ := ((min t T : ℝ≥0) : ℝ) - ((min s T : ℝ≥0) : ℝ)
    let Z (p : P) := canonicalPathEval T t p i - canonicalPathEval T s p i
    let ν := eulerTimeSlice (min s T) (min t T)
    MemLp Z 4 μ ∧
      (∫ p, (Z p)^4 ∂μ) ≤
        8 * (Δ^3 * (∫ r, ∫ p : P, (b r (canonicalPathEval T r p) i)^4 ∂μ ∂ν) +
        (boundedMartingaleEvenPowerConstant 2).toReal * Δ *
          (∫ r, ∫ p : P, (eulerCovarianceCoefficient σ i i r (canonicalPathEval T r p))^2 ∂μ ∂ν)) := by
  dsimp only
  let P := CanonicalPath T (ι → ℝ)
  let D := canonicalCoefficientIntegral T (fun r y => b r y i)
  let M := canonicalEulerMartingaleCoordinate T b x i
  let c := eulerCovarianceCoefficient σ i i
  let A := canonicalCoefficientIntegral T c
  let Δ := ((min t T : ℝ≥0) : ℝ) - ((min s T : ℝ≥0) : ℝ)
  let ν := eulerTimeSlice (min s T) (min t T)
  have hCcm := continuous_eulerCovarianceCoefficient hσ i i
  have hCcb := norm_eulerCovarianceCoefficient_le hC₀ hC i i
  have hMat : Martingale (fun t => M t * M t - A t) (canonicalPathNaturalFiltration T) μ := by
    convert hQ using 1
    funext u p
    simp only [M, A, c, canonicalEulerCompensatedProduct, Pi.sub_apply, Pi.mul_apply]
  have hM₂ (r : ℝ≥0) : MemLp (M r) 2 μ := by
    have hSq := (canonicalEulerMartingaleCoordinate_sq_eq_covariance hInit hσ hC₀ hC i hQ r).1
    have hm := continuous_canonicalEulerMartingaleCoordinate T r x i (hb i) (fun r y => hB r y i)
    exact (memLp_two_iff_integrable_sq hm.stronglyMeasurable.aestronglyMeasurable).2 hSq
  have hMC (p : P) : Continuous (fun r => M r p) := by
    have hEval : Continuous (fun r => canonicalPathEval T r p i) := (continuous_apply i).comp
      ((continuous_joint_pathEval T).comp (continuous_id.prodMk continuous_const))
    exact (hEval.sub continuous_const).sub (continuous_canonicalCoeff_time T (hb i) p)
  have hAC (p : P) : Continuous (fun r => A r p) :=
    continuous_canonicalCoeff_time T hCcm p
  have hAM : ∀ᵐ p ∂μ, Monotone (fun r => A r p) :=
    Eventually.of_forall fun p => monotone_canonicalCoefficientIntegral_of_nonneg T hCcm hCcb
      (fun r y => Finset.sum_nonneg fun j _ => mul_self_nonneg (σ r y i j)) p
  have hASq := integral_pow_coefficientIntegral_sub_le T hCcm hCcb μ hst (Or.inl rfl : (2 : ℕ) = 2 ∨ 2 = 4)
  have hDFour := integral_pow_coefficientIntegral_sub_le T (hb i) (fun r y => hB r y i) μ hst
    (Or.inr rfl : (4 : ℕ) = 2 ∨ 4 = 4)
  have hNFour := continuous_raw_martingale_increment_fourth_integrable_le hM hM₂ hMC hMat hAC hAM hst hASq.1
  let U (p : P) := D t p - D s p
  let V (p : P) := M t p - M s p
  have hU₄ : MemLp U 4 μ := memLp_four_of_integrable_pow_four
    (((continuous_canonicalCoefficientIntegral T t (b := fun r y => b r y i) (hb i) (fun r y => hB r y i)).sub
      (continuous_canonicalCoefficientIntegral T s (b := fun r y => b r y i) (hb i) (fun r y => hB r y i))).stronglyMeasurable.aestronglyMeasurable)
      hDFour.1
  have hV₄ : MemLp V 4 μ := memLp_four_of_integrable_pow_four ((hM₂ t).sub (hM₂ s)).aestronglyMeasurable hNFour.1
  have he (p : P) : canonicalPathEval T t p i - canonicalPathEval T s p i = U p + V p := by
    dsimp [U, V, D, M, canonicalEulerMartingaleCoordinate]
    ring
  simp_rw [he]
  refine ⟨hU₄.add hV₄, (integral_pow_four_add_le hU₄ hV₄).trans ?_⟩
  have hMass := eulerTimeSlice_mass (min s T) (min t T) (min_le_min_right T hst)
  change (ν.real univ) = Δ at hMass
  have hDS : (∫ p : P, (U p)^4 ∂μ) ≤ Δ^3 *
      (∫ r, ∫ p : P, (b r (canonicalPathEval T r p) i)^4 ∂μ ∂ν) := by
    have h := hDFour.2
    change (∫ p : P, (U p)^4 ∂μ) ≤ (ν.real univ)^3 *
      (∫ r, ∫ p : P, (b r (canonicalPathEval T r p) i)^4 ∂μ ∂ν) at h
    rwa [hMass] at h
  have hCS : (∫ p : P, (A t p - A s p)^2 ∂μ) ≤ Δ *
      (∫ r, ∫ p : P, (c r (canonicalPathEval T r p))^2 ∂μ ∂ν) := by
    have h := hASq.2
    change (∫ p : P, (A t p - A s p)^2 ∂μ) ≤ (ν.real univ)^1 *
      (∫ r, ∫ p : P, (c r (canonicalPathEval T r p))^2 ∂μ ∂ν) at h
    rwa [hMass, pow_one] at h
  have hNS := hNFour.2.trans (mul_le_mul_of_nonneg_left hCS ENNReal.toReal_nonneg)
  have hUB := mul_le_mul_of_nonneg_left (add_le_add hDS hNS) (show (0 : ℝ) ≤ 8 by norm_num)
  exact hUB.trans_eq (by dsimp [Δ, c]; ring)

#print axioms RoughHeston.integral_fourth_canonicalEulerState_sub_le_energy

end RoughHeston
