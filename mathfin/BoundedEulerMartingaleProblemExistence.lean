import EulerWeakMartingaleProblem

/-! Existence of the bounded continuous finite-dimensional martingale problem. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston

/-- Existence for bounded continuous coefficients from the actual dyadic
Euler laws, given a vector driver with Gaussian components and diagonal
predictable step covariance. -/
theorem exists_boundedEuler_martingale_problem_with_driver {Ω ι κ : Type*}
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
    : ∃ P : ProbabilityMeasure (CanonicalPath T (ι → ℝ)),
      (P : Measure (CanonicalPath T (ι → ℝ))) {p | canonicalPathEval T 0 p = x} = 1 ∧
      (∀ i, Martingale (canonicalEulerMartingaleCoordinate T b x i)
        (canonicalPathNaturalFiltration T) (P : Measure _)) ∧
      (∀ i l, Martingale (canonicalEulerCompensatedProduct T b σ x i l)
        (canonicalPathNaturalFiltration T) (P : Measure _)) := by
  have hbmeas (r : ℝ≥0) (i : ι) : Measurable (fun y => b r y i) :=
    ((hb i).comp (continuous_const.prodMk continuous_id)).measurable
  have hσmeas (r : ℝ≥0) (i : ι) (k : κ) : Measurable (fun y => σ r y i k) :=
    ((hσ i k).comp (continuous_const.prodMk continuous_id)).measurable
  obtain ⟨P, φ, hφ, hweak⟩ := eulerLinearInterpolationLaw_subsequence hT
    (uniformDyadicGrids T).grid (fun j => 2^j)
    (fun j k _ => uniformDyadicGrid_strictMono hT j k.lt_succ_self)
    (uniform_dyadic_first_vertex T) (uniform_dyadic_terminal_vertex T)
    x hbmeas hσmeas hW hW₂ hB₀ hC₀ hB hC hGaussian hCov
  refine ⟨P, eulerDyadicLaw_weak_limit_martingale_problem hT x hb hσ hW hW₂
    hB₀ hC₀ hB hC hGaussian hCov hφ ?_⟩
  exact hweak

#print axioms RoughHeston.exists_boundedEuler_martingale_problem_with_driver

end RoughHeston
