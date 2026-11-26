import EulerRemoveSpatialTruncation
import BoundedEulerMartingaleProblemExistence

/-! Existence for continuous coefficients with linear growth. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston

/-- Continuous finite-dimensional coefficients of common linear growth
have a canonical martingale-problem solution, using the actual Euler and
radial-cutoff approximations supplied by a Gaussian vector driver. -/
theorem exists_linearGrowthEuler_martingale_problem_with_driver {Ω ι κ : Type*}
    {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    [Fintype ι] [Fintype κ] [DecidableEq κ] {𝒢 : Filtration ℝ≥0 m}
    {T : ℝ≥0} (hT : 0 < T)
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    {W : κ → ℝ≥0 → Ω → ℝ} (x : ι → ℝ)
    (hb : ∀ i, Continuous (fun z : ℝ≥0 × (ι → ℝ) => b z.1 z.2 i))
    (hσ : ∀ i j, Continuous (fun z : ℝ≥0 × (ι → ℝ) => σ z.1 z.2 i j))
    (hW : ∀ j, Martingale (W j) 𝒢 μ) (hW₂ : ∀ j t, MemLp (W j t) 2 μ)
    {L : ℝ} (hL : 0 ≤ L)
    (hB : ∀ t y i, ‖b t y i‖ ≤ L*(1+‖y‖)) (hC : ∀ t y i j, ‖σ t y i j‖ ≤ L*(1+‖y‖))
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
  classical
  have hExist (n : ℕ) :
      ∃ Pn : ProbabilityMeasure (CanonicalPath T (ι → ℝ)),
        (Pn : Measure (CanonicalPath T (ι → ℝ))) {p | canonicalPathEval T 0 p = x} = 1 ∧
        (∀ i, Martingale (canonicalEulerMartingaleCoordinate T (radialEulerDrift ((n : ℝ)+1) b) x i)
          (canonicalPathNaturalFiltration T) (Pn : Measure _)) ∧
        (∀ i l, Martingale (canonicalEulerCompensatedProduct T (radialEulerDrift ((n : ℝ)+1) b)
          (radialEulerDiffusion ((n : ℝ)+1) σ) x i l)
          (canonicalPathNaturalFiltration T) (Pn : Measure _)) := by
    let R : ℝ := n+1
    let B : ℝ := L*(1+R)
    have hR : 0 < R := by dsimp [R]; positivity
    have hB₀ : 0 ≤ B := by dsimp [B, R]; positivity
    have hb' (i : ι) := continuous_comp_radialTruncation hR (c := fun r y => b r y i) (hb i)
    have hσ' (i : ι) (j : κ) := continuous_comp_radialTruncation hR (c := fun r y => σ r y i j) (hσ i j)
    have hB' (t : ℝ≥0) (y : ι → ℝ) (i : ι) := (radialEulerCoefficient_bounds hR hL (fun r z => hB r z i)).1 t y
    have hC' (t : ℝ≥0) (y : ι → ℝ) (i : ι) (j : κ) := (radialEulerCoefficient_bounds hR hL (fun r z => hC r z i j)).1 t y
    exact exists_boundedEuler_martingale_problem_with_driver (b := radialEulerDrift R b)
      (σ := radialEulerDiffusion R σ) hT x hb' hσ' hW hW₂ hB₀ hB₀ hB' hC' hGaussian hCov
  choose Pn hInit hM hQ using hExist
  obtain ⟨P, φ, hφ, hweak⟩ :=
    radialEulerMartingaleProblem_subsequence hT x hb hσ hL hB hC Pn hInit hM hQ
  exact ⟨P, radialEulerLaw_weak_limit_martingale_problem x hb hσ hL hB hC Pn hInit hM hQ hφ hweak⟩

#print axioms RoughHeston.exists_linearGrowthEuler_martingale_problem_with_driver

end RoughHeston
