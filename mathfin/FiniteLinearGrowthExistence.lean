import LinearGrowthEulerExistence
import FiniteGaussianEulerDriver

/-! Existence of the bounded continuous finite-dimensional martingale problem. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston

/-- The canonical martingale problem for continuous coefficients of linear growth in
any two finite state and noise index sets has a solution. -/
theorem exists_linearGrowthEuler_martingale_problem {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    {T : ℝ≥0} (hT : 0 < T)
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    (x : ι → ℝ)
    (hb : ∀ i, Continuous (fun z : ℝ≥0 × (ι → ℝ) => b z.1 z.2 i))
    (hσ : ∀ i j, Continuous (fun z : ℝ≥0 × (ι → ℝ) => σ z.1 z.2 i j))
    {L : ℝ} (hL : 0 ≤ L)
    (hB : ∀ t y i, ‖b t y i‖ ≤ L*(1+‖y‖)) (hC : ∀ t y i j, ‖σ t y i j‖ ≤ L*(1+‖y‖))
    : ∃ P : ProbabilityMeasure (CanonicalPath T (ι → ℝ)),
      (P : Measure (CanonicalPath T (ι → ℝ))) {p | canonicalPathEval T 0 p = x} = 1 ∧
      (∀ i, Martingale (canonicalEulerMartingaleCoordinate T b x i)
        (canonicalPathNaturalFiltration T) (P : Measure _)) ∧
      (∀ i l, Martingale (canonicalEulerCompensatedProduct T b σ x i l)
        (canonicalPathNaturalFiltration T) (P : Measure _)) := by
  obtain ⟨Ω, m, μ, hμ, F, W, hm, h₂, law, cov⟩ := exists_finite_gaussian_euler_driver κ
  let : MeasurableSpace Ω := m
  let : IsProbabilityMeasure μ := hμ
  apply exists_linearGrowthEuler_martingale_problem_with_driver hT x hb hσ hm h₂
    hL hB hC
  · intro j k a
    exact law a _ _ ((uniformDyadicGrid_strictMono hT j k.lt_succ_self).le)
  · intro j k a b
    exact cov a b _ _ ((uniformDyadicGrid_strictMono hT j k.lt_succ_self).le)

#print axioms exists_linearGrowthEuler_martingale_problem

end RoughHeston
