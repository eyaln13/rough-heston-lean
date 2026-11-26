import LinearGrowthEulerExistence
import FiniteEulerMartingaleExistence
import WeakLimitMomentTests

/-! The squared uniform path norm survives the radial-cutoff construction. -/

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston

/-- In the weak construction by radial cutoffs, keep the second moment of
the uniform path norm along with the martingale problem. -/
theorem exists_linearGrowthEuler_martingale_problem_and_sup_moment_of_cutoffs
    {ι κ : Type*} [Fintype ι] [Fintype κ] {T : ℝ≥0} (hT : 0 < T)
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    (x : ι → ℝ)
    (hb : ∀ i, Continuous (fun z : ℝ≥0 × (ι → ℝ) => b z.1 z.2 i))
    (hσ : ∀ i j, Continuous (fun z : ℝ≥0 × (ι → ℝ) => σ z.1 z.2 i j))
    {L : ℝ} (hL : 0 ≤ L)
    (hB : ∀ t y i, ‖b t y i‖ ≤ L*(1+‖y‖)) (hC : ∀ t y i j, ‖σ t y i j‖ ≤ L*(1+‖y‖))
    (hExists : ∀ n : ℕ, ∃ Pn : ProbabilityMeasure (CanonicalPath T (ι → ℝ)),
      (Pn : Measure (CanonicalPath T (ι → ℝ))) {p | canonicalPathEval T 0 p = x} = 1 ∧
      (∀ i, Martingale (canonicalEulerMartingaleCoordinate T (radialEulerDrift ((n : ℝ)+1) b) x i)
        (canonicalPathNaturalFiltration T) (Pn : Measure _)) ∧
      (∀ i l, Martingale (canonicalEulerCompensatedProduct T (radialEulerDrift ((n : ℝ)+1) b)
        (radialEulerDiffusion ((n : ℝ)+1) σ) x i l)
        (canonicalPathNaturalFiltration T) (Pn : Measure _))) :
    ∃ P : ProbabilityMeasure (CanonicalPath T (ι → ℝ)),
      MemLp (fun p : CanonicalPath T (ι → ℝ) => ‖p‖) 2 (P : Measure _) ∧
      (P : Measure (CanonicalPath T (ι → ℝ))) {p | canonicalPathEval T 0 p = x} = 1 ∧
      (∀ i, Martingale (canonicalEulerMartingaleCoordinate T b x i)
        (canonicalPathNaturalFiltration T) (P : Measure _)) ∧
      (∀ i l, Martingale (canonicalEulerCompensatedProduct T b σ x i l)
        (canonicalPathNaturalFiltration T) (P : Measure _)) := by
  classical
  choose Pn hInit hM hQ using hExists
  obtain ⟨P, φ, hφ, hweak⟩ :=
    radialEulerMartingaleProblem_subsequence hT x hb hσ hL hB hC Pn hInit hM hQ
  let K := 6 * (Fintype.card ι : ℝ) * ((T : ℝ) + Fintype.card κ) * L^2
  let H := 2 * (3 * (∑ i, (x i)^2) + K * (T : ℝ)) * Real.exp ((2*K+1) * (T : ℝ))
  let Bsup := 3 * (∑ i, (x i)^2) + 6 * (Fintype.card ι : ℝ) * L^2 *
    (T : ℝ) * ((T : ℝ) + 4 * Fintype.card κ) * (1 + H)
  have hSup (n : ℕ) :
      Integrable (fun p : CanonicalPath T (ι → ℝ) => ‖p‖^2) (Pn n : Measure _) ∧
        (∫ p : CanonicalPath T (ι → ℝ), ‖p‖^2 ∂(Pn n : Measure _)) ≤ Bsup := by
    let R : ℝ := n+1
    have hR : 0 < R := by dsimp [R]; positivity
    have hP : 0 ≤ L*(1+R) := by positivity
    have hB' (i : ι) := radialEulerCoefficient_bounds hR hL (fun r z => hB r z i)
    have hC' (i : ι) (j : κ) := radialEulerCoefficient_bounds hR hL (fun r z => hC r z i j)
    exact canonicalEulerPath_sq_norm_le_linear_growth (hInit n)
      (fun i => continuous_comp_radialTruncation hR (c := fun r y => b r y i) (hb i))
      (fun i j => continuous_comp_radialTruncation hR (c := fun r y => σ r y i j) (hσ i j))
      hP hP hL (fun t y i => (hB' i).1 t y) (fun t y i j => (hC' i j).1 t y)
      (fun t y i => (hB' i).2 t y) (fun t y i j => (hC' i j).2 t y)
      (hM n) (fun i => hQ n i i)
  have hLp (n : ℕ) : MemLp (fun p : CanonicalPath T (ι → ℝ) => ‖p‖) 2 (Pn n : Measure _) :=
    (memLp_two_iff_integrable_sq continuous_norm.aestronglyMeasurable).2 (hSup n).1
  have hP₂ := (weak_limit_memLp_two_and_sq_moment_bound hweak continuous_norm
    (fun n => hLp (φ n)) (fun n => (hSup (φ n)).2)).1
  exact ⟨P, hP₂, radialEulerLaw_weak_limit_martingale_problem x hb hσ hL hB hC Pn hInit hM hQ hφ hweak⟩

/-- Unconditional finite-dimensional existence retaining the uniform path moment. -/
theorem exists_linearGrowthEuler_martingale_problem_and_sup_moment
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] {T : ℝ≥0} (hT : 0 < T)
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    (x : ι → ℝ)
    (hb : ∀ i, Continuous (fun z : ℝ≥0 × (ι → ℝ) => b z.1 z.2 i))
    (hσ : ∀ i j, Continuous (fun z : ℝ≥0 × (ι → ℝ) => σ z.1 z.2 i j))
    {L : ℝ} (hL : 0 ≤ L)
    (hB : ∀ t y i, ‖b t y i‖ ≤ L*(1+‖y‖)) (hC : ∀ t y i j, ‖σ t y i j‖ ≤ L*(1+‖y‖)) :
    ∃ P : ProbabilityMeasure (CanonicalPath T (ι → ℝ)),
      MemLp (fun p : CanonicalPath T (ι → ℝ) => ‖p‖) 2 (P : Measure _) ∧
      (P : Measure (CanonicalPath T (ι → ℝ))) {p | canonicalPathEval T 0 p = x} = 1 ∧
      (∀ i, Martingale (canonicalEulerMartingaleCoordinate T b x i)
        (canonicalPathNaturalFiltration T) (P : Measure _)) ∧
      (∀ i l, Martingale (canonicalEulerCompensatedProduct T b σ x i l)
        (canonicalPathNaturalFiltration T) (P : Measure _)) := by
  apply exists_linearGrowthEuler_martingale_problem_and_sup_moment_of_cutoffs hT x hb hσ hL hB hC
  intro n
  let R : ℝ := n+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hP : 0 ≤ L*(1+R) := by positivity
  exact exists_boundedEuler_martingale_problem (b := radialEulerDrift R b)
    (σ := radialEulerDiffusion R σ) hT x
    (fun i => continuous_comp_radialTruncation hR (c := fun r y => b r y i) (hb i))
    (fun i j => continuous_comp_radialTruncation hR (c := fun r y => σ r y i j) (hσ i j)) hP hP
    (fun t y i => (radialEulerCoefficient_bounds hR hL (fun r z => hB r z i)).1 t y)
    (fun t y i j => (radialEulerCoefficient_bounds hR hL (fun r z => hC r z i j)).1 t y)

#print axioms RoughHeston.exists_linearGrowthEuler_martingale_problem_and_sup_moment_of_cutoffs
#print axioms RoughHeston.exists_linearGrowthEuler_martingale_problem_and_sup_moment

end RoughHeston
