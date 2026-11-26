import StochasticFoundation

open MeasureTheory Filter Set
open scoped MeasureTheory NNReal ENNReal BigOperators

namespace RoughHeston

variable {Ω ι κ : Type*} {m : MeasurableSpace Ω}
  [Fintype ι] [Fintype κ] {μ : Measure Ω} {𝒢 : Filtration ℝ≥0 m}

/-- Explicit Euler states along an ordered grid for a finite-dimensional
drift and diffusion matrix. -/
noncomputable def eulerGridState (grid : ℕ →o ℝ≥0)
    (b : ℝ≥0 → (ι → ℝ) → ι → ℝ) (σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ)
    (W : κ → ℝ≥0 → Ω → ℝ) (x : ι → ℝ) : ℕ → Ω → ι → ℝ
  | 0, _, i => x i
  | n + 1, ω, i =>
    let X := eulerGridState grid b σ W x n ω
    X i + b (grid n) X i * ((grid (n + 1) : ℝ) - (grid n : ℝ)) +
      ∑ j, σ (grid n) X i j * (W j (grid (n + 1)) ω - W j (grid n) ω)

theorem eulerGridState_stronglyAdapted (grid : ℕ →o ℝ≥0)
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    {W : κ → ℝ≥0 → Ω → ℝ} (x : ι → ℝ)
    (hb : ∀ t i, Measurable (fun y => b t y i))
    (hσ : ∀ t i j, Measurable (fun y => σ t y i j))
    (hW : ∀ j, StronglyAdapted 𝒢 (W j)) :
    StronglyAdapted (gridFiltration 𝒢 grid) (eulerGridState grid b σ W x) := by
  intro n
  induction n with
  | zero => exact stronglyMeasurable_const
  | succ n ih =>
    have hle : 𝒢 (grid n) ≤ 𝒢 (grid (n + 1)) := 𝒢.mono (grid.monotone n.le_succ)
    let X := eulerGridState grid b σ W x n
    have hX : StronglyMeasurable[𝒢 (grid (n + 1))] X := ih.mono hle
    let : MeasurableSpace Ω := 𝒢 (grid (n + 1))
    apply Measurable.stronglyMeasurable
    apply Measurable.of_eval
    intro i
    apply StronglyMeasurable.measurable
    change StronglyMeasurable[𝒢 (grid (n + 1))] (fun ω =>
      X ω i + b (grid n) (X ω) i * ((grid (n + 1) : ℝ) - (grid n : ℝ)) +
        ∑ j, σ (grid n) (X ω) i j * (W j (grid (n + 1)) ω - W j (grid n) ω))
    have hXi : StronglyMeasurable[𝒢 (grid (n + 1))] (fun ω => X ω i) :=
      ((measurable_pi_apply i).comp hX.measurable).stronglyMeasurable
    have hBi := ((hb (grid n) i).comp hX.measurable).stronglyMeasurable
    refine (hXi.add (hBi.mul stronglyMeasurable_const)).add ?_
    let : MeasurableSpace Ω := 𝒢 (grid (n + 1))
    apply Measurable.stronglyMeasurable
    exact Finset.measurable_sum _ fun j _ =>
      ((hσ (grid n) i j).comp hX.measurable).mul
        (((hW j (grid (n + 1))).sub ((hW j (grid n)).mono hle)).measurable)

/-- Each noise coordinate in the Euler recursion is a martingale on
the sampled joint filtration. -/
theorem eulerGridState_noise_martingale [IsFiniteMeasure μ] (grid : ℕ →o ℝ≥0)
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    {W : κ → ℝ≥0 → Ω → ℝ} (x : ι → ℝ) (i : ι)
    (hb : ∀ t i, Measurable (fun y => b t y i))
    (hσ : ∀ t i j, Measurable (fun y => σ t y i j))
    (hW : ∀ j, Martingale (W j) 𝒢 μ) (hW₂ : ∀ j t, MemLp (W j t) 2 μ)
    {C : ℝ} (hC : ∀ t y i j, ‖σ t y i j‖ ≤ C) :
    let X := eulerGridState grid b σ W x
    let a (j : κ) (n : ℕ) (ω : Ω) := σ (grid n) (X n ω) i j
    Martingale (fun n ω => ∑ j, gridIntegral grid (a j) (W j) n ω)
      (gridFiltration 𝒢 grid) μ := by
  intro X a
  have hX := eulerGridState_stronglyAdapted grid x hb hσ (fun j => (hW j).stronglyAdapted)
  have hA (j : κ) (n : ℕ) : StronglyMeasurable[𝒢 (grid n)] (a j n) :=
    ((hσ (grid n) i j).comp (hX n).measurable).stronglyMeasurable
  have ht (j : κ) (n : ℕ) : MemLp (a j n) ⊤ μ := MemLp.of_bound
    ((hA j n).mono (𝒢.le _)).aestronglyMeasurable C (ae_of_all μ fun ω => hC _ _ _ _)
  have hm (j : κ) : Martingale (gridIntegral grid (a j) (W j)) (gridFiltration 𝒢 grid) μ :=
    grid_integral_martingale grid (hW j) (hW₂ j) (hA j) (ht j)
  classical
  have hsum (s : Finset κ) :
      Martingale (fun n ω => ∑ j ∈ s, gridIntegral grid (a j) (W j) n ω)
        (gridFiltration 𝒢 grid) μ := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      change Martingale (0 : ℕ → Ω → ℝ) (gridFiltration 𝒢 grid) μ
      exact martingale_zero ℝ (gridFiltration 𝒢 grid) μ
    | insert j s hj ih =>
      convert (hm j).add ih using 1
      ext n ω
      simp only [Finset.sum_insert hj, Pi.add_apply]
  exact hsum Finset.univ

end RoughHeston

#print axioms RoughHeston.eulerGridState_stronglyAdapted
#print axioms RoughHeston.eulerGridState_noise_martingale
