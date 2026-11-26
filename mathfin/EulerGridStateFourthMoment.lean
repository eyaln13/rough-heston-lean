import EulerGridFourthMoment

/-! Fourth moments of the bounded-coefficient Euler state. -/

open MeasureTheory ProbabilityTheory Filter
open scoped MeasureTheory NNReal ENNReal

namespace RoughHeston

variable {Ω ι κ : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℝ≥0 m} [Fintype ι] [Fintype κ]

private theorem integrable_four (f : Ω → ℝ) (hf : MemLp f 4 μ) :
    Integrable (fun ω => f ω ^ 4) μ := by
  have h := hf.integrable_norm_pow (p := 4) (by decide)
  convert h using 1
  ext ω
  rw [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity : 0 ≤ f ω ^ 4)]

omit [Fintype ι] in
private theorem abs_sub_le_euler_drift_elapsed (grid : ℕ →o ℝ≥0)
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    {W : κ → ℝ≥0 → Ω → ℝ} (x : ι → ℝ) (i : ι)
    {B : ℝ} (hB : ∀ t y i, ‖b t y i‖ ≤ B) {a z : ℕ} (haz : a ≤ z) (ω : Ω) :
    |(eulerGridState grid b σ W x z ω i - eulerGridState grid b σ W x a ω i) -
      (eulerGridNoise grid b σ W x i z ω - eulerGridNoise grid b σ W x i a ω)| ≤
        B * ((grid z : ℝ) - (grid a : ℝ)) := by
  let X (n : ℕ) := eulerGridState grid b σ W x n ω i
  let N (n : ℕ) := eulerGridNoise grid b σ W x i n ω
  let D (n : ℕ) := X n - X a - (N n - N a)
  change |D z| ≤ _
  induction z, haz using Nat.le_induction with
  | base => simp [D]
  | succ n hn ih =>
    let d := b (grid n) (eulerGridState grid b σ W x n ω) i
    let Δ := (grid (n + 1) : ℝ) - (grid n : ℝ)
    have hΔ : 0 ≤ Δ := sub_nonneg.mpr (NNReal.coe_le_coe.mpr (grid.monotone n.le_succ))
    have hX : X (n + 1) = X n + d * Δ + eulerGridNoiseIncrement grid b σ W x i n ω := by
      dsimp only [X, d, Δ, eulerGridNoiseIncrement]
      rw [eulerGridState]
    have hN : N (n + 1) = N n + eulerGridNoiseIncrement grid b σ W x i n ω := by
      simp only [N, eulerGridNoise, runningSum_succ, Pi.add_apply]
    have hD : D (n + 1) = D n + d * Δ := by
      dsimp only [D]
      rw [hX,hN]
      ring
    calc
      _ = |D n + d * Δ| := by rw [hD]
      _ ≤ |D n| + |d * Δ| := abs_add_le _ _
      _ = |D n| + |d| * Δ := by rw [abs_mul, abs_of_nonneg hΔ]
      _ ≤ B * ((grid n : ℝ) - (grid a : ℝ)) + B * Δ :=
        add_le_add ih (mul_le_mul_of_nonneg_right (hB _ _ _) hΔ)
      _ = _ := by dsimp [Δ]; ring

/-- Each coordinate of a bounded Euler state satisfies a fourth-moment
bound on every block, with the drift contributing only order elapsed time
to the fourth power. -/
theorem integral_eulerGridState_sub_fourth_le [DecidableEq κ] [IsProbabilityMeasure μ]
    (grid : ℕ →o ℝ≥0) {b : ℝ≥0 → (ι → ℝ) → ι → ℝ}
    {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ} {W : κ → ℝ≥0 → Ω → ℝ} (x : ι → ℝ) (i : ι)
    (hb : ∀ t i, Measurable (fun y => b t y i))
    (hσ : ∀ t i j, Measurable (fun y => σ t y i j))
    (hW : ∀ j, Martingale (W j) 𝒢 μ) (hW₂ : ∀ j t, MemLp (W j t) 2 μ)
    {B C : ℝ} (_hB₀ : 0 ≤ B) (hC₀ : 0 ≤ C)
    (hB : ∀ t y i, ‖b t y i‖ ≤ B) (hC : ∀ t y i j, ‖σ t y i j‖ ≤ C)
    (hGaussian : ∀ n j, HasLaw (W j (grid (n + 1)) - W j (grid n))
      (gaussianReal 0 (grid (n + 1) - grid n)) μ)
    (hCov : ∀ n j k, μ[(W j (grid (n + 1)) - W j (grid n)) *
        (W k (grid (n + 1)) - W k (grid n)) | 𝒢 (grid n)] =ᵐ[μ]
      fun _ => if j = k then ((grid (n + 1) : ℝ) - (grid n : ℝ)) else 0)
    {a z : ℕ} (haz : a ≤ z) :
    MemLp (fun ω => eulerGridState grid b σ W x z ω i - eulerGridState grid b σ W x a ω i) 4 μ ∧
    (∫ ω, (eulerGridState grid b σ W x z ω i - eulerGridState grid b σ W x a ω i)^4 ∂μ) ≤
      8 * (B * ((grid z : ℝ) - (grid a : ℝ)))^4 +
      8 * (4 * ((Fintype.card κ : ℝ) * C^2)^2 +
        3 * ((Fintype.card κ : ℝ)^4 * C^4 * standardGaussianFourthMoment)) *
        ((grid z : ℝ) - (grid a : ℝ))^2 := by
  let X (k : ℕ) (ω : Ω) := eulerGridState grid b σ W x k ω i
  let d := eulerGridNoiseIncrement grid b σ W x i
  let N := eulerGridNoise grid b σ W x i
  let Y : Ω → ℝ := X z - X a
  let V : Ω → ℝ := N z - N a
  let D := Y - V
  let Δ := (grid z : ℝ) - (grid a : ℝ)
  let K := 4 * ((Fintype.card κ : ℝ) * C^2)^2 +
        3 * ((Fintype.card κ : ℝ)^4 * C^4 * standardGaussianFourthMoment)
  have hΔ : 0 ≤ Δ := sub_nonneg.mpr (NNReal.coe_le_coe.mpr (grid.monotone haz))
  have hX := eulerGridState_stronglyAdapted grid x hb hσ (fun j => (hW j).stronglyAdapted)
  have hXm (n : ℕ) : StronglyMeasurable[m] (X n) :=
    (((measurable_pi_apply i).comp (hX n).measurable).stronglyMeasurable).mono (𝒢.le _)
  have hN₄ (n : ℕ) : MemLp (N n) 4 μ := by
    refine memLp_runningSum (d := d) (fun k => ?_) n
    let a (j : κ) (ω : Ω) := σ (grid k) (eulerGridState grid b σ W x k ω) i j
    let δ (j : κ) := W j (grid (k + 1)) - W j (grid k)
    have ha (j : κ) : StronglyMeasurable[𝒢 (grid k)] (a j) :=
      ((hσ _ i j).comp (hX k).measurable).stronglyMeasurable
    have hA (j : κ) : MemLp (a j) ⊤ μ :=
      memLp_top_of_bound ((ha j).mono (𝒢.le _)).aestronglyMeasurable C
        (Eventually.of_forall fun ω => hC _ _ _ _)
    have hδ (j : κ) : MemLp (δ j) 4 μ := (hGaussian k j).memLp
      (by simpa using memLp_id_gaussianReal (μ := 0) (v := grid (k + 1) - grid k) (4 : ℝ≥0))
    change MemLp (fun ω => ∑ j, a j ω * δ j ω) 4 μ
    exact memLp_finsetSum Finset.univ fun j _ => (hA j).mul (hδ j)
  have hV₄ : MemLp V 4 μ := (hN₄ z).sub (hN₄ a)
  have hBdd (ω : Ω) : |D ω| ≤ B * Δ :=
    abs_sub_le_euler_drift_elapsed grid x i hB haz ω
  have hD₄ : MemLp D 4 μ := MemLp.of_bound
    (((hXm z).sub (hXm a)).aestronglyMeasurable.sub hV₄.aestronglyMeasurable) (B * Δ)
    (Eventually.of_forall hBdd)
  have hEq (ω : Ω) : Y ω = D ω + V ω := by simp [D, Pi.sub_apply]
  have hY₄ : MemLp Y 4 μ := MemLp.ae_eq (Eventually.of_forall fun ω => (hEq ω).symm) (hD₄.add hV₄)
  refine ⟨hY₄, ?_⟩
  have hPoint (ω : Ω) : Y ω ^ 4 ≤ 8 * (B * Δ)^4 + 8 * V ω ^ 4 := by
    rw [hEq]
    have hDpow : D ω ^ 4 ≤ (B * Δ)^4 := by
      have h := pow_le_pow_left₀ (abs_nonneg _) (hBdd ω) 4
      rwa [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ D ω ^ 4)] at h
    have hFirst : (D ω + V ω)^4 ≤ 8 * (D ω ^ 4 + V ω ^ 4) := by
      have h1 : (D ω + V ω)^2 ≤ 2 * (D ω ^ 2 + V ω ^ 2) := by
        nlinarith [sq_nonneg (D ω - V ω)]
      have h2 : (D ω ^ 2 + V ω ^ 2)^2 ≤ 2 * (D ω ^ 4 + V ω ^4) := by
        nlinarith [sq_nonneg (D ω ^ 2 - V ω ^ 2)]
      nlinarith [pow_le_pow_left₀ (sq_nonneg (D ω + V ω)) h1 2]
    linarith
  have hV4 := integrable_four V hV₄
  have hNoise : (∫ ω, V ω ^ 4 ∂μ) ≤ K * Δ^2 :=
    integral_eulerGridNoise_sub_fourth_le grid x i hb hσ hW hW₂ hC₀ hC hGaussian hCov haz
  change (∫ ω, Y ω ^ 4 ∂μ) ≤ 8 * (B * Δ)^4 + 8 * K * Δ^2
  calc
    _ ≤ ∫ ω, 8 * (B * Δ)^4 + 8 * V ω ^ 4 ∂μ :=
      integral_mono (integrable_four Y hY₄) ((integrable_const _).add (hV4.const_mul 8)) hPoint
    _ = 8 * (B * Δ)^4 + 8 * (∫ ω, V ω ^ 4 ∂μ) := by
      rw [integral_add (integrable_const _) (hV4.const_mul 8)]
      simp [integral_const_mul]
    _ ≤ _ := by linarith

#print axioms RoughHeston.integral_eulerGridState_sub_fourth_le

end RoughHeston
