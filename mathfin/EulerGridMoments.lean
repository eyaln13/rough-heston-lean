import EulerGridCovariance
import DensityMartingalePairing

/-! Increment moment estimates for the Euler grid. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped MeasureTheory NNReal ENNReal BigOperators

namespace RoughHeston

variable {Ω ι κ : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℝ≥0 m} [Fintype ι] [Fintype κ]

private theorem real_grid_sub_nonneg (grid : ℕ →o ℝ≥0) {a b : ℕ} (hab : a ≤ b) :
    0 ≤ ((grid b : ℝ) - (grid a : ℝ)) :=
  sub_nonneg.mpr (NNReal.coe_le_coe.mpr (grid.monotone hab))

private theorem abs_runningSum_sub_le_grid (grid : ℕ →o ℝ≥0)
    {d : ℕ → Ω → ℝ} {C : ℝ}
    (h : ∀ n ω, |d n ω| ≤ C * ((grid (n + 1) : ℝ) - (grid n : ℝ)))
    {a b : ℕ} (hab : a ≤ b) (ω : Ω) :
    |runningSum d b ω - runningSum d a ω| ≤ C * ((grid b : ℝ) - (grid a : ℝ)) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [runningSum_succ, Pi.add_apply]
    calc
      _ = |(runningSum d n ω - runningSum d a ω) + d n ω| := by
        congr 1
        ring
      _ ≤ |runningSum d n ω - runningSum d a ω| + |d n ω| := abs_add_le _ _
      _ ≤ C * ((grid n : ℝ) - (grid a : ℝ)) +
          C * ((grid (n + 1) : ℝ) - (grid n : ℝ)) := add_le_add ih (h n ω)
      _ = _ := by ring

private theorem integral_sq_sub_eq_compensator [IsFiniteMeasure μ] {F : Filtration ℕ m}
    {N A : ℕ → Ω → ℝ} (hN : Martingale N F μ)
    (hQ : Martingale (fun n ω => N n ω ^ 2 - A n ω) F μ)
    (hN₂ : ∀ n, MemLp (N n) 2 μ) {a b : ℕ} (hab : a ≤ b) :
    (∫ ω, (N b ω - N a ω)^2 ∂μ) = ∫ ω, A b ω - A a ω ∂μ := by
  have hA (n : ℕ) : Integrable (A n) μ := by
    have hi := (hN₂ n).integrable_sq.sub (hQ.integrable n)
    exact hi.congr (Eventually.of_forall fun ω => by
      change N n ω ^ 2 - (N n ω ^ 2 - A n ω) = A n ω
      ring)
  have hCross :
      (∫ ω, N b ω * N a ω ∂μ) = ∫ ω, N a ω ^ 2 ∂μ := by
    simpa only [pow_two] using integral_martingale_mul_past_of_memLp_two hN hab
      (hN.stronglyMeasurable a).aestronglyMeasurable (hN₂ a) (hN₂ b)
  have hQeq :
      (∫ ω, N b ω ^ 2 - A b ω ∂μ) = ∫ ω, N a ω ^ 2 - A a ω ∂μ :=
    (integral_condExp (F.le a)).symm.trans (integral_congr_ae (hQ.condExp_ae_eq hab))
  rw [integral_sub (hN₂ b).integrable_sq (hA b),
    integral_sub (hN₂ a).integrable_sq (hA a)] at hQeq
  have hProd : Integrable (fun ω => N b ω * N a ω) μ :=
    (hN₂ b).integrable_mul (hN₂ a)
  have hSum : Integrable (fun ω => N b ω ^ 2 + N a ω ^ 2) μ :=
    (hN₂ b).integrable_sq.add (hN₂ a).integrable_sq
  calc
    _ = ∫ ω, (N b ω ^ 2 + N a ω ^ 2) - 2 * (N b ω * N a ω) ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun _ => by ring
    _ = _ := by
      rw [integral_sub hSum (hProd.const_mul 2),
        integral_add (hN₂ b).integrable_sq (hN₂ a).integrable_sq,
        integral_const_mul, hCross, integral_sub (hA b) (hA a)]
      linarith

variable (grid : ℕ →o ℝ≥0)
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    {W : κ → ℝ≥0 → Ω → ℝ} (x : ι → ℝ) (i : ι)

private theorem eulerGridNoise_memLp
    (hb : ∀ t i, Measurable (fun y => b t y i))
    (hσ : ∀ t i j, Measurable (fun y => σ t y i j))
    (hW : ∀ j, StronglyAdapted 𝒢 (W j)) (hW₂ : ∀ j t, MemLp (W j t) 2 μ)
    {C : ℝ} (hC : ∀ t y i j, ‖σ t y i j‖ ≤ C) (n : ℕ) :
    MemLp (eulerGridNoise grid b σ W x i n) 2 μ := by
  have hX := eulerGridState_stronglyAdapted grid x hb hσ hW
  apply memLp_runningSum _ n
  intro k
  let a (j : κ) (ω : Ω) := σ (grid k) (eulerGridState grid b σ W x k ω) i j
  have hA (j : κ) : StronglyMeasurable[𝒢 (grid k)] (a j) :=
    ((hσ _ i j).comp (hX k).measurable).stronglyMeasurable
  have hTop (j : κ) : MemLp (a j) ⊤ μ :=
    memLp_top_of_bound ((hA j).mono (𝒢.le _)).aestronglyMeasurable C
      (Eventually.of_forall fun ω => hC _ _ _ _)
  change MemLp (fun ω => ∑ j, a j ω * (W j (grid (k + 1)) ω - W j (grid k) ω)) 2 μ
  exact memLp_finsetSum Finset.univ fun j _ => (hTop j).mul ((hW₂ j _).sub (hW₂ j _))

/-- The covariance compensator gives a uniform second-moment estimate
for arbitrary blocks of Euler noise, with the exact time increment. -/
theorem integral_eulerGridNoise_sub_sq_le [IsProbabilityMeasure μ] [DecidableEq κ]
    (hb : ∀ t i, Measurable (fun y => b t y i))
    (hσ : ∀ t i j, Measurable (fun y => σ t y i j))
    (hW : ∀ j, Martingale (W j) 𝒢 μ) (hW₂ : ∀ j t, MemLp (W j t) 2 μ)
    {C : ℝ} (hC₀ : 0 ≤ C) (hC : ∀ t y i j, ‖σ t y i j‖ ≤ C)
    (hCov : ∀ n j k, μ[(W j (grid (n + 1)) - W j (grid n)) *
        (W k (grid (n + 1)) - W k (grid n)) | 𝒢 (grid n)] =ᵐ[μ]
      fun _ => if j = k then ((grid (n + 1) : ℝ) - (grid n : ℝ)) else 0)
    {a z : ℕ} (haz : a ≤ z) :
    (∫ ω, (eulerGridNoise grid b σ W x i z ω - eulerGridNoise grid b σ W x i a ω)^2 ∂μ) ≤
      (Fintype.card κ : ℝ) * C^2 * ((grid z : ℝ) - (grid a : ℝ)) := by
  let N := eulerGridNoise grid b σ W x i
  let q := eulerGridCovarianceIncrement grid b σ W x i i
  let A := runningSum q
  have hN : Martingale N (gridFiltration 𝒢 grid) μ := by
    convert eulerGridState_noise_martingale grid x i hb hσ hW hW₂ hC using 1
    ext n ω
    exact eulerGridNoise_eq_driver_grid_integrals grid b σ W x i n ω
  have hN₂ : ∀ n, MemLp (N n) 2 μ :=
    eulerGridNoise_memLp grid x i hb hσ (fun j => (hW j).stronglyAdapted) hW₂ hC
  have hQ : Martingale (fun n ω => N n ω ^ 2 - A n ω) (gridFiltration 𝒢 grid) μ := by
    rw [show (fun n ω => N n ω ^ 2 - A n ω) = fun n => N n * N n - A n by
      funext n ω; simp only [pow_two, Pi.mul_apply, Pi.sub_apply]]
    exact eulerGridNoise_compensated_product_martingale grid x i i hb hσ hW hW₂ hC hCov
  have hStep (n : ℕ) (ω : Ω) :
      |q n ω| ≤ ((Fintype.card κ : ℝ) * C^2) * ((grid (n + 1) : ℝ) - (grid n : ℝ)) := by
    let v (j : κ) := σ (grid n) (eulerGridState grid b σ W x n ω) i j
    let dt := (grid (n + 1) : ℝ) - (grid n : ℝ)
    have hdt : 0 ≤ dt := real_grid_sub_nonneg grid n.le_succ
    have hsum : ∑ j, v j * v j ≤ (Fintype.card κ : ℝ) * C^2 := by
      calc
        _ ≤ ∑ _j : κ, C^2 := Finset.sum_le_sum fun j _ => by
          have hj : |v j| ≤ C := hC _ _ _ _
          nlinarith [sq_abs (v j), mul_nonneg (sub_nonneg.mpr hj) (add_nonneg hC₀ (abs_nonneg (v j)))]
        _ = _ := by simp
    change |dt * ∑ j, v j * v j| ≤ _
    rw [abs_of_nonneg (mul_nonneg hdt (Finset.sum_nonneg fun j _ => mul_self_nonneg (v j)))]
    simpa only [mul_comm dt] using mul_le_mul_of_nonneg_left hsum hdt
  have hBound (ω : Ω) : A z ω - A a ω ≤
      (Fintype.card κ : ℝ) * C^2 * ((grid z : ℝ) - (grid a : ℝ)) :=
    (le_abs_self _).trans (abs_runningSum_sub_le_grid grid hStep haz ω)
  have hInt (n : ℕ) : Integrable (A n) μ := by
    have hi := (hN₂ n).integrable_sq.sub (hQ.integrable n)
    exact hi.congr (Eventually.of_forall fun ω => by
      change N n ω ^ 2 - (N n ω ^ 2 - A n ω) = A n ω
      ring)
  change (∫ ω, (N z ω - N a ω)^2 ∂μ) ≤ _
  rw [integral_sq_sub_eq_compensator hN hQ hN₂ haz]
  exact (integral_mono ((hInt z).sub (hInt a)) (integrable_const _) hBound).trans_eq
    (by simp)

/-- Each Euler state coordinate has a uniform second-moment increment
bound. The contribution of the bounded drift is quadratic in elapsed time. -/
theorem integral_eulerGridState_sub_sq_le [IsProbabilityMeasure μ] [DecidableEq κ]
    (hb : ∀ t i, Measurable (fun y => b t y i))
    (hσ : ∀ t i j, Measurable (fun y => σ t y i j))
    (hW : ∀ j, Martingale (W j) 𝒢 μ) (hW₂ : ∀ j t, MemLp (W j t) 2 μ)
    {B C : ℝ} (hB₀ : 0 ≤ B) (hC₀ : 0 ≤ C)
    (hB : ∀ t y i, ‖b t y i‖ ≤ B) (hC : ∀ t y i j, ‖σ t y i j‖ ≤ C)
    (hCov : ∀ n j k, μ[(W j (grid (n + 1)) - W j (grid n)) *
        (W k (grid (n + 1)) - W k (grid n)) | 𝒢 (grid n)] =ᵐ[μ]
      fun _ => if j = k then ((grid (n + 1) : ℝ) - (grid n : ℝ)) else 0)
    {a z : ℕ} (haz : a ≤ z) :
    (∫ ω, (eulerGridState grid b σ W x z ω i - eulerGridState grid b σ W x a ω i)^2 ∂μ) ≤
      2 * (B * ((grid z : ℝ) - (grid a : ℝ)))^2 +
        2 * ((Fintype.card κ : ℝ) * C^2 * ((grid z : ℝ) - (grid a : ℝ))) := by
  let X := eulerGridState grid b σ W x
  let d (n : ℕ) (ω : Ω) := b (grid n) (X n ω) i * ((grid (n + 1) : ℝ) - (grid n : ℝ))
  let D := runningSum d
  let q := eulerGridNoiseIncrement grid b σ W x i
  let N := runningSum q
  let dt := (grid z : ℝ) - (grid a : ℝ)
  change (∫ ω, (X z ω i - X a ω i)^2 ∂μ) ≤ _
  have hS (n : ℕ) (ω : Ω) : X n ω i = x i + D n ω + N n ω := by
    induction n with
    | zero => simp [D, N, X, eulerGridState]
    | succ n hn =>
      have hs : X (n + 1) ω i = X n ω i + d n ω + q n ω := by
        dsimp only [X, d, q, eulerGridNoiseIncrement]
        rw [eulerGridState]
      rw [hs, hn]
      simp only [D, N, runningSum_succ, Pi.add_apply]
      ring
  have hDi (n : ℕ) : MemLp (D n) 2 μ := by
    have hX := eulerGridState_stronglyAdapted grid x hb hσ (fun j => (hW j).stronglyAdapted)
    refine memLp_runningSum (fun n => ?_) n
    have hm : StronglyMeasurable[𝒢 (grid n)] (fun ω => b (grid n) (X n ω) i) :=
      ((hb _ i).comp (hX n).measurable).stronglyMeasurable
    have htop : MemLp (fun ω => b (grid n) (X n ω) i) ⊤ μ :=
      memLp_top_of_bound (hm.mono (𝒢.le _)).aestronglyMeasurable B
        (Eventually.of_forall fun ω => hB _ _ _)
    exact (htop.mono_exponent (by simp : (2 : ℝ≥0∞) ≤ ⊤)).mul_const _
  have hNi (n : ℕ) : MemLp (N n) 2 μ :=
    eulerGridNoise_memLp grid x i hb hσ (fun j => (hW j).stronglyAdapted) hW₂ hC n
  have hDrift (ω : Ω) : |D z ω - D a ω| ≤ B * dt := by
    apply abs_runningSum_sub_le_grid grid (d := d) _ haz ω
    intro n ω
    rw [show d n ω = b (grid n) (X n ω) i * ((grid (n + 1) : ℝ) - (grid n : ℝ)) from rfl,
      abs_mul, abs_of_nonneg (real_grid_sub_nonneg grid n.le_succ)]
    exact mul_le_mul_of_nonneg_right (hB _ _ _) (real_grid_sub_nonneg grid n.le_succ)
  let dX (ω : Ω) := D z ω - D a ω
  let dN (ω : Ω) := N z ω - N a ω
  have hdi : MemLp dX 2 μ := (hDi z).sub (hDi a)
  have hni : MemLp dN 2 μ := (hNi z).sub (hNi a)
  have hMain : (∫ ω, (X z ω i - X a ω i)^2 ∂μ) =
        ∫ ω, (dX ω + dN ω)^2 ∂μ := by
    apply integral_congr_ae
    exact Eventually.of_forall fun ω => by dsimp only [dX, dN]; rw [hS, hS]; ring
  have hdt : 0 ≤ dt := real_grid_sub_nonneg grid haz
  have hPoint (ω : Ω) : (dX ω + dN ω)^2 ≤ 2 * (B * dt)^2 + 2 * (dN ω)^2 := by
    have h1 : (dX ω)^2 ≤ (B * dt)^2 := by
      have hd := hDrift ω
      change |dX ω| ≤ B * dt at hd
      nlinarith [sq_abs (dX ω),
        mul_nonneg (sub_nonneg.mpr hd) (add_nonneg (mul_nonneg hB₀ hdt) (abs_nonneg (dX ω)))]
    nlinarith [sq_nonneg (dX ω - dN ω)]
  have hRHS : Integrable (fun ω => 2 * (B * dt)^2 + 2 * (dN ω)^2) μ :=
    (integrable_const _).add (hni.integrable_sq.const_mul 2)
  rw [hMain]
  calc
    _ ≤ ∫ ω, 2 * (B * dt)^2 + 2 * (dN ω)^2 ∂μ :=
      integral_mono (hdi.add hni).integrable_sq hRHS hPoint
    _ = 2 * (B * dt)^2 + 2 * (∫ ω, (dN ω)^2 ∂μ) := by
      rw [integral_add (integrable_const _) (hni.integrable_sq.const_mul 2)]
      simp [integral_const_mul]
    _ ≤ _ := add_le_add (le_refl (2 * (B * dt)^2))
      (mul_le_mul_of_nonneg_left (integral_eulerGridNoise_sub_sq_le grid x i hb hσ hW hW₂
        hC₀ hC hCov haz) (show (0 : ℝ) ≤ 2 by norm_num))

#print axioms RoughHeston.integral_eulerGridNoise_sub_sq_le
#print axioms RoughHeston.integral_eulerGridState_sub_sq_le

end RoughHeston
