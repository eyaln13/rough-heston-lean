import EulerStoppedGridTests

/-! Exact bounded continuous past tests for the grid covariance compensator. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BoundedContinuousFunction

namespace RoughHeston

variable {Ω ι κ : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  [Fintype ι] [Fintype κ] {𝒢 : Filtration ℝ≥0 m}

/-- The scalar `(i,l)` coordinate of the covariance matrix. -/
noncomputable def eulerCovarianceCoefficient
    (σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ) (i l : ι) (r : ℝ≥0) (y : ι → ℝ) : ℝ :=
  ∑ j, σ r y i j * σ r y l j

theorem measurable_eulerCovarianceCoefficient
    {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    (hσ : ∀ t i j, Measurable (fun y => σ t y i j)) (i l : ι) (r : ℝ≥0) :
    Measurable (eulerCovarianceCoefficient σ i l r) :=
  Finset.measurable_sum _ fun j _ => (hσ r i j).mul (hσ r l j)

theorem continuous_eulerCovarianceCoefficient
    {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    (hσ : ∀ i j, Continuous (fun z : ℝ≥0 × (ι → ℝ) => σ z.1 z.2 i j)) (i l : ι) :
    Continuous (Function.uncurry (eulerCovarianceCoefficient σ i l)) :=
  continuous_finsetSum _ fun j _ => (hσ i j).mul (hσ l j)

theorem norm_eulerCovarianceCoefficient_le
    {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    {C : ℝ} (hC₀ : 0 ≤ C) (hC : ∀ t y i j, ‖σ t y i j‖ ≤ C)
    (i l : ι) (r : ℝ≥0) (y : ι → ℝ) :
    ‖eulerCovarianceCoefficient σ i l r y‖ ≤ (Fintype.card κ : ℝ) * C^2 := by
  unfold eulerCovarianceCoefficient
  calc
    _ ≤ ∑ j, ‖σ r y i j * σ r y l j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : κ, C^2 := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, pow_two]
      exact mul_le_mul (hC r y i j) (hC r y l j) (norm_nonneg _) hC₀
    _ = _ := by simp

/-- Compensated product of two canonical grid noise coordinates. -/
noncomputable def canonicalGridEulerCompensatedProduct (T : ℝ≥0) (grid : ℕ →o ℝ≥0)
    (b : ℝ≥0 → (ι → ℝ) → ι → ℝ) (σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ)
    (x : ι → ℝ) (i l : ι) (a : ℕ) (p : CanonicalPath T (ι → ℝ)) : ℝ :=
  canonicalGridEulerNoise T grid b x i a p * canonicalGridEulerNoise T grid b x l a p -
    canonicalGridCoefficientSum T grid (eulerCovarianceCoefficient σ i l) a p

theorem measurable_canonicalGridEulerCompensatedProduct (T : ℝ≥0) (grid : ℕ →o ℝ≥0)
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    (hb : ∀ t i, Measurable (fun y => b t y i)) (hσ : ∀ t i j, Measurable (fun y => σ t y i j))
    (x : ι → ℝ) (i l : ι) (a : ℕ) :
    Measurable (canonicalGridEulerCompensatedProduct T grid b σ x i l a) :=
  ((measurable_canonicalGridEulerNoise T grid hb x i a).mul
    (measurable_canonicalGridEulerNoise T grid hb x l a)).sub
      (measurable_canonicalGridCoefficientSum T grid (measurable_eulerCovarianceCoefficient hσ i l) a)

theorem canonicalGridEulerCompensatedProduct_eq_eulerGrid
    (T : ℝ≥0) (grid : ℕ →o ℝ≥0) (b : ℝ≥0 → (ι → ℝ) → ι → ℝ)
    (σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ) (W : κ → ℝ≥0 → Ω → ℝ) (x : ι → ℝ)
    (i l : ι) {n a : ℕ} (hg : ∀ k < n, grid k < grid (k+1)) (hT : grid n ≤ T)
    (ha : a ≤ n) (ω : Ω) :
    canonicalGridEulerCompensatedProduct T grid b σ x i l a
      (gridLinearInterpolateVectorPath T grid (fun k => eulerGridState grid b σ W x k ω) n) =
      eulerGridNoise grid b σ W x i a ω * eulerGridNoise grid b σ W x l a ω -
        runningSum (eulerGridCovarianceIncrement grid b σ W x i l) a ω := by
  unfold canonicalGridEulerCompensatedProduct
  rw [canonicalGridEulerNoise_eq_eulerGridNoise T grid b σ W x i hg hT ha,
    canonicalGridEulerNoise_eq_eulerGridNoise T grid b σ W x l hg hT ha,
    canonicalGridCoefficientSum_gridLinearInterpolateVectorPath T grid _ _ hg hT ha]
  congr 1
  simp only [runningSum, Finset.sum_apply, eulerCovarianceCoefficient, eulerGridCovarianceIncrement]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- The actual covariance-compensated Euler products satisfy all
bounded continuous stopped-path tests at intervals between grid vertices. -/
theorem eulerCanonicalGridCompensatedProduct_past_test
    [DecidableEq κ] [IsProbabilityMeasure μ]
    (T : ℝ≥0) (grid : ℕ →o ℝ≥0) {n a z : ℕ}
    (hg : ∀ k < n, grid k < grid (k+1)) (hT : grid n ≤ T)
    (haz : a ≤ z) (hzn : z ≤ n) {s : ℝ≥0} (hs : s ≤ grid a)
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    {W : κ → ℝ≥0 → Ω → ℝ} (x : ι → ℝ) (i l : ι)
    (hb : ∀ t i, Measurable (fun y => b t y i))
    (hσ : ∀ t i j, Measurable (fun y => σ t y i j))
    (hW : ∀ j, Martingale (W j) 𝒢 μ) (hW₂ : ∀ j t, MemLp (W j t) 2 μ)
    {C : ℝ} (hC : ∀ t y i j, ‖σ t y i j‖ ≤ C)
    (hCov : ∀ k j l, μ[(W j (grid (k+1)) - W j (grid k)) *
      (W l (grid (k+1)) - W l (grid k)) | 𝒢 (grid k)] =ᵐ[μ]
      fun _ => if j = l then ((grid (k+1) : ℝ) - (grid k : ℝ)) else 0)
    (f : CanonicalPath T (ι → ℝ) →ᵇ ℝ) :
    let I (ω : Ω) := gridLinearInterpolateVectorPath T grid
      (fun k => eulerGridState grid b σ W x k ω) n
    (∫ p, (canonicalGridEulerCompensatedProduct T grid b σ x i l z p -
      canonicalGridEulerCompensatedProduct T grid b σ x i l a p) *
        f (canonicalStoppedPath T s p) ∂(μ.map I)) = 0 := by
  dsimp only
  let X := eulerGridState grid b σ W x
  let I (ω : Ω) := gridLinearInterpolateVectorPath T grid (fun k => X k ω) n
  let F := gridFiltration 𝒢 grid
  let M (k : ℕ) := eulerGridNoise grid b σ W x i k * eulerGridNoise grid b σ W x l k -
    runningSum (eulerGridCovarianceIncrement grid b σ W x i l) k
  have hX := eulerGridState_stronglyAdapted grid x hb hσ (fun j => (hW j).stronglyAdapted)
  have hI : Measurable I := measurable_gridLinearInterpolateVectorPath T grid X
    (fun k i => ((measurable_pi_apply i).comp (hX k).measurable).mono (𝒢.le _) le_rfl) n
  have hM : Martingale M F μ :=
    eulerGridNoise_compensated_product_martingale grid x i l hb hσ hW hW₂ hC hCov
  have hY : StronglyMeasurable[F a] (fun ω => f (canonicalStoppedPath T s (I ω))) :=
    (f.continuous.measurable.comp
      (measurable_gridLinearInterpolateVectorPath_stopped T grid X hX (haz.trans hzn) hs)).stronglyMeasurable
  have hTest : Measurable (fun p => (canonicalGridEulerCompensatedProduct T grid b σ x i l z p -
      canonicalGridEulerCompensatedProduct T grid b σ x i l a p) * f (canonicalStoppedPath T s p)) :=
    ((measurable_canonicalGridEulerCompensatedProduct T grid hb hσ x i l z).sub
      (measurable_canonicalGridEulerCompensatedProduct T grid hb hσ x i l a)).mul
        (f.continuous.measurable.comp (continuous_canonicalStoppedPath T s).measurable)
  rw [integral_map hI.aemeasurable hTest.aestronglyMeasurable]
  change (∫ ω, (canonicalGridEulerCompensatedProduct T grid b σ x i l z (I ω) -
    canonicalGridEulerCompensatedProduct T grid b σ x i l a (I ω)) *
      f (canonicalStoppedPath T s (I ω)) ∂μ) = 0
  calc
    _ = ∫ ω, (M z ω - M a ω) * f (canonicalStoppedPath T s (I ω)) ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun ω => by
        dsimp only [I, X, M]
        rw [canonicalGridEulerCompensatedProduct_eq_eulerGrid T grid b σ W x i l hg hT hzn,
          canonicalGridEulerCompensatedProduct_eq_eulerGrid T grid b σ W x i l hg hT (haz.trans hzn)]
        simp only [Pi.sub_apply, Pi.mul_apply]
    _ = 0 := integral_martingale_sub_mul_bounded_continuous_past hM haz hY
      (fun ω => f.norm_coe_le_norm (canonicalStoppedPath T s (I ω)))

#print axioms RoughHeston.canonicalGridEulerCompensatedProduct_eq_eulerGrid
#print axioms RoughHeston.eulerCanonicalGridCompensatedProduct_past_test

end RoughHeston
