import EulerGridSystem
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Integration

/-! Predictable covariance of the Euler-grid noise on the sampled joint filtration. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped MeasureTheory NNReal ENNReal BigOperators ProbabilityTheory

namespace RoughHeston

variable {Ω ι κ : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℝ≥0 m} [Fintype ι] [Fintype κ]

/-- Matrix row applied to the driving noise on one Euler cell. -/
noncomputable def eulerGridNoiseIncrement (grid : ℕ →o ℝ≥0)
    (b : ℝ≥0 → (ι → ℝ) → ι → ℝ) (σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ)
    (W : κ → ℝ≥0 → Ω → ℝ) (x : ι → ℝ) (i : ι) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ j, σ (grid n) (eulerGridState grid b σ W x n ω) i j *
    (W j (grid (n + 1)) ω - W j (grid n) ω)

/-- The time step times the inner product of two rows of the diffusion
matrix evaluated at the left endpoint of the Euler cell. -/
noncomputable def eulerGridCovarianceIncrement (grid : ℕ →o ℝ≥0)
    (b : ℝ≥0 → (ι → ℝ) → ι → ℝ) (σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ)
    (W : κ → ℝ≥0 → Ω → ℝ) (x : ι → ℝ) (i l : ι) (n : ℕ) (ω : Ω) : ℝ :=
  ((grid (n + 1) : ℝ) - (grid n : ℝ)) *
    ∑ j, σ (grid n) (eulerGridState grid b σ W x n ω) i j *
      σ (grid n) (eulerGridState grid b σ W x n ω) l j

omit [Fintype κ] in
/-- Joint independence from the past and independent centered components
with a common second moment give the diagonal conditional covariance. -/
theorem condExp_product_of_independent_increments [IsFiniteMeasure μ] [DecidableEq κ]
    {F : MeasurableSpace Ω} (hF : F ≤ m) {d : κ → Ω → ℝ} {v : ℝ}
    (hd : ∀ j, @Measurable Ω ℝ m _ (d j))
    (hPast : Indep (MeasurableSpace.comap (fun ω j => d j ω) inferInstance) F μ)
    (hPair : ∀ j k, j ≠ k → d j ⟂ᵢ[μ] d k)
    (hMean : ∀ j, (∫ ω, d j ω ∂μ) = 0)
    (hSecond : ∀ j, (∫ ω, d j ω ^ 2 ∂μ) = v) (j k : κ) :
    μ[d j * d k | F] =ᵐ[μ] fun _ => if j = k then v else 0 := by
  let U (ω : Ω) (j : κ) := d j ω
  have hU : @Measurable Ω (κ → ℝ) m _ U := by
    let : MeasurableSpace Ω := m
    exact Measurable.of_eval hd
  let mU := MeasurableSpace.comap U inferInstance
  have hdm (j : κ) : StronglyMeasurable[mU] (d j) :=
    ((measurable_pi_apply j).comp (comap_measurable U)).stronglyMeasurable
  have h := condExp_indep_eq hU.comap_le hF ((hdm j).mul (hdm k)) hPast
  apply h.trans
  apply Eventually.of_forall
  intro ω
  by_cases he : j = k
  · subst k
    change (∫ ω, d j ω * d j ω ∂μ) = (if j = j then v else 0)
    rw [ite_eq_left rfl]
    simpa only [pow_two] using hSecond j
  · rw [(hPair j k he).integral_mul_eq_mul_integral
      (hd j).aestronglyMeasurable (hd k).aestronglyMeasurable, hMean j, zero_mul, ite_eq_right he]

private theorem condExp_product_weighted_finite_sum [DecidableEq κ]
    {F : Filtration ℕ m} {n : ℕ} {a b d : κ → Ω → ℝ} {v : ℝ}
    (ha : ∀ j, StronglyMeasurable[F n] (a j)) (hb : ∀ j, StronglyMeasurable[F n] (b j))
    (haTop : ∀ j, MemLp (a j) ⊤ μ) (hbTop : ∀ j, MemLp (b j) ⊤ μ)
    (hd₂ : ∀ j, MemLp (d j) 2 μ)
    (hCov : ∀ j k, μ[d j * d k | F n] =ᵐ[μ] fun _ => if j = k then v else 0) :
    μ[(∑ j, a j * d j) * (∑ j, b j * d j) | F n] =ᵐ[μ]
      fun ω => v * ∑ j, a j ω * b j ω := by
  let P (p : κ × κ) := (a p.1 * d p.1) * (b p.2 * d p.2)
  have hInt (p : κ × κ) : Integrable (P p) μ := by
    have hi : MemLp (a p.1 * d p.1) 2 μ := (haTop p.1).mul (hd₂ p.1)
    have hk : MemLp (b p.2 * d p.2) 2 μ := (hbTop p.2).mul (hd₂ p.2)
    exact hi.integrable_mul hk
  have hEq : (∑ j, a j * d j) * (∑ j, b j * d j) = ∑ p : κ × κ, P p := by
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
  have hp (p : κ × κ) : μ[P p | F n] =ᵐ[μ] fun ω =>
      a p.1 ω * b p.2 ω * (if p.1 = p.2 then v else 0) :=
    (predictable_increment_covariance (k := n) (ha p.1) (hb p.2)
      (haTop p.1) (hbTop p.2) (hd₂ p.1) (hd₂ p.2)).trans
        ((EventuallyEq.rfl).mul (hCov _ _))
  rw [hEq]
  refine (condExp_finsetSum (fun p _ => hInt p) (F n)).trans ?_
  have hall : ∀ᵐ ω ∂μ, ∀ p, μ[P p | F n] ω =
      a p.1 ω * b p.2 ω * (if p.1 = p.2 then v else 0) := ae_all_iff.2 hp
  filter_upwards [hall] with ω hω
  simp only [Finset.sum_apply, hω, Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single j]
  · simp [mul_comm]
  · intro k _ hkj
    simp [Ne.symm hkj]
  · simp

/-- Conditional product of the actual Euler noise increments. The driver
increment covariance is specified on the same joint filtration. -/
theorem condExp_eulerGridNoiseIncrement_product [DecidableEq κ] (grid : ℕ →o ℝ≥0)
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    {W : κ → ℝ≥0 → Ω → ℝ} (x : ι → ℝ) (i l : ι) (n : ℕ)
    (hb : ∀ t i, Measurable (fun y => b t y i))
    (hσ : ∀ t i j, Measurable (fun y => σ t y i j))
    (hW : ∀ j, StronglyAdapted 𝒢 (W j)) (hW₂ : ∀ j t, MemLp (W j t) 2 μ)
    {C : ℝ} (hC : ∀ t y i j, ‖σ t y i j‖ ≤ C)
    (hCov : ∀ j k, μ[(W j (grid (n + 1)) - W j (grid n)) *
        (W k (grid (n + 1)) - W k (grid n)) | 𝒢 (grid n)] =ᵐ[μ]
      fun _ => if j = k then ((grid (n + 1) : ℝ) - (grid n : ℝ)) else 0) :
    μ[eulerGridNoiseIncrement grid b σ W x i n *
        eulerGridNoiseIncrement grid b σ W x l n | 𝒢 (grid n)] =ᵐ[μ]
      eulerGridCovarianceIncrement grid b σ W x i l n := by
  let a (i : ι) (j : κ) (ω : Ω) := σ (grid n) (eulerGridState grid b σ W x n ω) i j
  have hX := eulerGridState_stronglyAdapted grid x hb hσ hW
  have hA (i : ι) (j : κ) : StronglyMeasurable[𝒢 (grid n)] (a i j) :=
    ((hσ _ i j).comp (hX n).measurable).stronglyMeasurable
  have hTop (i : ι) (j : κ) : MemLp (a i j) ⊤ μ :=
    memLp_top_of_bound ((hA i j).mono (𝒢.le _)).aestronglyMeasurable C
      (Eventually.of_forall fun ω => hC _ _ _ _)
  let d (j : κ) := W j (grid (n + 1)) - W j (grid n)
  have hd (j : κ) : MemLp (d j) 2 μ := (hW₂ j _).sub (hW₂ j _)
  have h := condExp_product_weighted_finite_sum (F := gridFiltration 𝒢 grid)
    (n := n) (hA i) (hA l) (hTop i) (hTop l) hd hCov
  have he (i : ι) : eulerGridNoiseIncrement grid b σ W x i n = ∑ j, a i j * d j := by
    funext ω
    simp only [eulerGridNoiseIncrement, a, d, Finset.sum_apply, Pi.mul_apply, Pi.sub_apply]
  rw [he i, he l]
  exact h

/-- The accumulated martingale noise in one Euler coordinate. -/
noncomputable def eulerGridNoise (grid : ℕ →o ℝ≥0)
    (b : ℝ≥0 → (ι → ℝ) → ι → ℝ) (σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ)
    (W : κ → ℝ≥0 → Ω → ℝ) (x : ι → ℝ) (i : ι) : ℕ → Ω → ℝ :=
  runningSum (eulerGridNoiseIncrement grid b σ W x i)

omit [Fintype ι] in
/-- Summing the row increments or first forming each driving grid
integral gives the same Euler noise. -/
theorem eulerGridNoise_eq_driver_grid_integrals (grid : ℕ →o ℝ≥0)
    (b : ℝ≥0 → (ι → ℝ) → ι → ℝ) (σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ)
    (W : κ → ℝ≥0 → Ω → ℝ) (x : ι → ℝ) (i : ι) (n : ℕ) (ω : Ω) :
    eulerGridNoise grid b σ W x i n ω =
      ∑ j, gridIntegral grid (fun k ω => σ (grid k) (eulerGridState grid b σ W x k ω) i j)
        (W j) n ω := by
  simp only [eulerGridNoise, eulerGridNoiseIncrement, runningSum, gridIntegral,
    Finset.sum_apply, Pi.mul_apply, Pi.sub_apply]
  rw [Finset.sum_comm]

/-- The explicit covariance-increment formula is predictable on the grid. -/
theorem eulerGridCovarianceIncrement_stronglyMeasurable (grid : ℕ →o ℝ≥0)
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    {W : κ → ℝ≥0 → Ω → ℝ} (x : ι → ℝ) (i l : ι) (n : ℕ)
    (hb : ∀ t i, Measurable (fun y => b t y i))
    (hσ : ∀ t i j, Measurable (fun y => σ t y i j))
    (hW : ∀ j, StronglyAdapted 𝒢 (W j)) :
    StronglyMeasurable[𝒢 (grid n)] (eulerGridCovarianceIncrement grid b σ W x i l n) := by
  have hX := eulerGridState_stronglyAdapted grid x hb hσ hW
  unfold eulerGridCovarianceIncrement
  let : MeasurableSpace Ω := 𝒢 (grid n)
  apply Measurable.stronglyMeasurable
  exact measurable_const.mul (Finset.measurable_sum _ fun j _ =>
    ((hσ _ i j).comp (hX n).measurable).mul ((hσ _ l j).comp (hX n).measurable))

/-- Products of Euler noise coordinates, minus the running sum of the
computed left-endpoint covariance, are martingales on the joint grid. -/
theorem eulerGridNoise_compensated_product_martingale [IsFiniteMeasure μ] [DecidableEq κ]
    (grid : ℕ →o ℝ≥0)
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    {W : κ → ℝ≥0 → Ω → ℝ} (x : ι → ℝ) (i l : ι)
    (hb : ∀ t i, Measurable (fun y => b t y i))
    (hσ : ∀ t i j, Measurable (fun y => σ t y i j))
    (hW : ∀ j, Martingale (W j) 𝒢 μ) (hW₂ : ∀ j t, MemLp (W j t) 2 μ)
    {C : ℝ} (hC : ∀ t y i j, ‖σ t y i j‖ ≤ C)
    (hCov : ∀ n j k, μ[(W j (grid (n + 1)) - W j (grid n)) *
        (W k (grid (n + 1)) - W k (grid n)) | 𝒢 (grid n)] =ᵐ[μ]
      fun _ => if j = k then ((grid (n + 1) : ℝ) - (grid n : ℝ)) else 0) :
    Martingale (fun n =>
      eulerGridNoise grid b σ W x i n * eulerGridNoise grid b σ W x l n -
        runningSum (eulerGridCovarianceIncrement grid b σ W x i l) n)
      (gridFiltration 𝒢 grid) μ := by
  let F := gridFiltration 𝒢 grid
  let X := eulerGridState grid b σ W x
  let D := eulerGridNoiseIncrement grid b σ W x
  let N := eulerGridNoise grid b σ W x
  let A := eulerGridCovarianceIncrement grid b σ W x i l
  have hX := eulerGridState_stronglyAdapted grid x hb hσ (fun j => (hW j).stronglyAdapted)
  have hN (i : ι) : Martingale (N i) F μ := by
    convert eulerGridState_noise_martingale grid x i hb hσ hW hW₂ hC using 1
    ext n ω
    exact eulerGridNoise_eq_driver_grid_integrals grid b σ W x i n ω
  have hD (i : ι) (n : ℕ) : D i n = N i (n + 1) - N i n := by
    simp only [N, D, eulerGridNoise, runningSum_succ, add_sub_cancel_left]
  have hDNext (i : ι) (n : ℕ) : StronglyMeasurable[F (n + 1)] (D i n) := by
    rw [hD]
    exact ((hN i).stronglyMeasurable (n + 1)).sub
      (((hN i).stronglyMeasurable n).mono (F.mono n.le_succ))
  have hDzero (i : ι) (n : ℕ) : μ[D i n | F n] =ᵐ[μ] 0 := by
    rw [hD]
    exact conditional_mean_martingale_increment (hN i) n.le_succ
  have hD₂ (i : ι) (n : ℕ) : MemLp (D i n) 2 μ := by
    let a (j : κ) (ω : Ω) := σ (grid n) (X n ω) i j
    have ha (j : κ) : StronglyMeasurable[𝒢 (grid n)] (a j) :=
      ((hσ _ i j).comp (hX n).measurable).stronglyMeasurable
    have hTop (j : κ) : MemLp (a j) ⊤ μ :=
      memLp_top_of_bound ((ha j).mono (𝒢.le _)).aestronglyMeasurable C
        (Eventually.of_forall fun ω => hC _ _ _ _)
    change MemLp (fun ω => ∑ j, a j ω * (W j (grid (n + 1)) ω - W j (grid n) ω)) 2 μ
    exact memLp_finsetSum Finset.univ fun j _ =>
      (hTop j).mul ((hW₂ j _).sub (hW₂ j _))
  have hAm (n : ℕ) : StronglyMeasurable[F n] (A n) :=
    eulerGridCovarianceIncrement_stronglyMeasurable grid x i l n hb hσ
      (fun j => (hW j).stronglyAdapted)
  have hAsum : StronglyAdapted F (runningSum A) := adapted_runningSum
    (fun n => (hAm n).mono (F.mono n.le_succ))
  have hCovStep (n : ℕ) : stepCovariance μ F (D i) (D l) n =ᵐ[μ] A n :=
    condExp_eulerGridNoiseIncrement_product grid x i l n hb hσ
      (fun j => (hW j).stronglyAdapted) hW₂ hC (hCov n)
  have hCovSum (n : ℕ) :
      runningSum (stepCovariance μ F (D i) (D l)) n =ᵐ[μ] runningSum A n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [runningSum_succ, runningSum_succ]
      exact ih.add (hCovStep n)
  have hComp := compensated_running_product_martingale (hDNext i) (hDNext l)
    (hD₂ i) (hD₂ l) (hDzero i) (hDzero l)
  have hEq (n : ℕ) :
      runningSum (D i) n * runningSum (D l) n -
          runningSum (stepCovariance μ F (D i) (D l)) n =ᵐ[μ]
        N i n * N l n - runningSum A n :=
    (EventuallyEq.rfl).sub (hCovSum n)
  change Martingale (fun n => N i n * N l n - runningSum A n) F μ
  refine ⟨fun n => (((hN i).stronglyMeasurable n).mul ((hN l).stronglyMeasurable n)).sub
    (hAsum n), ?_⟩
  intro s t hst
  exact (condExp_congr_ae (hEq t).symm).trans ((hComp.condExp_ae_eq hst).trans (hEq s))

/-- Independent vector increments from the past, independent components,
and their diagonal variance identify the actual Euler compensator. -/
theorem eulerGridNoise_compensated_product_of_independent_increments
    [IsFiniteMeasure μ] [DecidableEq κ] (grid : ℕ →o ℝ≥0)
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    {W : κ → ℝ≥0 → Ω → ℝ} (x : ι → ℝ) (i l : ι)
    (hb : ∀ t i, Measurable (fun y => b t y i))
    (hσ : ∀ t i j, Measurable (fun y => σ t y i j))
    (hW : ∀ j, Martingale (W j) 𝒢 μ) (hW₂ : ∀ j t, MemLp (W j t) 2 μ)
    {C : ℝ} (hC : ∀ t y i j, ‖σ t y i j‖ ≤ C)
    (hPast : ∀ n, Indep (MeasurableSpace.comap
      (fun ω j => W j (grid (n + 1)) ω - W j (grid n) ω) inferInstance) (𝒢 (grid n)) μ)
    (hPair : ∀ n j k, j ≠ k →
      (W j (grid (n + 1)) - W j (grid n)) ⟂ᵢ[μ] (W k (grid (n + 1)) - W k (grid n)))
    (hSecond : ∀ n j, (∫ ω, (W j (grid (n + 1)) ω - W j (grid n) ω) ^ 2 ∂μ) =
      ((grid (n + 1) : ℝ) - (grid n : ℝ))) :
    Martingale (fun n =>
      eulerGridNoise grid b σ W x i n * eulerGridNoise grid b σ W x l n -
        runningSum (eulerGridCovarianceIncrement grid b σ W x i l) n)
      (gridFiltration 𝒢 grid) μ := by
  apply eulerGridNoise_compensated_product_martingale grid x i l hb hσ hW hW₂ hC
  intro n j k
  let d (j : κ) := W j (grid (n + 1)) - W j (grid n)
  have hM (j : κ) (t : ℝ≥0) : Measurable (W j t) :=
    (((hW j).stronglyMeasurable t).mono (𝒢.le t)).measurable
  have hd (j : κ) : Measurable (d j) := (hM j _).sub (hM j _)
  have hMean (j : κ) : (∫ ω, d j ω ∂μ) = 0 := by
    have hi := (hW j).setIntegral_eq (grid.monotone n.le_succ)
      (MeasurableSet.univ : MeasurableSet[𝒢 (grid n)] (Set.univ : Set Ω))
    rw [Measure.restrict_univ] at hi
    change (∫ ω, W j (grid (n + 1)) ω - W j (grid n) ω ∂μ) = 0
    rw [integral_sub ((hW j).integrable _) ((hW j).integrable _), hi, sub_self]
  exact condExp_product_of_independent_increments (𝒢.le _) hd (hPast n) (hPair n)
    hMean (hSecond n) j k

#print axioms condExp_product_of_independent_increments
#print axioms condExp_eulerGridNoiseIncrement_product
#print axioms eulerGridNoise_eq_driver_grid_integrals
#print axioms eulerGridCovarianceIncrement_stronglyMeasurable
#print axioms eulerGridNoise_compensated_product_martingale
#print axioms eulerGridNoise_compensated_product_of_independent_increments

end RoughHeston
