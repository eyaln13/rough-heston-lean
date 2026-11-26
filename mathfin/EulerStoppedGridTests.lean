import EulerWeakLawExtraction
import DensityMartingalePairing

/-! Exact drift reconstruction and past tests for the interpolated Euler law at grid vertices. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BoundedContinuousFunction

namespace RoughHeston

variable {Ω ι κ : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  [Fintype ι] [Fintype κ] {𝒢 : Filtration ℝ≥0 m}

private theorem gridLinearInterpolate_prefix (grid : ℕ →o ℝ≥0) (f : ℕ → ℝ)
    {a n : ℕ} (ha : a ≤ n) {s : ℝ≥0} (hs : s ≤ grid a) :
    gridLinearInterpolate grid f n s = gridLinearInterpolate grid f a s := by
  induction n, ha using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    have h0 : gridCellFraction grid n s = 0 := by
      have hs' : s ≤ grid n := hs.trans (grid.monotone hn)
      have hden := sub_nonneg.mpr (NNReal.coe_le_coe.mpr (grid.monotone n.le_succ))
      have hnum := sub_nonpos.mpr (NNReal.coe_le_coe.mpr hs')
      unfold gridCellFraction
      exact max_eq_left ((min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg hnum hden))
    rw [gridLinearInterpolate, h0, zero_mul, add_zero, ih]

private theorem measurable_gridLinearInterpolate_prefix {m₀ : MeasurableSpace Ω}
    (grid : ℕ →o ℝ≥0) (X : ℕ → Ω → ℝ) (n : ℕ) (s : ℝ≥0)
    (hX : ∀ k ≤ n, Measurable[m₀] (X k)) :
    Measurable[m₀] (fun ω => gridLinearInterpolate grid (fun k => X k ω) n s) := by
  induction n with
  | zero => exact hX 0 le_rfl
  | succ n ih =>
    exact (ih (fun k hk => hX k (hk.trans n.le_succ))).add
      (measurable_const.mul ((hX (n+1) le_rfl).sub (hX n n.le_succ)))

omit [Fintype κ] in
/-- A stopped affine interpolation is measurable at any grid vertex
which is at or after the stopping time. -/
theorem measurable_gridLinearInterpolateVectorPath_stopped
    (T : ℝ≥0) (grid : ℕ →o ℝ≥0) (X : ℕ → Ω → ι → ℝ)
    (hX : StronglyAdapted (gridFiltration 𝒢 grid) X) {a n : ℕ} (ha : a ≤ n)
    {s : ℝ≥0} (hs : s ≤ grid a) :
    Measurable[𝒢 (grid a)] (fun ω =>
      canonicalStoppedPath T s (gridLinearInterpolateVectorPath T grid (fun k => X k ω) n)) := by
  let : MeasurableSpace Ω := 𝒢 (grid a)
  apply ContinuousMap.measurable_iff_eval.mpr
  intro r
  apply Measurable.of_eval
  intro i
  let t := min r.val s
  have ht : t ≤ grid a := (min_le_right _ _).trans hs
  have he (ω : Ω) : gridLinearInterpolate grid (fun k => X k ω i) n t =
      gridLinearInterpolate grid (fun k => X k ω i) a t :=
    gridLinearInterpolate_prefix grid _ ha ht
  change Measurable[𝒢 (grid a)] (fun ω =>
    gridLinearInterpolate grid (fun k => X k ω i) n t)
  simp_rw [he]
  refine measurable_gridLinearInterpolate_prefix grid (fun k ω => X k ω i) a t fun k hk => ?_
  exact (measurable_pi_apply i).comp
    ((hX k).mono (𝒢.mono (grid.monotone hk))).measurable

/-- The Euler state equals the initial value plus the accumulated drift
and accumulated martingale noise. -/
theorem eulerGridState_eq_initial_add_drift_add_noise (grid : ℕ →o ℝ≥0)
    (b : ℝ≥0 → (ι → ℝ) → ι → ℝ) (σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ)
    (W : κ → ℝ≥0 → Ω → ℝ) (x : ι → ℝ) (i : ι) (a : ℕ) (ω : Ω) :
    eulerGridState grid b σ W x a ω i = x i +
      runningSum (fun k ω => b (grid k) (eulerGridState grid b σ W x k ω) i *
        ((grid (k+1) : ℝ) - (grid k : ℝ))) a ω +
      eulerGridNoise grid b σ W x i a ω := by
  induction a with
  | zero => simp [eulerGridState, eulerGridNoise]
  | succ a ih =>
    have hS : eulerGridState grid b σ W x (a+1) ω i =
        eulerGridState grid b σ W x a ω i +
          b (grid a) (eulerGridState grid b σ W x a ω) i *
            ((grid (a+1) : ℝ) - (grid a : ℝ)) +
          eulerGridNoiseIncrement grid b σ W x i a ω := by
      rw [eulerGridState, eulerGridNoiseIncrement]
    rw [hS, ih]
    simp only [eulerGridNoise, runningSum_succ, Pi.add_apply]
    ring

omit [Fintype κ] in
/-- The canonical drift quadrature on the completed cells of the grid. -/
noncomputable def canonicalGridCoefficientSum (T : ℝ≥0) (grid : ℕ →o ℝ≥0)
    (c : ℝ≥0 → (ι → ℝ) → ℝ) (a : ℕ) (p : CanonicalPath T (ι → ℝ)) : ℝ :=
  runningSum (fun k p => c (grid k) (canonicalPathEval T (grid k) p) *
    ((grid (k+1) : ℝ) - (grid k : ℝ))) a p

omit [Fintype κ] in
/-- The drift-subtracted coordinate at a grid vertex, defined on all
canonical paths so it can be integrated against the interpolant law. -/
noncomputable def canonicalGridEulerNoise (T : ℝ≥0) (grid : ℕ →o ℝ≥0)
    (b : ℝ≥0 → (ι → ℝ) → ι → ℝ) (x : ι → ℝ) (i : ι)
    (a : ℕ) (p : CanonicalPath T (ι → ℝ)) : ℝ :=
  canonicalPathEval T (grid a) p i - x i -
    canonicalGridCoefficientSum T grid (fun r y => b r y i) a p

omit [Fintype κ] in
theorem canonicalPathEval_gridLinearInterpolateVectorPath_at_vertex
    (T : ℝ≥0) (grid : ℕ →o ℝ≥0) (X : ℕ → ι → ℝ) {n a : ℕ}
    (hg : ∀ k < n, grid k < grid (k+1)) (hT : grid n ≤ T) (ha : a ≤ n) :
    canonicalPathEval T (grid a) (gridLinearInterpolateVectorPath T grid X n) = X a := by
  have haT : grid a ≤ T := (grid.monotone ha).trans hT
  funext i
  change gridLinearInterpolate grid (fun k => X k i) n (min (grid a) T) = X a i
  rw [min_eq_left haT, gridLinearInterpolate_at_vertex grid _ hg ha]

omit [Fintype κ] in
theorem canonicalGridCoefficientSum_gridLinearInterpolateVectorPath
    (T : ℝ≥0) (grid : ℕ →o ℝ≥0) (X : ℕ → ι → ℝ) (c : ℝ≥0 → (ι → ℝ) → ℝ)
    {n a : ℕ} (hg : ∀ k < n, grid k < grid (k+1)) (hT : grid n ≤ T) (ha : a ≤ n) :
    canonicalGridCoefficientSum T grid c a (gridLinearInterpolateVectorPath T grid X n) =
      ∑ k ∈ Finset.range a, c (grid k) (X k) * ((grid (k+1) : ℝ) - (grid k : ℝ)) := by
  unfold canonicalGridCoefficientSum
  simp only [runningSum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [canonicalPathEval_gridLinearInterpolateVectorPath_at_vertex T grid X hg hT
    ((Finset.mem_range.mp hk).le.trans ha)]

/-- Under the actual Euler interpolation, the canonical grid noise
observable coincides pathwise with the centered grid martingale. -/
theorem canonicalGridEulerNoise_eq_eulerGridNoise
    (T : ℝ≥0) (grid : ℕ →o ℝ≥0) (b : ℝ≥0 → (ι → ℝ) → ι → ℝ)
    (σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ) (W : κ → ℝ≥0 → Ω → ℝ) (x : ι → ℝ)
    (i : ι) {n a : ℕ} (hg : ∀ k < n, grid k < grid (k+1)) (hT : grid n ≤ T)
    (ha : a ≤ n) (ω : Ω) :
    canonicalGridEulerNoise T grid b x i a
      (gridLinearInterpolateVectorPath T grid (fun k => eulerGridState grid b σ W x k ω) n) =
      eulerGridNoise grid b σ W x i a ω := by
  unfold canonicalGridEulerNoise
  rw [canonicalPathEval_gridLinearInterpolateVectorPath_at_vertex T grid _ hg hT ha,
    canonicalGridCoefficientSum_gridLinearInterpolateVectorPath T grid _ _ hg hT ha,
    eulerGridState_eq_initial_add_drift_add_noise grid b σ W x i a ω]
  simp only [runningSum, Finset.sum_apply]
  ring

omit [Fintype κ] in
theorem measurable_canonicalGridCoefficientSum (T : ℝ≥0) (grid : ℕ →o ℝ≥0)
    {c : ℝ≥0 → (ι → ℝ) → ℝ} (hc : ∀ r, Measurable (c r)) (a : ℕ) :
    Measurable (canonicalGridCoefficientSum T grid c a) := by
  let d (k : ℕ) (p : CanonicalPath T (ι → ℝ)) :=
    c (grid k) (canonicalPathEval T (grid k) p) * ((grid (k+1) : ℝ) - (grid k : ℝ))
  have hm (k : ℕ) : Measurable (d k) :=
    ((hc (grid k)).comp (continuous_canonicalPathEval T (grid k)).measurable).mul measurable_const
  change Measurable (∑ k ∈ Finset.range a, d k)
  have he : (∑ k ∈ Finset.range a, d k) = fun p => ∑ k ∈ Finset.range a, d k p := by
    funext p
    simp only [Finset.sum_apply]
  rw [he]
  exact Finset.measurable_sum (Finset.range a) (f := d) fun k _ => hm k

omit [Fintype κ] in
theorem measurable_canonicalGridEulerNoise (T : ℝ≥0) (grid : ℕ →o ℝ≥0)
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} (hb : ∀ t i, Measurable (fun y => b t y i))
    (x : ι → ℝ) (i : ι) (a : ℕ) :
    Measurable (canonicalGridEulerNoise T grid b x i a) :=
  (((measurable_pi_apply i).comp (continuous_canonicalPathEval T (grid a)).measurable).sub
    measurable_const).sub (measurable_canonicalGridCoefficientSum T grid (fun r => hb r i) a)

omit [Fintype κ] in
theorem integral_martingale_sub_mul_bounded_continuous_past
    [IsFiniteMeasure μ] {F : Filtration ℕ m} {M : ℕ → Ω → ℝ} (hM : Martingale M F μ)
    {a z : ℕ} (haz : a ≤ z) {Y : Ω → ℝ} (hY : StronglyMeasurable[F a] Y)
    {C : ℝ} (hC : ∀ ω, ‖Y ω‖ ≤ C) :
    (∫ ω, (M z ω - M a ω) * Y ω ∂μ) = 0 := by
  have hY' : AEStronglyMeasurable Y μ := (hY.mono (F.le a)).aestronglyMeasurable
  have hI (k : ℕ) : Integrable (fun ω => M k ω * Y ω) μ :=
    (hM.integrable k).mul_bdd hY' (Eventually.of_forall hC)
  simp_rw [sub_mul]
  rw [integral_sub (hI z) (hI a),
    integral_martingale_mul_past hM haz hY.aestronglyMeasurable (hI z), sub_self]

/-- The actual Euler noise satisfies the past tests on the interpolant
law at grid vertices. The stopped testing time is at or before the first
tested vertex, so the entire interpolated past is measurable there. -/
theorem eulerCanonicalGridNoise_past_test [IsProbabilityMeasure μ]
    (T : ℝ≥0) (grid : ℕ →o ℝ≥0) {n a z : ℕ}
    (hg : ∀ k < n, grid k < grid (k+1)) (hT : grid n ≤ T)
    (haz : a ≤ z) (hzn : z ≤ n) {s : ℝ≥0} (hs : s ≤ grid a)
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    {W : κ → ℝ≥0 → Ω → ℝ} (x : ι → ℝ) (i : ι)
    (hb : ∀ t i, Measurable (fun y => b t y i))
    (hσ : ∀ t i j, Measurable (fun y => σ t y i j))
    (hW : ∀ j, Martingale (W j) 𝒢 μ) (hW₂ : ∀ j t, MemLp (W j t) 2 μ)
    {C : ℝ} (hC : ∀ t y i j, ‖σ t y i j‖ ≤ C)
    (f : CanonicalPath T (ι → ℝ) →ᵇ ℝ) :
    let I (ω : Ω) := gridLinearInterpolateVectorPath T grid
      (fun k => eulerGridState grid b σ W x k ω) n
    (∫ p, (canonicalGridEulerNoise T grid b x i z p -
      canonicalGridEulerNoise T grid b x i a p) * f (canonicalStoppedPath T s p) ∂(μ.map I)) = 0 := by
  dsimp only
  let X := eulerGridState grid b σ W x
  let I (ω : Ω) := gridLinearInterpolateVectorPath T grid (fun k => X k ω) n
  let F := gridFiltration 𝒢 grid
  let M := eulerGridNoise grid b σ W x i
  have hX := eulerGridState_stronglyAdapted grid x hb hσ (fun j => (hW j).stronglyAdapted)
  have hI : Measurable I := measurable_gridLinearInterpolateVectorPath T grid X
    (fun k i => ((measurable_pi_apply i).comp (hX k).measurable).mono (𝒢.le _) le_rfl) n
  have hM : Martingale M F μ := by
    convert eulerGridState_noise_martingale grid x i hb hσ hW hW₂ hC using 1
    ext r ω
    exact eulerGridNoise_eq_driver_grid_integrals grid b σ W x i r ω
  have hY : StronglyMeasurable[F a] (fun ω => f (canonicalStoppedPath T s (I ω))) :=
    (f.continuous.measurable.comp
      (measurable_gridLinearInterpolateVectorPath_stopped T grid X hX (haz.trans hzn) hs)).stronglyMeasurable
  have hTest : Measurable (fun p => (canonicalGridEulerNoise T grid b x i z p -
      canonicalGridEulerNoise T grid b x i a p) * f (canonicalStoppedPath T s p)) :=
    ((measurable_canonicalGridEulerNoise T grid hb x i z).sub
      (measurable_canonicalGridEulerNoise T grid hb x i a)).mul
        (f.continuous.measurable.comp (continuous_canonicalStoppedPath T s).measurable)
  rw [integral_map hI.aemeasurable hTest.aestronglyMeasurable]
  change (∫ ω, (canonicalGridEulerNoise T grid b x i z (I ω) -
    canonicalGridEulerNoise T grid b x i a (I ω)) * f (canonicalStoppedPath T s (I ω)) ∂μ) = 0
  calc
    _ = ∫ ω, (M z ω - M a ω) * f (canonicalStoppedPath T s (I ω)) ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun ω => by
        dsimp only [I, X, M]
        rw [canonicalGridEulerNoise_eq_eulerGridNoise T grid b σ W x i hg hT hzn,
          canonicalGridEulerNoise_eq_eulerGridNoise T grid b σ W x i hg hT (haz.trans hzn)]
    _ = 0 := integral_martingale_sub_mul_bounded_continuous_past hM haz hY
      (fun ω => f.norm_coe_le_norm (canonicalStoppedPath T s (I ω)))

#print axioms RoughHeston.measurable_gridLinearInterpolateVectorPath_stopped
#print axioms RoughHeston.canonicalGridEulerNoise_eq_eulerGridNoise
#print axioms RoughHeston.eulerCanonicalGridNoise_past_test

end RoughHeston
