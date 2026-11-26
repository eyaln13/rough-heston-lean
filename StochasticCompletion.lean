import StochasticFoundation
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
Mean-square completion of the terminal stochastic integral on nested dyadic
grids, for a square-integrable martingale with a compensated square.

The convergence hypothesis is on the predictable coefficients, measured
using increments of the compensator. We do not assume convergence of the
stochastic sums. A density theorem for dyadic coefficients in the full
predictable L² space and a continuous version as the terminal time varies
are separate steps.
-/

open MeasureTheory Filter
open scoped BigOperators MeasureTheory ProbabilityTheory Topology NNReal

namespace RoughHeston

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

/-- A sequence of nested grids, where each coarse interval is split in two. -/
structure NestedDyadicGrids (ι : Type*) [Preorder ι] where
  grid : ℕ → (ℕ →o ι)
  refine : ∀ j, grid j = evenGrid (grid (j + 1))

/-- Equally spaced dyadic grids on nonnegative time, with terminal time T. -/
noncomputable def uniformDyadicGrids (T : ℝ≥0) : NestedDyadicGrids ℝ≥0 where
  grid j := ⟨fun k => (k : ℝ≥0) * T / (2 ^ j : ℝ≥0), by
    intro k l hkl
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hkl) (zero_le : 0 ≤ T)) (by positivity)⟩
  refine j := by
    apply OrderHom.ext
    funext k
    change (k : ℝ≥0) * T / (2 ^ j : ℝ≥0) =
      ((2 * k : ℕ) : ℝ≥0) * T / (2 ^ (j + 1) : ℝ≥0)
    push_cast
    rw [pow_succ]
    have hp : (2 ^ j : ℝ≥0) ≠ 0 := by positivity
    field_simp

@[simp] theorem uniform_dyadic_first_vertex (T : ℝ≥0) (j : ℕ) :
    (uniformDyadicGrids T).grid j 0 = 0 := by
  change ((0 : ℕ) : ℝ≥0) * T / (2 ^ j : ℝ≥0) = 0
  simp

@[simp] theorem uniform_dyadic_terminal_vertex (T : ℝ≥0) (j : ℕ) :
    (uniformDyadicGrids T).grid j (2 ^ j) = T := by
  change ((2 ^ j : ℕ) : ℝ≥0) * T / (2 ^ j : ℝ≥0) = T
  push_cast
  rw [mul_comm, mul_div_cancel_right₀ _ (by positivity : (2 ^ j : ℝ≥0) ≠ 0)]

theorem NestedDyadicGrids.vertex_at_refinement [Preorder ι]
    (G : NestedDyadicGrids ι) (j r k : ℕ) :
    G.grid j k = G.grid (j + r) (2 ^ r * k) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [ih, G.refine (j + r)]
    change G.grid (j + r + 1) (2 * (2 ^ r * k)) = G.grid (j + (r + 1)) (2 ^ (r + 1) * k)
    rw [pow_succ', Nat.mul_assoc, Nat.add_assoc]

/-- A weight repeated on the finer grid stays measurable at the finer
left endpoint. -/
theorem NestedDyadicGrids.predictable_lift [Preorder ι]
    (G : NestedDyadicGrids ι) (𝒢 : Filtration ι m)
    {a : ℕ → Ω → ℝ} {j : ℕ}
    (ha : ∀ k, StronglyMeasurable[𝒢 (G.grid j k)] (a k))
    (r k : ℕ) : StronglyMeasurable[𝒢 (G.grid (j + r) k)] (a (k / 2 ^ r)) := by
  refine (ha (k / 2 ^ r)).mono (𝒢.mono ?_)
  rw [G.vertex_at_refinement j r (k / 2 ^ r)]
  apply (G.grid (j + r)).monotone
  simpa only [Nat.mul_comm] using Nat.div_mul_le_self k (2 ^ r)

/-- Consistency after any finite number of dyadic refinements. -/
theorem NestedDyadicGrids.integral_at_refinement [Preorder ι]
    (G : NestedDyadicGrids ι) (j r n : ℕ)
    (a : ℕ → Ω → ℝ) (X : ι → Ω → ℝ) :
    gridIntegral (G.grid (j + r)) (fun k => a (k / 2 ^ r)) X (2 ^ r * n) =
      gridIntegral (G.grid j) a X n := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h := grid_integral_invariant_under_doubling (G.grid (j + r + 1))
      (fun k => a (k / 2 ^ r)) X (2 ^ r * n)
    rw [← G.refine (j + r)] at h
    rw [← ih, ← h]
    have ha : (fun k : ℕ => a (k / 2 ^ (r + 1))) = fun k => a (k / 2 / 2 ^ r) := by
      funext k
      rw [Nat.div_div_eq_div_mul, pow_succ']
    rw [ha, pow_succ', Nat.mul_assoc]
    simp only [Nat.add_assoc]

/-- The terminal sum at level j, with 2^j increments. -/
def dyadicTerminal [Preorder ι] (G : NestedDyadicGrids ι) (j : ℕ)
    (a : ℕ → Ω → ℝ) (X : ι → Ω → ℝ) : Ω → ℝ :=
  gridIntegral (G.grid j) a X (2 ^ j)

/-- Mean-square energy of the difference between a coarse weight and a
fine weight, integrated against increments of the compensator on their
common fine grid. -/
noncomputable def dyadicRefinementEnergy [Preorder ι]
    (μ : Measure Ω) (G : NestedDyadicGrids ι) (C : ι → Ω → ℝ)
    (j r : ℕ) (a b : ℕ → Ω → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ (j + r)),
    ∫ ω, (a (k / 2 ^ r) ω - b k ω) ^ 2 *
      (C (G.grid (j + r) (k + 1)) ω - C (G.grid (j + r) k) ω) ∂μ

theorem grid_integral_memLp_two [Preorder ι]
    (grid : ℕ →o ι) {X : ι → Ω → ℝ} (hX₂ : ∀ t, MemLp (X t) 2 μ)
    {a : ℕ → Ω → ℝ} (haTop : ∀ k, MemLp (a k) ⊤ μ) (n : ℕ) :
    MemLp (gridIntegral grid a X n) 2 μ :=
  memLp_runningSum (fun k => (haTop k).mul ((hX₂ _).sub (hX₂ _))) n

/-- The simple Itô isometry with a random compensator. -/
theorem grid_integral_square_compensator [Preorder ι] [IsFiniteMeasure μ]
    {𝒢 : Filtration ι m} (grid : ℕ →o ι) {X C : ι → Ω → ℝ}
    (hX : Martingale X 𝒢 μ) (hX₂ : ∀ t, MemLp (X t) 2 μ)
    (hC : Martingale (fun t => X t * X t - C t) 𝒢 μ)
    {a : ℕ → Ω → ℝ} (ha : ∀ k, StronglyMeasurable[𝒢 (grid k)] (a k))
    (haTop : ∀ k, MemLp (a k) ⊤ μ) (n : ℕ) :
    (∫ ω, (gridIntegral grid a X n ω) ^ 2 ∂μ) =
      ∑ k ∈ Finset.range n, ∫ ω, (a k ω) ^ 2 *
        (C (grid (k + 1)) ω - C (grid k) ω) ∂μ := by
  simpa only [pow_two] using
    grid_integral_cross_isometry grid hX hX hC hX₂ hX₂ ha ha haTop haTop n

/-- Exact distance formula for two finite stochastic integrals from
different levels. Their difference is evaluated on the common refinement. -/
theorem dyadic_terminal_refinement_energy [Preorder ι] [IsFiniteMeasure μ]
    {𝒢 : Filtration ι m} (G : NestedDyadicGrids ι) {X C : ι → Ω → ℝ}
    (hX : Martingale X 𝒢 μ) (hX₂ : ∀ t, MemLp (X t) 2 μ)
    (hC : Martingale (fun t => X t * X t - C t) 𝒢 μ)
    {j r : ℕ} {a b : ℕ → Ω → ℝ}
    (ha : ∀ k, StronglyMeasurable[𝒢 (G.grid j k)] (a k))
    (hb : ∀ k, StronglyMeasurable[𝒢 (G.grid (j + r) k)] (b k))
    (haTop : ∀ k, MemLp (a k) ⊤ μ) (hbTop : ∀ k, MemLp (b k) ⊤ μ) :
    (∫ ω, (dyadicTerminal G j a X ω - dyadicTerminal G (j + r) b X ω) ^ 2 ∂μ) =
      dyadicRefinementEnergy μ G C j r a b := by
  have hcommon : dyadicTerminal G j a X - dyadicTerminal G (j + r) b X =
      gridIntegral (G.grid (j + r)) (fun k => a (k / 2 ^ r) - b k) X (2 ^ (j + r)) := by
    unfold dyadicTerminal
    rw [← G.integral_at_refinement j r (2 ^ j) a X,
      grid_integral_sub_weights, pow_add, Nat.mul_comm (2 ^ j) (2 ^ r)]
  change (∫ ω, ((dyadicTerminal G j a X - dyadicTerminal G (j + r) b X) ω) ^ 2 ∂μ) = _
  rw [hcommon]
  exact grid_integral_square_compensator (G.grid (j + r)) hX hX₂ hC
    (fun k => (G.predictable_lift 𝒢 ha r k).sub (hb k))
    (fun k => (haTop (k / 2 ^ r)).sub (hbTop k)) _

/-- The square of the L² norm is the integrated square of a representative. -/
theorem norm_toLp_two_sq {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ ω, f ω ^ 2 ∂μ := by
  have hnonneg : 0 ≤ ∫ ω, f ω ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  rw [Lp.norm_toLp, hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hnonneg _), ← one_div,
    ← Real.sqrt_eq_rpow, Real.sq_sqrt hnonneg]

/-- The same identity for distances between two L² equivalence classes. -/
theorem dist_toLp_two_sq {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (dist (hf.toLp f) (hg.toLp g)) ^ 2 = ∫ ω, (f ω - g ω) ^ 2 ∂μ := by
  rw [dist_eq_norm, ← hf.toLp_sub hg, norm_toLp_two_sq]
  rfl

/-- The terminal random variable as an L² equivalence class. -/
noncomputable def dyadicTerminalLp [Preorder ι] (G : NestedDyadicGrids ι) (j : ℕ)
    {a : ℕ → Ω → ℝ} {X : ι → Ω → ℝ} (hX₂ : ∀ t, MemLp (X t) 2 μ)
    (haTop : ∀ k, MemLp (a k) ⊤ μ) : Lp ℝ 2 μ :=
  (grid_integral_memLp_two (G.grid j) hX₂ haTop (2 ^ j)).toLp (dyadicTerminal G j a X)

/-- The energy identity in the metric of the complete L² space. -/
theorem dyadic_terminalLp_refinement_energy [Preorder ι] [IsFiniteMeasure μ]
    {𝒢 : Filtration ι m} (G : NestedDyadicGrids ι) {X C : ι → Ω → ℝ}
    (hX : Martingale X 𝒢 μ) (hX₂ : ∀ t, MemLp (X t) 2 μ)
    (hC : Martingale (fun t => X t * X t - C t) 𝒢 μ)
    {j r : ℕ} {a b : ℕ → Ω → ℝ}
    (ha : ∀ k, StronglyMeasurable[𝒢 (G.grid j k)] (a k))
    (hb : ∀ k, StronglyMeasurable[𝒢 (G.grid (j + r) k)] (b k))
    (haTop : ∀ k, MemLp (a k) ⊤ μ) (hbTop : ∀ k, MemLp (b k) ⊤ μ) :
    (dist (dyadicTerminalLp G j hX₂ haTop) (dyadicTerminalLp G (j + r) hX₂ hbTop)) ^ 2 =
      dyadicRefinementEnergy μ G C j r a b := by
  unfold dyadicTerminalLp dyadicTerminal
  rw [dist_toLp_two_sq]
  exact dyadic_terminal_refinement_energy G hX hX₂ hC ha hb haTop hbTop

/-- Construction of a terminal stochastic integral for an energy-Cauchy
sequence of predictable dyadic coefficients. The stochastic sums converge
in L², and their limit is unique in that space. -/
theorem exists_unique_dyadic_terminal_limit [Preorder ι] [IsFiniteMeasure μ]
    {𝒢 : Filtration ι m} (G : NestedDyadicGrids ι) {X C : ι → Ω → ℝ}
    (hX : Martingale X 𝒢 μ) (hX₂ : ∀ t, MemLp (X t) 2 μ)
    (hC : Martingale (fun t => X t * X t - C t) 𝒢 μ)
    {a : ℕ → ℕ → Ω → ℝ}
    (ha : ∀ j k, StronglyMeasurable[𝒢 (G.grid j k)] (a j k))
    (haTop : ∀ j k, MemLp (a j k) ⊤ μ)
    (henergy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j ≥ N, ∀ r : ℕ,
      dyadicRefinementEnergy μ G C j r (a j) (a (j + r)) < ε) :
    ∃! I : Lp ℝ 2 μ, Tendsto (fun j => dyadicTerminalLp G j hX₂ (haTop j)) atTop (𝓝 I) := by
  let u := fun j => dyadicTerminalLp G j hX₂ (haTop j)
  have hc : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := henergy (ε ^ 2) (sq_pos_of_pos hε)
    use N
    intro j hj k hk
    have hd (j : ℕ) (hj : N ≤ j) (r : ℕ) : dist (u j) (u (j + r)) < ε := by
      have hh : dist (u j) (u (j + r)) ^ 2 < ε ^ 2 :=
        (dyadic_terminalLp_refinement_energy G hX hX₂ hC (ha j) (ha (j + r))
          (haTop j) (haTop (j + r))).trans_lt (hN j hj r)
      by_contra! hn
      exact (not_le_of_gt hh) (pow_le_pow_left₀ hε.le hn 2)
    rcases le_total j k with hjk | hkj
    · simpa only [Nat.add_sub_of_le hjk] using hd j hj (k - j)
    · rw [dist_comm]
      simpa only [Nat.add_sub_of_le hkj] using hd k hk (j - k)
  obtain ⟨I, hI⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨I, hI, fun J hJ => tendsto_nhds_unique hJ hI⟩

/-- Approximation independence: two coefficient sequences with vanishing
same-level energy distance have the same terminal integral. -/
theorem dyadic_terminal_limit_independent [Preorder ι] [IsFiniteMeasure μ]
    {𝒢 : Filtration ι m} (G : NestedDyadicGrids ι) {X C : ι → Ω → ℝ}
    (hX : Martingale X 𝒢 μ) (hX₂ : ∀ t, MemLp (X t) 2 μ)
    (hC : Martingale (fun t => X t * X t - C t) 𝒢 μ)
    {a b : ℕ → ℕ → Ω → ℝ}
    (ha : ∀ j k, StronglyMeasurable[𝒢 (G.grid j k)] (a j k))
    (hb : ∀ j k, StronglyMeasurable[𝒢 (G.grid j k)] (b j k))
    (haTop : ∀ j k, MemLp (a j k) ⊤ μ) (hbTop : ∀ j k, MemLp (b j k) ⊤ μ)
    {I J : Lp ℝ 2 μ}
    (hI : Tendsto (fun j => dyadicTerminalLp G j hX₂ (haTop j)) atTop (𝓝 I))
    (hJ : Tendsto (fun j => dyadicTerminalLp G j hX₂ (hbTop j)) atTop (𝓝 J))
    (hclose : Tendsto (fun j => dyadicRefinementEnergy μ G C j 0 (a j) (b j))
      atTop (𝓝 0)) : I = J := by
  have hdist : Tendsto (fun j => dist (dyadicTerminalLp G j hX₂ (haTop j))
      (dyadicTerminalLp G j hX₂ (hbTop j)) ^ 2) atTop (𝓝 (dist I J ^ 2)) :=
    (hI.dist hJ).pow 2
  have heq : (fun j => dist (dyadicTerminalLp G j hX₂ (haTop j))
      (dyadicTerminalLp G j hX₂ (hbTop j)) ^ 2) =
      (fun j => dyadicRefinementEnergy μ G C j 0 (a j) (b j)) := by
    funext j
    simpa only [Nat.add_zero] using dyadic_terminalLp_refinement_energy
      (r := 0) G hX hX₂ hC (ha j) (hb j) (haTop j) (hbTop j)
  rw [heq] at hdist
  exact dist_eq_zero.mp (sq_eq_zero_iff.mp (tendsto_nhds_unique hdist hclose))

@[simp] theorem grid_integral_zero_weights [Preorder ι]
    (grid : ℕ →o ι) (X : ι → Ω → ℝ) (n : ℕ) :
    gridIntegral grid (fun _ => (0 : Ω → ℝ)) X n = 0 := by
  induction n with
  | zero => simp [gridIntegral]
  | succ n ih => rw [gridIntegral_succ, ih, zero_mul, add_zero]

/-- The squared norm of the terminal stochastic integral is the limit of
the compensator-weighted energies of its approximants. -/
theorem dyadic_terminal_limit_isometry [Preorder ι] [IsFiniteMeasure μ]
    {𝒢 : Filtration ι m} (G : NestedDyadicGrids ι) {X C : ι → Ω → ℝ}
    (hX : Martingale X 𝒢 μ) (hX₂ : ∀ t, MemLp (X t) 2 μ)
    (hC : Martingale (fun t => X t * X t - C t) 𝒢 μ)
    {a : ℕ → ℕ → Ω → ℝ}
    (ha : ∀ j k, StronglyMeasurable[𝒢 (G.grid j k)] (a j k))
    (haTop : ∀ j k, MemLp (a j k) ⊤ μ) {I : Lp ℝ 2 μ}
    (hI : Tendsto (fun j => dyadicTerminalLp G j hX₂ (haTop j)) atTop (𝓝 I)) :
    Tendsto (fun j => dyadicRefinementEnergy μ G C j 0 (a j) (fun _ => 0))
      atTop (𝓝 (‖I‖ ^ 2)) := by
  have heq (j : ℕ) : ‖dyadicTerminalLp G j hX₂ (haTop j)‖ ^ 2 =
      dyadicRefinementEnergy μ G C j 0 (a j) (fun _ => 0) := by
    unfold dyadicTerminalLp dyadicTerminal
    rw [norm_toLp_two_sq]
    have hz (k : ℕ) : StronglyMeasurable[𝒢 (G.grid (j + 0) k)] (0 : Ω → ℝ) :=
      stronglyMeasurable_const
    have hL (k : ℕ) : MemLp (0 : Ω → ℝ) ⊤ μ := MemLp.zero
    have h := dyadic_terminal_refinement_energy (r := 0) G hX hX₂ hC
      (ha j) hz (haTop j) hL
    simpa only [dyadicTerminal, Nat.add_zero, grid_integral_zero_weights, Pi.zero_apply,
      sub_zero] using h
  simpa only [heq] using hI.norm.pow 2

/-- A pointwise bound on the difference of two grid integrands gives
an energy bound in terms of the expected total compensator increment.
The pointwise bounds may hold only almost surely on each grid cell. -/
theorem dyadic_refinement_energy_le_of_uniform_bound [Preorder ι]
    [IsFiniteMeasure μ]
    (G : NestedDyadicGrids ι) {C : ι → Ω → ℝ} (hint : ∀ t, Integrable (C t) μ)
    (hmon : ∀ s t, s ≤ t → C s ≤ᵐ[μ] C t)
    {j r : ℕ} {a b : ℕ → Ω → ℝ} (haTop : ∀ k, MemLp (a k) ⊤ μ)
    (hbTop : ∀ k, MemLp (b k) ⊤ μ)
    {δ : ℝ}
    (hclose : ∀ k ∈ Finset.range (2 ^ (j + r)),
      ∀ᵐ ω ∂μ, |a (k / 2 ^ r) ω - b k ω| ≤ δ) :
    dyadicRefinementEnergy μ G C j r a b ≤
      δ ^ 2 * (∫ ω, C (G.grid (j + r) (2 ^ (j + r))) ω - C (G.grid (j + r) 0) ω ∂μ) := by
  let g := G.grid (j + r)
  let D := fun k => C (g (k + 1)) - C (g k)
  let f := fun k => a (k / 2 ^ r) - b k
  have hintegral (k : ℕ) (hk : k ∈ Finset.range (2 ^ (j + r))) :
      (∫ ω, (f k ω) ^ 2 * D k ω ∂μ) ≤ δ ^ 2 * (∫ ω, D k ω ∂μ) := by
    rw [← integral_const_mul]
    have hDint : Integrable (D k) μ := (hint _).sub (hint _)
    have hfTop : MemLp (f k) ⊤ μ := (haTop _).sub (hbTop _)
    have hsqTop : MemLp (f k * f k) ⊤ μ := hfTop.mul hfTop
    have hlp : MemLp ((f k * f k) * D k) 1 μ :=
      hsqTop.mul (memLp_one_iff_integrable.mpr hDint)
    have hleft : Integrable (fun ω => (f k ω) ^ 2 * D k ω) μ := by
      simp only [pow_two]
      exact memLp_one_iff_integrable.mp hlp
    refine integral_mono_ae hleft (hDint.const_mul _) ?_
    filter_upwards [hclose k hk, hmon (g k) (g (k + 1)) (g.monotone k.le_succ)]
      with ω hω hCω
    have hDω : 0 ≤ D k ω := sub_nonneg.mpr hCω
    have hsq : (f k ω) ^ 2 ≤ δ ^ 2 := by
      rw [← sq_abs (f k ω)]
      exact pow_le_pow_left₀ (abs_nonneg _) hω 2
    exact mul_le_mul_of_nonneg_right hsq hDω
  have htele (n : ℕ) :
      (∑ k ∈ Finset.range n, ∫ ω, D k ω ∂μ) =
        ∫ ω, C (g n) ω - C (g 0) ω ∂μ := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have h₁ := integral_sub (hint (g n)) (hint (g 0))
      have h₂ := integral_sub (hint (g (n + 1))) (hint (g n))
      have h₃ := integral_sub (hint (g (n + 1))) (hint (g 0))
      change (∫ ω, (C (g n) - C (g 0)) ω ∂μ) +
        (∫ ω, (C (g (n + 1)) - C (g n)) ω ∂μ) =
        ∫ ω, (C (g (n + 1)) - C (g 0)) ω ∂μ
      simp only [Pi.sub_apply]
      rw [h₁, h₂, h₃]
      ring
  change (∑ k ∈ Finset.range (2 ^ (j + r)), ∫ ω, (f k ω)^2 * D k ω ∂μ) ≤ _
  refine (Finset.sum_le_sum hintegral).trans_eq ?_
  rw [← Finset.mul_sum, htele]

/-- Fine left endpoints lie in the coarse cell whose coefficient they
inherit. -/
theorem uniform_dyadic_coarse_cell (T : ℝ≥0) (j r k : ℕ) :
    let G := uniformDyadicGrids T
    let s := G.grid j (k / 2 ^ r)
    let t := G.grid (j + r) k
    s ≤ t ∧ t ≤ s + T / (2 ^ j : ℝ≥0) := by
  let G := uniformDyadicGrids T
  have hp : 0 < 2 ^ r := pow_pos (by decide : 0 < (2 : ℕ)) _
  have hlow : 2 ^ r * (k / 2 ^ r) ≤ k := by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self k (2 ^ r)
  have hhigh : k ≤ 2 ^ r * (k / 2 ^ r + 1) :=
    (Nat.div_lt_iff_lt_mul hp).mp (Nat.lt_succ_self (k / 2 ^ r)) |>.le.trans_eq (Nat.mul_comm _ _)
  change G.grid j (k / 2 ^ r) ≤ G.grid (j + r) k ∧
    G.grid (j + r) k ≤ G.grid j (k / 2 ^ r) + T / (2 ^ j : ℝ≥0)
  constructor
  · rw [G.vertex_at_refinement j r (k / 2 ^ r)]
    exact (G.grid (j + r)).monotone hlow
  · have hs : G.grid (j + r) k ≤ G.grid j (k / 2 ^ r + 1) := by
      rw [G.vertex_at_refinement j r (k / 2 ^ r + 1)]
      exact (G.grid (j + r)).monotone hhigh
    refine hs.trans_eq ?_
    change ((k / 2 ^ r + 1 : ℕ) : ℝ≥0) * T / (2 ^ j : ℝ≥0) =
      ((k / 2 ^ r : ℕ) : ℝ≥0) * T / (2 ^ j : ℝ≥0) + T / (2 ^ j : ℝ≥0)
    push_cast
    rw [add_mul, one_mul, add_div]

/-- A bounded adapted integrand with a deterministic uniform modulus in
essential-supremum distance has an L² terminal integral. The coefficients
are its values at the dyadic left endpoints. -/
theorem exists_unique_integral_of_uniformly_continuous_weights
    [IsFiniteMeasure μ] {𝒢 : Filtration ℝ≥0 m} (T : ℝ≥0)
    {X C H : ℝ≥0 → Ω → ℝ}
    (hX : Martingale X 𝒢 μ) (hX₂ : ∀ t, MemLp (X t) 2 μ)
    (hC : Martingale (fun t => X t * X t - C t) 𝒢 μ)
    (hCint : ∀ t, Integrable (C t) μ) (hCmon : ∀ s t, s ≤ t → C s ≤ᵐ[μ] C t)
    (hH : StronglyAdapted 𝒢 H) (hHtop : ∀ t, MemLp (H t) ⊤ μ)
    (hmod : ∀ δ : ℝ, 0 < δ → ∃ η : ℝ≥0, 0 < η ∧
      ∀ s t : ℝ≥0, s ≤ t → t ≤ T → t ≤ s + η →
      ∀ᵐ ω ∂μ, |H s ω - H t ω| ≤ δ) :
    let G := uniformDyadicGrids T
    ∃! I : Lp ℝ 2 μ, Tendsto
      (fun j => dyadicTerminalLp G j hX₂ (fun k => hHtop (G.grid j k))) atTop (𝓝 I) := by
  let G := uniformDyadicGrids T
  let a := fun j k => H (G.grid j k)
  change ∃! I : Lp ℝ 2 μ, Tendsto
    (fun j => dyadicTerminalLp G j hX₂ (fun k => hHtop (G.grid j k))) atTop (𝓝 I)
  apply exists_unique_dyadic_terminal_limit (a := a) G hX hX₂ hC
    (fun j k => hH (G.grid j k)) (fun j k => hHtop (G.grid j k))
  intro ε hε
  let M : ℝ := ∫ ω, C T ω - C 0 ω ∂μ
  have hM : 0 ≤ M := integral_nonneg_of_ae (by
    filter_upwards [hCmon 0 T (zero_le : 0 ≤ T)] with ω hω
    exact sub_nonneg.mpr hω)
  let δ : ℝ := Real.sqrt (ε / (M + 1))
  have hδ : 0 < δ := Real.sqrt_pos_of_pos (div_pos hε (by linarith))
  have hsmall : δ ^ 2 * M < ε := by
    dsimp [δ]
    rw [Real.sq_sqrt (by positivity), div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by linarith : 0 < M + 1)).mpr
    nlinarith
  obtain ⟨η, hη, hηmod⟩ := hmod δ hδ
  have hmesh : Tendsto (fun j : ℕ => T / (2 ^ j : ℝ≥0)) atTop (𝓝 0) := by
    have hpow := NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (2 : ℝ≥0)⁻¹ < 1 by exact_mod_cast (by norm_num : (2 : ℝ)⁻¹ < 1))
    simpa only [div_eq_mul_inv, inv_pow, mul_zero] using
      (tendsto_const_nhds (x := T)).mul hpow
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hmesh.eventually_lt_const hη)
  refine ⟨N, fun j hj r => ?_⟩
  have henergy := dyadic_refinement_energy_le_of_uniform_bound
    (j := j) (r := r) (a := a j) (b := a (j + r)) (δ := δ) G hCint hCmon
    (fun k => hHtop (G.grid j k)) (fun k => hHtop (G.grid (j + r) k)) ?_
  · have he : δ ^ 2 *
        (∫ ω, C (G.grid (j + r) (2 ^ (j + r))) ω - C (G.grid (j + r) 0) ω ∂μ) =
        δ ^ 2 * M := by simp [G, M]
    exact (henergy.trans_eq he).trans_lt hsmall
  · intro k hk
    have hk' : k ≤ 2 ^ (j + r) := (Finset.mem_range.mp hk).le
    have hT : G.grid (j + r) k ≤ T := by
      simpa [G] using (G.grid (j + r)).monotone hk'
    obtain ⟨hlo, hhi⟩ := uniform_dyadic_coarse_cell T j r k
    exact hηmod _ _ hlo hT (hhi.trans (add_le_add_right (hN j hj).le _))

/-- A random bound on the grid coefficient error. Integrability is
provided by the essentially bounded envelope and the integrable
compensator. -/
theorem dyadic_refinement_energy_le_of_bounded_envelope [Preorder ι]
    [IsFiniteMeasure μ]
    (G : NestedDyadicGrids ι) {C : ι → Ω → ℝ} (hint : ∀ t, Integrable (C t) μ)
    (hmon : ∀ s t, s ≤ t → C s ≤ᵐ[μ] C t)
    {j r : ℕ} {a b : ℕ → Ω → ℝ} (haTop : ∀ k, MemLp (a k) ⊤ μ)
    (hbTop : ∀ k, MemLp (b k) ⊤ μ)
    {δ : Ω → ℝ} (hδ : MemLp δ ⊤ μ)
    (hclose : ∀ k ∈ Finset.range (2 ^ (j + r)),
      ∀ᵐ ω ∂μ, |a (k / 2 ^ r) ω - b k ω| ≤ δ ω) :
    dyadicRefinementEnergy μ G C j r a b ≤
      ∫ ω, δ ω ^ 2 *
        (C (G.grid (j + r) (2 ^ (j + r))) ω - C (G.grid (j + r) 0) ω) ∂μ := by
  let g := G.grid (j + r)
  let D := fun k => C (g (k + 1)) - C (g k)
  let f := fun k => a (k / 2 ^ r) - b k
  let W := fun t => (δ * δ) * C t
  have hδ₂ : MemLp (δ * δ) ⊤ μ := hδ.mul hδ
  have hW (t : ι) : Integrable (W t) μ :=
    memLp_one_iff_integrable.mp (hδ₂.mul (memLp_one_iff_integrable.mpr (hint t)))
  have hintegral (k : ℕ) (hk : k ∈ Finset.range (2 ^ (j + r))) :
      (∫ ω, (f k ω) ^ 2 * D k ω ∂μ) ≤
        ∫ ω, (W (g (k + 1)) - W (g k)) ω ∂μ := by
    have hDint : Integrable (D k) μ := (hint _).sub (hint _)
    have hfTop : MemLp (f k) ⊤ μ := (haTop _).sub (hbTop _)
    have hsqTop : MemLp (f k * f k) ⊤ μ := hfTop.mul hfTop
    have hlp : MemLp ((f k * f k) * D k) 1 μ :=
      hsqTop.mul (memLp_one_iff_integrable.mpr hDint)
    have hleft : Integrable (fun ω => (f k ω) ^ 2 * D k ω) μ := by
      simp only [pow_two]
      exact memLp_one_iff_integrable.mp hlp
    refine integral_mono_ae hleft ((hW _).sub (hW _)) ?_
    filter_upwards [hclose k hk, hmon (g k) (g (k + 1)) (g.monotone k.le_succ)]
      with ω hω hCω
    have hDω : 0 ≤ D k ω := sub_nonneg.mpr hCω
    have hsq : (f k ω) ^ 2 ≤ (δ ω) ^ 2 := by
      rw [← sq_abs (f k ω)]
      exact pow_le_pow_left₀ (abs_nonneg _) hω 2
    have hwt : δ ω ^ 2 * D k ω = (W (g (k + 1)) - W (g k)) ω := by
      simp only [D, W, Pi.mul_apply, Pi.sub_apply]
      ring
    exact (mul_le_mul_of_nonneg_right hsq hDω).trans_eq hwt
  have htele (n : ℕ) :
      (∑ k ∈ Finset.range n, ∫ ω, (W (g (k + 1)) - W (g k)) ω ∂μ) =
        ∫ ω, (W (g n) - W (g 0)) ω ∂μ := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [Pi.sub_apply, integral_sub (hW _) (hW _)]
      ring
  change (∑ k ∈ Finset.range (2 ^ (j + r)), ∫ ω, (f k ω)^2 * D k ω ∂μ) ≤ _
  refine (Finset.sum_le_sum hintegral).trans_eq ?_
  rw [htele]
  apply integral_congr_ae
  filter_upwards with ω
  simp only [W, g, Pi.mul_apply, Pi.sub_apply]
  ring

/-- An almost surely vanishing, uniformly bounded envelope for the
entire tail of the dyadic coefficient differences suffices for
mean-square completion. The expectation bound uses dominated
convergence with the total compensator increment as its weight. -/
theorem exists_unique_integral_under_modulus_envelope
    [IsFiniteMeasure μ] {𝒢 : Filtration ℝ≥0 m} (T : ℝ≥0)
    {X C H : ℝ≥0 → Ω → ℝ} {e : ℕ → Ω → ℝ} {B : ℝ}
    (hX : Martingale X 𝒢 μ) (hX₂ : ∀ t, MemLp (X t) 2 μ)
    (hC : Martingale (fun t => X t * X t - C t) 𝒢 μ)
    (hCint : ∀ t, Integrable (C t) μ) (hCmon : ∀ s t, s ≤ t → C s ≤ᵐ[μ] C t)
    (hH : StronglyAdapted 𝒢 H) (hHtop : ∀ t, MemLp (H t) ⊤ μ)
    (heTop : ∀ n, MemLp (e n) ⊤ μ)
    (heB : ∀ n, ∀ᵐ ω ∂μ, |e n ω| ≤ B)
    (he0 : ∀ᵐ ω ∂μ, Tendsto (fun n => e n ω) atTop (𝓝 0))
    (hclose : ∀ N j, N ≤ j → ∀ r k : ℕ, k < 2 ^ (j + r) →
      ∀ᵐ ω ∂μ, |H ((uniformDyadicGrids T).grid j (k / 2 ^ r)) ω -
        H ((uniformDyadicGrids T).grid (j + r) k) ω| ≤ e N ω) :
    let G := uniformDyadicGrids T
    ∃! I : Lp ℝ 2 μ, Tendsto
      (fun j => dyadicTerminalLp G j hX₂ (fun k => hHtop (G.grid j k))) atTop (𝓝 I) := by
  let G := uniformDyadicGrids T
  let a := fun j k => H (G.grid j k)
  let d := C T - C 0
  let cost : ℕ → Ω → ℝ := fun n ω => (e n ω)^2 * d ω
  have hd : Integrable d μ := (hCint T).sub (hCint 0)
  have hf (n : ℕ) : AEStronglyMeasurable (cost n) μ := by
    simp only [cost, pow_two]
    exact ((heTop n).aestronglyMeasurable.mul (heTop n).aestronglyMeasurable).mul hd.aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ ω ∂μ, ‖cost n ω‖ ≤ B ^ 2 * ‖d ω‖ := by
    filter_upwards [heB n] with ω hω
    have he₂ : (e n ω)^2 ≤ B^2 := by
      rw [← sq_abs (e n ω)]
      exact pow_le_pow_left₀ (abs_nonneg _) hω 2
    rw [show cost n ω = (e n ω)^2 * d ω from rfl, norm_mul,
      Real.norm_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_right he₂ (norm_nonneg _)
  have hlim : Tendsto (fun n => ∫ ω, cost n ω ∂μ) atTop (𝓝 0) := by
    have hp : ∀ᵐ ω ∂μ, Tendsto (fun n => cost n ω) atTop (𝓝 ((0 : Ω → ℝ) ω)) := by
      filter_upwards [he0] with ω hω
      simpa only [cost, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, Pi.zero_apply]
        using (hω.pow 2).mul tendsto_const_nhds
    simpa using tendsto_integral_of_dominated_convergence (fun ω => B ^ 2 * ‖d ω‖)
      hf (hd.norm.const_mul _) hbound hp
  change ∃! I : Lp ℝ 2 μ, Tendsto
    (fun j => dyadicTerminalLp G j hX₂ (fun k => hHtop (G.grid j k))) atTop (𝓝 I)
  apply exists_unique_dyadic_terminal_limit (a := a) G hX hX₂ hC
    (fun j k => hH (G.grid j k)) (fun j k => hHtop (G.grid j k))
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually_lt_const hε)
  refine ⟨N, fun j hj r => ?_⟩
  have hb := dyadic_refinement_energy_le_of_bounded_envelope
    (j := j) (r := r) (a := a j) (b := a (j + r)) G hCint hCmon
    (fun k => hHtop (G.grid j k)) (fun k => hHtop (G.grid (j + r) k)) (heTop N)
    (fun k hk => hclose N j hj r k (Finset.mem_range.mp hk))
  exact (by simpa [G, d, cost, Pi.sub_apply] using hb :
    dyadicRefinementEnergy μ G C j r (a j) (a (j + r)) ≤ ∫ ω, cost N ω ∂μ).trans_lt
    (hN N le_rfl)

/-- A deterministic continuous path has a uniform modulus on the
compact integration interval. -/
private theorem path_modulus {T : ℝ≥0} {f : ℝ≥0 → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 T)) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ≥0, 0 < η ∧ ∀ s t : ℝ≥0, s ≤ t → t ≤ T → t ≤ s + η →
      |f s - f t| ≤ ε := by
  have h :=
    Metric.uniformContinuousOn_iff.mp (isCompact_Icc.uniformContinuousOn_of_continuous hf)
  obtain ⟨d, hd, hmod⟩ := h ε hε
  let η : ℝ≥0 := ⟨d / 2, by positivity⟩
  refine ⟨η, show (0 : ℝ) < d / 2 by positivity, fun s t hst ht hspan => ?_⟩
  have hdist : dist s t < d := by
    change dist (s : ℝ) (t : ℝ) < d
    have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
    have hspan' : (t : ℝ) ≤ (s : ℝ) + η := by exact_mod_cast hspan
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst')]
    change (t : ℝ) ≤ (s : ℝ) + d / 2 at hspan'
    linarith
  exact (hmod s ⟨zero_le, hst.trans ht⟩ t ⟨zero_le, ht⟩ hdist).le

/-- Terminal stochastic integral of an adapted, essentially bounded
integrand with almost surely continuous paths on the given interval.
The pathwise modulus may be random. -/
theorem exists_unique_integral_of_bounded_continuous_paths
    [IsFiniteMeasure μ] {𝒢 : Filtration ℝ≥0 m} (T : ℝ≥0)
    {X C H : ℝ≥0 → Ω → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hX : Martingale X 𝒢 μ) (hX₂ : ∀ t, MemLp (X t) 2 μ)
    (hC : Martingale (fun t => X t * X t - C t) 𝒢 μ)
    (hCint : ∀ t, Integrable (C t) μ) (hCmon : ∀ s t, s ≤ t → C s ≤ᵐ[μ] C t)
    (hH : StronglyAdapted 𝒢 H) (hHtop : ∀ t, MemLp (H t) ⊤ μ)
    (hcts : ∀ᵐ ω ∂μ, ContinuousOn (fun t => H t ω) (Set.Icc 0 T))
    (hbounded : ∀ᵐ ω ∂μ, ∀ t ≤ T, |H t ω| ≤ B) :
    let G := uniformDyadicGrids T
    ∃! I : Lp ℝ 2 μ, Tendsto
      (fun j => dyadicTerminalLp G j hX₂ (fun k => hHtop (G.grid j k))) atTop (𝓝 I) := by
  classical
  let G := uniformDyadicGrids T
  let diff := fun j r k ω => |H (G.grid j (k / 2 ^ r)) ω - H (G.grid (j + r) k) ω|
  let entry := fun N j r k ω =>
    if N ≤ j ∧ k < 2 ^ (j + r) then ENNReal.ofReal (diff j r k ω) else 0
  let E : ℕ → Ω → ENNReal := fun N ω => ⨆ j : ℕ, ⨆ r : ℕ, ⨆ k : ℕ, entry N j r k ω
  let e : ℕ → Ω → ℝ := fun N ω => (E N ω).toReal
  have hHmeas (t : ℝ≥0) : Measurable (H t) := ((hH t).mono (𝒢.le t)).measurable
  have hdiff (j r k : ℕ) : Measurable (diff j r k) :=
    continuous_abs.measurable.comp ((hHmeas _).sub (hHmeas _))
  have hEmeas (N : ℕ) : Measurable (E N) := by
    apply Measurable.iSup
    intro j
    apply Measurable.iSup
    intro r
    apply Measurable.iSup
    intro k
    by_cases h : N ≤ j ∧ k < 2 ^ (j + r)
    · simpa [entry, h] using (hdiff j r k).ennreal_ofReal
    · simp [entry, h]
  have hmesh : Tendsto (fun j : ℕ => T / (2 ^ j : ℝ≥0)) atTop (𝓝 0) := by
    have hpow := NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (2 : ℝ≥0)⁻¹ < 1 by exact_mod_cast (by norm_num : (2 : ℝ)⁻¹ < 1))
    simpa only [div_eq_mul_inv, inv_pow, mul_zero] using
      (tendsto_const_nhds (x := T)).mul hpow
  have hvalid (j r k : ℕ) (hk : k < 2 ^ (j + r)) : G.grid (j + r) k ≤ T := by
    simpa [G] using (G.grid (j + r)).monotone hk.le
  have hEB (N : ℕ) : ∀ᵐ ω ∂μ, E N ω ≤ ENNReal.ofReal (2 * B) := by
    filter_upwards [hbounded] with ω hω
    refine iSup_le fun j => iSup_le fun r => iSup_le fun k => ?_
    by_cases h : N ≤ j ∧ k < 2 ^ (j + r)
    · obtain ⟨hlo, _⟩ := uniform_dyadic_coarse_cell T j r k
      have ht := hvalid j r k h.2
      have h₁ := hω _ (hlo.trans ht)
      have h₂ := hω _ ht
      have hb : diff j r k ω ≤ 2 * B := by
        dsimp [diff]
        have htri := abs_sub_le (H (G.grid j (k / 2 ^ r)) ω) (0 : ℝ)
          (H (G.grid (j + r) k) ω)
        rw [sub_zero, zero_sub, abs_neg] at htri
        linarith
      simpa [entry, h] using ENNReal.ofReal_le_ofReal hb
    · simp [entry, h]
  have heB (N : ℕ) : ∀ᵐ ω ∂μ, |e N ω| ≤ 2 * B := by
    filter_upwards [hEB N] with ω hω
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hω
    rw [ENNReal.toReal_ofReal (by positivity)] at hreal
    simpa [e, abs_of_nonneg ENNReal.toReal_nonneg] using hreal
  have heTop (N : ℕ) : MemLp (e N) ⊤ μ :=
    memLp_top_of_bound (hEmeas N).ennreal_toReal.aestronglyMeasurable (2 * B)
      (by simpa [Real.norm_eq_abs] using heB N)
  have he0 : ∀ᵐ ω ∂μ, Tendsto (fun N => e N ω) atTop (𝓝 0) := by
    filter_upwards [hcts] with ω hω
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨η, hη, hmod⟩ := path_modulus hω (show 0 < ε / 2 by positivity)
    obtain ⟨J, hJ⟩ := eventually_atTop.mp (hmesh.eventually_lt_const hη)
    refine ⟨J, fun N hN => ?_⟩
    have hE : E N ω ≤ ENNReal.ofReal (ε / 2) := by
      refine iSup_le fun j => iSup_le fun r => iSup_le fun k => ?_
      by_cases h : N ≤ j ∧ k < 2 ^ (j + r)
      · obtain ⟨hlo, hhi⟩ := uniform_dyadic_coarse_cell T j r k
        have hspan : G.grid (j + r) k ≤ G.grid j (k / 2 ^ r) + η :=
          hhi.trans (add_le_add_right (hJ j (hN.trans h.1)).le _)
        simpa [entry, h] using ENNReal.ofReal_le_ofReal (hmod _ _ hlo (hvalid j r k h.2) hspan)
      · simp [entry, h]
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hE
    rw [ENNReal.toReal_ofReal (by positivity)] at hh
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (show 0 ≤ e N ω from ENNReal.toReal_nonneg)]
    exact hh.trans_lt (by linarith)
  refine exists_unique_integral_under_modulus_envelope T hX hX₂ hC hCint hCmon
    hH hHtop heTop heB he0 ?_
  intro N j hNj r k hk
  filter_upwards [hEB N] with ω hω
  have hf : E N ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hω
  have hh : ENNReal.ofReal (diff j r k ω) ≤ E N ω := by
    have hentry : entry N j r k ω ≤ E N ω :=
      le_iSup_of_le j (le_iSup_of_le r (le_iSup (fun l => entry N j r l ω) k))
    simpa [entry, hNj, hk] using hentry
  have hr := ENNReal.toReal_mono hf hh
  rw [ENNReal.toReal_ofReal (abs_nonneg _)] at hr
  exact hr

end RoughHeston

#print axioms RoughHeston.NestedDyadicGrids.integral_at_refinement
#print axioms RoughHeston.NestedDyadicGrids.predictable_lift
#print axioms RoughHeston.grid_integral_square_compensator
#print axioms RoughHeston.dyadic_terminal_refinement_energy
#print axioms RoughHeston.dist_toLp_two_sq
#print axioms RoughHeston.dyadic_terminalLp_refinement_energy
#print axioms RoughHeston.exists_unique_dyadic_terminal_limit
#print axioms RoughHeston.dyadic_terminal_limit_independent

#print axioms RoughHeston.uniform_dyadic_terminal_vertex

#print axioms RoughHeston.dyadic_terminal_limit_isometry

#print axioms RoughHeston.dyadic_refinement_energy_le_of_uniform_bound
#print axioms RoughHeston.uniform_dyadic_coarse_cell
#print axioms RoughHeston.exists_unique_integral_of_uniformly_continuous_weights

#print axioms RoughHeston.dyadic_refinement_energy_le_of_bounded_envelope
#print axioms RoughHeston.exists_unique_integral_under_modulus_envelope

#print axioms RoughHeston.exists_unique_integral_of_bounded_continuous_paths
