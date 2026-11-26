import StochasticCompletion

/-! Deterministic left-endpoint interpolation on the uniform dyadic grid. -/

open Set Filter
open scoped BigOperators NNReal Topology

namespace RoughHeston

/-- Each point strictly after the initial grid vertex and at most the
terminal vertex lies in a half-open grid cell. -/
theorem exists_grid_cell (grid : ℕ →o ℝ≥0) {n : ℕ} {s : ℝ≥0}
    (hs : s ∈ Ioc (grid 0) (grid n)) :
    ∃ k < n, s ∈ Ioc (grid k) (grid (k + 1)) := by
  induction n with
  | zero => exact (not_lt_of_ge hs.2 hs.1).elim
  | succ n ih =>
    by_cases h : s ≤ grid n
    · obtain ⟨k, hk, hc⟩ := ih ⟨hs.1, h⟩
      exact ⟨k, hk.trans (Nat.lt_succ_self n), hc⟩
    · exact ⟨n, Nat.lt_succ_self n, lt_of_not_ge h, hs.2⟩

private theorem grid_cell_unique (grid : ℕ →o ℝ≥0) {s : ℝ≥0} {k l : ℕ}
    (hk : s ∈ Ioc (grid k) (grid (k + 1)))
    (hl : s ∈ Ioc (grid l) (grid (l + 1))) : k = l := by
  rcases lt_trichotomy k l with hkl | hkl | hkl
  · exact (not_lt_of_ge (hk.2.trans (grid.monotone (Nat.succ_le_of_lt hkl))) hl.1).elim
  · exact hkl
  · exact (not_lt_of_ge (hl.2.trans (grid.monotone (Nat.succ_le_of_lt hkl))) hk.1).elim

/-- Step interpolation obtained by sampling each cell at its left endpoint. -/
noncomputable def uniformDyadicStep (T : ℝ≥0) (j : ℕ) (f : ℝ≥0 → ℝ) (s : ℝ≥0) : ℝ :=
  let grid := (uniformDyadicGrids T).grid j
  ∑ k ∈ Finset.range (2 ^ j), (Ioc (grid k) (grid (k + 1))).indicator (fun _ => f (grid k)) s

/-- At a point in a cell, the step interpolation takes the corresponding
left-endpoint value. -/
theorem uniformDyadicStep_eq_of_cell {T s : ℝ≥0} {j k : ℕ}
    (f : ℝ≥0 → ℝ) (hk : k < 2 ^ j)
    (hs : s ∈ Ioc ((uniformDyadicGrids T).grid j k) ((uniformDyadicGrids T).grid j (k + 1))) :
    uniformDyadicStep T j f s = f ((uniformDyadicGrids T).grid j k) := by
  classical
  unfold uniformDyadicStep
  rw [Finset.sum_eq_single k]
  · rw [indicator_of_mem hs]
  · intro q _ hq
    apply indicator_of_notMem
    exact fun hq' => hq (grid_cell_unique ((uniformDyadicGrids T).grid j) hq' hs)
  · intro h
    exact (h (Finset.mem_range.mpr hk)).elim

/-- Every interpolated value on the horizon is one of the cell coefficients. -/
theorem uniformDyadicStep_eq_coeff {T s : ℝ≥0}
    (f : ℝ≥0 → ℝ) (hs : s ∈ Ioc 0 T) (j : ℕ) :
    ∃ k < 2 ^ j, s ∈ Ioc ((uniformDyadicGrids T).grid j k) ((uniformDyadicGrids T).grid j (k + 1)) ∧
      uniformDyadicStep T j f s = f ((uniformDyadicGrids T).grid j k) := by
  have hmem : s ∈ Ioc ((uniformDyadicGrids T).grid j 0)
      ((uniformDyadicGrids T).grid j (2 ^ j)) := by simpa only
    [uniform_dyadic_first_vertex, uniform_dyadic_terminal_vertex] using hs
  obtain ⟨k, hk, hc⟩ := exists_grid_cell ((uniformDyadicGrids T).grid j) hmem
  exact ⟨k, hk, hc, uniformDyadicStep_eq_of_cell f hk hc⟩

private theorem dyadic_step_next_vertex (T : ℝ≥0) (j k : ℕ) :
    (uniformDyadicGrids T).grid j (k + 1) =
      (uniformDyadicGrids T).grid j k + T / (2 ^ j : ℝ≥0) := by
  change ((k + 1 : ℕ) : ℝ≥0) * T / (2 ^ j : ℝ≥0) =
    (k : ℝ≥0) * T / (2 ^ j : ℝ≥0) + T / (2 ^ j : ℝ≥0)
  push_cast
  rw [add_mul, one_mul, add_div]

/-- Dyadic step interpolation converges at each point of the half-open
horizon for a continuous function on the closed horizon. -/
theorem tendsto_uniformDyadicStep {T s : ℝ≥0} {f : ℝ≥0 → ℝ}
    (hf : ContinuousOn f (Icc 0 T)) (hs : s ∈ Ioc 0 T) :
    Tendsto (fun j => uniformDyadicStep T j f s) atTop (𝓝 (f s)) := by
  choose k hk hc he using uniformDyadicStep_eq_coeff f hs
  let x (j : ℕ) := (uniformDyadicGrids T).grid j (k j)
  have hx (j : ℕ) : x j ∈ Icc 0 T := ⟨zero_le, (hc j).1.le.trans hs.2⟩
  have hmesh : Tendsto (fun j : ℕ => T / (2 ^ j : ℝ≥0)) atTop (𝓝 0) := by
    have hp := NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (2 : ℝ≥0)⁻¹ < 1 by exact_mod_cast (by norm_num : (2 : ℝ)⁻¹ < 1))
    simpa only [div_eq_mul_inv, inv_pow, mul_zero] using (tendsto_const_nhds (x := T)).mul hp
  have hmeshR : Tendsto (fun j : ℕ => ((T / (2 ^ j : ℝ≥0) : ℝ≥0) : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, NNReal.coe_zero] using
      (NNReal.continuous_coe.tendsto (0 : ℝ≥0)).comp hmesh
  have hdist (j : ℕ) : dist (x j) s ≤ ((T / (2 ^ j : ℝ≥0) : ℝ≥0) : ℝ) := by
    have hleft : (x j : ℝ) ≤ (s : ℝ) := by exact_mod_cast (hc j).1.le
    have hright : (s : ℝ) ≤ (x j : ℝ) + ((T / (2 ^ j : ℝ≥0) : ℝ≥0) : ℝ) := by
      have hh := (hc j).2
      rw [dyadic_step_next_vertex] at hh
      exact_mod_cast hh
    rw [NNReal.dist_eq, abs_of_nonpos (sub_nonpos.mpr hleft)]
    linarith
  have hxt : Tendsto x atTop (𝓝 s) :=
    tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero (fun _ => dist_nonneg) hdist hmeshR)
  have hxw : Tendsto x atTop (𝓝[Icc (0 : ℝ≥0) T] s) :=
    tendsto_nhdsWithin_iff.mpr ⟨hxt, Eventually.of_forall hx⟩
  have hfs : Tendsto f (𝓝[Icc (0 : ℝ≥0) T] s) (𝓝 (f s)) := hf s ⟨zero_le, hs.2⟩
  exact (hfs.comp hxw).congr (fun j => (he j).symm)

end RoughHeston

#print axioms RoughHeston.exists_grid_cell
#print axioms RoughHeston.uniformDyadicStep_eq_coeff
#print axioms RoughHeston.tendsto_uniformDyadicStep
