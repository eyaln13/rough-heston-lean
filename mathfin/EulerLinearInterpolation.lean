import DyadicStepApproximation
import CanonicalPairPath

/-! Continuous affine interpolation of a finite deterministic grid. -/

open Set
open scoped NNReal

namespace RoughHeston

/-- The fraction of a deterministic cell elapsed at time `s`. -/
noncomputable def gridCellFraction (grid : ℕ →o ℝ≥0) (k : ℕ) (s : ℝ≥0) : ℝ :=
  max 0 (min 1 (((s : ℝ) - (grid k : ℝ)) /
    ((grid (k + 1) : ℝ) - (grid k : ℝ))))

private theorem gridCellFraction_eq_zero (grid : ℕ →o ℝ≥0) {k : ℕ} {s : ℝ≥0}
    (hs : s ≤ grid k) : gridCellFraction grid k s = 0 := by
  have hden := sub_nonneg.mpr (NNReal.coe_le_coe.mpr (grid.monotone k.le_succ))
  have hnum := sub_nonpos.mpr (NNReal.coe_le_coe.mpr hs)
  unfold gridCellFraction
  exact max_eq_left ((min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg hnum hden))

private theorem gridCellFraction_eq_one (grid : ℕ →o ℝ≥0) {k : ℕ} {s : ℝ≥0}
    (hk : grid k < grid (k + 1)) (hs : grid (k + 1) ≤ s) : gridCellFraction grid k s = 1 := by
  have hden := sub_pos.mpr (NNReal.coe_lt_coe.mpr hk)
  have hnum : (grid (k+1) : ℝ) - (grid k : ℝ) ≤ (s : ℝ) - (grid k : ℝ) :=
    sub_le_sub_right (NNReal.coe_le_coe.mpr hs) _
  unfold gridCellFraction
  rw [min_eq_left ((le_div_iff₀ hden).2 (by simpa only [one_mul] using hnum)),
    max_eq_right (by norm_num)]

private theorem gridCellFraction_eq_affine (grid : ℕ →o ℝ≥0) {k : ℕ} {s : ℝ≥0}
    (hk : grid k < grid (k + 1)) (hs : s ∈ Icc (grid k) (grid (k + 1))) :
    gridCellFraction grid k s =
      ((s : ℝ) - (grid k : ℝ)) / ((grid (k + 1) : ℝ) - (grid k : ℝ)) := by
  have hden := sub_pos.mpr (NNReal.coe_lt_coe.mpr hk)
  have hnum0 := sub_nonneg.mpr (NNReal.coe_le_coe.mpr hs.1)
  have hnum1 : (s : ℝ) - (grid k : ℝ) ≤ (grid (k+1) : ℝ) - (grid k : ℝ) :=
    sub_le_sub_right (NNReal.coe_le_coe.mpr hs.2) _
  unfold gridCellFraction
  rw [min_eq_right ((div_le_iff₀ hden).2 (by simpa only [one_mul] using hnum1)),
    max_eq_right (div_nonneg hnum0 hden.le)]

/-- The interpolation is globally continuous in its time argument, and
it is constant past its last grid cell. -/
noncomputable def gridLinearInterpolate (grid : ℕ →o ℝ≥0) (f : ℕ → ℝ) : ℕ → ℝ≥0 → ℝ
  | 0, _ => f 0
  | n + 1, s => gridLinearInterpolate grid f n s +
    gridCellFraction grid n s * (f (n + 1) - f n)

theorem continuous_gridLinearInterpolate (grid : ℕ →o ℝ≥0) (f : ℕ → ℝ) (n : ℕ) :
    Continuous (gridLinearInterpolate grid f n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have h : Continuous (gridCellFraction grid n) := by
      unfold gridCellFraction
      exact continuous_const.max (continuous_const.min
        ((NNReal.continuous_coe.sub continuous_const).div_const _))
    exact ih.add (h.mul continuous_const)

private theorem gridLinearInterpolate_eq_on_before (grid : ℕ →o ℝ≥0) (f : ℕ → ℝ)
    {k n : ℕ} (hkn : k ≤ n) {s : ℝ≥0} (hs : s ≤ grid k) :
    gridLinearInterpolate grid f n s = gridLinearInterpolate grid f k s := by
  induction n, hkn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [gridLinearInterpolate, gridCellFraction_eq_zero grid (hs.trans (grid.monotone hn)),
      zero_mul, add_zero, ih]

private theorem gridLinearInterpolate_eq_on_after (grid : ℕ →o ℝ≥0) (f : ℕ → ℝ)
    (n : ℕ) (hgrid : ∀ k < n, grid k < grid (k + 1)) {s : ℝ≥0} (hs : grid n ≤ s) :
    gridLinearInterpolate grid f n s = f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [gridLinearInterpolate, gridCellFraction_eq_one grid (hgrid n n.lt_succ_self) hs,
      ih (fun k hk => hgrid k (hk.trans n.lt_succ_self))
        ((grid.monotone n.le_succ).trans hs), one_mul]
    ring

/-- Affine formula on each closed cell of the finite grid. -/
theorem gridLinearInterpolate_eq_on_cell (grid : ℕ →o ℝ≥0) (f : ℕ → ℝ) {n k : ℕ}
    (hgrid : ∀ q < n, grid q < grid (q + 1)) (hk : k < n)
    {s : ℝ≥0} (hs : s ∈ Icc (grid k) (grid (k + 1))) :
    gridLinearInterpolate grid f n s = f k +
      ((s : ℝ) - (grid k : ℝ)) / ((grid (k + 1) : ℝ) - (grid k : ℝ)) *
        (f (k+1) - f k) := by
  rw [gridLinearInterpolate_eq_on_before grid f hk, gridLinearInterpolate,
    gridLinearInterpolate_eq_on_after grid f k (fun q hq => hgrid q (hq.trans hk)) hs.1,
    gridCellFraction_eq_affine grid (hgrid k hk) hs]
  exact hs.2

/-- The interpolant reproduces all sampled values at grid vertices. -/
theorem gridLinearInterpolate_at_vertex (grid : ℕ →o ℝ≥0) (f : ℕ → ℝ) {k n : ℕ}
    (hgrid : ∀ q < n, grid q < grid (q + 1)) (hk : k ≤ n) :
    gridLinearInterpolate grid f n (grid k) = f k :=
  (gridLinearInterpolate_eq_on_before grid f hk le_rfl).trans
    (gridLinearInterpolate_eq_on_after grid f k (fun q hq => hgrid q (hq.trans_le hk)) le_rfl)

theorem exists_grid_closed_cell (grid : ℕ →o ℝ≥0) {n : ℕ} (hn : 0 < n)
    {s : ℝ≥0} (hs : s ∈ Icc (grid 0) (grid n)) :
    ∃ k < n, s ∈ Icc (grid k) (grid (k + 1)) := by
  rcases eq_or_lt_of_le hs.1 with he | hlt
  · exact ⟨0, hn, hs.1, he.symm.le.trans (grid.monotone (Nat.zero_le 1))⟩
  · obtain ⟨k, hk, h⟩ := exists_grid_cell grid ⟨hlt, hs.2⟩
    exact ⟨k, hk, h.1.le, h.2⟩

theorem measurable_gridLinearInterpolate_eval {Ω : Type*} [MeasurableSpace Ω]
    (grid : ℕ →o ℝ≥0) (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k)) (n : ℕ)
    (s : ℝ≥0) :
    Measurable (fun ω => gridLinearInterpolate grid (fun k => X k ω) n s) := by
  induction n with
  | zero => exact hX 0
  | succ n ih => exact ih.add (measurable_const.mul ((hX (n+1)).sub (hX n)))

/-- Two continuous interpolants viewed as one canonical pair path. -/
noncomputable def gridLinearInterpolatePairPath (T : ℝ≥0) (grid : ℕ →o ℝ≥0)
    (X Y : ℕ → ℝ) (n : ℕ) : CanonicalPath T (ℝ × ℝ) where
  toFun s := (gridLinearInterpolate grid X n s, gridLinearInterpolate grid Y n s)
  continuous_toFun := ((continuous_gridLinearInterpolate grid X n).comp continuous_subtype_val).prodMk
    ((continuous_gridLinearInterpolate grid Y n).comp continuous_subtype_val)

theorem measurable_gridLinearInterpolatePairPath {Ω : Type*} [MeasurableSpace Ω]
    (T : ℝ≥0) (grid : ℕ →o ℝ≥0) (X Y : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hY : ∀ k, Measurable (Y k)) (n : ℕ) :
    Measurable (fun ω => gridLinearInterpolatePairPath T grid (fun k => X k ω) (fun k => Y k ω) n) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro s
  exact (measurable_gridLinearInterpolate_eval grid X hX n s).prodMk
    (measurable_gridLinearInterpolate_eval grid Y hY n s)

#print axioms RoughHeston.continuous_gridLinearInterpolate
#print axioms RoughHeston.gridLinearInterpolate_eq_on_cell
#print axioms RoughHeston.gridLinearInterpolate_at_vertex
#print axioms RoughHeston.measurable_gridLinearInterpolatePairPath

end RoughHeston
