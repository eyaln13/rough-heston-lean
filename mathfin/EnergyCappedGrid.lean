import StochasticFoundation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory Set Filter
open scoped BigOperators MeasureTheory

namespace RoughHeston

/-- The uncapped quadratic energy accumulated before cell n. -/
noncomputable def gridEnergy (h a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, h j * a j ^ 2

/-- A predictable cell consumes its original energy up to the energy
budget remaining at its left endpoint. -/
noncomputable def gridCappedRatio (δ : ℝ) (h a : ℕ → ℝ) (n : ℕ) : ℝ :=
  let q := h n * a n ^ 2
  if 0 < q then Real.sqrt (min 1 (max 0 (δ - gridEnergy h a n) / q)) else 1

noncomputable def gridCappedCoefficient (δ : ℝ) (h a : ℕ → ℝ) (n : ℕ) : ℝ :=
  a n * gridCappedRatio δ h a n

theorem gridCappedRatio_bounds (δ : ℝ) (h a : ℕ → ℝ) (n : ℕ) :
    gridCappedRatio δ h a n ∈ Icc (0 : ℝ) 1 := by
  dsimp only [gridCappedRatio]
  split
  · exact ⟨Real.sqrt_nonneg _, (Real.sqrt_le_sqrt (min_le_left _ _)).trans_eq Real.sqrt_one⟩
  · exact ⟨zero_le_one, le_rfl⟩

private theorem gridCappedCoefficient_energy {δ : ℝ} {h a : ℕ → ℝ} {n : ℕ}
    (hh : 0 ≤ h n) :
    h n * gridCappedCoefficient δ h a n ^ 2 =
      min (h n * a n ^ 2) (max 0 (δ - gridEnergy h a n)) := by
  let q := h n * a n ^ 2
  let k := max 0 (δ - gridEnergy h a n)
  have hq : 0 ≤ q := mul_nonneg hh (sq_nonneg _)
  have hk : 0 ≤ k := le_max_left _ _
  by_cases hq₀ : 0 < q
  · unfold gridCappedCoefficient gridCappedRatio
    change h n * (a n * (if 0 < q then Real.sqrt (min 1 (k / q)) else 1)) ^ 2 = min q k
    rw [ite_eq_left hq₀, mul_pow, Real.sq_sqrt (le_min zero_le_one (div_nonneg hk hq))]
    rw [← mul_assoc]
    change q * min 1 (k / q) = min q k
    by_cases hle : k ≤ q
    · rw [min_eq_right ((div_le_one hq₀).2 hle), min_eq_right hle, mul_comm,
        div_mul_cancel₀ _ hq₀.ne']
    · have hle' : q ≤ k := le_of_not_ge hle
      rw [min_eq_left ((one_le_div hq₀).2 hle'), min_eq_left hle', mul_one]
  · have hqeq : q = 0 := le_antisymm (le_of_not_gt hq₀) hq
    unfold gridCappedCoefficient gridCappedRatio
    change h n * (a n * (if 0 < q then Real.sqrt (min 1 (k / q)) else 1)) ^ 2 = min q k
    rw [ite_eq_right hq₀, mul_one, show h n * a n ^ 2 = q from rfl,
      hqeq, min_eq_left hk]

private theorem min_energy_increment {δ E q : ℝ} (hq : 0 ≤ q) :
    min δ (E + q) - min δ E = min q (max 0 (δ - E)) := by
  by_cases hE : E ≤ δ
  · rw [min_eq_right hE, max_eq_right (sub_nonneg.mpr hE)]
    by_cases hq' : q ≤ δ - E
    · have hE' : E + q ≤ δ := by linarith
      rw [min_eq_right hE', min_eq_left hq']
      ring
    · have hE' : δ ≤ E + q := by linarith [le_of_not_ge hq']
      rw [min_eq_left hE', min_eq_right (le_of_not_ge hq')]
  · have hE' : δ ≤ E := le_of_not_ge hE
    rw [min_eq_left hE', min_eq_left (by linarith), max_eq_left (sub_nonpos.mpr hE'),
      min_eq_right hq, sub_self]

/-- On every finite grid, the capped weights spend exactly the
minimum of the original energy and the budget. -/
theorem gridEnergy_capped_eq_min {δ : ℝ} (hδ : 0 ≤ δ) {h a : ℕ → ℝ}
    (hh : ∀ n, 0 ≤ h n) (n : ℕ) :
    gridEnergy h (gridCappedCoefficient δ h a) n = min δ (gridEnergy h a n) := by
  induction n with
  | zero => simp [gridEnergy, min_eq_right hδ]
  | succ n ih =>
    have hsum (u : ℕ → ℝ) : gridEnergy h u (n + 1) =
        gridEnergy h u n + h n * u n ^ 2 := Finset.sum_range_succ _ _
    rw [hsum, hsum, ih, gridCappedCoefficient_energy (hh n),
      ← min_energy_increment (mul_nonneg (hh n) (sq_nonneg (a n)))]
    ring

/-- Capping a grid approximation changes its squared energy by at most
the amount by which the original approximation exceeds the budget. -/
theorem gridEnergy_capping_error_le {δ : ℝ} (hδ : 0 ≤ δ)
    {h a : ℕ → ℝ} (hh : ∀ n, 0 ≤ h n) (n : ℕ) :
    gridEnergy h (fun j => a j - gridCappedCoefficient δ h a j) n ≤
      max 0 (gridEnergy h a n - δ) := by
  have hpoint (j : ℕ) : h j * (a j - gridCappedCoefficient δ h a j) ^ 2 ≤
      h j * a j ^ 2 - h j * gridCappedCoefficient δ h a j ^ 2 := by
    let r := gridCappedRatio δ h a j
    obtain ⟨hr₀, hr₁⟩ := gridCappedRatio_bounds δ h a j
    have hr : (1 - r) ^ 2 ≤ 1 - r ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ r from hr₀) (sub_nonneg.mpr (show r ≤ 1 from hr₁))]
    change h j * (a j - a j * r) ^ 2 ≤ h j * a j ^ 2 - h j * (a j * r) ^ 2
    calc
      _ = (h j * a j ^ 2) * (1 - r) ^ 2 := by ring
      _ ≤ (h j * a j ^ 2) * (1 - r ^ 2) :=
        mul_le_mul_of_nonneg_left hr (mul_nonneg (hh j) (sq_nonneg _))
      _ = _ := by ring
  calc
    _ ≤ ∑ j ∈ Finset.range n, (h j * a j ^ 2 - h j * gridCappedCoefficient δ h a j ^ 2) :=
      Finset.sum_le_sum fun j _ => hpoint j
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      change gridEnergy h a n - gridEnergy h (gridCappedCoefficient δ h a) n = _
      rw [gridEnergy_capped_eq_min hδ hh]
      by_cases hl : gridEnergy h a n ≤ δ
      · rw [min_eq_right hl, sub_self, max_eq_left (sub_nonpos.mpr hl)]
      · have hl' := le_of_not_ge hl
        rw [min_eq_left hl', max_eq_right (sub_nonneg.mpr hl')]

/-- Capping does not introduce any dependence on future grid values. -/
theorem gridCappedCoefficient_stronglyMeasurable {Ω : Type*} {m : MeasurableSpace Ω}
    {𝒢 : Filtration ℕ m} {a : ℕ → Ω → ℝ} (ha : ∀ n, StronglyMeasurable[𝒢 n] (a n))
    (δ : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    StronglyMeasurable[𝒢 n] (fun ω => gridCappedCoefficient δ h (fun j => a j ω) n) := by
  let : MeasurableSpace Ω := 𝒢 n
  let q (ω : Ω) := h n * a n ω ^ 2
  let E (ω : Ω) := gridEnergy h (fun j => a j ω) n
  have hq : Measurable q := measurable_const.mul ((ha n).measurable.pow_const (2 : ℕ))
  have hE : Measurable E := Finset.measurable_sum _ fun j hj =>
    measurable_const.mul (((ha j).mono (𝒢.mono (Finset.mem_range.mp hj).le)).measurable.pow_const (2 : ℕ))
  have hR : Measurable (fun ω => if 0 < q ω then Real.sqrt (min 1 (max 0 (δ - E ω) / q ω)) else 1) :=
    Measurable.ite (measurableSet_lt measurable_const hq)
      (measurable_const.min ((measurable_const.max (measurable_const.sub hE)).div hq)).sqrt
      measurable_const
  exact ((ha n).measurable.mul hR).stronglyMeasurable

end RoughHeston

#print axioms RoughHeston.gridEnergy_capped_eq_min
#print axioms RoughHeston.gridEnergy_capping_error_le
#print axioms RoughHeston.gridCappedCoefficient_stronglyMeasurable
