import FractionalResolventSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! The second-kind resolvent factored into a single profile of κt^α.
Estimates on a compact set of arguments are uniform in the rescaled
mean-reversion coefficient. -/

open MeasureTheory Set Filter
open scoped Topology

namespace RoughHeston

noncomputable def fractionalResolventProfile (α x : ℝ) : ℝ :=
  ∑' n : ℕ, x^n/Real.Gamma (((n:ℝ)+1)*α)

theorem fractionalResolventProfile_zero (α : ℝ) :
    fractionalResolventProfile α 0 = 1/Real.Gamma α := by
  rw [fractionalResolventProfile,tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]

theorem fractionalResolventProfile_summable {α : ℝ} (hα : 0 < α) (x : ℝ) :
    Summable (fun n : ℕ => x^n/Real.Gamma (((n:ℝ)+1)*α)) := by
  apply Summable.of_norm_bounded (summable_fractionalResolvent_abs_coefficients hα x)
  intro n
  simp only [Real.norm_eq_abs,abs_div,abs_pow,
    abs_of_pos (Real.Gamma_pos_of_pos (by positivity : 0 < ((n:ℝ)+1)*α)) ,le_refl]

theorem fractionalSecondKindResolvent_factor {α κ t : ℝ} (ht : 0 < t) :
    fractionalSecondKindResolvent α κ t = t^(α-1)*fractionalResolventProfile α (-κ*t^α) := by
  rw [fractionalSecondKindResolvent, fractionalResolventProfile, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [fractionalK, ite_eq_right (not_le.mpr ht),
    show ((n:ℝ)+1)*α-1 = (α-1) + α*(n:ℝ) by ring,Real.rpow_add ht,Real.rpow_mul ht.le,
    Real.rpow_natCast,mul_pow]
  ring

/-- A uniform Lipschitz bound obtained by summing the weighted Gamma
coefficients. This also bounds perturbations around the value at zero. -/
theorem fractionalResolventProfile_lipschitz_on {α A : ℝ} (hα : 0 < α) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ, |x| ≤ A → |y| ≤ A →
      |fractionalResolventProfile α x-fractionalResolventProfile α y| ≤ C*|x-y| := by
  let w (n : ℕ) := ((n:ℝ)+1)*A^n/Real.Gamma (((n:ℝ)+1)*α)
  have hw : Summable w := summable_fractionalResolvent_coefficients hα A
  have hAn : 0 ≤ A := zero_le_one.trans hA
  have hwn (n : ℕ) : 0 ≤ w n := by
    dsimp [w]; exact div_nonneg (by positivity) (Real.Gamma_pos_of_pos (by positivity)).le
  refine ⟨∑' n,w n,tsum_nonneg hwn,?_⟩
  intro x y hx hy
  let f (n : ℕ) := x^n/Real.Gamma (((n:ℝ)+1)*α)-y^n/Real.Gamma (((n:ℝ)+1)*α)
  have hb (n : ℕ) : ‖f n‖ ≤ w n*|x-y| := by
    have hp := abs_pow_sub_pow_le (a := x) (b := y) (n := n)
    have hp' : max |x| |y| ^ (n-1) ≤ A^n :=
      (pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg _)) (max_le hx hy) _).trans
        (pow_le_pow_right₀ hA (Nat.sub_le _ _))
    have hc : |x^n-y^n| ≤ |x-y| *(((n:ℝ)+1)*A^n) := by
      apply hp.trans
      rw [mul_assoc]
      gcongr
      linarith
    dsimp only [f,w]
    rw [← sub_div, Real.norm_eq_abs,abs_div,
      abs_of_pos (Real.Gamma_pos_of_pos (by positivity : 0 < ((n:ℝ)+1)*α))]
    calc _ ≤ _ := div_le_div_of_nonneg_right hc (Real.Gamma_pos_of_pos (by positivity)).le
         _ = _ := by ring
  have hnorm := (hw.mul_right |x-y|).of_nonneg_of_le (fun n => norm_nonneg (f n)) hb
  rw [fractionalResolventProfile, fractionalResolventProfile,
    ← (fractionalResolventProfile_summable hα x).tsum_sub (fractionalResolventProfile_summable hα y)]
  change ‖∑' n,f n‖ ≤ _
  calc _ ≤ ∑' n, ‖f n‖ := norm_tsum_le_tsum_norm hnorm
       _ ≤ ∑' n, w n*|x-y| := hnorm.tsum_le_tsum hb (hw.mul_right _)
       _ = _ := tsum_mul_right

#print axioms fractionalResolventProfile_zero
#print axioms fractionalSecondKindResolvent_factor
#print axioms fractionalResolventProfile_lipschitz_on

end RoughHeston
