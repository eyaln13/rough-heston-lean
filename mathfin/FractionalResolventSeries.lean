import FractionalKernelSemigroup
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Set Filter MeasureTheory
open scoped Topology

namespace RoughHeston

/-- Gamma growth dominates the weighted geometric coefficients of the
second-kind resolvent and its termwise time derivative. -/
theorem summable_fractionalResolvent_coefficients {α : ℝ} (hα : 0 < α) (z : ℝ) :
    Summable (fun n : ℕ => ((n : ℝ)+1) * z^n / Real.Gamma (((n : ℝ)+1)*α)) := by
  obtain ⟨R, hR, hRa⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    ((tendsto_rpow_atTop hα).eventually_gt_atTop (2 * |z|))).exists
  let D := Real.exp (-(R+1)) * R ^ (α-1)
  let r := 2 * |z| / R ^ α
  have hRα : 0 < R ^ α := Real.rpow_pos_of_pos hR _
  have hD : 0 < D := mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hR _)
  have hr₀ : 0 ≤ r := div_nonneg (by positivity) hRα.le
  have hr₁ : r < 1 := (div_lt_one hRα).2 hRa
  have hsum : Summable (fun n : ℕ => D⁻¹ * r^n) :=
    (summable_geometric_of_lt_one hr₀ hr₁).mul_left _
  obtain ⟨N, hN⟩ := exists_nat_ge (1 / α)
  apply hsum.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn₀ : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hx : 1 ≤ ((n : ℝ)+1)*α :=
    ((div_le_iff₀ hα).mp (hN.trans hcast)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hα.le)
  have hΓ : 0 < Real.Gamma (((n : ℝ)+1)*α) := Real.Gamma_pos_of_pos (zero_lt_one.trans_le hx)
  have hpow : R ^ (((n : ℝ)+1)*α-1) = R ^ (α-1) * (R ^ α)^n := by
    rw [show ((n : ℝ)+1)*α-1 = (α-1) + α*(n : ℝ) by ring,
      Real.rpow_add hR, Real.rpow_mul hR.le, Real.rpow_natCast]
  have hΓlow : D * (R ^ α)^n ≤ Real.Gamma (((n : ℝ)+1)*α) := by
    simpa only [hpow, mul_assoc, D] using gamma_ge_of_unit_interval hR hx
  have hbnd : ∀ k : ℕ, k+1 ≤ (2 : ℕ)^k := by
    intro k
    induction k with
    | zero => simp
    | succ k hk => rw [pow_succ]; omega
  have hc : (n : ℝ) + 1 ≤ (2 : ℝ)^n := by exact_mod_cast hbnd n
  rw [norm_div, norm_mul, norm_pow, Real.norm_of_nonneg (by positivity : 0 ≤ (n : ℝ)+1),
    Real.norm_of_nonneg hΓ.le, Real.norm_eq_abs z]
  calc
    _ ≤ (2 : ℝ)^n * |z|^n / Real.Gamma (((n : ℝ)+1)*α) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) hΓ.le
    _ ≤ (2 : ℝ)^n * |z|^n / (D * (R ^ α)^n) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos hD (pow_pos hRα _)) hΓlow
    _ = _ := by
      rw [← mul_pow, show r = 2 * |z| / R ^ α from rfl, div_pow]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring


theorem summable_fractionalResolvent_abs_coefficients {α : ℝ} (hα : 0 < α) (z : ℝ) :
    Summable (fun n : ℕ => |z|^n / Real.Gamma (((n : ℝ)+1)*α)) := by
  refine Summable.of_nonneg_of_le (g := fun n : ℕ => |z|^n / Real.Gamma (((n : ℝ)+1)*α))
    (fun n => div_nonneg (by positivity) (Real.Gamma_pos_of_pos (by positivity)).le) ?_
    (summable_fractionalResolvent_coefficients hα |z|)
  intro n
  have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  exact div_le_div_of_nonneg_right (le_mul_of_one_le_left (by positivity) (by linarith))
    (Real.Gamma_pos_of_pos (by positivity)).le

/-- The second-kind fractional resolvent, given by the alternating
series of convolution powers. -/
noncomputable def fractionalSecondKindResolvent (α κ t : ℝ) : ℝ :=
  ∑' n : ℕ, (-κ)^n * fractionalK (((n : ℝ)+1)*α) t

theorem fractionalSecondKindResolvent_norm_summable {α T t : ℝ} (hα : 0 < α)
    (κ : ℝ) (ht : 0 < t) (htT : t ≤ T) :
    Summable (fun n : ℕ => ‖(-κ)^n * fractionalK (((n : ℝ)+1)*α) t‖) := by
  let z := |κ| * T^α
  have hT : 0 < T := ht.trans_le htT
  have h₀ : 0 ≤ t^(α-1) := Real.rpow_nonneg ht.le _
  have hz : 0 ≤ z := mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hT.le _)
  have hterm (n : ℕ) : ‖(-κ)^n * fractionalK (((n : ℝ)+1)*α) t‖ =
      t^(α-1) * ((|κ| * t^α)^n / Real.Gamma (((n : ℝ)+1)*α)) := by
    have hg := (Real.Gamma_pos_of_pos (by positivity : 0 < ((n : ℝ)+1)*α)).le
    have he : t^(((n : ℝ)+1)*α-1) = t^(α-1)*(t^α)^n := by
      rw [show ((n : ℝ)+1)*α-1 = (α-1) + α*(n : ℝ) by ring,
        Real.rpow_add ht, Real.rpow_mul ht.le, Real.rpow_natCast]
    rw [fractionalK, ite_eq_right (not_le.mpr ht), norm_mul, norm_pow, norm_neg,
      Real.norm_eq_abs κ, Real.norm_of_nonneg (div_nonneg (Real.rpow_nonneg ht.le _) hg), he, mul_pow]
    ring
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((summable_fractionalResolvent_abs_coefficients hα z).mul_left (t^(α-1)))
  rw [hterm, abs_of_nonneg hz]
  have hh : |κ| * t^α ≤ z :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht.le htT hα.le) (abs_nonneg _)
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg ht.le _)) hh n)
    (Real.Gamma_pos_of_pos (by positivity)).le) h₀

end RoughHeston

#print axioms RoughHeston.summable_fractionalResolvent_coefficients

#print axioms RoughHeston.summable_fractionalResolvent_abs_coefficients
#print axioms RoughHeston.fractionalSecondKindResolvent_norm_summable
