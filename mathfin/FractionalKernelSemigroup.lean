import FractionalBoundaryHistory

open MeasureTheory Set Filter
open scoped MeasureTheory Topology

namespace RoughHeston

/-- Convolution of two positive-order fractional kernels adds the orders. -/
theorem fractionalK_convolution_add {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) :
    volterraConvolution (fractionalK a) (fractionalK b) t = fractionalK (a+b) t := by
  have hΓa := (Real.Gamma_pos_of_pos ha).ne'
  have hΓb := (Real.Gamma_pos_of_pos hb).ne'
  have hΓab := (Real.Gamma_pos_of_pos (add_pos ha hb)).ne'
  have hβ := (real_beta_weight_scaled (a := b) (b := a) hb ha ht).2
  dsimp only at hβ
  have he : (∫ y in Ioc (0 : ℝ) t, fractionalK a (t-y) * fractionalK b y) =
      (∫ y in Ioc (0 : ℝ) t, y ^ (b-1) * (t-y) ^ (a-1)) /
        (Real.Gamma b * Real.Gamma a) := by
    rw [← integral_div, ← restrict_Ioo_eq_restrict_Ioc]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro y hy
    dsimp only
    rw [fractionalK, fractionalK, ite_eq_right (not_le.mpr (sub_pos.mpr hy.2)),
      ite_eq_right (not_le.mpr hy.1), div_mul_div_comm]
    ac_rfl
  unfold volterraConvolution
  rw [he, hβ, fractionalK, ite_eq_right (not_le.mpr ht), add_comm b a]
  field_simp [hΓa, hΓb, hΓab]

/-- Iterating the fractional kernel gives the explicit kernel of order
`(n+1)α`. -/
noncomputable def fractionalKIterate (α : ℝ) : ℕ → ℝ → ℝ
  | 0 => fractionalK α
  | n+1 => volterraConvolution (fractionalK α) (fractionalKIterate α n)

theorem fractionalKIterate_eq {α : ℝ} (hα : 0 < α) (n : ℕ) :
    fractionalKIterate α n = fractionalK ((n+1)*α) := by
  induction n with
  | zero => simp [fractionalKIterate]
  | succ n ih =>
    funext t
    rw [fractionalKIterate, ih]
    by_cases ht : 0 < t
    · rw [fractionalK_convolution_add hα (by positivity) ht]
      congr 1
      push_cast
      ring
    · simp [volterraConvolution, fractionalK, le_of_not_gt ht]

/-- A fixed interval in the Gamma integral gives an exponential lower
bound with any base larger than one. -/
theorem gamma_ge_of_unit_interval {R z : ℝ} (hR : 0 < R) (hz : 1 ≤ z) :
    Real.exp (-(R+1)) * R ^ (z-1) ≤ Real.Gamma z := by
  have hz₀ : 0 < z := zero_lt_one.trans_le hz
  let f (x : ℝ) := Real.exp (-x) * x ^ (z-1)
  have hsub : Ioc R (R+1) ⊆ Ioi (0 : ℝ) := fun _ hx => hR.trans hx.1
  have hi : IntegrableOn f (Ioi (0 : ℝ)) := Real.GammaIntegral_convergent hz₀
  have hc : (∫ _x in Ioc R (R+1), Real.exp (-(R+1)) * R ^ (z-1)) =
      Real.exp (-(R+1)) * R ^ (z-1) := by
    rw [← intervalIntegral.integral_of_le (by linarith : R ≤ R+1)]
    simp
  rw [Real.Gamma_eq_integral hz₀, ← hc]
  calc
    _ ≤ ∫ x in Ioc R (R+1), f x := by
      apply setIntegral_mono_on (integrableOn_const measure_Ioc_lt_top.ne) (hi.mono_set hsub)
        measurableSet_Ioc
      intro x hx
      exact mul_le_mul
        (Real.exp_le_exp.mpr (neg_le_neg hx.2))
        (Real.rpow_le_rpow hR.le hx.1.le (sub_nonneg.mpr hz))
        (Real.rpow_nonneg hR.le _) (Real.exp_pos _).le
    _ ≤ _ := setIntegral_mono_set hi
      ((ae_restrict_mem measurableSet_Ioi).mono fun x hx =>
        mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hx.le _)) (ae_of_all _ hsub)

end RoughHeston

#print axioms RoughHeston.fractionalK_convolution_add
#print axioms RoughHeston.fractionalKIterate_eq
#print axioms RoughHeston.gamma_ge_of_unit_interval
