import LaplaceBoundary
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace RoughHeston

/-- The large-charge Laplace estimate for accumulated cluster mass
gives the small-mass probability with exponent one half. -/
theorem cluster_mass_lower_tail_of_laplace {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {J : Ω → ℝ} (hJ : Measurable J)
    (hJ₀ : ∀ᵐ ω ∂μ, 0 ≤ J ω) {a s α C x : ℝ}
    (ha : 0 < a) (hs : 0 < s) (hx : 0 < x) (hx₁ : x ≤ 1)
    (hL : ∀ q ≥ a / s ^ (2*α),
      (∫ ω, Real.exp (-q * J ω) ∂μ) ≤ C / (Real.sqrt q * s^α)) :
    μ.real {ω | J ω ≤ x*s^(2*α)} ≤
      (Real.exp a * C / Real.sqrt a) * Real.sqrt x := by
  let y := x*s^(2*α)
  let q := a/y
  let E := {ω | J ω ≤ y}
  have hsα : 0 < s^α := Real.rpow_pos_of_pos hs _
  have hs₂ : s^(2*α) = (s^α)^2 := by
    rw [mul_comm 2 α, Real.rpow_mul hs.le, Real.rpow_two]
  have hy : 0 < y := mul_pos hx (Real.rpow_pos_of_pos hs _)
  have hq : 0 < q := div_pos ha hy
  have hqmin : a / s^(2*α) ≤ q :=
    div_le_div_of_nonneg_left ha.le hy (mul_le_of_le_one_left
      (Real.rpow_nonneg hs.le _) hx₁)
  have hqy : q*y = a := div_mul_cancel₀ _ hy.ne'
  have hE : MeasurableSet E := measurableSet_le hJ measurable_const
  let f (ω : Ω) := Real.exp (-q*J ω)
  have hfm : Measurable f := (hJ.const_mul (-q)).exp
  have hf₀ (ω : Ω) : 0 ≤ f ω := (Real.exp_pos _).le
  have hfi : Integrable f μ := by
    refine (integrable_const (1 : ℝ)).mono' hfm.aestronglyMeasurable ?_
    filter_upwards [hJ₀] with ω hω
    rw [Real.norm_of_nonneg (hf₀ ω)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq.le) hω)
  have hsmall : Real.exp (-a) * μ.real E ≤ ∫ ω, f ω ∂μ := by
    have hle (ω : Ω) : E.indicator (fun _ => Real.exp (-a)) ω ≤ f ω := by
      by_cases hω : ω ∈ E
      · rw [indicator_of_mem hω]
        apply Real.exp_le_exp.mpr
        rw [← hqy, ← neg_mul]
        exact mul_le_mul_of_nonpos_left (show J ω ≤ y from hω) (neg_nonpos.mpr hq.le)
      · rw [indicator_of_notMem hω]
        exact hf₀ ω
    have h := integral_mono ((integrable_const (Real.exp (-a))).indicator hE) hfi hle
    rwa [integral_indicator hE, setIntegral_const, smul_eq_mul, mul_comm] at h
  have hscale : Real.sqrt q * s^α = Real.sqrt a / Real.sqrt x := by
    dsimp [q, y]
    rw [hs₂, Real.sqrt_div ha.le, Real.sqrt_mul hx.le, Real.sqrt_sq hsα.le]
    have hxs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
    field_simp [hxs.ne', hsα.ne']
  have hterm : μ.real E ≤ Real.exp a * (C / (Real.sqrt q * s^α)) := by
    apply (mul_le_mul_iff_of_pos_left (Real.exp_pos (-a))).mp
    rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    exact hsmall.trans (hL q hqmin)
  rw [hscale, div_div_eq_mul_div] at hterm
  exact hterm.trans_eq (by ring)

end RoughHeston

#print axioms RoughHeston.cluster_mass_lower_tail_of_laplace
