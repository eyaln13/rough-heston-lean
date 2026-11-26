import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

open MeasureTheory Filter

namespace RoughHeston.GirsanovPort

/-- A subprobability bound for every exponential perturbation of a
normalized density forces its linear variation to have zero mean. -/
theorem integral_linear_perturbation_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {D L A : Ω → ℝ}
    (hD : Integrable D μ) (hD₀ : 0 ≤ᵐ[μ] D)
    (hL : Integrable (fun ω => D ω * L ω) μ)
    (hA : Integrable (fun ω => D ω * A ω) μ)
    (hExp : ∀ e : ℝ, Integrable (fun ω => D ω * Real.exp (e * L ω - e ^ 2 * A ω / 2)) μ)
    (hBound : ∀ e : ℝ, (∫ ω, D ω * Real.exp (e * L ω - e ^ 2 * A ω / 2) ∂μ) ≤ ∫ ω, D ω ∂μ) :
    (∫ ω, D ω * L ω ∂μ) = 0 := by
  let x := ∫ ω, D ω * L ω ∂μ
  let a := ∫ ω, D ω * A ω ∂μ
  have hvar (e : ℝ) : e*x - e^2/2*a ≤ 0 := by
    let f (ω : Ω) := D ω + (e * (D ω * L ω) - (e^2/2) * (D ω * A ω))
    have hfi : Integrable f μ := hD.add ((hL.const_mul e).sub (hA.const_mul (e^2/2)))
    have hle : f ≤ᵐ[μ] fun ω => D ω * Real.exp (e * L ω - e^2 * A ω / 2) := by
      filter_upwards [hD₀] with ω hω
      calc
        _ = D ω * (1 + (e*L ω - e^2*A ω/2)) := by dsimp [f]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa only [add_comm] using Real.add_one_le_exp (e * L ω - e^2 * A ω / 2)) hω
    have h := (integral_mono_ae hfi (hExp e) hle).trans (hBound e)
    change (∫ ω, D ω + (e * (D ω * L ω) - (e^2/2) * (D ω * A ω)) ∂μ) ≤ _ at h
    have hs := integral_add hD ((hL.const_mul e).sub (hA.const_mul (e^2/2)))
    rw [integral_sub' (hL.const_mul e) (hA.const_mul (e^2/2)), integral_const_mul, integral_const_mul] at hs
    simp only [Pi.sub_apply] at hs
    rw [hs] at h
    exact (add_le_iff_nonpos_right _).mp h
  by_contra hx
  let b := |a| + 1
  have hb : 0 < b := by dsimp [b]; positivity
  have hb₂ : 0 < b - a/2 := by have ha := le_abs_self a; dsimp [b]; linarith
  have he : (x/b)*x - (x/b)^2/2*a = (x/b)^2 * (b-a/2) := by field_simp
  have hpos : 0 < (x/b)^2 * (b-a/2) :=
    mul_pos (sq_pos_of_ne_zero (div_ne_zero hx hb.ne')) hb₂
  rw [← he] at hpos
  exact hpos.not_ge (hvar (x/b))

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.integral_linear_perturbation_zero
