import StochasticFoundation
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
Identities for the common-driver construction in Section 5.
The regularization uses bounded continuous integrands at each positive
regularization parameter, including where both variance processes vanish.
The martingale test verifies the last step of the identification once
the three compensated products have been obtained.
-/

open MeasureTheory Filter
open scoped MeasureTheory ProbabilityTheory Topology

namespace RoughHeston

/-- For a rank-one pair with instantaneous amplitudes `a` and `b`,
normalizing their sum by `a+b+d` gives the first coefficient below.
The second coefficient multiplies an orthogonal Brownian motion. -/
theorem common_driver_regularized_coefficients {a b : ℝ} {d : ℕ → ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : ∀ n, 0 < d n)
    (hd0 : Tendsto d atTop (𝓝 0)) :
    let p := fun n => (a + b) / (a + b + d n)
    let q := fun n => d n / (a + b + d n)
    (∀ n, 0 ≤ p n ∧ 0 ≤ q n ∧ p n + q n = 1 ∧ p n ^ 2 + q n ^ 2 ≤ 1) ∧
      Tendsto (fun n => p n ^ 2 + q n ^ 2) atTop (𝓝 1) ∧
      Tendsto (fun n => a * p n) atTop (𝓝 a) ∧
      Tendsto (fun n => b * p n) atTop (𝓝 b) := by
  let p := fun n => (a + b) / (a + b + d n)
  let q := fun n => d n / (a + b + d n)
  have hpos (n : ℕ) : 0 < a + b + d n :=
    add_pos_of_nonneg_of_pos (add_nonneg ha hb) (hd n)
  refine ⟨fun n => ?_, ?_⟩
  · have hp : 0 ≤ p n := div_nonneg (add_nonneg ha hb) (hpos n).le
    have hq : 0 ≤ q n := div_nonneg (hd n).le (hpos n).le
    have hsum : p n + q n = 1 := by
      change (a + b) / (a + b + d n) + d n / (a + b + d n) = 1
      rw [← add_div, div_self (hpos n).ne']
    exact ⟨hp, hq, hsum, by nlinarith [mul_nonneg hp hq]⟩
  by_cases hab : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp only [zero_add, zero_div, ha0, hb0, zero_mul]
    simpa only [div_self (hd _).ne', zero_pow (by decide : (2 : ℕ) ≠ 0), one_pow, zero_add] using
      (⟨tendsto_const_nhds, tendsto_const_nhds, tendsto_const_nhds⟩ :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) ∧
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) ∧
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · have hdenom : Tendsto (fun n => a + b + d n) atTop (𝓝 (a + b)) := by
      simpa only [add_zero] using (tendsto_const_nhds (x := a + b)).add hd0
    have hp : Tendsto p atTop (𝓝 1) := by
      simpa only [p, Pi.div_def, div_self hab] using
        (tendsto_const_nhds (x := a + b)).div hdenom hab
    have hq : Tendsto q atTop (𝓝 0) := by
      simpa only [q, Pi.div_def, zero_div] using hd0.div hdenom hab
    refine ⟨?_, ?_, ?_⟩
    · simpa only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] using
        (hp.pow 2).add (hq.pow 2)
    · simpa only [mul_one] using (tendsto_const_nhds (x := a)).mul hp
    · simpa only [mul_one] using (tendsto_const_nhds (x := b)).mul hp

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

/-- If two martingales admit the same compensator for their squares and
for their product, the square of their difference is a martingale. -/
theorem difference_square_martingale_of_common_compensator [Preorder ι]
    {𝒢 : Filtration ι m} {X Y C : ι → Ω → ℝ}
    (hX : Martingale (fun t => X t * X t - C t) 𝒢 μ)
    (hY : Martingale (fun t => Y t * Y t - C t) 𝒢 μ)
    (hXY : Martingale (fun t => X t * Y t - C t) 𝒢 μ) :
    Martingale (fun t ω => (X t ω - Y t ω) ^ 2) 𝒢 μ := by
  convert (hX.add hY).sub (hXY.smul 2) using 1
  ext t ω
  simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The matching compensated products and the same starting value
identify continuous processes up to indistinguishability. -/
theorem indistinguishable_of_common_compensator [Preorder ι] [OrderBot ι]
    [TopologicalSpace ι] [TopologicalSpace.SeparableSpace ι] [IsFiniteMeasure μ]
    {𝒢 : Filtration ι m} {X Y C : ι → Ω → ℝ}
    (hX : Martingale (fun t => X t * X t - C t) 𝒢 μ)
    (hY : Martingale (fun t => Y t * Y t - C t) 𝒢 μ)
    (hXY : Martingale (fun t => X t * Y t - C t) 𝒢 μ)
    (hXc : ∀ᵐ ω ∂μ, Continuous (fun t => X t ω))
    (hYc : ∀ᵐ ω ∂μ, Continuous (fun t => Y t ω))
    (h0 : X ⊥ =ᵐ[μ] Y ⊥) : ∀ᵐ ω ∂μ, ∀ t, X t ω = Y t ω := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ι
  refine indistinguishable_of_ae_eq_on_dense hDc hDd hXc hYc (fun t _ => ?_)
  have h₀ : X ⊥ - Y ⊥ =ᵐ[μ] 0 := h0.mono (fun ω h => by simp [h])
  have h := zero_of_square_martingale (X := fun t => X t - Y t)
    (difference_square_martingale_of_common_compensator hX hY hXY) (bot_le : ⊥ ≤ t) h₀
  exact h.mono (fun _ hω => sub_eq_zero.mp hω)

end RoughHeston

#print axioms RoughHeston.common_driver_regularized_coefficients
#print axioms RoughHeston.difference_square_martingale_of_common_compensator
#print axioms RoughHeston.indistinguishable_of_common_compensator
