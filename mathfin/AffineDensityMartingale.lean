import BoundedLocalMartingale
import Mathlib.Analysis.SpecialFunctions.Exp

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped Topology NNReal

namespace RoughHeston

/-- Timewise bounds for an almost surely continuous process give one
uniform bound off a single null set. -/
theorem ae_uniform_bound_of_timewise_bound {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} {X : ℝ≥0 → Ω → ℝ} {C : ℝ}
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => X t ω)) (hb : ∀ t, ∀ᵐ ω ∂μ, ‖X t ω‖ ≤ C) :
    ∀ᵐ ω ∂μ, ∀ t, ‖X t ω‖ ≤ C := by
  obtain ⟨A, hA, hd⟩ := exists_countable_dense ℝ≥0
  have hf : ∀ᵐ ω ∂μ, ∀ t ∈ A, ‖X t ω‖ ≤ C :=
    (ae_ball_iff hA).2 fun t _ => hb t
  filter_upwards [hc, hf] with ω hcont hω
  have hclosed : IsClosed {t | ‖X t ω‖ ≤ C} := isClosed_le hcont.norm continuous_const
  have hcl : closure A ⊆ {t | ‖X t ω‖ ≤ C} := closure_minimal hω hclosed
  rw [hd.closure_eq] at hcl
  exact fun t => hcl (mem_univ t)

/-- The affine terminal and future identities give the exponential
density at the intermediate time once the past payoff is removed. -/
theorem affine_density_split_exponent {payoff initial past future N A NT AT : ℝ}
    (hTerminal : payoff = initial + NT + AT)
    (hFuture : payoff = past + future + (NT-N) + (AT-A)) :
    Real.exp (-N-A) = Real.exp (initial-past-future) := by
  congr 1
  linarith

/-- A bounded affine local exponential gives the conditional Laplace
transform from its terminal payoff and future exponent. -/
theorem conditional_laplace_of_affine_local_density {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝒢 : Filtration ℝ≥0 m} {D : ℝ≥0 → Ω → ℝ}
    {s T : ℝ≥0} (hs : s ≤ T) {payoff future : Ω → ℝ} (c : ℝ)
    (had : StronglyAdapted 𝒢 D) (hD : IsLocalMartingale D 𝒢 μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => D t ω))
    (hb : ∀ t, ∀ᵐ ω ∂μ, ‖D t ω‖ ≤ Real.exp c)
    (hT : D T =ᵐ[μ] fun ω => Real.exp (c-payoff ω))
    (hF : D s =ᵐ[μ] fun ω => Real.exp (c-future ω)) :
    μ[(fun ω => Real.exp (-payoff ω)) | 𝒢 s] =ᵐ[μ] fun ω => Real.exp (-future ω) := by
  have hM := martingale_of_bounded_localMartingale had hD (Real.exp_pos c).le
    (ae_uniform_bound_of_timewise_bound hc hb)
  have hpay : (fun ω => Real.exp (-payoff ω)) =ᵐ[μ] Real.exp (-c) • D T := by
    filter_upwards [hT] with ω hω
    rw [Pi.smul_apply, smul_eq_mul, hω, ← Real.exp_add]
    congr 1
    ring
  refine ((condExp_congr_ae hpay).trans (condExp_smul (Real.exp (-c)) (D T) (𝒢 s))).trans ?_
  filter_upwards [hM.condExp_ae_eq hs, hF] with ω hCond hω
  rw [Pi.smul_apply, smul_eq_mul, hCond, hω, ← Real.exp_add]
  congr 1
  ring

end RoughHeston

#print axioms RoughHeston.ae_uniform_bound_of_timewise_bound
#print axioms RoughHeston.affine_density_split_exponent
#print axioms RoughHeston.conditional_laplace_of_affine_local_density
