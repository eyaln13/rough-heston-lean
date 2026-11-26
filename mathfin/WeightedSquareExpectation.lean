import RawDeterministicWeightedMartingale
import ClusterRealMomentTransfer

/-! The expected bracket controls the second moment of an actual weighted
martingale, including the first-moment exponent in the time estimate. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

/-- A zero-start martingale's compensated square yields exactly the
expected bracket at each terminal time. -/
theorem integral_martingale_sq_eq_clock
    {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 m} {Y A : ℝ≥0 → Ω → ℝ}
    (hY₂ : ∀ t, MemLp (Y t) 2 μ) (hQ : Martingale (fun t => Y t*Y t-A t) F μ)
    (hY₀ : ∀ᵐ ω ∂μ, Y 0 ω = 0) (hA₀ : ∀ᵐ ω ∂μ, A 0 ω = 0) (t : ℝ≥0) :
    Integrable (A t) μ ∧ (∫ ω, Y t ω ^ 2 ∂μ) = ∫ ω, A t ω ∂μ := by
  have hi : Integrable (fun ω => Y t ω ^ 2) μ := (hY₂ t).integrable_sq
  have hQi := hQ.integrable t
  have ha : Integrable (A t) μ := (hi.sub hQi).congr (Eventually.of_forall fun ω => by
    change Y t ω ^ 2 - (Y t ω*Y t ω-A t ω) = A t ω
    ring)
  have hQ₀ : (fun ω => Y 0 ω*Y 0 ω-A 0 ω) =ᵐ[μ] (fun _ => 0) := by
    filter_upwards [hY₀, hA₀] with ω hY hA
    simp [hY, hA]
  have hMean := hQ.setIntegral_eq (show (0:ℝ≥0) ≤ t from zero_le)
    (show MeasurableSet[F 0] (univ : Set Ω) from MeasurableSet.univ)
  rw [setIntegral_univ, setIntegral_univ] at hMean
  have hzero : (∫ ω, Y 0 ω*Y 0 ω-A 0 ω ∂μ) = 0 :=
    (integral_congr_ae hQ₀).trans (integral_zero _ _)
  have hb : (∫ ω, Y t ω ^ 2-A t ω ∂μ) = 0 := by
    simpa only [Pi.sub_apply, Pi.mul_apply, pow_two] using hMean.symm.trans hzero
  rw [integral_sub hi ha] at hb
  exact ⟨ha, sub_eq_zero.mp hb⟩

/-- Given the actual bracket and a uniform first moment of the
nonnegative variance input, the weighted terminal second moment
is bounded by the deterministic squared weight integral. -/
theorem lintegral_martingale_sq_le_weighted_clock
    {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {S : Type*} [MeasurableSpace S] {ν : Measure S} [SFinite ν]
    {F : Filtration ℝ≥0 m} {Y A : ℝ≥0 → Ω → ℝ}
    (hY₂ : ∀ t, MemLp (Y t) 2 μ) (hQ : Martingale (fun t => Y t*Y t-A t) F μ)
    (hY₀ : ∀ᵐ ω ∂μ, Y 0 ω = 0) (hA₀ : ∀ᵐ ω ∂μ, A 0 ω = 0) (t : ℝ≥0)
    {w : S → ℝ≥0∞} {V : S → Ω → ℝ≥0∞} {C : ℝ≥0∞}
    (hw : Measurable w) (hV : Measurable (Function.uncurry V))
    (hClk : ∀ᵐ ω ∂μ, 0 ≤ A t ω ∧ ENNReal.ofReal (A t ω) = ∫⁻ s, w s*V s ω ∂ν)
    (hMoment : ∀ᵐ s ∂ν, (∫⁻ ω, V s ω ∂μ) ≤ C) :
    (∫⁻ ω, ‖Y t ω‖ₑ ^ (2 : ℕ) ∂μ) ≤ (∫⁻ s, w s ∂ν)*C := by
  obtain ⟨hAi, hEq⟩ := integral_martingale_sq_eq_clock hY₂ hQ hY₀ hA₀ t
  have hEqLp : (∫⁻ ω, ‖Y t ω‖ₑ ^ (2 : ℕ) ∂μ) = ENNReal.ofReal (∫ ω, Y t ω ^ 2 ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hY₂ t).integrable_sq (Eventually.of_forall fun ω => sq_nonneg _)]
    apply lintegral_congr
    intro ω
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
  rw [hEqLp, hEq, ofReal_integral_eq_lintegral_ofReal hAi (hClk.mono fun _ h => h.1)]
  have hC := weighted_kernel_moment_time_profile_of_one_le (m := (1:ℝ)) le_rfl hw hV
    (c := fun _ => C) (by simpa only [ENNReal.rpow_one] using hMoment)
  simp only [ENNReal.rpow_one, sub_self, ENNReal.rpow_zero, one_mul, lintegral_mul_const _ hw] at hC
  exact (lintegral_congr_ae (hClk.mono fun _ h => h.2)).le.trans hC

#print axioms RoughHeston.integral_martingale_sq_eq_clock
#print axioms RoughHeston.lintegral_martingale_sq_le_weighted_clock

end RoughHeston
