import JointItoPowerMoments
import JointTimeEnergyProfile
import ClusterKernelMomentEndpoint

/-! Model moment bounds for a square-root noise row with a
deterministic time weight on the physical filtration. -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace RoughHeston.GirsanovPort

open SHEStochastic

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 m} {H : ℝ≥0} {B : ℝ≥0 → Ω → ℝ}

/-- The kernel may be signed, as occurs in increments. All bounds
retain the individual moment at each age. -/
theorem heston_sqrt_row_moment_time_profile (hb : MathFinBridge.BrownianOn P F H B)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[F 0] A)
    (hB₂ : ∀ t, MemLp (B t) 2 P) (hB : Martingale B F P)
    (hclock : Martingale (fun t ω => B t ω^2-((min t H:ℝ≥0):ℝ)) F P)
    (n : ℕ) {σ : ℝ} {K : ℝ≥0 → ℝ} (hK : Measurable K)
    {U : ℝ≥0 → Ω → ℝ} (hU : Measurable (Function.uncurry U))
    (hn : ∀ᵐ ω ∂P, ∀ᵐ t ∂hestonTimeMeasure H, 0 ≤ U t ω)
    (u : Lp ℝ 2 (jointPredictableMeasure F P H))
    (hu : u =ᵐ[jointPredictableMeasure F P H] (fun z => σ*K z.1*Real.sqrt (U z.1 z.2)))
    {c : ℝ≥0 → ℝ≥0∞}
    (hc : ∀ᵐ t ∂hestonTimeMeasure H, (∫⁻ ω, (ENNReal.ofReal (U t ω))^(2^n:ℕ) ∂P) ≤ c t) :
    (∫⁻ ω, ENNReal.ofReal (‖jointItoIntegralCLM H hB₂ u ω‖^(2*(2^n))) ∂P) ≤
      (NativeScalarBDG.constant n : ℝ≥0∞) *
      ((∫⁻ t, ENNReal.ofReal ((σ*K t)^2) ∂hestonTimeMeasure H)^(((2^n:ℕ):ℝ)-1) *
       ∫⁻ t, ENNReal.ofReal ((σ*K t)^2)*c t ∂hestonTimeMeasure H) := by
  letI : IsFiniteMeasure (hestonTimeMeasure H) := by unfold hestonTimeMeasure; infer_instance
  let w (t : ℝ≥0) := ENNReal.ofReal ((σ*K t)^2)
  let V (t : ℝ≥0) (ω : Ω) := ENNReal.ofReal (U t ω)
  have hw : Measurable w := by dsimp [w]; fun_prop
  have hV : Measurable (Function.uncurry V) := ENNReal.measurable_ofReal.comp hU
  have hpow : (1:ℝ) ≤ ((2^n:ℕ):ℝ) := by
    exact_mod_cast (Nat.one_le_pow n 2 (by decide))
  have hc' : ∀ᵐ t ∂hestonTimeMeasure H, (∫⁻ ω, V t ω^((2^n:ℕ):ℝ) ∂P) ≤ c t := by
    simpa only [V, ENNReal.rpow_natCast] using hc
  have hm := weighted_kernel_moment_time_profile_of_one_le hpow hw hV hc'
  simp only [ENNReal.rpow_natCast] at hm
  have henergy := joint_sqrt_row_lintegral_energy u hu hn
  refine (jointIto_power_two_estimate hb hnull hB₂ hB hclock n u).trans ?_
  apply mul_le_mul_right
  refine le_trans (le_of_eq ?_) hm
  apply lintegral_congr_ae
  filter_upwards [henergy] with ω hω
  exact congrArg (fun z : ℝ≥0∞ => z^(2^n:ℕ)) hω

#print axioms heston_sqrt_row_moment_time_profile

end RoughHeston.GirsanovPort
