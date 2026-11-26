import RoughHestonPriceFromVariance
import HestonContinuousLogMartingale

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston.GirsanovPort

open SHEStochastic

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} {H : ℝ≥0} {W V : ℝ≥0 → Ω → ℝ}

set_option maxHeartbeats 1100000 in
/-- Construct the strictly positive price for any given physical Brownian
motion and nonnegative continuous variance of bounded first moments. Its
coefficient `S √V` is integrated on the same supplied usual filtration
as the Brownian law and the variance. -/
theorem exists_heston_price_sde [F.IsComplete μ] [F.IsRightContinuous]
    (hW : MathFinBridge.BrownianOn μ F H W)
    (hVa : StronglyAdapted F V) (hVc : ∀ ω, Continuous (fun t => V t ω))
    (hV₀ : ∀ t ω, 0 ≤ V t ω) (hVi : ∀ t, Integrable (V t) μ)
    {C : ℝ} (hVm : ∀ t, (∫ ω, V t ω ∂μ) ≤ C) {s₀ : ℝ} (hs₀ : 0 < s₀) :
    let hW₂ (t : ℝ≥0) := finiteBrownianOn_memLp hW (min t H) (min_le_right _ _) 2 (by norm_num)
    ∃ (u : Lp ℝ 2 (jointPredictableMeasure F μ H)) (N S : ℝ≥0 → Ω → ℝ),
      (⇑u =ᵐ[jointPredictableMeasure F μ H] fun p => Real.sqrt (V p.1 p.2)) ∧
      (∀ t ≤ H, N t =ᵐ[μ] jointItoIntegralCLM H hW₂ (NativeTimeCut.prior t u)) ∧
      N 0 = 0 ∧ Martingale N F μ ∧ (∀ ω, Continuous (fun t => N t ω)) ∧
      (∀ t ω, S t ω = s₀ * Real.exp (N t ω - (∫ r in (0:ℝ)..(t:ℝ), V r.toNNReal ω) / 2)) ∧
      IsStronglyPredictable F S ∧ (∀ ω, Continuous (fun t => S t ω)) ∧
      (∀ ω, S 0 ω = s₀) ∧ (∀ t ω, 0 < S t ω) ∧
      HasLocalizedJointBrownianIntegral H F μ hW₂ (fun t ω => S t ω * Real.sqrt (V t ω))
        (fun t ω => S t ω - s₀) := by
  have hVp : IsStronglyPredictable F V := hVa.isStronglyPredictable_of_leftContinuous
    (fun ω _ => (hVc ω).continuousWithinAt)
  have hL2 : MemLp (fun p : ℝ≥0 × Ω => Real.sqrt (V p.1 p.2)) 2 (jointPredictableMeasure F μ H) :=
    sqrt_variance_memLp_joint H hVp hV₀ hVi hVm
  obtain ⟨hW₂,u,N,hu,_,_,_,_,_,hN,_,hNc,hNz,hNf,hPrior,_⟩ :=
    exists_heston_continuous_log_martingale hW hVa hVc hV₀ hVi hVm
  have he : u = hL2.toLp (fun p : ℝ≥0 × Ω => Real.sqrt (V p.1 p.2)) :=
    Lp.ext (hu.trans hL2.coeFn_toLp.symm)
  have hS := rough_heston_price_of_joint_log_integral hW hN.stronglyAdapted hNc
    (fun ω => congrFun hNz ω) hNf hVp hVc hV₀ hL2
    (fun t ht => by
      have hp := hPrior t ht
      erw [he] at hp
      exact hp) hs₀
  let S (t : ℝ≥0) (ω : Ω) := s₀ * Real.exp (N t ω - (∫ r in (0:ℝ)..(t:ℝ), V r.toNNReal ω) / 2)
  exact ⟨u, N, S, hu, hPrior, hNz, hN, hNc, fun _ _ => rfl, hS⟩

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.exists_heston_price_sde
