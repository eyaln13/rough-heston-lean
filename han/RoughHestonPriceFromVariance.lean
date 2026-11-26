import LocalizedPriceExponential
import FiniteBrownianFrozenMartingales

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston.GirsanovPort

open SHEStochastic SHE SHE.PredictableL2

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} {H : ℝ≥0} {W N V : ℝ≥0 → Ω → ℝ}

/-- The time energy of the square root is the integrated variance. -/
theorem affineEnergyClock_sqrt_variance (hV₀ : ∀ t ω, 0 ≤ V t ω) (t : ℝ≥0) (ω : Ω) :
    affineEnergyClock (fun r x => Real.sqrt (V r x)) t ω =
      ∫ r in (0:ℝ)..(t:ℝ), V r.toNNReal ω := by
  unfold affineEnergyClock
  exact intervalIntegral.integral_congr fun r _ => Real.sq_sqrt (hV₀ r.toNNReal ω)

set_option maxHeartbeats 1000000 in
/-- A continuous nonnegative variance and a continuous version of its
log integral against the given physical Brownian motion determine a
strictly positive asset price. The resulting SDE is represented by
ordinary joint Itô integrals on a single increasing localization. -/
theorem rough_heston_price_of_joint_log_integral [F.IsComplete μ] [F.IsRightContinuous]
    (hW : MathFinBridge.BrownianOn μ F H W)
    (hN : StronglyAdapted F N) (hNc : ∀ ω, Continuous (fun t => N t ω))
    (hN₀ : ∀ ω, N 0 ω = 0) (hNfreeze : ∀ t, N t = N (min t H))
    (hV : IsStronglyPredictable F V) (hVc : ∀ ω, Continuous (fun t => V t ω))
    (hV₀ : ∀ t ω, 0 ≤ V t ω)
    (hL2 : MemLp (fun p : ℝ≥0 × Ω => Real.sqrt (V p.1 p.2)) 2 (jointPredictableMeasure F μ H))
    (hPrefix : let hW₂ (t : ℝ≥0) := finiteBrownianOn_memLp hW (min t H) (min_le_right _ _) 2 (by norm_num)
      ∀ t ≤ H, N t =ᵐ[μ] jointItoIntegralCLM H hW₂
        (NativeTimeCut.prior t (hL2.toLp (fun p : ℝ≥0 × Ω => Real.sqrt (V p.1 p.2)))))
    {s₀ : ℝ} (hs₀ : 0 < s₀) :
    let hW₂ (t : ℝ≥0) := finiteBrownianOn_memLp hW (min t H) (min_le_right _ _) 2 (by norm_num)
    let S (t : ℝ≥0) (ω : Ω) := s₀ * Real.exp (N t ω - (∫ r in (0:ℝ)..(t:ℝ), V r.toNNReal ω) / 2)
    IsStronglyPredictable F S ∧ (∀ ω, Continuous (fun t => S t ω)) ∧
      (∀ ω, S 0 ω = s₀) ∧ (∀ t ω, 0 < S t ω) ∧
      HasLocalizedJointBrownianIntegral H F μ hW₂ (fun t ω => S t ω * Real.sqrt (V t ω))
        (fun t ω => S t ω - s₀) := by
  let g (t : ℝ≥0) (ω : Ω) := Real.sqrt (V t ω)
  have hg : IsStronglyPredictable F g := by
    let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    exact hV.measurable.sqrt.stronglyMeasurable
  have hgc (ω : Ω) : Continuous (fun t => g t ω) := Real.continuous_sqrt.comp (hVc ω)
  have hu : ⇑(hL2.toLp (Function.uncurry g)) =ᵐ[jointPredictableMeasure F μ H] Function.uncurry g :=
    hL2.coeFn_toLp
  have hnull : NullCompleteFiltration.ContainsNullSets F μ := fun t A hA =>
    Filtration.IsComplete.measurableSet_of_null (𝓕:=F) hA t
  obtain ⟨P,hP⟩ := exists_scalarNativeFamily_of_brownianOn hW (fun A _ hA => hnull 0 A hA)
  obtain ⟨hW₂,hWm,hWclock⟩ := finiteBrownianOn_frozen_martingales hW
  have hAgree (t : ℝ≥0) (ht : t ≤ H) : P.W () t =ᵐ[μ] W (min t H) := by
    rw [min_eq_left ht]
    exact hP t ht
  have hPr (t : ℝ≥0) : N t =ᵐ[μ] jointItoIntegralCLM H hW₂
      (NativeTimeCut.prior t (hL2.toLp (Function.uncurry g))) := by
    by_cases ht : t ≤ H
    · exact hPrefix t ht
    · rw [hNfreeze t, min_eq_right (le_of_not_ge ht)]
      have he (u : Lp ℝ 2 (jointPredictableMeasure F μ H)) :
          NativeTimeCut.prior t u = NativeTimeCut.prior H u := by
        apply Lp.ext
        filter_upwards [NativeTimeCut.prior_ae t u,NativeTimeCut.prior_ae H u,
          ae_fst_mem_Ioo_jointPredictableMeasure (𝒢:=F) (μ:=μ) H] with p h₁ h₂ hp
        rw [h₁,h₂]
        simp [not_lt_of_ge hp.2.le,not_lt_of_ge (hp.2.le.trans (le_of_not_ge ht))]
      rw [he]
      exact hPrefix H le_rfl
  have hS := localized_joint_price_exponential P hnull hW₂ hWm hWclock hAgree hN hNc hN₀ hg hgc
    (hL2.toLp (Function.uncurry g)) hu hPr hs₀
  simpa only [g,jointStochasticExponential,affineEnergyClock_sqrt_variance hV₀] using hS

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.rough_heston_price_of_joint_log_integral
