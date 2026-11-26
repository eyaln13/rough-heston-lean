import ContinuousJointAmplitude
import JointAmplitudeClocks
import FiniteBrownianFrozenMartingales

open MeasureTheory ProbabilityTheory Filter Set
open scoped MeasureTheory ProbabilityTheory Topology NNReal ENNReal Interval

namespace RoughHeston

open SHEStochastic GirsanovPort

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} {T : ℝ≥0} {B V : ℝ≥0 → Ω → ℝ}

omit [IsProbabilityMeasure μ] in
private theorem complete_continuous_zero_version [F.IsComplete μ]
    {X : ℝ≥0 → Ω → ℝ}
    (hX : Martingale X F μ) (hX0 : X 0 =ᵐ[μ] 0)
    (hXc : ∀ᵐ ω ∂μ, Continuous (fun t => X t ω))
    (hXf : ∀ t, X t = X (min t T)) :
    ∃ Y : ℝ≥0 → Ω → ℝ, Martingale Y F μ ∧ (∀ t, Y t =ᵐ[μ] X t) ∧
      (∀ ω, Continuous (fun t => Y t ω)) ∧ Y 0 = 0 ∧
      ∀ t, Y t = Y (min t T) := by
  classical
  let good : Set Ω := {ω | Continuous (fun t => X t ω) ∧ X 0 ω = 0}
  have hgood : ∀ᵐ ω ∂μ, ω ∈ good := by
    filter_upwards [hXc, hX0] with ω hc hz
    exact ⟨hc,hz⟩
  have hnull : μ goodᶜ = 0 := ae_iff.mp hgood
  have hF0 : MeasurableSet[F 0] good := by
    simpa only [compl_compl] using
      (Filtration.IsComplete.measurableSet_of_null (𝓕 := F) hnull 0).compl
  let Y (t : ℝ≥0) := good.indicator (X t)
  have he (t : ℝ≥0) : Y t =ᵐ[μ] X t := hgood.mono fun _ hω => indicator_of_mem hω _
  refine ⟨Y, ⟨fun t => (hX.stronglyAdapted t).indicator (F.mono zero_le good hF0), ?_⟩,
    he, ?_, ?_, fun t => congrArg good.indicator (hXf t)⟩
  · intro s t hst
    exact (condExp_congr_ae (he t)).trans ((hX.condExp_ae_eq hst).trans (he s).symm)
  · intro ω
    by_cases hω : ω ∈ good
    · simpa only [Y, indicator_of_mem hω] using hω.1
    · simpa only [Y, indicator_of_notMem hω] using
        (continuous_const : Continuous (fun _ : ℝ≥0 => (0 : ℝ)))
  · funext ω
    by_cases hω : ω ∈ good
    · simpa only [Y, indicator_of_mem hω, Pi.zero_apply] using hω.2
    · simp only [Y, indicator_of_notMem hω, Pi.zero_apply]

/-- The Brownian log-price integral for a continuous nonnegative
variance in a complete common filtration. The predictable row is the
pointwise square root. Both bracket processes are the ordinary
pathwise primitives and the causal sections use the fixed-horizon Itô map. -/
theorem exists_heston_continuous_log_martingale [F.IsComplete μ]
    (hB : MathFinBridge.BrownianOn μ F T B)
    (hVa : StronglyAdapted F V) (hVc : ∀ ω, Continuous (fun t => V t ω))
    (hV₀ : ∀ t ω, 0 ≤ V t ω) (hVi : ∀ t, Integrable (V t) μ)
    {C : ℝ} (hVm : ∀ t, (∫ ω, V t ω ∂μ) ≤ C) :
    let W : ℝ≥0 → Ω → ℝ := fun t => B (min t T)
    let a : ℝ≥0 → Ω → ℝ := fun t ω => Real.sqrt (V t ω)
    ∃ (hW₂ : ∀ t, MemLp (W t) 2 μ)
      (u : Lp ℝ 2 (jointPredictableMeasure F μ T)) (N : ℝ≥0 → Ω → ℝ),
      (⇑u =ᵐ[jointPredictableMeasure F μ T] Function.uncurry a) ∧
      IsStronglyPredictable F a ∧
      (∀ ω, Continuous (fun t => a t ω)) ∧
      Martingale W F μ ∧ (∀ᵐ ω ∂μ, Continuous (fun t => W t ω)) ∧
      Martingale (fun t ω => W t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) F μ ∧
      Martingale N F μ ∧ (∀ t, MemLp (N t) 2 μ) ∧
      (∀ ω, Continuous (fun t => N t ω)) ∧ N 0 = 0 ∧
      (∀ t, N t = N (min t T)) ∧
      (∀ t ≤ T, N t =ᵐ[μ] (jointItoIntegralCLM T hW₂ (NativeTimeCut.prior t u) : Ω → ℝ)) ∧
      HasAmplitudeCutoffIntegral F μ T W N a ∧
      (∀ t, Integrable (stoppedAmplitudePrimitive T V t) μ) ∧
      StronglyAdapted F (stoppedAmplitudePrimitive T V) ∧
      (∀ ω, Continuous (fun t => stoppedAmplitudePrimitive T V t ω)) ∧
      Martingale (fun t => N t * N t - stoppedAmplitudePrimitive T V t) F μ ∧
      Martingale (fun t => N t * W t - stoppedAmplitudePrimitive T a t) F μ := by
  let W : ℝ≥0 → Ω → ℝ := fun t => B (min t T)
  let a : ℝ≥0 → Ω → ℝ := fun t ω => Real.sqrt (V t ω)
  have haa : StronglyAdapted F a := fun t =>
    Real.continuous_sqrt.comp_stronglyMeasurable (hVa t)
  have hac (ω : Ω) : Continuous (fun t => a t ω) := Real.continuous_sqrt.comp (hVc ω)
  have hap : IsStronglyPredictable F a := haa.isStronglyPredictable_of_leftContinuous
    (fun ω _ => (hac ω).continuousWithinAt)
  have hVp : IsStronglyPredictable F V := hVa.isStronglyPredictable_of_leftContinuous
    (fun ω _ => (hVc ω).continuousWithinAt)
  have ha₂ : MemLp (Function.uncurry a) 2 (jointPredictableMeasure F μ T) :=
    sqrt_variance_memLp_joint T hVp hV₀ hVi hVm
  have ha (t : ℝ≥0) (ω : Ω) : 0 ≤ a t ω := Real.sqrt_nonneg _
  have hWc : ∀ᵐ ω ∂μ, Continuous (fun t => W t ω) := by
    filter_upwards [hB.continuous_paths] with ω hω
    exact hω.comp_continuous (continuous_id.min continuous_const)
      (fun s => ⟨zero_le, min_le_right s T⟩)
  have hW0 : W 0 =ᵐ[μ] 0 := by simpa only [W, min_eq_left zero_le] using hB.zero_at_start
  have hWf (t : ℝ≥0) : W t = W (min t T) := by simp only [W, min_assoc, min_self]
  obtain ⟨hW₂,hW,hClock⟩ := finiteBrownianOn_frozen_martingales hB
  obtain ⟨X,hX,hX₂,hXc,hX0,hXf,hCut,hPrior⟩ :=
    exists_continuous_joint_amplitude_integral hW hW₂ hWc hClock haa hap hac ha ha₂
  obtain ⟨N,hN,hNe,hNc,hN0,hNf⟩ := complete_continuous_zero_version hX hX0 hXc hXf
  have hN₂ (t : ℝ≥0) : MemLp (N t) 2 μ := (memLp_congr_ae (hNe t)).mpr (hX₂ t)
  have hNCut : HasAmplitudeCutoffIntegral F μ T W N a := by
    obtain ⟨J,hJ,hJ₂,hJl,hXl⟩ := hCut
    refine ⟨J,hJ,hJ₂,hJl,fun t => (hXl t).congr (fun n => ?_)⟩
    exact eLpNorm_congr_ae (EventuallyEq.rfl.sub (hNe (min t T)).symm)
  obtain ⟨hAi, hAprod, hMix⟩ :=
    amplitudeCutoff_actual_clocks hW hW₂ hW0 hWf hClock hN hN₂ hNf hNCut haa hap hac ha ha₂
  have hsq : (fun t ω => a t ω ^ 2) = V := by
    funext t ω
    exact Real.sq_sqrt (hV₀ t ω)
  rw [hsq] at hAi hAprod
  exact ⟨hW₂, ha₂.toLp (Function.uncurry a), N, ha₂.coeFn_toLp, hap, hac,
    hW, hWc, hClock, hN, hN₂, hNc, hN0, hNf,
    (fun t ht => (hNe t).trans (hPrior t ht)), hNCut, hAi,
    stoppedAmplitudePrimitive_adapted hVa hVc, stoppedAmplitudePrimitive_continuous hVc, hAprod, hMix⟩

end RoughHeston

#print axioms RoughHeston.exists_heston_continuous_log_martingale
