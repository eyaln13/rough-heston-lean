import JointDyadicSimple
import DyadicStepApproximation

open MeasureTheory ProbabilityTheory Filter Set
open scoped MeasureTheory ProbabilityTheory Topology NNReal ENNReal

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}

/-- Almost everywhere convergence dominated by a square-integrable
function gives convergence in the L² seminorm. -/
theorem tendsto_eLpNorm_two_dominated {S : Type*} {mS : MeasurableSpace S}
    {ν : Measure S} {d : ℕ → S → ℝ} {c : S → ℝ} (hc : MemLp c 2 ν)
    (hmeas : ∀ n, AEStronglyMeasurable (d n) ν)
    (hbound : ∀ n, ∀ᵐ x ∂ν, ‖d n x‖ ≤ ‖c x‖)
    (hpoint : ∀ᵐ x ∂ν, Tendsto (fun n => d n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (d n) 2 ν) atTop (𝓝 0) := by
  have hs : Tendsto (fun n => ∫ x, d n x ^ 2 ∂ν) atTop (𝓝 0) := by
    have hconv : ∀ᵐ x ∂ν, Tendsto (fun n => d n x ^ 2) atTop (𝓝 ((0 : S → ℝ) x)) := by
      filter_upwards [hpoint] with x hx
      simpa only [Pi.zero_apply, zero_pow (by decide : (2 : ℕ) ≠ 0)] using hx.pow 2
    have hdom (n : ℕ) : ∀ᵐ x ∂ν, ‖d n x ^ 2‖ ≤ c x ^ 2 := by
      filter_upwards [hbound n] with x hx
      rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs (d n x), ← sq_abs (c x)]
      exact pow_le_pow_left₀ (abs_nonneg _) (by simpa only [Real.norm_eq_abs] using hx) 2
    simpa only [Pi.pow_apply, Pi.zero_apply, integral_zero] using
      tendsto_integral_of_dominated_convergence (fun x => c x ^ 2)
        (fun n => (hmeas n).pow 2) hc.integrable_sq hdom hconv
  have hexp (n : ℕ) : eLpNorm (d n) 2 ν = ENNReal.ofReal (Real.sqrt (∫ x, d n x ^ 2 ∂ν)) := by
    have hp : MemLp (d n) 2 ν := hc.mono (hmeas n) (hbound n)
    have hr := congrArg Real.sqrt (norm_toLp_two_sq hp)
    rw [Real.sqrt_sq (norm_nonneg _)] at hr
    rw [← hr, Lp.norm_toLp, ENNReal.ofReal_toReal hp.eLpNorm_ne_top]
  simpa only [Function.comp_def, Real.sqrt_zero, ENNReal.ofReal_zero, ← hexp] using
    (ENNReal.continuous_ofReal.tendsto (Real.sqrt 0)).comp
      ((Real.continuous_sqrt.tendsto 0).comp hs)

/-- Bounded, almost everywhere convergence of predictable simple
weights gives mean-square convergence of their elementary integrals. -/
theorem jointItoIntegralCLM_of_bounded_simple_limits [IsFiniteMeasure μ] (T : ℝ≥0)
    (hM : Martingale M 𝒢 μ) (hM₂ : ∀ t, MemLp (M t) 2 μ)
    (hclock : Martingale (fun t ω => M t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) 𝒢 μ)
    (S : ℕ → JointTBoundedSP T 𝒢) {f : ℝ≥0 × Ω → ℝ}
    (hfsm : StronglyMeasurable[𝒢.predictable] f)
    (hf₂ : MemLp f 2 (jointPredictableMeasure 𝒢 μ T))
    {C : ℝ}
    (hbd : ∀ j, ∀ᵐ z ∂(MathFin.ItoIntegralCLM.timeMeasureHorizon T).prod μ,
      ‖Function.uncurry ⇑(S j).val z - f z‖ ≤ C)
    (hval : ∀ᵐ z ∂(MathFin.ItoIntegralCLM.timeMeasureHorizon T).prod μ,
      Tendsto (fun j => Function.uncurry ⇑(S j).val z - f z) atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm (jointItoSimple M (S j).val -
      (jointItoIntegralCLM T hM₂ (hf₂.toLp f) : Ω → ℝ)) 2 μ) atTop (𝓝 0) := by
  let ν := (MathFin.ItoIntegralCLM.timeMeasureHorizon T).prod μ
  let U (j : ℕ) := Function.uncurry ⇑(S j).val
  let d (j : ℕ) := U j - f
  have hsm (j : ℕ) : StronglyMeasurable[𝒢.predictable] (d j) := by
    have hU : StronglyMeasurable[𝒢.predictable] (U j) := (S j).val.isStronglyPredictable
    exact hU.sub hfsm
  have hcb : MemLp (fun _ : ℝ≥0 × Ω => C) 2 ν := memLp_const C
  have hconv := tendsto_eLpNorm_two_dominated hcb
    (fun j => ((hsm j).mono 𝒢.predictable_le_prod).aestronglyMeasurable)
    (fun j => (hbd j).mono fun _ h => h.trans (by rw [Real.norm_eq_abs]; exact le_abs_self C))
    hval
  let F := hf₂.toLp f
  let x (j : ℕ) := jointSimpleAssembly (μ := μ) T 𝒢 (S j)
  have hd (j : ℕ) : edist (x j) F = eLpNorm (d j) 2 ν := by
    change edist ((simpleProcessUncurry_memLp_joint T (S j).val).toLp (U j))
      (hf₂.toLp f) = _
    rw [Lp.edist_toLp_toLp]
    exact eLpNorm_trim 𝒢.predictable_le_prod (hsm j)
  have hx : Tendsto x atTop (𝓝 F) :=
    tendsto_iff_edist_tendsto_0.mpr (by simpa only [hd] using hconv)
  let I := jointItoIntegralCLM (𝒢 := 𝒢) T hM₂
  have hI : Tendsto (fun j => edist (I (x j)) (I F)) atTop (𝓝 0) :=
    tendsto_iff_edist_tendsto_0.mp ((I.continuous.tendsto F).comp hx)
  refine hI.congr (fun j => ?_)
  rw [Lp.edist_def]
  have he : (I (x j) : Ω → ℝ) =ᵐ[μ] jointItoSimple M (S j).val := by
    rw [show I (x j) = jointItoAssembly T hM₂ (S j) from
      jointItoIntegralCLM_agrees T hM₂ hM hclock (S j)]
    exact (memLp_jointItoSimple hM₂ (S j).val).coeFn_toLp
  exact eLpNorm_congr_ae (he.sub EventuallyEq.rfl)

private noncomputable def jointDyadicSP (T : ℝ≥0) {H : ℝ≥0 → Ω → ℝ}
    (hHa : StronglyAdapted 𝒢 H) {C : ℝ} (hHB : ∀ t ω, ‖H t ω‖ ≤ C)
    (j : ℕ) : JointTBoundedSP T 𝒢 :=
  jointGridSP ((uniformDyadicGrids T).grid j) (n := 2 ^ j) (by simp)
    (fun k => (hHa ((uniformDyadicGrids T).grid j k)).measurable)
    (fun k ω => hHB ((uniformDyadicGrids T).grid j k) ω)

/-- The joint Itô integral agrees with the terminal uniform dyadic
sums for bounded adapted weights with continuous paths. -/
theorem jointItoIntegralCLM_dyadic [IsFiniteMeasure μ] (T : ℝ≥0)
    (hM : Martingale M 𝒢 μ) (hM₂ : ∀ t, MemLp (M t) 2 μ)
    (hclock : Martingale (fun t ω => M t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) 𝒢 μ)
    {H : ℝ≥0 → Ω → ℝ} {C : ℝ}
    (hHa : StronglyAdapted 𝒢 H)
    (hHsm : StronglyMeasurable[𝒢.predictable] (Function.uncurry H))
    (hHcts : ∀ᵐ ω ∂μ, ContinuousOn (fun t => H t ω) (Icc 0 T))
    (hHB : ∀ t ω, ‖H t ω‖ ≤ C)
    (hH₂ : MemLp (Function.uncurry H) 2 (jointPredictableMeasure 𝒢 μ T)) :
    Tendsto (fun j => eLpNorm
      (dyadicTerminal (uniformDyadicGrids T) j
        (fun k => H ((uniformDyadicGrids T).grid j k)) M -
        (jointItoIntegralCLM T hM₂ (hH₂.toLp (Function.uncurry H)) : Ω → ℝ)) 2 μ) atTop (𝓝 0) := by
  let ν := (MathFin.ItoIntegralCLM.timeMeasureHorizon T).prod μ
  let S (j : ℕ) := jointDyadicSP T hHa hHB j
  let U (j : ℕ) := Function.uncurry ⇑(S j).val
  let d (j : ℕ) := U j - Function.uncurry H
  have ht : ∀ᵐ z : ℝ≥0 × Ω ∂ν, z.1 ∈ Ioc 0 T :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
  have hc : ∀ᵐ z : ℝ≥0 × Ω ∂ν, ContinuousOn (fun t => H t z.2) (Icc 0 T) :=
    Measure.quasiMeasurePreserving_snd.ae hHcts
  have hstep (j : ℕ) (z : ℝ≥0 × Ω) :
      U j z = uniformDyadicStep T j (fun t => H t z.2) z.1 := by
    exact congrFun (jointGridSP_uncurry ((uniformDyadicGrids T).grid j) (n := 2 ^ j)
      (T := T) (by simp) (fun k => (hHa ((uniformDyadicGrids T).grid j k)).measurable)
      (fun k ω => hHB ((uniformDyadicGrids T).grid j k) ω)) z
  have hbd (j : ℕ) : ∀ᵐ z ∂ν, ‖d j z‖ ≤ 2 * C := by
    filter_upwards [ht] with z hz
    obtain ⟨k, _, _, hk⟩ := uniformDyadicStep_eq_coeff (fun t => H t z.2) hz j
    change ‖U j z - H z.1 z.2‖ ≤ _
    rw [hstep j z, hk]
    have hsum := add_le_add (hHB ((uniformDyadicGrids T).grid j k) z.2) (hHB z.1 z.2)
    simpa only [two_mul] using (norm_sub_le _ _).trans hsum
  have hval : ∀ᵐ z ∂ν, Tendsto (fun j => d j z) atTop (𝓝 0) := by
    filter_upwards [ht, hc] with z hz hzc
    have hu : Tendsto (fun j => U j z) atTop (𝓝 (H z.1 z.2)) := by
      simpa only [hstep] using tendsto_uniformDyadicStep hzc hz
    change Tendsto (fun j => U j z - H z.1 z.2) atTop (𝓝 0)
    simpa only [Pi.sub_def, sub_self] using hu.sub (tendsto_const_nhds (x := H z.1 z.2))
  refine (jointItoIntegralCLM_of_bounded_simple_limits T hM hM₂ hclock S hHsm hH₂ hbd hval).congr
    (fun j => ?_)
  rw [show jointItoSimple M (S j).val = dyadicTerminal (uniformDyadicGrids T) j
    (fun k => H ((uniformDyadicGrids T).grid j k)) M from
      jointItoSimple_jointGridSP M ((uniformDyadicGrids T).grid j) (n := 2 ^ j) (T := T)
        (by simp) (fun k => (hHa ((uniformDyadicGrids T).grid j k)).measurable)
        (fun k ω => hHB ((uniformDyadicGrids T).grid j k) ω)]

end RoughHeston

#print axioms RoughHeston.tendsto_eLpNorm_two_dominated
#print axioms RoughHeston.jointItoIntegralCLM_of_bounded_simple_limits
#print axioms RoughHeston.jointItoIntegralCLM_dyadic
