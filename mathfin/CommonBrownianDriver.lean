import TheoremStatement
import FiniteHorizonLevy
import RankOneCompensators

open MeasureTheory Filter
open scoped MeasureTheory ProbabilityTheory Topology NNReal ENNReal

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℝ≥0 m} {T : ℝ≥0}

/-- The Brownian modification is Brownian for the exact filtration and
horizon in the variance assertion. -/
theorem isBrownianOn_modification_of_unit_clock [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} {T : ℝ≥0} {M : ℝ≥0 → Ω → ℝ}
    (hnull : ∀ N : Set Ω, MeasurableSet N → μ N = 0 → MeasurableSet[𝒢 0] N)
    (hM : Martingale M 𝒢 μ)
    (hMsq : Martingale (fun t ω => M t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) 𝒢 μ)
    (hcts : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (h0 : M 0 =ᵐ[μ] 0) :
    ∃ B : ℝ≥0 → Ω → ℝ, IsBrownianOn μ 𝒢 T B ∧ ∀ t, B t =ᵐ[μ] M t := by
  obtain ⟨B, hB, he⟩ :=
    MathFinBridge.brownianOn_modification_of_measurable_nulls hnull hM hMsq hcts h0
  exact ⟨B, ⟨hB.adapted, hB.zero_at_start, hB.continuous_paths,
    hB.normal_increment, hB.independent_of_past⟩, he⟩


/-- Timewise almost sure equality of drivers preserves the integrals
defined by the dyadic amplitude cutoffs. -/
theorem HasAmplitudeCutoffIntegral.congr_driver
    {B B' M a : ℝ≥0 → Ω → ℝ}
    (h : HasAmplitudeCutoffIntegral 𝒢 μ T B M a)
    (he : ∀ t, B t =ᵐ[μ] B' t) :
    HasAmplitudeCutoffIntegral 𝒢 μ T B' M a := by
  obtain ⟨J, hJ, hJ₂, hgrid, hlimit⟩ := h
  refine ⟨J, hJ, hJ₂, fun n t ht => (hgrid n t ht).congr (fun j => ?_), hlimit⟩
  let P := (uniformDyadicGrids T).grid j
  have htimes : ∀ᵐ ω ∂μ, ∀ k, B (min t (P k)) ω = B' (min t (P k)) ω :=
    ae_all_iff.mpr fun k => he (min t (P k))
  let w (k : ℕ) (ω : Ω) := min (a (P k) ω) (n : ℝ)
  have hsum : gridIntegralProcess P w B (2 ^ j) t =ᵐ[μ]
      gridIntegralProcess P w B' (2 ^ j) t := by
    filter_upwards [htimes] with ω hω
    simp only [gridIntegralProcess, Finset.sum_apply, stochasticStep,
      Pi.mul_apply, Pi.sub_apply, hω]
  exact eLpNorm_congr_ae (hsum.sub EventuallyEq.rfl)

/-- The Brownian modification preserves its unit clock and the
amplitude-cutoff representations on the same filtration. -/
theorem pair_has_common_brownian_of_unit_clock_with_compensator [IsProbabilityMeasure μ]
    {M N a b : ℝ≥0 → Ω → ℝ}
    (hnull : ∀ E : Set Ω, MeasurableSet E → μ E = 0 → MeasurableSet[𝒢 0] E)
    (h : ∃ B : ℝ≥0 → Ω → ℝ, Martingale B 𝒢 μ ∧ (∀ t, MemLp (B t) 2 μ) ∧
      (B 0 =ᵐ[μ] 0) ∧ (∀ᵐ ω ∂μ, Continuous (fun t => B t ω)) ∧
      Martingale (fun t ω => B t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) 𝒢 μ ∧
      HasAmplitudeCutoffIntegral 𝒢 μ T B M a ∧ HasAmplitudeCutoffIntegral 𝒢 μ T B N b) :
    ∃ B : ℝ≥0 → Ω → ℝ, IsBrownianOn μ 𝒢 T B ∧
      Martingale B 𝒢 μ ∧ (∀ t, MemLp (B t) 2 μ) ∧
      Martingale (fun t ω => B t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) 𝒢 μ ∧
      HasAmplitudeCutoffIntegral 𝒢 μ T B M a ∧ HasAmplitudeCutoffIntegral 𝒢 μ T B N b := by
  obtain ⟨B, hB, hB₂, hB0, hBc, hBsq, hM, hN⟩ := h
  obtain ⟨B', hB', he⟩ :=
    isBrownianOn_modification_of_unit_clock hnull hB hBsq hBc hB0
  have martingale_congr {U V : ℝ≥0 → Ω → ℝ} (hU : Martingale U 𝒢 μ)
      (hV : StronglyAdapted 𝒢 V) (hUV : ∀ t, V t =ᵐ[μ] U t) :
      Martingale V 𝒢 μ := by
    refine ⟨hV, fun s t hst => ?_⟩
    exact (condExp_congr_ae (hUV t)).trans ((hU.condExp_ae_eq hst).trans (hUV s).symm)
  have hB'm : Martingale B' 𝒢 μ := martingale_congr hB hB'.adapted he
  have hB'sm : StronglyAdapted 𝒢 (fun t ω => B' t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) :=
    fun t => ((hB'.adapted t).pow 2).sub stronglyMeasurable_const
  have hB'sq : Martingale (fun t ω => B' t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) 𝒢 μ :=
    martingale_congr hBsq hB'sm (fun t => (he t).mono fun _ hw => congrArg (fun w : ℝ => w ^ 2 - ↑(min t T)) hw)
  exact ⟨B', hB', hB'm, fun t => (hB₂ t).ae_eq (he t).symm, hB'sq,
    hM.congr_driver (fun t => (he t).symm), hN.congr_driver (fun t => (he t).symm)⟩

/-- The simultaneous cutoff representations survive the Brownian
modification on the joint filtration. The premise is precisely the
output of the rank-one common-driver construction. -/
theorem pair_has_common_brownian_of_unit_clock [IsProbabilityMeasure μ]
    {M N a b : ℝ≥0 → Ω → ℝ}
    (hnull : ∀ E : Set Ω, MeasurableSet E → μ E = 0 → MeasurableSet[𝒢 0] E)
    (h : ∃ B : ℝ≥0 → Ω → ℝ, Martingale B 𝒢 μ ∧ (∀ t, MemLp (B t) 2 μ) ∧
      (B 0 =ᵐ[μ] 0) ∧ (∀ᵐ ω ∂μ, Continuous (fun t => B t ω)) ∧
      Martingale (fun t ω => B t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) 𝒢 μ ∧
      HasAmplitudeCutoffIntegral 𝒢 μ T B M a ∧ HasAmplitudeCutoffIntegral 𝒢 μ T B N b) :
    ∃ B : ℝ≥0 → Ω → ℝ, IsBrownianOn μ 𝒢 T B ∧
      HasAmplitudeCutoffIntegral 𝒢 μ T B M a ∧ HasAmplitudeCutoffIntegral 𝒢 μ T B N b := by
  obtain ⟨B, hB, _, _, _, hM, hN⟩ :=
    pair_has_common_brownian_of_unit_clock_with_compensator hnull h
  exact ⟨B, hB, hM, hN⟩

end RoughHeston

#print axioms RoughHeston.isBrownianOn_modification_of_unit_clock
#print axioms RoughHeston.HasAmplitudeCutoffIntegral.congr_driver
#print axioms RoughHeston.pair_has_common_brownian_of_unit_clock

#print axioms RoughHeston.pair_has_common_brownian_of_unit_clock_with_compensator
