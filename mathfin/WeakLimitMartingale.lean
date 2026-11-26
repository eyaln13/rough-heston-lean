import StochasticFoundation
import WeakLimitMomentTests
import BoundedContinuousMartingaleTests

open MeasureTheory Filter Set
open scoped MeasureTheory BoundedContinuousFunction Topology ENNReal

namespace RoughHeston

/-- Approximate tests against bounded continuous functions of the past
pass to the weak limit under uniform second moments of the weighted
increments and imply the martingale test for every measurable past event. -/
theorem martingale_of_weak_limit_of_boundedContinuous_past_tests
    {Ω E ι I : Type*} [TopologicalSpace Ω] [mΩ : MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] [PseudoMetricSpace E] [mE : MeasurableSpace E]
    [BorelSpace E] [Preorder ι] {l : Filter I} [NeBot l]
    {Pn : I → ProbabilityMeasure Ω} {P : ProbabilityMeasure Ω}
    (hweak : Tendsto Pn l (𝓝 P)) {𝒢 : Filtration ι mΩ}
    {M : ι → Ω → ℝ} (hMadapted : StronglyAdapted 𝒢 M)
    (hMcontinuous : ∀ t, Continuous (M t))
    (hMint : ∀ t, Integrable (M t) (P : Measure Ω))
    {past : ι → Ω → E} (hpastContinuous : ∀ s, Continuous (past s))
    (hpastAlg : ∀ s, 𝒢 s = mE.comap (past s))
    (htest : ∀ s t, s ≤ t → ∀ f : E →ᵇ ℝ,
      Tendsto (fun i => ∫ ω, (M t ω - M s ω) * f (past s ω) ∂(Pn i : Measure Ω)) l (𝓝 0))
    (hmoment : ∀ s t, s ≤ t → ∀ f : E →ᵇ ℝ, ∃ C : ℝ, ∀ i,
      MemLp (fun ω => (M t ω - M s ω) * f (past s ω)) 2 (Pn i : Measure Ω) ∧
      (∫ ω, ((M t ω - M s ω) * f (past s ω)) ^ 2 ∂(Pn i : Measure Ω)) ≤ C) :
    Martingale M 𝒢 (P : Measure Ω) := by
  refine martingale_of_past_set_integrals hMadapted hMint ?_
  intro s t hst A hA
  rw [hpastAlg s] at hA
  obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hA
  refine setIntegral_preimage_eq_of_boundedContinuous_tests (hpastContinuous s).measurable
    (hMint s) (hMint t) ?_ hB
  intro f
  have hg : Continuous (fun ω => (M t ω - M s ω) * f (past s ω)) :=
    ((hMcontinuous t).sub (hMcontinuous s)).mul (f.continuous.comp (hpastContinuous s))
  obtain ⟨C, hC⟩ := hmoment s t hst f
  exact tendsto_nhds_unique
    (tendsto_integral_of_weak_of_uniform_sq_moment' hweak hg
      (fun i => (hC i).1) (fun i => (hC i).2)) (htest s t hst f)

end RoughHeston

#print axioms RoughHeston.martingale_of_weak_limit_of_boundedContinuous_past_tests
