import AffinePointTimeEnergy
import StoppedAffineRowEnergy
import NativeShortHorizon

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston.GirsanovPort

/-- Extend the observation's deterministic time row by zero up to
the common Brownian horizon. -/
theorem reflected_riccati_zero_extension_memLp_two {s H : ℝ≥0} (hs : s ≤ H)
    {w : ℝ → ℝ} (hw : Measurable w) (hw₂ : IntegrableOn (fun r => w r ^ 2) (Ioc 0 (s:ℝ)))
    (σ : ℝ) :
    MemLp ((Ioc (0:ℝ≥0) s).indicator (fun t => σ*w ((s:ℝ)-(t:ℝ)))) 2 (hestonTimeMeasure H) := by
  have hm : (hestonTimeMeasure H).restrict (Ioc (0:ℝ≥0) s) = hestonTimeMeasure s := by
    rw [hestonTimeMeasure_eq_horizon,hestonTimeMeasure_eq_horizon,
      MathFin.ItoIntegralCLM.timeMeasureHorizon,MathFin.ItoIntegralCLM.timeMeasureHorizon,
      Measure.restrict_restrict measurableSet_Ioc,inter_eq_left.mpr (Ioc_subset_Ioc_right hs)]
  have hmSet : MeasurableSet (Ioc (0:ℝ≥0) s) := measurableSet_Ioc
  apply (memLp_indicator_iff_restrict hmSet.nullMeasurableSet).2
  rw [hm]
  exact reflected_riccati_memLp_two s hw hw₂ σ

variable {Ω : Type*} [m : MeasurableSpace Ω] {F : Filtration ℝ≥0 m}

/-- Restricting a random exit time to the deterministic observation is
again a stopping time in the same filtration. -/
theorem affine_observation_stop {s : ℝ≥0} {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0))) :
    IsStoppingTime F (fun ω => (min s (τ ω) : WithTop ℝ≥0)) := by
  simpa only [WithTop.coe_min] using (isStoppingTime_const F s).min hτ

/-- The deterministic zero extension does not change the stopped row. -/
theorem stoppedAffineTestRow_zero_extension
    {s b : ℝ≥0} {τ : Ω → ℝ≥0} {L Y : ℝ≥0 → Ω → ℝ} {k : ℝ≥0 → ℝ}
    (hτ : ∀ ω, τ ω≤s) :
    stoppedAffineTestRow ((Ioc (0:ℝ≥0) s).indicator k) L Y b τ =
      stoppedAffineTestRow k L Y b τ := by
  funext t ω
  by_cases ht : b<t ∧ t≤τ ω
  · have hm : t ∈ Ioc (0:ℝ≥0) s := ⟨zero_le.trans_lt ht.1,ht.2.trans (hτ ω)⟩
    simp only [stoppedAffineTestRow,ite_eq_left ht,indicator_of_mem hm]
  · simp only [stoppedAffineTestRow,ite_eq_right ht]

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.reflected_riccati_zero_extension_memLp_two
#print axioms RoughHeston.GirsanovPort.affine_observation_stop
#print axioms RoughHeston.GirsanovPort.stoppedAffineTestRow_zero_extension
