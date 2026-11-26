import CanonicalPairPath
import StochasticFoundation

/-! Passing martingales to the law of the joint canonical trajectories. -/

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped NNReal ENNReal Topology

namespace RoughHeston

/-- Taking a measurable image preserves martingale tests when the
measurability of each earlier pullback is known in the original filtration. -/
theorem martingale_measure_map_of_filtration_measurable {Ω P I : Type*}
    {mΩ : MeasurableSpace Ω} {mP : MeasurableSpace P} [Preorder I]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : Filtration I mΩ} {G : Filtration I mP} {φ : Ω → P}
    (hφ : Measurable φ) (hFil : ∀ t, Measurable[F t, G t] φ) {M : I → P → ℝ}
    (hMa : StronglyAdapted G M) (hM : Martingale (fun t p => M t (φ p)) F μ) :
    Martingale M G (Measure.map φ μ) := by
  have hm (t : I) : Measurable (M t) := (hMa t).measurable.mono (G.le t) le_rfl
  have hi (t : I) : Integrable (M t) (Measure.map φ μ) :=
    (integrable_map_measure (hm t).stronglyMeasurable.aestronglyMeasurable hφ.aemeasurable).2
      (hM.integrable t)
  apply martingale_of_past_set_integrals hMa hi
  intro s t hst A hA
  rw [setIntegral_map (G.le s A hA) (hi s).aestronglyMeasurable hφ.aemeasurable,
    setIntegral_map (G.le s A hA) (hi t).aestronglyMeasurable hφ.aemeasurable]
  exact hM.setIntegral_eq hst (hFil s hA)

variable {Ω E : Type*} [m : MeasurableSpace Ω]
  [TopologicalSpace E] [MetrizableSpace E] [SecondCountableTopology E] [RegularSpace E]
  [MeasurableSpace E] [BorelSpace E]

/-- Measurability of all evaluations gives measurability into the full
Borel sigma-algebra of continuous trajectories. -/
theorem measurable_canonicalPath_of_evaluations {T : ℝ≥0} {φ : Ω → CanonicalPath T E}
    (hφ : ∀ t : CanonicalPathTime T, Measurable (fun ω => φ ω t)) : Measurable φ := by
  rw [measurable_iff_comap_le, ContinuousMap.measurableSpace_eq_iSup_comap_eval]
  simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp, iSup_le_iff]
  exact fun t => (hφ t).comap_le

/-- A measurable map of trajectories is measurable at each canonical
past when every adapted time coordinate is pulled back. -/
theorem filtration_measurable_canonicalPath_of_adapted {T : ℝ≥0} {φ : Ω → CanonicalPath T E}
    {F : Filtration ℝ≥0 m}
    (hφ : Adapted F (fun t ω => canonicalPathEval T t (φ ω))) (t : ℝ≥0) :
    Measurable[F t, canonicalPathNaturalFiltration (E := E) T t] φ := by
  apply Measurable.of_comap_le
  change MeasurableSpace.comap φ (⨆ j ≤ t, MeasurableSpace.comap (canonicalPathEval T j) inferInstance) ≤ F t
  simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp, iSup_le_iff]
  exact fun j hj => ((hφ j).mono (F.mono hj) le_rfl).comap_le

#print axioms RoughHeston.martingale_measure_map_of_filtration_measurable
#print axioms RoughHeston.measurable_canonicalPath_of_evaluations
#print axioms RoughHeston.filtration_measurable_canonicalPath_of_adapted

end RoughHeston
