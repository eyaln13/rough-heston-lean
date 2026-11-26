import ClusterPhysicalSupBound

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston

/-- The old-law mean is continuous when the variance has an integrable
path supremum. This applies as well after conditioning at birth. -/
theorem continuous_cluster_mean_of_dominated {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {U : ℝ≥0 → Ω → ℝ} {D : Ω → ℝ}
    (hU : ∀ t, Measurable (U t)) (hc : ∀ ω, Continuous fun t => U t ω)
    (hD : Integrable D P) (hdom : ∀ᵐ ω ∂P, ∀ t, ‖U t ω‖≤‖D ω‖) :
    Continuous fun t => ∫ ω,U t ω ∂P := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact tendsto_integral_filter_of_dominated_convergence (fun ω => ‖D ω‖)
    (Eventually.of_forall fun s => (hU s).aestronglyMeasurable)
    (Eventually.of_forall fun s => hdom.mono fun ω hw => hw s)
    hD.norm (ae_of_all P fun ω => (hc ω).continuousAt)

#print axioms continuous_cluster_mean_of_dominated

end RoughHeston
