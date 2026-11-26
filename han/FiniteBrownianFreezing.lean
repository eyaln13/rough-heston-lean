import FiniteBrownianFrozenMartingales

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston.GirsanovPort

/-- A finite-horizon Brownian driver can be frozen at its terminal
time while retaining the same Brownian law on the supplied filtration. -/
theorem finiteBrownianOn_freeze {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 m} {r : ℝ≥0} {B : ℝ≥0 → Ω → ℝ}
    (hB : MathFinBridge.BrownianOn P F r B) :
    MathFinBridge.BrownianOn P F r (fun t => B (min t r)) := by
  refine ⟨fun t => (hB.adapted _).mono (F.mono (min_le_left t r)),?_,?_,?_,?_⟩
  · simpa only [min_eq_left (zero_le : (0:ℝ≥0)≤r)] using hB.zero_at_start
  · filter_upwards [hB.continuous_paths] with ω hω
    apply hω.comp ((continuous_id.min continuous_const).continuousOn)
    exact fun t ht => ⟨zero_le,min_le_right _ _⟩
  · intro s t hst ht
    simpa only [min_eq_left ht,min_eq_left (hst.trans ht)] using hB.normal_increment s t hst ht
  · intro s t hst ht
    simpa only [min_eq_left ht,min_eq_left (hst.trans ht)] using hB.independent_of_past s t hst ht

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.finiteBrownianOn_freeze
