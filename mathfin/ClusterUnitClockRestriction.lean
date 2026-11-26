import CommonBrownianDriver
import ClusterPulseHorizonConsistency

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston.GirsanovPort

/-- The original unit-clock martingale, frozen at a shorter age, is
Brownian on that age horizon in the filtration used for the cluster. -/
theorem cluster_unit_clock_brownian_on_age {Ω : Type*} [m : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : Filtration ℝ≥0 m} {T t : ℝ≥0}
    {B : ℝ≥0 → Ω → ℝ} (ht : t ≤ T)
    (hnull : ∀ N : Set Ω, MeasurableSet N → P N=0 → MeasurableSet[F 0] N)
    (hB : Martingale B F P) (hclock : Martingale (fun r ω => B r ω^2-((min r T:ℝ≥0):ℝ)) F P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun r => B r ω)) (h0 : B 0 =ᵐ[P] 0) :
    MathFinBridge.BrownianOn P F t (fun r => B (min r t)) := by
  let X (r : ℝ≥0) := B (min r t)
  have hX : Martingale X F P := martingale_freeze_at hB t
  have hXc : ∀ᵐ ω ∂P, Continuous (fun r => X r ω) :=
    hc.mono fun ω hw => hw.comp (continuous_id.min continuous_const)
  have hXclock : Martingale (fun r ω => X r ω^2-((min r t:ℝ≥0):ℝ)) F P := by
    simpa only [X,min_assoc,min_eq_left ht] using martingale_freeze_at hclock t
  have hX₀ : X 0 =ᵐ[P] 0 := by simpa only [X,min_eq_left (show (0:ℝ≥0) ≤ t from zero_le)] using h0
  obtain ⟨W,hW,he⟩ := MathFinBridge.brownianOn_modification_of_measurable_nulls hnull hX hXclock hXc hX₀
  refine ⟨hX.stronglyAdapted,hX₀,hXc.mono (fun _ hw => hw.continuousOn),?_,?_⟩
  · intro r s hrs hs
    exact (Measure.map_congr ((he s).sub (he r))).symm.trans (hW.normal_increment r s hrs hs)
  · intro r s hrs hs
    have hW' : @IndepFun Ω ℝ Ω m (borel ℝ) (F r) (fun ω => W s ω-W r ω) id P := by
      change Indep _ (MeasurableSpace.comap id (F r)) P
      simpa only [MeasurableSpace.comap_id] using hW.independent_of_past r s hrs hs
    have hX' := hW'.congr ((he s).sub (he r)) (EventuallyEq.rfl : id =ᵐ[P] id)
    change Indep _ (MeasurableSpace.comap id (F r)) P at hX'
    simpa only [MeasurableSpace.comap_id, X, Pi.sub_def] using hX'

#print axioms cluster_unit_clock_brownian_on_age

end RoughHeston.GirsanovPort
