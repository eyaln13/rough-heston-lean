import StoppedBurstSeparation
import UndoClusterBias

/-! The small-age choice δ=r^(2η/3) in the probability estimate and the
single-birth bound under the original law. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace RoughHeston

/-- One age cutoff works for all meshes when the constants in the
stopped occupation and energy estimates are uniform. -/
theorem eventually_small_age_separation {η p : ℝ} (hη : 0 < η) (hp : 0 < p) (C D : ℝ) :
    ∀ᶠ r : ℝ in 𝓝[>] (0:ℝ), p/2 ≤ p - p/4 -
      C*r^η / r^(2*η/3) - D*r^η - Real.sqrt (r^(2*η/3))/2 := by
  have h1 : Tendsto (fun r : ℝ => r^(η/3)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hc := (continuous_id.rpow_const (p := η/3) (fun _ => Or.inr (by positivity))).continuousAt
      (x := (0:ℝ))
    simpa [Real.zero_rpow (by positivity : η/3 ≠ 0)] using (hc.continuousWithinAt (s := Ioi 0)).tendsto
  have h2 : Tendsto (fun r : ℝ => r^η) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa [Real.zero_rpow hη.ne'] using
      ((continuous_id.rpow_const (p := η) (fun _ => Or.inr hη.le)).continuousAt
        (x := (0:ℝ))).continuousWithinAt.tendsto (s := Ioi 0)
  have hlim : Tendsto (fun r : ℝ => C*r^(η/3)+D*r^η+r^(η/3)/2) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa using ((h1.const_mul C).add (h2.const_mul D)).add (h1.div_const 2)
  filter_upwards [self_mem_nhdsWithin, (tendsto_order.mp hlim).2 (p/4) (by positivity)] with r hr h
  have hr' : 0 < r := hr
  have hratio : r^η/r^(2*η/3) = r^(η/3) := by
    rw [← Real.rpow_sub hr', show η-2*η/3=η/3 by ring]
  have hs : Real.sqrt (r^(2*η/3)) = r^(η/3) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hr'.le]
    congr 1
    ring
  rw [mul_div_assoc,hratio,hs]
  linarith

/-- A size-biased burst with a mass cap yields the required linear
bound in the immigration mass under the original law, on the birth event. -/
theorem original_single_birth_burst {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {birth : Set Ω} {ε cap threshold p a : ℝ}
    {U Y Z : Ω → ℝ} (hb : 0 < P birth) (ha : a ≤ P.real birth)
    (hε : 0 < ε) (hc : 0 < cap) (hp : 0 ≤ p)
    (hu : Measurable U) (hy : Measurable Y) (hz : Measurable Z)
    (hQ : p ≤ (birthConditionedSizeBiasedLaw P birth Z ε).real
      ({ω | threshold ≤ U ω ∧ Z ω ≤ cap} ∩ {ω | Y ω = 0})) :
    (a*p/cap)*ε ≤ P.real ({ω | threshold ≤ U ω ∧ Y ω = 0} ∩ birth) := by
  let E := {ω | threshold ≤ U ω ∧ Y ω = 0}
  have hm : MeasurableSet E :=
    (measurableSet_le measurable_const hu).inter (measurableSet_eq_fun hy measurable_const)
  have he : E ∩ {ω | Z ω ≤ cap} =
    {ω | threshold ≤ U ω ∧ Z ω ≤ cap} ∩ {ω | Y ω = 0} := by
    ext ω
    exact and_assoc.trans (and_congr_right fun _ => and_comm) |>.trans and_assoc.symm
  have h := measureReal_inter_birth_lower_bound_of_conditioned_size_bias hb hε hc hz hm (he ▸ hQ)
  calc
    _ = a*ε*p/cap := by ring
    _ ≤ _ := (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha hε.le) hp) hc.le).trans h

#print axioms eventually_small_age_separation
#print axioms original_single_birth_burst

end RoughHeston
