import WeakLimitMomentTests
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-! Uniform-on-compact errors with uniformly integrable tails vanish in
expectation along a weakly convergent sequence of path laws. -/

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace RoughHeston

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X]

theorem compact_uniform_tails_of_weak_sequence {Pn : ℕ → ProbabilityMeasure X}
    {P : ProbabilityMeasure X} (hweak : Tendsto Pn atTop (𝓝 P)) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K : Set X, IsCompact K ∧ ∀ n, (Pn n : Measure X) Kᶜ ≤ ε := by
  let S := Set.range Pn
  have hc : IsCompact (closure S) := hweak.isCompact_insert_range.of_isClosed_subset
    isClosed_closure
    (closure_minimal (subset_insert _ _) hweak.isCompact_insert_range.isClosed)
  have ht := isTightMeasureSet_of_isCompact_closure hc
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at ht
  obtain ⟨K, hK, hsmall⟩ := ht ε hε
  exact ⟨K, hK, fun n => hsmall _ ⟨Pn n, ⟨⟨n, rfl⟩, rfl⟩⟩⟩

/-- A continuous bounded test may be replaced by approximating tests
whose errors vanish uniformly on compact sets and are uniformly in L².
The errors themselves need only be measurable. -/
theorem tendsto_integral_norm_zero_of_uniform_on_compacts_of_weak
    {Pn : ℕ → ProbabilityMeasure X} {P : ProbabilityMeasure X}
    (hweak : Tendsto Pn atTop (𝓝 P)) {D : ℕ → X → ℝ}
    {C : ℝ} (hC : 0 ≤ C)
    (hD : ∀ n, MemLp (D n) 2 (Pn n : Measure X))
    (hSq : ∀ n, (∫ x, (D n x)^2 ∂(Pn n : Measure X)) ≤ C)
    (hCompact : ∀ K : Set X, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ x ∈ K, ‖D n x‖ < ε) :
    Tendsto (fun n => ∫ x, ‖D n x‖ ∂(Pn n : Measure X)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  let R := 4 * (C + 1) / ε
  let δ := ε / (4 * (R + 1))
  have hR : 0 < R := by dsimp [R]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨K, hK, htail⟩ := compact_uniform_tails_of_weak_sequence hweak (ENNReal.ofReal_pos.2 hδ)
  filter_upwards [hCompact K hK (ε / 4) (by positivity)] with n hn
  let ν : Measure X := (Pn n : Measure X)
  have hnint : Integrable (D n) ν := (hD n).integrable one_le_two
  have hsq := (hD n).integrable_sq
  have hIn : (∫ x in K, ‖D n x‖ ∂ν) ≤ ε / 4 := by
    calc
      _ ≤ ∫ _ in K, ε / 4 ∂ν :=
        setIntegral_mono_on hnint.norm.integrableOn (integrable_const _).integrableOn hK.measurableSet
          (fun x hx => (hn x hx).le)
      _ = ν.real K * (ε / 4) := by rw [setIntegral_const, smul_eq_mul]
      _ ≤ _ := by
        have hνK : ν.real K ≤ 1 := by
          rw [measureReal_def]
          exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2 (prob_le_one)
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hνK (by positivity : 0 ≤ ε / 4)
  have hRT : R * δ ≤ ε / 4 := by
    have h := div_mul_cancel₀ ε (show 4 * (R + 1) ≠ 0 from by positivity)
    have he : δ * (4 * (R + 1)) = ε := h
    nlinarith [mul_nonneg hδ.le (show 0 ≤ (1 : ℝ) by norm_num)]
  have hCR : R⁻¹ * C ≤ ε / 4 := by
    have hEq : R * ε = 4 * (C + 1) := div_mul_cancel₀ _ hε.ne'
    have hm : C ≤ R * (ε / 4) := by linarith
    have h := (mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hR.le))
    rwa [← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul] at h
  have hOutsidePoint (x : X) : ‖D n x‖ ≤ R + R⁻¹ * (D n x)^2 := by
    let u := |D n x|
    change u ≤ _
    by_cases hu : u ≤ R
    · exact hu.trans (le_add_of_nonneg_right (mul_nonneg (inv_nonneg.mpr hR.le) (sq_nonneg _)))
    · have hh : R * u ≤ u^2 := by
        simpa only [pow_two] using mul_le_mul_of_nonneg_right (le_of_not_ge hu) (abs_nonneg _)
      have h' := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hR.le)
      rw [← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul] at h'
      have hu2 : u ^ 2 = (D n x)^2 := sq_abs _
      rw [hu2] at h'
      exact h'.trans (le_add_of_nonneg_left hR.le)
  have hOut : (∫ x in Kᶜ, ‖D n x‖ ∂ν) ≤ ε / 4 + ε / 4 := by
    have hDom : Integrable (fun x => R + R⁻¹ * (D n x)^2) ν :=
      (integrable_const _).add (hsq.const_mul _)
    have hComp : ν.real Kᶜ ≤ δ := by
      rw [measureReal_def, ← ENNReal.toReal_ofReal hδ.le]
      exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).2 (htail n)
    calc
      _ ≤ ∫ x in Kᶜ, R + R⁻¹ * (D n x)^2 ∂ν :=
        setIntegral_mono_on hnint.norm.integrableOn hDom.integrableOn
          hK.measurableSet.compl (fun x _ => hOutsidePoint x)
      _ = R * ν.real Kᶜ + R⁻¹ * (∫ x in Kᶜ, (D n x)^2 ∂ν) := by
        rw [integral_add (integrable_const R) (hsq.const_mul _).integrableOn, setIntegral_const,
          smul_eq_mul, integral_const_mul, mul_comm (ν.real Kᶜ)]
      _ ≤ R * δ + R⁻¹ * C := by
        apply add_le_add (mul_le_mul_of_nonneg_left hComp hR.le)
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hR.le)
        exact (integral_mono_measure Measure.restrict_le_self
          (Eventually.of_forall fun x => sq_nonneg _) hsq).trans (hSq n)
      _ ≤ _ := add_le_add hRT hCR
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  rw [← integral_add_compl hK.measurableSet hnint.norm]
  linarith

#print axioms RoughHeston.compact_uniform_tails_of_weak_sequence
#print axioms RoughHeston.tendsto_integral_norm_zero_of_uniform_on_compacts_of_weak

end RoughHeston
