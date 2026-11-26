import FractionalCoupledPathLaw
import CanonicalProperPathTightness
import WeakLimitTimeMoments
import DeterministicMartingaleShift

/-! Nonnegativity, initial data, and all physical martingale tests pass
to the weak limit on the fixed joint path space. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BoundedContinuousFunction

namespace RoughHeston

theorem ae_mem_closed_of_probability_weak_limit
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {Pn : ℕ → ProbabilityMeasure X} {P : ProbabilityMeasure X}
    (hweak : Tendsto Pn atTop (𝓝 P)) {S : Set X} (hS : IsClosed S)
    (hAE : ∀ n, ∀ᵐ p ∂(Pn n : Measure X), p ∈ S) :
    ∀ᵐ p ∂(P : Measure X), p ∈ S := by
  have hone (n : ℕ) : (Pn n : Measure X) S = 1 :=
    ((ae_mem_iff_measure_eq hS.measurableSet.nullMeasurableSet).1 (hAE n)).trans measure_univ
  apply (ae_mem_iff_measure_eq hS.measurableSet.nullMeasurableSet).2
  rw [measure_univ]
  apply le_antisymm ((measure_mono (subset_univ S)).trans_eq measure_univ)
  simpa only [hone, limsup_const] using ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hweak hS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "J" => CoupledPhysicalState ι

/-- The simultaneous nonnegative physical region for all focal rows. -/
def canonicalPhysicalNonnegative (T : ℝ≥0) : Set (CanonicalPath T J) :=
  {p | ∀ (i : Option ι) (t : CanonicalPathTime T), 0 ≤ (p t).1 i}

theorem isClosed_canonicalPhysicalNonnegative (T : ℝ≥0) :
    IsClosed (canonicalPhysicalNonnegative (ι := ι) T) := by
  have he : canonicalPhysicalNonnegative (ι := ι) T =
      ⋂ i : Option ι, ⋂ t : CanonicalPathTime T, {p : CanonicalPath T J | 0 ≤ (p t).1 i} := by
    ext p
    simp [canonicalPhysicalNonnegative]
  rw [he]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro t
  exact isClosed_le continuous_const
    ((continuous_apply i).comp ((continuous_eval_const t).fst))

def canonicalPhysicalInitialSet (T : ℝ≥0) (v : Option ι → ℝ) : Set (CanonicalPath T J) :=
  {p | canonicalPathEval T 0 p = (v, 0)}

theorem isClosed_canonicalPhysicalInitialSet (T : ℝ≥0) (v : Option ι → ℝ) :
    IsClosed (canonicalPhysicalInitialSet T v) :=
  (isClosed_singleton (x := (v, 0))).preimage (continuous_canonicalPathEval T 0)

namespace FractionalCoupledSmoothLaw

variable {T : ℝ≥0} {α κ σ : ℝ} {n : ℕ} {v : Option ι → ℝ} {β : Option ι → ℝ≥0 → ℝ}
  (L : FractionalCoupledSmoothLaw T α n κ σ v β)
  {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B)

theorem ae_fixedPhysical_nonnegative :
    ∀ᵐ p ∂(L.fixedPhysicalLaw hB hβ hβB : Measure _),
      p ∈ canonicalPhysicalNonnegative (ι := ι) T := by
  let φ := L.fixedPhysicalPath hB hβ hβB
  change ∀ᵐ p ∂Measure.map φ (L.law : Measure _), p ∈ canonicalPhysicalNonnegative T
  apply (ae_map_iff (L.measurable_fixedPhysicalPath hB hβ hβB).aemeasurable
    (isClosed_canonicalPhysicalNonnegative (ι := ι) T).measurableSet).2
  filter_upwards [L.nonneg] with q hq
  intro i t
  have ht : canonicalEvalTime T t = t := Subtype.ext (min_eq_left t.property.2)
  have hEval := L.canonicalPathEval_fixedPhysicalPath hB hβ hβB t q
  change φ q (canonicalEvalTime T t) = _ at hEval
  rw [ht] at hEval
  rw [hEval]
  exact hq i t t.property

theorem ae_fixedPhysical_initial :
    ∀ᵐ p ∂(L.fixedPhysicalLaw hB hβ hβB : Measure _),
      p ∈ canonicalPhysicalInitialSet T v := by
  let φ := L.fixedPhysicalPath hB hβ hβB
  change ∀ᵐ p ∂Measure.map φ (L.law : Measure _), p ∈ canonicalPhysicalInitialSet T v
  apply (ae_map_iff (L.measurable_fixedPhysicalPath hB hβ hβB).aemeasurable
    (isClosed_canonicalPhysicalInitialSet T v).measurableSet).2
  have hResidual : ∀ᵐ q ∂(L.law : Measure _), ∀ i : Option ι, L.residual i 0 q = 0 :=
    ae_all_iff.2 fun i => L.residual_starts_zero i hB hβ hβB
  filter_upwards [L.initial, hResidual] with q h0 hR
  change canonicalPathEval T 0 (L.fixedPhysicalPath hB hβ hβB q) = (v, 0)
  rw [L.canonicalPathEval_fixedPhysicalPath hB hβ hβB]
  apply Prod.ext <;> funext i
  · change fractionalCoupledSmoothPath T α n β 0 q (i, none) = v i
    rw [h0]
    rfl
  · exact hR i

end FractionalCoupledSmoothLaw

/-- Pass any fixed canonical continuous martingale functional with
uniform timewise second moments to the weak limit. -/
theorem canonicalPhysical_martingale_of_weak_limit
    {T : ℝ≥0} {Pn : ℕ → ProbabilityMeasure (CanonicalPath T J)}
    {P : ProbabilityMeasure (CanonicalPath T J)} (hweak : Tendsto Pn atTop (𝓝 P))
    {M : ℝ≥0 → CanonicalPath T J → ℝ}
    (hMc : ∀ t, Continuous (M t))
    (hMa : StronglyAdapted (canonicalPathNaturalFiltration T) M)
    (hMn : ∀ n, Martingale M (canonicalPathNaturalFiltration T) (Pn n : Measure _))
    (h₂ : ∀ t, ∃ C : ℝ, ∀ n, MemLp (M t) 2 (Pn n : Measure _) ∧
      (∫ p, (M t p)^2 ∂(Pn n : Measure _)) ≤ C) :
    Martingale M (canonicalPathNaturalFiltration T) (P : Measure _) := by
  have hAlg := canonicalPathNaturalFiltration_eq_comap_stopped (E := J) T
  have hS (n : ℕ) : Martingale (fun t p => M t p + (0 : ℝ))
      (canonicalPathNaturalFiltration T) (Pn n : Measure _) := by
    simpa only [add_zero] using hMn n
  exact martingale_of_weak_limit_of_uniform_time_sq_moments hweak hMa hMc
    (continuous_canonicalStoppedPath T) hAlg
    (tendsto_boundedContinuous_past_tests_of_deterministic_shift (d := fun _ _ => 0)
      (fun _ => tendsto_const_nhds) hS hAlg) h₂

#print axioms RoughHeston.ae_mem_closed_of_probability_weak_limit
#print axioms RoughHeston.FractionalCoupledSmoothLaw.ae_fixedPhysical_nonnegative
#print axioms RoughHeston.FractionalCoupledSmoothLaw.ae_fixedPhysical_initial
#print axioms RoughHeston.canonicalPhysical_martingale_of_weak_limit

end RoughHeston
