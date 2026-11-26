import FractionalAggregatePair
import CanonicalPulseCoordinates
import CanonicalClusterMixed

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Interval

namespace RoughHeston

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
local notation "Ω" => CanonicalPath T (CoupledPhysicalState ι)
local notation "F" => canonicalPathNaturalFiltration (E := CoupledPhysicalState ι) T

/-- Summing the residuals keeps exactly the diagonal cross bracket with
a specified cluster, including when the entire aggregate is zero. -/
theorem canonicalPhysicalAggregate_focal_martingale {P : Measure Ω} (σ : ℝ) (i : ι)
    (hC : ∀ j k : Option ι, Martingale (canonicalPhysicalCompensatedProduct T σ j k) F P) :
    Martingale (fun t p => canonicalPhysicalAggregateResidual T t p*canonicalPhysicalResidual T (some i) t p-
      canonicalPhysicalCompensator T σ (some i) (some i) t p) F P := by
  let J := canonicalPhysicalResidual T (some i)
  let C := canonicalPhysicalCompensator T σ (some i) (some i)
  have h (j : ι) : Martingale (fun t p => canonicalPhysicalResidual T (some j) t p*J t p-
      (if j=i then C t p else 0)) F P := by
    by_cases he : j=i
    · subst j
      convert hC (some i) (some i) using 1
      funext t p
      simp [J,C,canonicalPhysicalCompensatedProduct]
    · simpa [J,he,Pi.mul_def] using canonical_cluster_residual_product_martingale he (hC (some j) (some i))
  have hm := martingale_finset_sum_real Finset.univ (fun j _ => h j)
  convert hm using 1
  funext t p
  simp only [canonicalPhysicalAggregateResidual,Finset.sum_sub_distrib,Finset.sum_mul,
    Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rfl

/-- The companion/focal bracket is obtained on the same full-measure event
as all coordinate nonnegativity assertions. -/
theorem canonicalPhysical_companion_focal_clock (σ : ℝ) (i : ι) {p : Ω}
    (hp : p∈canonicalPhysicalNonnegative T) (t : ℝ≥0) (ht : t≤T) :
    canonicalPhysicalCompensator T σ none (some i) t p =
      ∫ s in (0:ℝ)..(t:ℝ),σ^2*canonicalPhysicalVariance T (some i) s.toNNReal p*
        Real.sqrt (canonicalPhysicalVariance T none s.toNNReal p) /
        Real.sqrt (canonicalPhysicalAggregate T s.toNNReal p) := by
  let q (s : ℝ≥0) := physicalCouplingDensity σ none (some i) (canonicalPathEval T s p).1
  have hq : Continuous q := ((continuous_physicalCouplingDensity σ none (some i)).comp continuous_fst).comp
      (p.continuous.comp ((continuous_id.min continuous_const).subtype_mk _))
  change (∫ s,q s ∂MathFin.ItoIntegralCLM.timeMeasureHorizon (min t T))=_
  rw [min_eq_left ht,← hestonTimeMeasure_eq_horizon,hestonTimeMeasure,
    integral_map continuous_real_toNNReal.measurable.aemeasurable hq.aestronglyMeasurable,
    restrict_Ioo_eq_restrict_Ioc,intervalIntegral.integral_of_le t.coe_nonneg]
  apply integral_congr_ae
  filter_upwards with s
  have hn (j : Option ι) : 0≤(canonicalPathEval T s.toNNReal p).1 j :=
    hp j (canonicalEvalTime T s.toNNReal)
  dsimp only [q]
  rw [physicalCouplingDensity_symm,physicalCouplingDensity_cluster_companion]
  simp_rw [max_eq_left (hn _)]
  simp only [canonicalPhysicalAggregate,canonicalPhysicalVariance]
  ring

#print axioms canonicalPhysicalAggregate_focal_martingale
#print axioms canonicalPhysical_companion_focal_clock

end RoughHeston
