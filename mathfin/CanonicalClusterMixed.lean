import CanonicalPulseCoordinates
import CanonicalPhysicalFiniteSums
import FixedMeshClusterCount

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators

namespace RoughHeston

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
local notation "Ω" => CanonicalPath T (CoupledPhysicalState ι)
local notation "𝒢" => canonicalPathNaturalFiltration (E := CoupledPhysicalState ι) T

/-- Different clusters have zero mutual covariance density in the physical
fixed-mesh law, even though both can have nonzero covariance with the companion. -/
theorem canonical_cluster_residual_product_martingale {μ : Measure Ω}
    {σ : ℝ} {i j : ι} (hij : i ≠ j)
    (hC : Martingale (canonicalPhysicalCompensatedProduct T σ (some i) (some j)) 𝒢 μ) :
    Martingale (fun t => canonicalPhysicalResidual T (some i) t *
      canonicalPhysicalResidual T (some j) t) 𝒢 μ := by
  have hz (v : Option ι→ℝ) : physicalCouplingDensity σ (some i) (some j) v = 0 := by
    rw [physicalCouplingDensity,smoothCoupledCovariance_cluster_cluster,ite_eq_right hij]
  convert hC using 1
  funext t p
  change _ = canonicalPhysicalResidual T (some i) t p * canonicalPhysicalResidual T (some j) t p -
    canonicalPhysicalCompensator T σ (some i) (some j) t p
  rw [canonicalPhysicalCompensator,canonicalCoefficientIntegral]
  simp only [hz,integral_zero,sub_zero,Pi.mul_apply]

/-- Projection from the physical mesh law to the aggregate and companion
variance paths. -/
def canonicalFixedMeshPairPath (T : ℝ≥0)
    (p : CanonicalPath T (CoupledPhysicalState ι)) : CanonicalPath T (ℝ×ℝ) :=
  (⟨fun z : CoupledPhysicalState ι => (∑ i : ι,z.1 (some i),z.1 none),
    (continuous_finsetSum _ fun i _ => (continuous_apply (some i)).comp continuous_fst).prodMk
      ((continuous_apply none).comp continuous_fst)⟩ : C(CoupledPhysicalState ι,ℝ×ℝ)).comp p

omit [DecidableEq ι] in
theorem continuous_canonicalFixedMeshPairPath :
    Continuous (canonicalFixedMeshPairPath (ι := ι) T) :=
  ContinuousMap.continuous_postcomp _

theorem canonicalCluster_le_aggregate {μ : Measure Ω} {v : Option ι→ℝ}
    (hI : ∀ᵐ p ∂μ,p∈canonicalPhysicalInitialSet T v)
    (hN : ∀ᵐ p ∂μ,p∈canonicalPhysicalNonnegative (ι := ι) T) (i : ι) :
    ∀ᵐ p ∂μ,∀ t,canonicalRegularVariance T (some i) (v (some i)) t p ≤
      (canonicalPathEval T t (canonicalFixedMeshPairPath T p)).1 := by
  filter_upwards [canonicalRegularVariance_ae_paths hI hN (some i),hN] with p hV hpn t
  rw [hV]
  change canonicalPhysicalVariance T (some i) t p ≤ ∑ j : ι,canonicalPhysicalVariance T (some j) t p
  exact Finset.single_le_sum (f := fun j => canonicalPhysicalVariance T (some j) t p)
    (fun j _ => hpn (some j) (canonicalEvalTime T t)) (Finset.mem_univ i)

omit [DecidableEq ι] in
theorem canonicalFixedMeshPairPath_companion (p : Ω) (t : ℝ≥0) :
    (canonicalPathEval T t (canonicalFixedMeshPairPath T p)).2 =
      canonicalPhysicalVariance T none t p := rfl

#print axioms canonical_cluster_residual_product_martingale
#print axioms canonicalCluster_le_aggregate
#print axioms canonicalFixedMeshPairPath_companion

end RoughHeston
