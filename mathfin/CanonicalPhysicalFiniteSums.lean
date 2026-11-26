import FractionalCoupledFixedMeshLimit

/-! Summing the observable residual martingales on the full cluster path space. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace RoughHeston

open MathFin.ItoIntegralCLM

set_option maxHeartbeats 1100000

theorem martingale_finset_sum_real {ι S Ω : Type*} [Preorder S] [mΩ : MeasurableSpace Ω]
    {F : Filtration S mΩ} {μ : Measure Ω} {M : ι → S → Ω → ℝ} (I : Finset ι)
    (hM : ∀ i ∈ I, Martingale (M i) F μ) :
    Martingale (fun t p => ∑ i ∈ I, M i t p) F μ := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact martingale_zero ℝ F μ
  | @insert a I ha hI =>
    have h := (hM a (Finset.mem_insert_self a I)).add (hI fun i hi => hM i (Finset.mem_insert_of_mem hi))
    change Martingale (fun t p => M a t p + ∑ i ∈ I, M i t p) F μ at h
    simpa only [Finset.sum_insert ha] using h

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
local notation "S" => CoupledPhysicalState ι
local notation "Ω" => CanonicalPath T S
local notation "F" => canonicalPathNaturalFiltration (E := S) T

def canonicalPhysicalAggregate (T : ℝ≥0) (t : ℝ≥0) (p : CanonicalPath T S) : ℝ :=
  ∑ i : ι, canonicalPhysicalVariance T (some i) t p

def canonicalPhysicalAggregateResidual (T : ℝ≥0) (t : ℝ≥0) (p : CanonicalPath T S) : ℝ :=
  ∑ i : ι, canonicalPhysicalResidual T (some i) t p

theorem integrable_canonicalPhysicalCovariance_density (σ : ℝ) (i j : Option ι) (t : ℝ≥0) (p : Ω) :
    Integrable (fun r => physicalCouplingDensity σ i j (canonicalPathEval T r p).1)
      (timeMeasureHorizon (min t T)) := by
  have h : Continuous (fun r => physicalCouplingDensity σ i j (canonicalPathEval T r p).1) :=
    ((continuous_physicalCouplingDensity σ i j).comp continuous_fst).comp
      (p.continuous.comp ((continuous_id.min continuous_const).subtype_mk _))
  exact (h.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self

theorem canonicalPhysicalAggregateResidual_martingale {μ : Measure Ω}
    (hM : ∀ i : Option ι, Martingale (canonicalPhysicalResidual T i) F μ) :
    Martingale (canonicalPhysicalAggregateResidual (ι := ι) T) F μ :=
  martingale_finset_sum_real Finset.univ (fun i _ => hM (some i))

theorem canonicalPhysicalAggregate_square_martingale {μ : Measure Ω} (σ : ℝ)
    (hQ : ∀ i j : Option ι, Martingale (canonicalPhysicalCompensatedProduct T σ i j) F μ) :
    Martingale (fun t p => canonicalPhysicalAggregateResidual T t p * canonicalPhysicalAggregateResidual T t p -
      ∫ r, (∑ i : ι, ∑ j : ι, physicalCouplingDensity σ (some i) (some j) (canonicalPathEval T r p).1)
          ∂timeMeasureHorizon (min t T)) F μ := by
  have hm : Martingale (fun t p => ∑ i : ι, ∑ j : ι,
      canonicalPhysicalCompensatedProduct T σ (some i) (some j) t p) F μ :=
    martingale_finset_sum_real Finset.univ fun i _ =>
      martingale_finset_sum_real Finset.univ (fun j _ => hQ (some i) (some j))
  convert hm using 1
  funext t p
  let ν := timeMeasureHorizon (min t T)
  let q (i j : ι) (r : ℝ≥0) := physicalCouplingDensity σ (some i) (some j) (canonicalPathEval T r p).1
  have hq (i j : ι) : Integrable (q i j) ν := integrable_canonicalPhysicalCovariance_density σ _ _ t p
  have hSum : (∫ r, (∑ i : ι, ∑ j : ι, q i j r) ∂ν) = ∑ i : ι, ∑ j : ι, ∫ r, q i j r ∂ν := by
    rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum _ fun j _ => hq i j)]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum Finset.univ (fun j _ => hq i j)
  change _-(∫ r, (∑ i : ι, ∑ j : ι, q i j r) ∂ν) = _
  rw [hSum]
  have hr : canonicalPhysicalAggregateResidual T t p * canonicalPhysicalAggregateResidual T t p =
      ∑ i : ι, ∑ j : ι, canonicalPhysicalResidual T (some i) t p * canonicalPhysicalResidual T (some j) t p := by
    unfold canonicalPhysicalAggregateResidual
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => Finset.mul_sum _ _ _)
  simp only [hr, canonicalPhysicalCompensatedProduct, canonicalPhysicalCompensator, canonicalCoefficientIntegral,
    Finset.sum_sub_distrib, q, ν]

theorem canonicalPhysicalAggregate_companion_martingale {μ : Measure Ω} (σ : ℝ)
    (hQ : ∀ i j : Option ι, Martingale (canonicalPhysicalCompensatedProduct T σ i j) F μ) :
    Martingale (fun t p => canonicalPhysicalAggregateResidual T t p * canonicalPhysicalResidual T none t p -
      ∫ r, (∑ i : ι, physicalCouplingDensity σ (some i) none (canonicalPathEval T r p).1)
          ∂timeMeasureHorizon (min t T)) F μ := by
  have hm : Martingale (fun t p => ∑ i : ι, canonicalPhysicalCompensatedProduct T σ (some i) none t p) F μ :=
    martingale_finset_sum_real Finset.univ fun i _ => hQ (some i) none
  convert hm using 1
  funext t p
  simp only [canonicalPhysicalAggregateResidual, canonicalPhysicalCompensatedProduct,
    canonicalPhysicalCompensator, canonicalCoefficientIntegral, Finset.sum_sub_distrib, Finset.sum_mul,
    integral_finsetSum Finset.univ (fun i _ => integrable_canonicalPhysicalCovariance_density σ (some i) none t p)]

#print axioms RoughHeston.canonicalPhysicalAggregateResidual_martingale
#print axioms RoughHeston.canonicalPhysicalAggregate_square_martingale
#print axioms RoughHeston.canonicalPhysicalAggregate_companion_martingale

end RoughHeston
