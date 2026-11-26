import FractionalCoupledLimitMomentBounds
import FractionalAggregatePairMartingales

/-! A fixed-mesh fractional law with its samplewise equations and
integrability, on its natural filtration. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

set_option maxHeartbeats 1100000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "Ω[" T "]" => CanonicalPath T (CoupledPhysicalState ι)
local notation "F[" T "]" => canonicalPathNaturalFiltration (E := CoupledPhysicalState ι) T

structure FractionalFixedMeshLaw (T : ℝ≥0) (α κ σ : ℝ) (v : Option ι → ℝ)
    (β : Option ι → ℝ≥0 → ℝ) where
  law : ProbabilityMeasure Ω[T]
  starts : ∀ᵐ p ∂(law : Measure Ω[T]), p ∈ canonicalPhysicalInitialSet T v
  nonnegative : ∀ᵐ p ∂(law : Measure Ω[T]), p ∈ canonicalPhysicalNonnegative (ι := ι) T
  residualMartingale : ∀ i : Option ι, Martingale (canonicalPhysicalResidual T i) F[T] (law : Measure Ω[T])
  productMartingale : ∀ i j : Option ι,
    Martingale (canonicalPhysicalCompensatedProduct T σ i j) F[T] (law : Measure Ω[T])
  inverse : ∀ i, ∀ᵐ p ∂(law : Measure Ω[T]), ∀ t ≤ T,
    volterraConvolution (fractionalL α) (fun s => canonicalPhysicalVariance T i s.toNNReal p-v i) (t:ℝ) =
      canonicalPhysicalResidual T i t p +
        ∫ r in (0:ℝ)..(t:ℝ), (β i r.toNNReal-κ*canonicalPhysicalVariance T i r.toNNReal p)
  varianceMoments : ∀ j : ℕ, ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ i u, u ≤ T →
    (∫⁻ p, ENNReal.ofReal (max (canonicalPhysicalVariance T i u p) 0)^(2^j:ℕ) ∂(law : Measure Ω[T])) ≤ C
  residualFourthMoments : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ i t,
    (∫⁻ p, ‖canonicalPhysicalResidual T i t p‖ₑ^4 ∂(law : Measure Ω[T])) ≤ C

variable {T : ℝ≥0} {α κ σ : ℝ} {v : Option ι → ℝ} {β : Option ι → ℝ≥0 → ℝ}

/-- An actual fractional law exists on each fixed finite mesh. -/
theorem exists_fractionalFixedMeshLaw
    (hT : 0 < T) (hα : 1/2 < α) (hα' : α < 1) (hκ : 0 ≤ κ)
    (hv : ∀ i, 0 ≤ v i) (hβ₀ : ∀ i t, 0 ≤ β i t)
    {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B) :
    Nonempty (FractionalFixedMeshLaw T α κ σ v β) := by
  obtain ⟨P, hi, hn, hM, hQ, hInteg, hvMom, hmMom⟩ :=
    exists_fixed_mesh_fractionalCoupled_limit_with_row_bounds (σ := σ) hT hα hα' hκ hv hβ₀ hB hβ hβB
  have hinv (i : Option ι) := ae_canonicalPhysical_inverse_of_integrated hT (by linarith : 0 < α)
    hα' i (hβ i) (hβB i) P (hInteg i)
  exact ⟨⟨P, hi, hn, hM, hQ, hinv, hvMom, hmMom⟩⟩

namespace FractionalFixedMeshLaw

variable (L : FractionalFixedMeshLaw T α κ σ v β)

noncomputable def pairLaw : ProbabilityMeasure (CanonicalPath T (ℝ × ℝ)) :=
  canonicalAggregatePairLaw L.law

theorem pairLaw_nonnegative :
    ∀ᵐ p ∂(L.pairLaw : Measure (CanonicalPath T (ℝ × ℝ))), ∀ t ≤ T,
      0 ≤ (canonicalPathEval T t p).1 ∧ 0 ≤ (canonicalPathEval T t p).2 :=
  canonicalAggregatePairLaw_nonnegative L.law L.nonnegative

theorem pairLaw_initial {v₀ : ℝ} (hvX : (∑ i : ι, v (some i)) = v₀) (hvY : v none = v₀) :
    ∀ᵐ p ∂(L.pairLaw : Measure (CanonicalPath T (ℝ × ℝ))), canonicalPathEval T 0 p = (v₀,v₀) := by
  have hS := (isClosed_singleton (x := (v₀,v₀))).preimage (continuous_canonicalPathEval T 0)
  let S : Set (CanonicalPath T (ℝ × ℝ)) := {p | canonicalPathEval T 0 p = (v₀,v₀)}
  have hSm : MeasurableSet S := hS.measurableSet
  change ∀ᵐ p ∂Measure.map canonicalAggregatePair (L.law : Measure Ω[T]), p ∈ S
  apply (ae_map_iff continuous_canonicalAggregatePair.measurable.aemeasurable hSm).2
  filter_upwards [L.starts] with p hp
  change canonicalPathEval T 0 p = (v,0) at hp
  change aggregatePairState (canonicalPathEval T 0 p) = (v₀,v₀)
  rw [hp]
  exact Prod.ext hvX hvY

theorem residual_memLp {i : Option ι} (t : ℝ≥0) :
    MemLp (canonicalPhysicalResidual T i t) 2 (L.law : Measure Ω[T]) := by
  obtain ⟨C,hC,hq⟩ := L.residualFourthMoments
  have hm := memLp_and_integral_norm_pow_of_lintegral (p := 4) (by decide)
    (continuous_canonicalPhysicalResidual T i t).measurable (b := C.toReal) ENNReal.toReal_nonneg (by
      simpa only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.ofReal_toReal hC] using hq i t)
  exact hm.1.mono_exponent (by norm_num)

theorem aggregateResidual_memLp (t : ℝ≥0) :
    MemLp (canonicalPhysicalAggregateResidual T t) 2 (L.law : Measure Ω[T]) :=
  memLp_finsetSum Finset.univ (fun i _ => L.residual_memLp (i := some i) t)

theorem variance_uniform_memLp (j : ℕ) :
    ∃ C : ℝ, ∀ i t, t ≤ T →
      MemLp (canonicalPhysicalVariance T i t) ((2^j:ℕ):ℝ≥0∞) (L.law : Measure Ω[T]) ∧
      ∫ p, (canonicalPhysicalVariance T i t p)^(2^j:ℕ) ∂(L.law : Measure Ω[T]) ≤ C := by
  obtain ⟨C,hC,hq⟩ := L.varianceMoments j
  refine ⟨C.toReal,?_⟩
  intro i t ht
  have hc : Continuous (canonicalPhysicalVariance T i t) :=
    ((continuous_apply i).comp continuous_fst).comp (continuous_canonicalPathEval T t)
  have hN : ∀ᵐ p ∂(L.law : Measure Ω[T]), 0 ≤ canonicalPhysicalVariance T i t p :=
    L.nonnegative.mono fun p hp => hp i (canonicalEvalTime T t)
  have he : (fun p => ‖canonicalPhysicalVariance T i t p‖) =ᵐ[(L.law : Measure Ω[T])]
      fun p => canonicalPhysicalVariance T i t p := hN.mono fun p hp => Real.norm_of_nonneg hp
  have hEq : (∫⁻ p, ENNReal.ofReal (‖canonicalPhysicalVariance T i t p‖^(2^j:ℕ)) ∂(L.law : Measure Ω[T])) =
      ∫⁻ p, ENNReal.ofReal (max (canonicalPhysicalVariance T i t p) 0)^(2^j:ℕ) ∂(L.law : Measure Ω[T]) := by
    apply lintegral_congr_ae
    filter_upwards [hN] with p hp
    rw [Real.norm_of_nonneg hp, ENNReal.ofReal_pow hp, max_eq_left hp]
  have hB : (∫⁻ p, ENNReal.ofReal (‖canonicalPhysicalVariance T i t p‖^(2^j:ℕ)) ∂(L.law : Measure Ω[T])) ≤
      ENNReal.ofReal C.toReal := by rw [hEq, ENNReal.ofReal_toReal hC]; exact hq i t ht
  obtain ⟨hm,hb⟩ := memLp_and_integral_norm_pow_of_lintegral (by positivity) hc.measurable ENNReal.toReal_nonneg hB
  exact ⟨hm, (le_of_eq (integral_congr_ae (he.mono fun p hp => congrArg (fun x : ℝ => x^(2^j:ℕ)) hp)).symm).trans hb⟩

end FractionalFixedMeshLaw

#print axioms RoughHeston.exists_fractionalFixedMeshLaw
#print axioms RoughHeston.FractionalFixedMeshLaw.variance_uniform_memLp

end RoughHeston
