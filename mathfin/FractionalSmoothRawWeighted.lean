import FractionalSmoothRowMomentData
import RawDeterministicWeightedMartingale
import ContinuousRawBDG

/-! Raw-filtration weighted martingales for actual smooth fractional
rows, ready for even-power bounds. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

set_option maxHeartbeats 900000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {T : ℝ≥0} {α κ σ : ℝ} {n : ℕ} {v : Option ι → ℝ} {β : Option ι → ℝ≥0 → ℝ}

namespace FractionalCoupledSmoothLaw

theorem variance_stronglyAdapted (L : FractionalCoupledSmoothLaw T α n κ σ v β) (i : Option ι) :
    StronglyAdapted (canonicalPathNaturalFiltration T) (L.variance i) := by
  have h := stronglyAdapted_translatedCanonicalState T
    (smoothCoupledImmigrationPrimitive (η := Fin (fractionalApproximationOrder n)) T
      (fractionalExponentialApproximation α n 0) β)
  exact fun t => (continuous_apply (i, none)).comp_stronglyMeasurable (h t)

theorem variance_memLp_two (L : FractionalCoupledSmoothLaw T α n κ σ v β) (i : Option ι)
    {B : ℝ} (hB : 0 ≤ B) (hβB : ∀ i t, ‖β i t‖ ≤ B) (t : ℝ≥0) :
    MemLp (L.variance i t) 2 (L.law : Measure _) := by
  let g := smoothCoupledImmigrationPrimitive (η := Fin (fractionalApproximationOrder n)) T
    (fractionalExponentialApproximation α n 0) β
  let C := ‖fractionalExponentialApproximation α n 0‖*B*(T:ℝ)
  have hLp : MemLp (fun p : CanonicalPath T (FractionalCoupledSmoothState ι n) => ‖p‖+C) 2
      (L.law : Measure _) := L.supMoment.add (memLp_const C)
  have hm : StronglyMeasurable[canonicalPathNaturalFiltration T t] (L.variance i t) :=
    L.variance_stronglyAdapted i t
  have hm' := hm.mono ((canonicalPathNaturalFiltration (E := FractionalCoupledSmoothState ι n) T).le t)
  apply hLp.mono hm'.aestronglyMeasurable
  apply Eventually.of_forall
  intro p
  have h : ‖g t‖ ≤ C := norm_smoothCoupledImmigrationPrimitive_le T
    (fractionalExponentialApproximation α n 0) β hB hβB t
  have hC : 0 ≤ C := by dsimp [C]; positivity
  rw [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) hC)]
  exact (norm_le_pi_norm (canonicalPathEval T t p + g t) (i, none)).trans
    ((norm_add_le _ _).trans (add_le_add (p.norm_coe_le_norm (canonicalEvalTime T t)) h))

/-- A smooth deterministic weight produces an actual, continuous
stochastic integral against any physical residual in the coupled law. -/
theorem rawDeterministicWeightedRow (L : FractionalCoupledSmoothLaw T α n κ σ v β)
    (hK : fractionalExponentialApproximation α n 0 ≠ 0)
    (i : Option ι) {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B)
    {H : ℝ≥0} (hH : H ≤ T) {g d : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g) (hd : Continuous d) (hgd : ∀ s, HasDerivAt g (d s) s) :
    let M := L.residual i
    let Y (t : ℝ≥0) (p : CanonicalPath T (FractionalCoupledSmoothState ι n)) :=
      g (min t H : ℝ≥0) * M (min t H) p - g 0 * M 0 p -
        ∫ r in (0 : ℝ)..((min t H : ℝ≥0):ℝ), d r * M r.toNNReal p
    let A (t : ℝ≥0) (p : CanonicalPath T (FractionalCoupledSmoothState ι n)) :=
      ∫ r in (0 : ℝ)..((min t H : ℝ≥0):ℝ), (g r)^2 * (σ^2 * max (L.variance i r.toNNReal p) 0)
    Martingale Y (canonicalPathNaturalFiltration T) (L.law : Measure _) ∧
      (∀ t, MemLp (Y t) 2 (L.law : Measure _)) ∧
      (∀ p, Continuous (fun t => Y t p)) ∧ (∀ p, Continuous (fun t => A t p)) ∧
      (∀ p, Monotone (fun t => A t p)) ∧ (∀ p, Y 0 p = 0) ∧ (∀ p, A 0 p = 0) ∧
      Martingale (fun t => Y t * Y t - A t) (canonicalPathNaturalFiltration T) (L.law : Measure _) := by
  dsimp only
  let Ω := CanonicalPath T (FractionalCoupledSmoothState ι n)
  let D (s : ℝ≥0) (p : Ω) := σ^2 * max (L.variance i s p) 0
  have hd₀ (s : ℝ≥0) (p : Ω) : 0 ≤ D s p := mul_nonneg (sq_nonneg _) (le_max_right _ _)
  have hDa : StronglyAdapted (canonicalPathNaturalFiltration T) D := by
    intro s
    have hc : Continuous (fun z : ℝ => σ^2*max z 0) :=
      continuous_const.mul (continuous_id.max continuous_const)
    exact hc.comp_stronglyMeasurable (L.variance_stronglyAdapted i s)
  have hDc (p : Ω) : Continuous (fun s => D s p) :=
    continuous_const.mul ((L.variance_continuous_time i hB hβ hβB p).max continuous_const)
  have hC (t : ℝ≥0) (ht : t ≤ H) : L.compensator i i t =ᵐ[(L.law : Measure Ω)]
      fun p => ∫ r in (0 : ℝ)..(t : ℝ), D r.toNNReal p :=
    Eventually.of_forall fun p => by
      rw [L.compensator_diag_eq_intervalIntegral i hB hβ hβB, min_eq_left (ht.trans hH)]
  have hCmon (s t : ℝ≥0) (hst : s ≤ t) :
      L.compensator i i s ≤ᵐ[(L.law : Measure Ω)] L.compensator i i t := by
    apply Eventually.of_forall
    intro p
    rw [L.compensator_diag_eq_intervalIntegral i hB hβ hβB,
      L.compensator_diag_eq_intervalIntegral i hB hβ hβB]
    simp_rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg _)]
    exact setIntegral_mono_set (((hDc p).comp continuous_real_toNNReal).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self) (Eventually.of_forall fun r => hd₀ r.toNNReal p)
      (Ioc_subset_Ioc_right (NNReal.coe_le_coe.mpr (min_le_min_right T hst))).eventuallyLE
  exact exists_raw_deterministic_weighted_martingale H hg hd hgd (L.residual_martingale i)
    (L.residual_memLp_two hK i hB hβ hβB) (L.residual_continuous_time i hB hβ hβB)
    (L.compensatedProduct_martingale hK i i) (L.compensator_diag_integrable hK i hB hβ hβB)
    hCmon hC hDa hDc hd₀

end FractionalCoupledSmoothLaw

#print axioms RoughHeston.FractionalCoupledSmoothLaw.variance_memLp_two
#print axioms RoughHeston.FractionalCoupledSmoothLaw.rawDeterministicWeightedRow

end RoughHeston
