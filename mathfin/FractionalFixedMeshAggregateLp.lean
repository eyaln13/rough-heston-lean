import PathLpContinuityFromFourthMoments
import FractionalFixedMeshBrownian

/-! The actual aggregate and companion variance rows have L² trajectories
on the Brownian extension of the fixed-mesh law. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston

open MathFin.ItoLocalMartingale (nullAugmentation)
set_option maxHeartbeats 1400000

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
  {α κ σ : ℝ} {v : Option ι → ℝ} {β : Option ι → ℝ≥0 → ℝ}
local notation "Ω" => CanonicalPath T (CoupledPhysicalState ι)
local notation "Ω'" => Ω × (ℝ≥0 → ℝ)
local notation "G" => canonicalPathNaturalFiltration (E := CoupledPhysicalState ι) T

noncomputable def aggregateVarianceX (T : ℝ≥0) (t : ℝ≥0)
    (p : CanonicalPath T (CoupledPhysicalState ι)) : ℝ :=
  canonicalFirstVariance (canonicalPathEval T t (canonicalAggregatePair p))

noncomputable def aggregateVarianceY (T : ℝ≥0) (t : ℝ≥0)
    (p : CanonicalPath T (CoupledPhysicalState ι)) : ℝ :=
  canonicalSecondVariance (canonicalPathEval T t (canonicalAggregatePair p))

private theorem eLpNorm_sum_rows_le {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) {f : ι → Ξ → ℝ}
    (I : Finset ι) : eLpNorm (fun ω => ∑ i ∈ I, f i ω) p μ ≤ ∑ i ∈ I, eLpNorm (f i) p μ := by
  induction I using Finset.induction_on with
  | empty => simp [Finset.sum_empty]
  | @insert i I hi ih =>
    simp only [Finset.sum_insert hi]
    exact (eLpNorm_add_le hp).trans (add_le_add_right ih _)

theorem eLpNorm_canonicalPhysicalVariance_uniform_dyadic (L : FractionalFixedMeshLaw T α κ σ v β)
    (j : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ i t,
      eLpNorm (canonicalPhysicalVariance T i t) ((2^j:ℕ):ℝ≥0∞) (L.law : Measure Ω) ≤ C := by
  obtain ⟨D,hD,hL⟩ := L.varianceMoments j
  let p := (2^j:ℕ)
  let C := D^(1/(p:ℝ))
  have hp : 0 < p := by dsimp [p]; positivity
  have hp₀ : (p:ℝ≥0∞) ≠ 0 := by exact_mod_cast hp.ne'
  have hptop : (p:ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top p
  have hCp : C ≠ ⊤ := by
    dsimp [C]
    exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hD
  refine ⟨C,hCp,?_⟩
  intro i t
  let u := min t T
  have he (q : Ω) : canonicalPhysicalVariance T i t q = canonicalPhysicalVariance T i u q := by
    have hE : canonicalEvalTime T t = canonicalEvalTime T u :=
      Subtype.ext (min_eq_left (min_le_right t T)).symm
    simp only [canonicalPhysicalVariance, canonicalPathEval, hE]
  have hV : Continuous (canonicalPhysicalVariance T i u) :=
    ((continuous_apply i).comp continuous_fst).comp (continuous_canonicalPathEval T u)
  rw [show canonicalPhysicalVariance T i t = canonicalPhysicalVariance T i u from funext he]
  change eLpNorm (canonicalPhysicalVariance T i u) (p:ℝ≥0∞) (L.law : Measure Ω) ≤ C
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hptop hV.aestronglyMeasurable,
    ENNReal.toReal_natCast]
  apply ENNReal.rpow_le_rpow _ (by positivity)
  have hh : (∫⁻ q, ‖canonicalPhysicalVariance T i u q‖ₑ^(p:ℝ) ∂(L.law : Measure Ω)) =
      ∫⁻ q, ENNReal.ofReal (max (canonicalPhysicalVariance T i u q) 0)^p ∂(L.law : Measure Ω) := by
    apply lintegral_congr_ae
    filter_upwards [L.nonnegative] with q hq
    have hh₀ : 0 ≤ canonicalPhysicalVariance T i u q := hq i (canonicalEvalTime T u)
    rw [ENNReal.rpow_natCast, ← ofReal_norm, Real.norm_of_nonneg hh₀, max_eq_left hh₀]
  rw [hh]
  exact hL i u (min_le_right _ _)

namespace FractionalFixedMeshLaw

variable (L : FractionalFixedMeshLaw T α κ σ v β)

/-- Fixed-mesh moment bounds for both aggregate coordinates on the same
extended space used to construct their shared Brownian driver. -/
theorem lifted_aggregate_eLpNorm_uniform_dyadic (j : ℕ) :
    let P := (L.law : Measure Ω).prod gaussianLimit
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ t,
      eLpNorm (fun z : Ω' => aggregateVarianceX T t z.1) ((2^j:ℕ):ℝ≥0∞) P ≤ C ∧
      eLpNorm (fun z : Ω' => aggregateVarianceY T t z.1) ((2^j:ℕ):ℝ≥0∞) P ≤ C := by
  intro P
  obtain ⟨D,hD,hL⟩ := eLpNorm_canonicalPhysicalVariance_uniform_dyadic L j
  let p : ℝ≥0∞ := ((2^j:ℕ):ℝ≥0∞)
  let μ := (L.law : Measure Ω)
  let C : ℝ≥0∞ := ((Fintype.card ι:ℕ):ℝ≥0∞)*D+D
  have hp : 1 ≤ p := by
    dsimp [p]
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact one_le_pow₀ (by norm_num)
  have hC : C ≠ ⊤ := by dsimp [C]; finiteness
  refine ⟨C,hC,?_⟩
  intro t
  have hXs : (aggregateVarianceX (ι := ι) T t) =ᵐ[μ]
      fun q => ∑ i : ι, canonicalPhysicalVariance T (some i) t q := by
    filter_upwards [L.nonnegative] with q hq
    change max 0 (∑ i : ι, canonicalPhysicalVariance T (some i) t q) = _
    exact max_eq_right (Finset.sum_nonneg fun i _ => hq (some i) (canonicalEvalTime T t))
  have hYs : (aggregateVarianceY (ι := ι) T t) =ᵐ[μ] canonicalPhysicalVariance T none t := by
    filter_upwards [L.nonnegative] with q hq
    change max 0 (canonicalPhysicalVariance T none t q) = _
    exact max_eq_right (hq none (canonicalEvalTime T t))
  have hXc : Continuous (aggregateVarianceX (ι := ι) T t) :=
    canonicalFirstVariance.continuous.comp ((continuous_canonicalPathEval T t).comp continuous_canonicalAggregatePair)
  have hYc : Continuous (aggregateVarianceY (ι := ι) T t) :=
    canonicalSecondVariance.continuous.comp ((continuous_canonicalPathEval T t).comp continuous_canonicalAggregatePair)
  have hPres : MeasurePreserving (Prod.fst : Ω' → Ω) P μ := measurePreserving_fst
  have hNorm {f : Ω → ℝ} (hf : Continuous f) :
      eLpNorm (fun z : Ω' => f z.1) p P = eLpNorm f p μ :=
    eLpNorm_comp_measurePreserving hf.aestronglyMeasurable hPres
  change eLpNorm (fun z : Ω' => aggregateVarianceX T t z.1) p P ≤ C ∧
    eLpNorm (fun z : Ω' => aggregateVarianceY T t z.1) p P ≤ C
  rw [hNorm hXc, hNorm hYc, eLpNorm_congr_ae hXs, eLpNorm_congr_ae hYs]
  refine ⟨(eLpNorm_sum_rows_le hp Finset.univ).trans ?_, (hL none t).trans le_add_self⟩
  calc
    _ ≤ ∑ _i : ι, D := Finset.sum_le_sum fun i _ => hL (some i) t
    _ = ((Fintype.card ι:ℕ):ℝ≥0∞)*D := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ C := le_self_add

end FractionalFixedMeshLaw

#print axioms RoughHeston.eLpNorm_canonicalPhysicalVariance_uniform_dyadic
#print axioms RoughHeston.FractionalFixedMeshLaw.lifted_aggregate_eLpNorm_uniform_dyadic

end RoughHeston
