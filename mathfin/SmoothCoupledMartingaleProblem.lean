import SmoothCoupledDiffusionRegularity
import SmoothCoupledDrift
import LinearGrowthEulerExistenceMoment

/-! Canonical martingale-problem existence for the actual finite-exponential
variance/memory system with bounded measurable deterministic immigration. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston

open MathFin.ItoIntegralCLM

set_option maxHeartbeats 800000

section Translation

variable {E : Type*} [NormedAddCommGroup E]

/-- Translate the canonical coordinate by a deterministic function of time. -/
def translatedCanonicalState (T : ℝ≥0) (g : ℝ≥0 → E) (t : ℝ≥0) (p : CanonicalPath T E) : E :=
  canonicalPathEval T t p + g t

theorem continuous_translatedCanonicalState_time (T : ℝ≥0) {g : ℝ≥0 → E}
    (hg : Continuous g) (p : CanonicalPath T E) :
    Continuous (fun t => translatedCanonicalState T g t p) :=
  (p.continuous.comp ((continuous_id.min continuous_const).subtype_mk _)).add hg

theorem continuous_translatedCanonicalState_path (T : ℝ≥0) (g : ℝ≥0 → E) (t : ℝ≥0) :
    Continuous (translatedCanonicalState T g t) :=
  (continuous_canonicalPathEval (E := E) T t).add continuous_const

variable [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

theorem stronglyAdapted_translatedCanonicalState (T : ℝ≥0) (g : ℝ≥0 → E) :
    StronglyAdapted (canonicalPathNaturalFiltration T) (translatedCanonicalState T g) := by
  have h : StronglyAdapted (canonicalPathNaturalFiltration (E := E) T) (canonicalPathEval (E := E) T) :=
    Filtration.stronglyAdapted_natural (fun t =>
      (ContinuousMap.measurable_eval (Y := E) (canonicalEvalTime T t)).stronglyMeasurable)
  intro t
  exact (h t).add stronglyMeasurable_const

end Translation

variable {ι η : Type*} [Fintype ι] [Fintype η] [DecidableEq ι]

local notation "S" => SmoothCoupledState ι η
local notation "J" => Option ι × Option η

noncomputable def smoothCoupledPath (T : ℝ≥0) (K₀ : ℝ) (β : Option ι → ℝ≥0 → ℝ) :
    ℝ≥0 → CanonicalPath T S → S :=
  translatedCanonicalState T (smoothCoupledImmigrationPrimitive T K₀ β)

noncomputable def smoothCoupledShiftedDrift (T : ℝ≥0) (K₀ κ ℓ₀ : ℝ) (v : Option ι → ℝ)
    (q rate : η → ℝ) (β : Option ι → ℝ≥0 → ℝ)
    (t : ℝ≥0) (z : S) : J → ℝ :=
  smoothCoupledDrift K₀ κ ℓ₀ v q rate t (z + smoothCoupledImmigrationPrimitive T K₀ β t)

noncomputable def smoothCoupledShiftedDiffusion (T : ℝ≥0) (K₀ σ : ℝ) (β : Option ι → ℝ≥0 → ℝ)
    (t : ℝ≥0) (z : S) : J → Option ι → ℝ :=
  smoothCoupledDiffusion K₀ σ t (z + smoothCoupledImmigrationPrimitive T K₀ β t)

theorem continuous_smoothCoupledShiftedDrift (T : ℝ≥0) (K₀ κ ℓ₀ : ℝ) (v : Option ι → ℝ)
    (q rate : η → ℝ) (β : Option ι → ℝ≥0 → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B) (k : J) :
    Continuous (fun w : ℝ≥0 × S => smoothCoupledShiftedDrift T K₀ κ ℓ₀ v q rate β w.1 w.2 k) :=
  (continuous_smoothCoupledDrift K₀ κ ℓ₀ v q rate k).comp (continuous_fst.prodMk
    (continuous_snd.add ((continuous_smoothCoupledImmigrationPrimitive T K₀ β hB hβ hβB).comp continuous_fst)))

theorem continuous_smoothCoupledShiftedDiffusion (T : ℝ≥0) (K₀ σ : ℝ)
    (β : Option ι → ℝ≥0 → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B) (k : J) (j : Option ι) :
    Continuous (fun w : ℝ≥0 × S => smoothCoupledShiftedDiffusion T K₀ σ β w.1 w.2 k j) :=
  (continuous_smoothCoupledDiffusion K₀ σ k j).comp (continuous_fst.prodMk
    (continuous_snd.add ((continuous_smoothCoupledImmigrationPrimitive T K₀ β hB hβ hβB).comp continuous_fst)))

theorem smoothCoupledShifted_linear_growth (T : ℝ≥0) (K₀ κ ℓ₀ σ : ℝ) (v : Option ι → ℝ)
    (q rate : η → ℝ) (β : Option ι → ℝ≥0 → ℝ) (hrate : ∀ j, 0 ≤ rate j)
    {B : ℝ} (hB : 0 ≤ B) (hβB : ∀ i t, ‖β i t‖ ≤ B) :
    ∃ L : ℝ, 0 ≤ L ∧
      (∀ t (z : S) k, ‖smoothCoupledShiftedDrift T K₀ κ ℓ₀ v q rate β t z k‖ ≤ L*(1+‖z‖)) ∧
      (∀ t (z : S) k j, ‖smoothCoupledShiftedDiffusion T K₀ σ β t z k j‖ ≤ L*(1+‖z‖)) := by
  obtain ⟨D, hD, hd⟩ := smoothCoupledDrift_linear_growth K₀ κ ℓ₀ v q rate hrate
  let G := max D (2*‖K₀*σ‖)
  let F := ‖K₀‖*B*(T : ℝ)
  have hG : 0 ≤ G := hD.le.trans (le_max_left _ _)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hBound (t : ℝ≥0) (z : S) :
      1 + ‖z + smoothCoupledImmigrationPrimitive T K₀ β t‖ ≤ (1+F)*(1+‖z‖) := by
    have h := (norm_add_le z _).trans (add_le_add_right
      (norm_smoothCoupledImmigrationPrimitive_le (η := η) T K₀ β hB hβB t) ‖z‖)
    nlinarith [mul_nonneg hF (norm_nonneg z)]
  refine ⟨G*(1+F), by positivity, ?_, ?_⟩
  · intro t z k
    refine (hd t _ k).trans ?_
    exact (mul_le_mul (show D ≤ G from le_max_left _ _) (hBound t z)
      (by positivity) hG).trans_eq (mul_assoc _ _ _).symm
  · intro t z k j
    refine (smoothCoupledDiffusion_linear_growth K₀ σ t _ k j).trans ?_
    exact (mul_le_mul (show 2*‖K₀*σ‖ ≤ G from le_max_right _ _) (hBound t z)
      (by positivity) hG).trans_eq (mul_assoc _ _ _).symm

noncomputable def smoothCoupledMartingale (T : ℝ≥0) (K₀ κ ℓ₀ : ℝ) (v : Option ι → ℝ)
    (q rate : η → ℝ) (β : Option ι → ℝ≥0 → ℝ) (k : J) :=
  canonicalEulerMartingaleCoordinate T (smoothCoupledShiftedDrift T K₀ κ ℓ₀ v q rate β)
    (smoothCoupledInitial v) k

noncomputable def smoothCoupledCompensator (T : ℝ≥0) (K₀ σ : ℝ) (β : Option ι → ℝ≥0 → ℝ)
    (k l : J) (t : ℝ≥0) (p : CanonicalPath T S) : ℝ :=
  ∫ r, eulerCovarianceCoefficient (smoothCoupledDiffusion K₀ σ) k l r
    (smoothCoupledPath T K₀ β r p) ∂timeMeasureHorizon (min t T)

theorem smoothCoupledCompensator_eq_canonical (T : ℝ≥0) (K₀ σ : ℝ) (β : Option ι → ℝ≥0 → ℝ)
    (k l : J) (t : ℝ≥0) (p : CanonicalPath T S) :
    smoothCoupledCompensator T K₀ σ β k l t p =
      canonicalCoefficientIntegral T
        (eulerCovarianceCoefficient (smoothCoupledShiftedDiffusion T K₀ σ β) k l) t p := rfl

/-- The deterministic forcing reappears exactly after adding its primitive. -/
theorem smoothCoupledPath_decomposition (T : ℝ≥0) (K₀ κ ℓ₀ : ℝ) (v : Option ι → ℝ)
    (q rate : η → ℝ) (β : Option ι → ℝ≥0 → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B)
    (t : ℝ≥0) (p : CanonicalPath T S) (k : J) :
    smoothCoupledPath T K₀ β t p k = smoothCoupledInitial v k +
      (∫ r, (smoothCoupledDrift K₀ κ ℓ₀ v q rate r (smoothCoupledPath T K₀ β r p) k +
        smoothCoupledImmigration K₀ β r k) ∂timeMeasureHorizon (min t T)) +
      smoothCoupledMartingale T K₀ κ ℓ₀ v q rate β k t p := by
  let ν := timeMeasureHorizon (min t T)
  let d (r : ℝ≥0) := smoothCoupledDrift K₀ κ ℓ₀ v q rate r (smoothCoupledPath T K₀ β r p) k
  let e (r : ℝ≥0) := smoothCoupledImmigration K₀ β r k
  have hX : Continuous (fun r => smoothCoupledPath T K₀ β r p) :=
    continuous_translatedCanonicalState_time T
      (continuous_smoothCoupledImmigrationPrimitive T K₀ β hB hβ hβB) p
  have hc : Continuous (fun w : ℝ≥0 × S => smoothCoupledDrift K₀ κ ℓ₀ v q rate w.1 w.2 k) :=
    continuous_smoothCoupledDrift K₀ κ ℓ₀ v q rate k
  have hPair : Continuous (fun r : ℝ≥0 => (r, smoothCoupledPath T K₀ β r p)) :=
    continuous_id.prodMk hX
  have hcomp := hc.comp hPair
  change Continuous d at hcomp
  have hd : Continuous d := hcomp
  have hdcc : IntegrableOn d (Icc 0 (min t T)) MathFin.ItoIntegralL2.timeMeasure := hd.integrableOn_Icc
  have hdI : Integrable d ν := hdcc.mono_set Ioc_subset_Icc_self
  have heI : Integrable e ν := (integrable_const (‖K₀‖*B)).mono'
    (measurable_smoothCoupledImmigration K₀ β hβ k).stronglyMeasurable.aestronglyMeasurable
    (Eventually.of_forall fun r => norm_smoothCoupledImmigration_le K₀ β hB hβB r k)
  change canonicalPathEval T t p k + (∫ r, e r ∂ν) =
    smoothCoupledInitial v k + (∫ r, d r + e r ∂ν) +
      (canonicalPathEval T t p k - smoothCoupledInitial v k - ∫ r, d r ∂ν)
  rw [integral_add hdI heI]
  ring

/-- Joint existence of the lifted system with its exact model
compensators and an integrable squared path envelope. -/
theorem exists_smoothCoupled_martingale_problem {T : ℝ≥0} (hT : 0 < T)
    (K₀ κ ℓ₀ σ : ℝ) (v : Option ι → ℝ) (q rate : η → ℝ) (β : Option ι → ℝ≥0 → ℝ)
    (hrate : ∀ j, 0 ≤ rate j) {B : ℝ} (hB : 0 ≤ B)
    (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B) :
    ∃ P : ProbabilityMeasure (CanonicalPath T S),
      MemLp (fun p : CanonicalPath T S => ‖p‖) 2 (P : Measure _) ∧
      (∀ᵐ p ∂(P : Measure (CanonicalPath T S)), smoothCoupledPath T K₀ β 0 p = smoothCoupledInitial v) ∧
      (∀ k, Martingale (smoothCoupledMartingale T K₀ κ ℓ₀ v q rate β k)
        (canonicalPathNaturalFiltration T) (P : Measure _)) ∧
      (∀ k l, Martingale (fun t p =>
        smoothCoupledMartingale T K₀ κ ℓ₀ v q rate β k t p *
          smoothCoupledMartingale T K₀ κ ℓ₀ v q rate β l t p -
          smoothCoupledCompensator T K₀ σ β k l t p)
        (canonicalPathNaturalFiltration T) (P : Measure _)) := by
  obtain ⟨L, hL, hd, hs⟩ := smoothCoupledShifted_linear_growth T K₀ κ ℓ₀ σ v q rate β hrate hB hβB
  obtain ⟨P, hP₂, hP₀, hM, hQ⟩ := exists_linearGrowthEuler_martingale_problem_and_sup_moment hT
    (smoothCoupledInitial v)
    (continuous_smoothCoupledShiftedDrift T K₀ κ ℓ₀ v q rate β hB hβ hβB)
    (continuous_smoothCoupledShiftedDiffusion T K₀ σ β hB hβ hβB) hL hd hs
  refine ⟨P, hP₂, ?_, hM, hQ⟩
  let A : Set (CanonicalPath T S) := {p | canonicalPathEval T 0 p = smoothCoupledInitial v}
  have hA : MeasurableSet A := (continuous_canonicalPathEval T 0).measurable (measurableSet_singleton _)
  have hAE : ∀ᵐ p ∂(P : Measure (CanonicalPath T S)), p ∈ A := by
    rw [ae_iff]
    change (P : Measure (CanonicalPath T S)) Aᶜ = 0
    rw [measure_compl hA (measure_ne_top _ _), show (P : Measure (CanonicalPath T S)) A = 1 from hP₀,
      measure_univ, tsub_self]
  filter_upwards [hAE] with p hp
  have he : canonicalPathEval T 0 p = smoothCoupledInitial v := hp
  simp [smoothCoupledPath, translatedCanonicalState, smoothCoupledImmigrationPrimitive_zero, he]

#print axioms RoughHeston.smoothCoupledPath_decomposition
#print axioms RoughHeston.exists_smoothCoupled_martingale_problem

end RoughHeston
