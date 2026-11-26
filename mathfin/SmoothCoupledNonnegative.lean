import SmoothCoupledMemory

/-! Nonnegativity of the actual coupled finite-exponential variances. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston

open MathFin.ItoIntegralCLM

set_option maxHeartbeats 900000

variable {ι η : Type*} [Fintype ι] [Fintype η] [DecidableEq ι]

local notation "S" => SmoothCoupledState ι η
local notation "J" => Option ι × Option η

theorem smoothCoupledCovariance_variance_diagonal (K₀ σ : ℝ) (t : ℝ≥0)
    (z : S) (i : Option ι) :
    eulerCovarianceCoefficient (smoothCoupledDiffusion K₀ σ) (i, none) (i, none) t z =
      (K₀*σ)^2 * smoothVariancePositive z i := by
  cases i with
  | none => exact smoothCoupledCovariance_Y_Y K₀ σ t z
  | some i => simp only [smoothCoupledCovariance_cluster_cluster, ite_true]

private theorem norm_smoothVariancePositive_le (z : S) (i : Option ι) :
    ‖smoothVariancePositive z i‖ ≤ ‖z‖ := by
  rw [Real.norm_of_nonneg (smoothVariancePositive_nonneg z i)]
  exact max_le ((le_abs_self _).trans (norm_le_pi_norm z (i, none))) (norm_nonneg _)

theorem integrable_smoothCoupledCompensator_variance_diagonal (T : ℝ≥0) (K₀ σ : ℝ)
    (β : Option ι → ℝ≥0 → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B)
    {μ : Measure (CanonicalPath T S)} [IsFiniteMeasure μ]
    (hP₂ : MemLp (fun p : CanonicalPath T S => ‖p‖) 2 μ) (i : Option ι) (t : ℝ≥0) :
    Integrable (smoothCoupledCompensator T K₀ σ β (i, none) (i, none) t) μ := by
  let g := smoothCoupledImmigrationPrimitive (η := η) T K₀ β
  let C := (K₀*σ)^2
  let H := ‖K₀‖*B*(T : ℝ)
  let c (r : ℝ≥0) (y : S) := C * smoothVariancePositive (y + g r) i
  have hC : 0 ≤ C := sq_nonneg _
  have hg : Continuous g := continuous_smoothCoupledImmigrationPrimitive T K₀ β hB hβ hβB
  have hgH (r : ℝ≥0) : ‖g r‖ ≤ H := norm_smoothCoupledImmigrationPrimitive_le T K₀ β hB hβB r
  have hc : Continuous (Function.uncurry c) := by
    apply continuous_const.mul
    exact (continuous_smoothVariancePositive i).comp (continuous_snd.add (hg.comp continuous_fst))
  have hcB (r : ℝ≥0) (y : S) : ‖c r y‖ ≤ C*(‖y‖+H) := by
    change ‖C * smoothVariancePositive (y + g r) i‖ ≤ C*(‖y‖+H)
    rw [norm_mul, Real.norm_of_nonneg hC]
    apply mul_le_mul_of_nonneg_left _ hC
    exact (norm_smoothVariancePositive_le _ i).trans
      ((norm_add_le _ _).trans (add_le_add_right (hgH r) ‖y‖))
  have hAc : Continuous (canonicalCoefficientIntegral T c t) :=
    continuous_canonicalCoefficientIntegral_of_bounded_truncations T t hc fun R hR =>
      ⟨C*(R+H), fun r y => (hcB r _).trans
        (mul_le_mul_of_nonneg_left (add_le_add_left (norm_radialTruncation_le_radius hR y) H) hC)⟩
  have hSame : smoothCoupledCompensator T K₀ σ β (i, none) (i, none) t =
      canonicalCoefficientIntegral T c t := by
    funext p
    simp [smoothCoupledCompensator, canonicalCoefficientIntegral, c, g, C,
      smoothCoupledPath, translatedCanonicalState, smoothCoupledCovariance_variance_diagonal]
  rw [hSame]
  have hInt : Integrable (fun p : CanonicalPath T S => C*(‖p‖+H)*(T:ℝ)) μ :=
    (((hP₂.integrable one_le_two).add (integrable_const H)).const_mul C).mul_const (T : ℝ)
  apply hInt.mono' hAc.aestronglyMeasurable
  apply Eventually.of_forall
  intro p
  have h := norm_integral_le_of_norm_le_const
    (μ := timeMeasureHorizon (min t T)) (f := fun r => c r (canonicalPathEval T r p))
    (C := C*(‖p‖+H)) (Eventually.of_forall fun r =>
      (hcB r _).trans (mul_le_mul_of_nonneg_left
        (add_le_add_left (p.norm_coe_le_norm (canonicalEvalTime T r)) H) hC))
  refine h.trans ?_
  rw [euler_timeMeasureHorizon_mass]
  exact mul_le_mul_of_nonneg_left (show ((min t T : ℝ≥0) : ℝ) ≤ T from min_le_right _ _)
    (mul_nonneg hC (add_nonneg (norm_nonneg p)
      (show 0 ≤ H from mul_nonneg (mul_nonneg (norm_nonneg _) hB) T.coe_nonneg)))

/-- The actual finite-exponential martingale problem stays in the
nonnegative variance region. The memory coordinates first identify with
nonnegative deterministic histories, so inward drift is verified directly. -/
theorem ae_smoothCoupled_variances_nonnegative
    (T : ℝ≥0) (K₀ κ ℓ₀ σ : ℝ) (v : Option ι → ℝ) (q rate : η → ℝ)
    (β : Option ι → ℝ≥0 → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B)
    (hK₀ : 0 ≤ K₀) (hℓ₀ : 0 ≤ ℓ₀) (hv : ∀ i, 0 ≤ v i)
    (hq : ∀ j, 0 ≤ q j) (hrate : ∀ j, 0 ≤ rate j) (hβ₀ : ∀ i t, 0 ≤ β i t)
    {μ : Measure (CanonicalPath T S)} [IsFiniteMeasure μ]
    (hP₂ : MemLp (fun p : CanonicalPath T S => ‖p‖) 2 μ)
    (h0 : ∀ᵐ p ∂μ, smoothCoupledPath T K₀ β 0 p = smoothCoupledInitial v)
    (hM : ∀ k : J, Martingale (smoothCoupledMartingale T K₀ κ ℓ₀ v q rate β k)
      (canonicalPathNaturalFiltration T) μ)
    (hQ : ∀ k : J, Martingale (fun t p =>
      smoothCoupledMartingale T K₀ κ ℓ₀ v q rate β k t p *
        smoothCoupledMartingale T K₀ κ ℓ₀ v q rate β k t p -
        smoothCoupledCompensator T K₀ σ β k k t p)
      (canonicalPathNaturalFiltration T) μ) :
    ∀ᵐ p ∂μ, ∀ i : Option ι, ∀ t ∈ Icc 0 T, 0 ≤ smoothCoupledPath T K₀ β t p (i, none) := by
  let Y := smoothCoupledPath (η := η) T K₀ β
  let g := smoothCoupledImmigrationPrimitive (η := η) T K₀ β
  let F := canonicalPathNaturalFiltration (E := S) T
  have hg : Continuous g := continuous_smoothCoupledImmigrationPrimitive T K₀ β hB hβ hβB
  have hYc (p : CanonicalPath T S) : Continuous (fun t => Y t p) :=
    continuous_translatedCanonicalState_time T hg p
  have hYa : StronglyAdapted F Y := stronglyAdapted_translatedCanonicalState T g
  have hmemory := ae_smoothCoupled_memory_eq_exponential T K₀ κ ℓ₀ σ v q rate β hB hβ hβB h0 hQ
  apply ae_all_iff.2
  intro i
  let k : J := (i, none)
  let X (t : ℝ≥0) (p : CanonicalPath T S) := Y t p k
  let M := smoothCoupledMartingale T K₀ κ ℓ₀ v q rate β k
  let A := smoothCoupledCompensator T K₀ σ β k k
  let b (t : ℝ≥0) (p : CanonicalPath T S) :=
    smoothCoupledDrift K₀ κ ℓ₀ v q rate t (Y t p) k + smoothCoupledImmigration K₀ β t k
  let Q (t : ℝ≥0) (p : CanonicalPath T S) := (K₀*σ)^2 * smoothVariancePositive (Y t p) i
  have hXc (p : CanonicalPath T S) : Continuous (fun t => X t p) :=
    (continuous_apply k).comp (hYc p)
  have hXa : Adapted F X :=
    fun t => (((continuous_apply k).comp_stronglyMeasurable (hYa t))).measurable
  have hQc (p : CanonicalPath T S) : Continuous (fun t => Q t p) :=
    continuous_const.mul ((continuous_smoothVariancePositive i).comp (hYc p))
  have hAeq (t : ℝ≥0) (p : CanonicalPath T S) :
      A t p = ∫ r, Q r p ∂timeMeasureHorizon (min t T) := by
    simp only [A, smoothCoupledCompensator, smoothCoupledCovariance_variance_diagonal, Q, Y, k]
  have hAc (p : CanonicalPath T S) : Continuous (fun t => A t p) := by
    simp_rw [hAeq]
    exact continuous_frozen_timeMeasureHorizon_integral T (hQc p)
  letI : NullSingletonClass MathFin.ItoIntegralL2.timeMeasure :=
    ⟨MathFin.ItoIntegralL2.timeMeasure_singleton⟩
  apply ae_nonnegative_of_inward_drift_and_compensated_square (𝒢 := F) (ν := MathFin.ItoIntegralL2.timeMeasure)
    (T := T) (X := X) (M := M) (A := A) (b := b) (q := Q) (x₀ := v i)
  · exact Eventually.of_forall fun p => (hXc p).continuousOn
  · exact continuous_smoothCoupledMartingale_time T K₀ κ ℓ₀ v q rate β hB hβ hβB k
  · exact hAc
  · exact hM k
  · simpa only [pow_two, M, A] using hQ k
  · exact isStoppingTime_hittingAfter_nonnegative_of_continuous hXa hXc
  · exact integrable_smoothCoupledCompensator_variance_diagonal T K₀ σ β hB hβ hβB hP₂ i
  · filter_upwards [h0] with p hp
    change 0 ≤ smoothCoupledPath T K₀ β 0 p (i, none)
    rw [hp]
    exact hv i
  · exact Eventually.of_forall fun p t ht => by
      simpa only [X, Y, M, k, b, smoothCoupledInitial, min_eq_left ht.2, timeMeasureHorizon] using
        smoothCoupledPath_decomposition T K₀ κ ℓ₀ v q rate β hB hβ hβB t p k
  · exact Eventually.of_forall fun p t ht => by
      simpa only [min_eq_left ht.2, timeMeasureHorizon] using hAeq t p
  · apply Eventually.of_forall
    intro p
    let d (r : ℝ≥0) := smoothCoupledDrift K₀ κ ℓ₀ v q rate r (Y r p) k
    let e (r : ℝ≥0) := smoothCoupledImmigration K₀ β r k
    have hc : Continuous (fun w : ℝ≥0 × S => smoothCoupledDrift K₀ κ ℓ₀ v q rate w.1 w.2 k) :=
      continuous_smoothCoupledDrift K₀ κ ℓ₀ v q rate k
    have hPair : Continuous (fun r : ℝ≥0 => (r, Y r p)) := continuous_id.prodMk (hYc p)
    have hd := hc.comp hPair
    change Continuous d at hd
    have hdcc : IntegrableOn d (Icc 0 T) MathFin.ItoIntegralL2.timeMeasure := hd.integrableOn_Icc
    have hdI : Integrable d (timeMeasureHorizon T) := hdcc.mono_set Ioc_subset_Icc_self
    have heI : Integrable e (timeMeasureHorizon T) := (integrable_const (‖K₀‖*B)).mono'
      (measurable_smoothCoupledImmigration K₀ β hβ k).stronglyMeasurable.aestronglyMeasurable
      (Eventually.of_forall fun r => norm_smoothCoupledImmigration_le K₀ β hB hβB r k)
    exact hdI.add heI
  · filter_upwards [hmemory] with p hp t ht hx
    have hclip : smoothVariancePositive (Y t p) i = 0 := max_eq_right hx.le
    have hm (j : η) : 0 ≤ Y t p (i, some j) :=
      (exponentialVarianceMemory_nonneg (rate j) _ t.coe_nonneg).trans_eq (hp i j t ht).symm
    constructor
    · simp only [b, k, smoothCoupledDrift_variance, hclip, mul_zero, sub_zero, smoothCoupledImmigration]
      exact add_nonneg (mul_nonneg hK₀
        (add_nonneg (mul_nonneg (hv i) (smoothExponentialResolvent_nonneg hℓ₀ hq t))
          (Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (hq j) (hrate j)) (hm j))))
        (mul_nonneg hK₀ (hβ₀ i t))
    · simp [Q, hclip]

#print axioms RoughHeston.integrable_smoothCoupledCompensator_variance_diagonal
#print axioms RoughHeston.ae_smoothCoupled_variances_nonnegative

end RoughHeston
