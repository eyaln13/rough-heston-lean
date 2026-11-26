import FractionalCoupledSmoothApproximations
import SmoothCoupledScaling
import SmoothKernelStochasticCompensator

/-! Exact weighted bracket data on each realized smooth fractional row,
in the form needed for terminal martingale moment estimates. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

open MathFin.ItoIntegralCLM

set_option maxHeartbeats 1000000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {T : ℝ≥0} {α κ σ : ℝ} {n : ℕ} {v : Option ι → ℝ} {β : Option ι → ℝ≥0 → ℝ}

namespace FractionalCoupledSmoothLaw

noncomputable def variance (_ : FractionalCoupledSmoothLaw T α n κ σ v β) (i : Option ι)
    (t : ℝ≥0) (p : CanonicalPath T (FractionalCoupledSmoothState ι n)) : ℝ :=
  fractionalCoupledSmoothPath T α n β t p (i, none)

noncomputable def residual (L : FractionalCoupledSmoothLaw T α n κ σ v β) (i : Option ι)
    (t : ℝ≥0) (p : CanonicalPath T (FractionalCoupledSmoothState ι n)) : ℝ :=
  smoothCoupledMartingale T (fractionalExponentialApproximation α n 0) κ L.ℓ₀ v L.q L.rate β (i, none) t p /
    fractionalExponentialApproximation α n 0

noncomputable def compensator (L : FractionalCoupledSmoothLaw T α n κ σ v β)
    (i j : Option ι) (t : ℝ≥0) (p : CanonicalPath T (FractionalCoupledSmoothState ι n)) : ℝ :=
  ∫ r, physicalCouplingDensity σ i j (fun a => L.variance a r p) ∂timeMeasureHorizon (min t T)

theorem residual_martingale (L : FractionalCoupledSmoothLaw T α n κ σ v β) (i : Option ι) :
    Martingale (L.residual i) (canonicalPathNaturalFiltration T) (L.law : Measure _) :=
  martingale_rescaledSmoothCoupledPhysicalCoordinate (L.martingale (i, none))

theorem compensatedProduct_martingale (L : FractionalCoupledSmoothLaw T α n κ σ v β)
    (hK : fractionalExponentialApproximation α n 0 ≠ 0) (i j : Option ι) :
    Martingale (fun t => L.residual i t * L.residual j t - L.compensator i j t)
      (canonicalPathNaturalFiltration T) (L.law : Measure _) :=
  martingale_rescaledSmoothCoupledPhysicalProduct T _ κ L.ℓ₀ σ hK
    v L.q L.rate β i j (L.compProduct (i, none) (j, none))

theorem compensator_diag (L : FractionalCoupledSmoothLaw T α n κ σ v β) (i : Option ι)
    (t : ℝ≥0) (p : CanonicalPath T (FractionalCoupledSmoothState ι n)) :
    L.compensator i i t p = ∫ r, σ^2 * max (L.variance i r p) 0 ∂timeMeasureHorizon (min t T) := by
  simp only [compensator, physicalCouplingDensity_diagonal]

theorem variance_continuous_time (L : FractionalCoupledSmoothLaw T α n κ σ v β) (i : Option ι)
    {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B)
    (p : CanonicalPath T (FractionalCoupledSmoothState ι n)) :
    Continuous (fun t => L.variance i t p) :=
  (continuous_apply (i, none)).comp (continuous_translatedCanonicalState_time T
    (continuous_smoothCoupledImmigrationPrimitive T _ β hB hβ hβB) p)

theorem residual_continuous_time (L : FractionalCoupledSmoothLaw T α n κ σ v β) (i : Option ι)
    {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B)
    (p : CanonicalPath T (FractionalCoupledSmoothState ι n)) :
    Continuous (fun t => L.residual i t p) :=
  (continuous_smoothCoupledMartingale_time T _ κ L.ℓ₀ v L.q L.rate β hB hβ hβB (i, none) p).div_const _

theorem residual_starts_zero (L : FractionalCoupledSmoothLaw T α n κ σ v β) (i : Option ι)
    {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B) :
    L.residual i 0 =ᵐ[(L.law : Measure _)] 0 := by
  filter_upwards [L.initial] with p hp
  have he := smoothCoupledPath_decomposition T (fractionalExponentialApproximation α n 0)
    κ L.ℓ₀ v L.q L.rate β hB hβ hβB 0 p (i, none)
  change smoothCoupledPath T (fractionalExponentialApproximation α n 0) β 0 p = smoothCoupledInitial v at hp
  rw [hp] at he
  have he' : smoothCoupledMartingale T (fractionalExponentialApproximation α n 0)
      κ L.ℓ₀ v L.q L.rate β (i, none) 0 p = 0 := by
    simpa [timeMeasureHorizon, eq_comm] using he
  simp [residual, he']

theorem compensator_diag_eq_intervalIntegral (L : FractionalCoupledSmoothLaw T α n κ σ v β)
    (i : Option ι) {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B)
    (t : ℝ≥0) (p : CanonicalPath T (FractionalCoupledSmoothState ι n)) :
    L.compensator i i t p =
      ∫ r in (0 : ℝ)..((min t T : ℝ≥0) : ℝ), σ^2 * max (L.variance i r.toNNReal p) 0 := by
  have h : Measurable (fun r => σ^2 * max (L.variance i r p) 0) :=
    (continuous_const.mul ((L.variance_continuous_time i hB hβ hβB p).max continuous_const)).measurable
  rw [L.compensator_diag, integral_timeMeasureHorizon_eq_intervalIntegral h]

theorem compensator_diag_integrable (L : FractionalCoupledSmoothLaw T α n κ σ v β)
    (hK : fractionalExponentialApproximation α n 0 ≠ 0)
    (i : Option ι) {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B)
    (t : ℝ≥0) :
    Integrable (L.compensator i i t) (L.law : Measure _) := by
  let K₀ := fractionalExponentialApproximation α n 0
  let A := smoothCoupledCompensator T K₀ σ β (i, (none : Option (Fin (fractionalApproximationOrder n))))
    (i, none) t
  have hA : Integrable A (L.law : Measure _) :=
    integrable_smoothCoupledCompensator_variance_diagonal T K₀ σ β hB hβ hβB L.supMoment i t
  convert hA.const_mul ((K₀^2)⁻¹) using 1
  funext p
  simp only [A, smoothCoupledCompensator, smoothCoupledCovariance_physical_project, integral_const_mul,
    compensator, variance, fractionalCoupledSmoothPath, K₀]
  field_simp

theorem residual_memLp_two (L : FractionalCoupledSmoothLaw T α n κ σ v β)
    (hK : fractionalExponentialApproximation α n 0 ≠ 0)
    (i : Option ι) {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B)
    (t : ℝ≥0) :
    MemLp (L.residual i t) 2 (L.law : Measure _) := by
  have he := (L.compensatedProduct_martingale hK i i).integrable t
  have ha := L.compensator_diag_integrable hK i hB hβ hβB t
  apply (memLp_two_iff_integrable_sq ((L.residual_martingale i).integrable t).aestronglyMeasurable).2
  have h := he.add ha
  convert h using 1
  funext p
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, sub_add_cancel, Pi.pow_apply, ← pow_two]

theorem exists_smooth_fractional_weighted_row (L : FractionalCoupledSmoothLaw T α n κ σ v β)
    (hK : fractionalExponentialApproximation α n 0 ≠ 0)
    (i : Option ι) {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B)
    {H : ℝ≥0} (hH : H ≤ T) :
    let Ω := CanonicalPath T (FractionalCoupledSmoothState ι n)
    ∃ J A : ℝ≥0 → Ω → ℝ,
      Martingale J (canonicalPathNaturalFiltration T) (L.law : Measure _) ∧
      (∀ t, MemLp (J t) 2 (L.law : Measure _)) ∧
      (∀ᵐ p ∂(L.law : Measure Ω), ContinuousOn (fun t => J t p) (Iic H)) ∧
      (∀ t ≤ H, A t =ᵐ[(L.law : Measure Ω)] fun p =>
        ∫ r in (0 : ℝ)..(t : ℝ), (fractionalExponentialApproximation α n ((H : ℝ)-r))^2 *
          (σ^2 * max (L.variance i r.toNNReal p) 0)) ∧
      Martingale (fun t => J (min t H) * J (min t H) - A t)
        (canonicalPathNaturalFiltration T) (L.law : Measure _) ∧
      J H =ᵐ[(L.law : Measure Ω)] fun p =>
        smoothKernelMartingaleConvolution (fractionalApproximationFinWeight α n)
          (fractionalApproximationFinRate n) (fun r : ℝ => L.residual i r.toNNReal p) H := by
  dsimp only
  let Ω := CanonicalPath T (FractionalCoupledSmoothState ι n)
  let D (r : ℝ) (p : Ω) := σ^2 * max (L.variance i r.toNNReal p) 0
  have hD₀ (r : ℝ) (p : Ω) : 0 ≤ D r p := mul_nonneg (sq_nonneg _) (le_max_right _ _)
  have hD (p : Ω) : Continuous (fun r => D r p) :=
    continuous_const.mul (((L.variance_continuous_time i hB hβ hβB p).comp
      continuous_real_toNNReal).max continuous_const)
  have hAi := L.compensator_diag_integrable hK i hB hβ hβB
  have hmon (s t : ℝ≥0) (hst : s ≤ t) : L.compensator i i s ≤ᵐ[(L.law : Measure _)]
      L.compensator i i t := by
    apply Eventually.of_forall
    intro p
    rw [L.compensator_diag_eq_intervalIntegral i hB hβ hβB,
      L.compensator_diag_eq_intervalIntegral i hB hβ hβB]
    simp_rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg _)]
    exact setIntegral_mono_set ((hD p).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (Eventually.of_forall fun r => hD₀ r p)
      (Ioc_subset_Ioc_right (NNReal.coe_le_coe.mpr (min_le_min_right T hst))).eventuallyLE
  have hC (t : ℝ≥0) (ht : t ≤ H) : L.compensator i i t =ᵐ[(L.law : Measure Ω)]
      fun p => ∫ r in (0 : ℝ)..(t : ℝ), D r p :=
    Eventually.of_forall fun p => by
      rw [L.compensator_diag_eq_intervalIntegral i hB hβ hβB, min_eq_left (ht.trans hH)]
  have hWD (p : Ω) : Continuous (fun r =>
      (smoothExponentialKernel (fractionalApproximationFinWeight α n) (fractionalApproximationFinRate n)
        ((H : ℝ)-(min r.toNNReal H : ℝ≥0)))^2 * D r p) := by
    have hTime : Continuous (fun r : ℝ => (H : ℝ)-(min r.toNNReal H : ℝ≥0)) :=
      continuous_const.sub (NNReal.continuous_coe.comp (continuous_real_toNNReal.min continuous_const))
    exact (((continuous_smoothExponentialKernel (fractionalApproximationFinWeight α n)
      (fractionalApproximationFinRate n)).comp hTime).pow 2).mul (hD p)
  have hDi : Integrable (fun p : Ω => ∫ r in (0 : ℝ)..(H : ℝ), |D r p|) (L.law : Measure _) := by
    refine (hAi H).congr ?_
    filter_upwards [hC H le_rfl] with p hp
    rw [hp]
    apply intervalIntegral.integral_congr
    intro r _
    simp [abs_of_nonneg (hD₀ r p)]
  obtain ⟨J, A, hJ, hJ₂, hJc, hJcomp, hQ, hTerm⟩ := exists_smooth_kernel_weighted_martingale
    (fractionalApproximationFinWeight α n) (fractionalApproximationFinRate n) H
    (L.residual_martingale i) (L.residual_memLp_two hK i hB hβ hβB)
    (L.residual_starts_zero i hB hβ hβB)
    (Eventually.of_forall fun p => L.residual_continuous_time i hB hβ hβB p)
    (L.compensatedProduct_martingale hK i i) hAi hmon hC
    (Eventually.of_forall fun p => (hD p).intervalIntegrable _ _)
    (Eventually.of_forall fun p => (hWD p).intervalIntegrable _ _) hDi
  exact ⟨J, A, hJ, hJ₂, hJc, fun t ht => by
    simpa only [D, smoothExponentialKernel_eq_fractionalExponentialApproximation] using hJcomp t ht,
    hQ, hTerm⟩

end FractionalCoupledSmoothLaw

#print axioms RoughHeston.FractionalCoupledSmoothLaw.exists_smooth_fractional_weighted_row

end RoughHeston
