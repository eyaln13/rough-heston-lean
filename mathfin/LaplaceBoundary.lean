import Verification
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
Measure-theoretic steps of the zero-boundary estimate. The affine
Laplace identities and the bounds on their exponents are the inputs.
-/

open MeasureTheory Filter Set
open scoped MeasureTheory ProbabilityTheory Topology ENNReal NNReal

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

/-- The Laplace weight at integer charge n. -/
noncomputable def laplaceBoundaryWeight (X : Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp (-(n : ℝ) * X ω)

private theorem measurable_laplaceBoundaryWeight {X : Ω → ℝ} (hX : Measurable X) (n : ℕ) :
    Measurable (laplaceBoundaryWeight X n) := (measurable_const.mul hX).exp

private theorem laplaceBoundaryWeight_nonneg (X : Ω → ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ laplaceBoundaryWeight X n ω := Real.exp_nonneg _

private theorem laplaceBoundaryWeight_le_one {X : Ω → ℝ} {ω : Ω} (h₀ : 0 ≤ X ω) (n : ℕ) :
    laplaceBoundaryWeight X n ω ≤ 1 := Real.exp_le_one_iff.2
  (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) h₀)

private theorem laplaceBoundaryWeight_integrable [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) (h₀ : ∀ᵐ ω ∂μ, 0 ≤ X ω) (n : ℕ) :
    Integrable (laplaceBoundaryWeight X n) μ :=
  (integrable_const (1 : ℝ)).mono' (measurable_laplaceBoundaryWeight hX n).aestronglyMeasurable
    (h₀.mono fun ω hω => by
      rw [Real.norm_of_nonneg (laplaceBoundaryWeight_nonneg X n ω)]
      exact laplaceBoundaryWeight_le_one hω n)

/-- Laplace weights select the zero set, also against an integrable
test function. -/
theorem tendsto_laplaceBoundary_weighted_integral {X Y : Ω → ℝ}
    (hX : Measurable X) (h₀ : ∀ᵐ ω ∂μ, 0 ≤ X ω) (hY : Integrable Y μ) :
    Tendsto (fun n : ℕ => ∫ ω, laplaceBoundaryWeight X n ω * Y ω ∂μ) atTop
      (𝓝 (∫ ω in {x | X x = 0}, Y ω ∂μ)) := by
  let A := {x | X x = 0}
  have hA : MeasurableSet A := measurableSet_eq_fun hX measurable_const
  rw [← integral_indicator hA]
  apply tendsto_integral_of_dominated_convergence (fun ω => ‖Y ω‖)
  · intro n
    exact (measurable_laplaceBoundaryWeight hX n).aestronglyMeasurable.mul hY.aestronglyMeasurable
  · exact hY.norm
  · intro n
    filter_upwards [h₀] with ω hω
    rw [norm_mul, Real.norm_of_nonneg (laplaceBoundaryWeight_nonneg X n ω)]
    exact mul_le_of_le_one_left (norm_nonneg _) (laplaceBoundaryWeight_le_one hω n)
  · filter_upwards [h₀] with ω hω₀
    by_cases h : X ω = 0
    · have hω : ω ∈ A := h
      simp only [laplaceBoundaryWeight, h, mul_zero, Real.exp_zero, one_mul, indicator_of_mem hω]
      exact tendsto_const_nhds
    · have hω : ω ∉ A := h
      have hp := lt_of_le_of_ne hω₀ (Ne.symm h)
      have htop : Tendsto (fun n : ℕ => (n : ℝ) * X ω) atTop atTop :=
        (tendsto_mul_const_atTop_of_pos hp).2 tendsto_natCast_atTop_atTop
      have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp htop
      simpa only [laplaceBoundaryWeight, Function.comp_def, neg_mul, zero_mul,
        indicator_of_notMem hω] using he.mul (tendsto_const_nhds (x := Y ω))

/-- The Laplace transform converges to the mass of the zero atom. -/
theorem tendsto_laplaceBoundary_atom [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) (h₀ : ∀ᵐ ω ∂μ, 0 ≤ X ω) :
    Tendsto (fun n : ℕ => ∫ ω, laplaceBoundaryWeight X n ω ∂μ) atTop
      (𝓝 (μ.real {x | X x = 0})) := by
  simpa only [mul_one, setIntegral_const, smul_eq_mul] using
    (tendsto_laplaceBoundary_weighted_integral hX h₀ (integrable_const (1 : ℝ)))

/-- A uniform bound on the exponent of the affine Laplace transform
gives a strictly positive atom at zero. -/
theorem laplaceBoundary_atom_of_affine_bound [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) (h₀ : ∀ᵐ ω ∂μ, 0 ≤ X ω) {D : ℝ} {ψ : ℕ → ℝ}
    (hAffine : ∀ n, (∫ ω, laplaceBoundaryWeight X n ω ∂μ) = Real.exp (-ψ n))
    (hBound : ∀ n, ψ n ≤ D) :
    Real.exp (-D) ≤ μ.real {x | X x = 0} ∧ 0 < μ {x | X x = 0} := by
  have h : Real.exp (-D) ≤ μ.real {x | X x = 0} :=
    ge_of_tendsto (tendsto_laplaceBoundary_atom hX h₀)
      (Eventually.of_forall fun n => by rw [hAffine n]; exact Real.exp_le_exp.2 (neg_le_neg (hBound n)))
  exact ⟨h, (ENNReal.toReal_pos_iff.mp ((Real.exp_pos _).trans_le h)).1⟩

/-- The probability measure conditional on an event of positive mass. -/
noncomputable def boundaryConditionedMeasure (μ : Measure Ω) (A : Set Ω) : Measure Ω :=
  (μ A)⁻¹ • μ.restrict A

theorem boundaryConditionedMeasure_isProbability [IsFiniteMeasure μ] {A : Set Ω}
    (hA : 0 < μ A) : IsProbabilityMeasure (boundaryConditionedMeasure μ A) := by
  constructor
  rw [boundaryConditionedMeasure, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hA.ne' (measure_ne_top μ A)

private theorem boundaryConditionedMeasure_real (A S : Set Ω) :
    (boundaryConditionedMeasure μ A).real S = (μ.restrict A).real S / μ.real A := by
  rw [boundaryConditionedMeasure, measureReal_ennreal_smul_apply,
    ENNReal.toReal_inv, div_eq_mul_inv, mul_comm]
  rfl

/-- Expectations conditional on an event are normalized set integrals. -/
theorem integral_boundaryConditionedMeasure (A : Set Ω) (Y : Ω → ℝ) :
    (∫ ω, Y ω ∂boundaryConditionedMeasure μ A) =
      (∫ ω in A, Y ω ∂μ) / μ.real A := by
  rw [boundaryConditionedMeasure, integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv]
  change (μ.real A)⁻¹ * _ = _
  rw [div_eq_mul_inv, mul_comm]

/-- The normalized Laplace-tilted law. -/
noncomputable def laplaceBoundaryTilt (μ : Measure Ω) (X : Ω → ℝ) (n : ℕ) : Measure Ω :=
  (ENNReal.ofReal (∫ ω, laplaceBoundaryWeight X n ω ∂μ))⁻¹ •
    μ.withDensity (fun ω => (Real.toNNReal (laplaceBoundaryWeight X n ω) : ℝ≥0∞))

/-- Expectation under the normalized Laplace-tilted law. -/
theorem laplaceBoundaryTilt_integral (X Y : Ω → ℝ) (hX : Measurable X) (n : ℕ) :
    (∫ ω, Y ω ∂laplaceBoundaryTilt μ X n) =
      (∫ ω, laplaceBoundaryWeight X n ω * Y ω ∂μ) /
        (∫ ω, laplaceBoundaryWeight X n ω ∂μ) := by
  have hw : Measurable (fun x => Real.toNNReal (laplaceBoundaryWeight X n x)) :=
    continuous_real_toNNReal.measurable.comp (measurable_laplaceBoundaryWeight hX n)
  rw [laplaceBoundaryTilt, integral_smul_measure, integral_withDensity_eq_integral_smul hw,
    smul_eq_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal (integral_nonneg
      (laplaceBoundaryWeight_nonneg X n)), div_eq_mul_inv]
  rw [mul_comm]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  change (Real.toNNReal (laplaceBoundaryWeight X n x) : ℝ) * Y x =
    laplaceBoundaryWeight X n x * Y x
  rw [Real.coe_toNNReal _ (laplaceBoundaryWeight_nonneg X n x)]


/-- Positivity of the zero atom makes each Laplace tilt a probability
measure. -/
theorem laplaceBoundaryTilt_isProbability [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) (h₀ : ∀ᵐ ω ∂μ, 0 ≤ X ω) (hA : 0 < μ {x | X x = 0}) (n : ℕ) :
    IsProbabilityMeasure (laplaceBoundaryTilt μ X n) := by
  let A := {x | X x = 0}
  have hAm : MeasurableSet A := measurableSet_eq_fun hX measurable_const
  have hAr : 0 < μ.real A := ENNReal.toReal_pos_iff.mpr ⟨hA, measure_lt_top μ A⟩
  have hle : μ.real A ≤ ∫ ω, laplaceBoundaryWeight X n ω ∂μ := by
    rw [← integral_indicator_one hAm]
    refine integral_mono ((integrable_const _).indicator hAm)
      (laplaceBoundaryWeight_integrable hX h₀ n) (fun ω => ?_)
    by_cases hω : ω ∈ A
    · have hz : X ω = 0 := hω
      rw [indicator_of_mem hω, laplaceBoundaryWeight, hz, mul_zero, Real.exp_zero, Pi.one_apply]
    · rw [indicator_of_notMem hω]
      exact laplaceBoundaryWeight_nonneg X n ω
  have hp : 0 < ∫ ω, laplaceBoundaryWeight X n ω ∂μ := hAr.trans_le hle
  have hI := laplaceBoundaryTilt_integral (μ := μ) X (fun _ => (1 : ℝ)) hX n
  simp only [integral_const, smul_eq_mul, mul_one, div_self hp.ne'] at hI
  constructor
  have hf : laplaceBoundaryTilt μ X n univ ≠ ∞ := by
    intro h
    rw [Measure.real, h, ENNReal.toReal_top] at hI
    exact zero_ne_one hI
  simpa only [ofReal_measureReal hf, ENNReal.ofReal_one] using congrArg ENNReal.ofReal hI

/-- Tilted expectations converge to conditioning on the zero atom. -/
theorem tendsto_laplaceBoundaryTilt_integral [IsFiniteMeasure μ] {X Y : Ω → ℝ}
    (hX : Measurable X) (h₀ : ∀ᵐ ω ∂μ, 0 ≤ X ω) (hY : Integrable Y μ)
    (hA : 0 < μ {x | X x = 0}) :
    Tendsto (fun n : ℕ => ∫ ω, Y ω ∂laplaceBoundaryTilt μ X n) atTop
      (𝓝 (∫ ω, Y ω ∂boundaryConditionedMeasure μ {x | X x = 0})) := by
  have hpos : 0 < μ.real {x | X x = 0} :=
    ENNReal.toReal_pos_iff.mpr ⟨hA, measure_lt_top _ _⟩
  have h := (tendsto_laplaceBoundary_weighted_integral hX h₀ hY).div
    (tendsto_laplaceBoundary_atom hX h₀) hpos.ne'
  rw [integral_boundaryConditionedMeasure]
  exact h.congr (fun n => (laplaceBoundaryTilt_integral X Y hX n).symm)

/-- Any eventual upper bound for the tilted mean passes to the mean
conditional on zero. -/
theorem boundaryConditionalMean_le_of_laplaceTilt [IsFiniteMeasure μ] {X Y : Ω → ℝ}
    (hX : Measurable X) (h₀ : ∀ᵐ ω ∂μ, 0 ≤ X ω) (hY : Integrable Y μ)
    (hA : 0 < μ {x | X x = 0}) {L : ℝ}
    (hBound : ∀ᶠ n : ℕ in atTop, (∫ ω, Y ω ∂laplaceBoundaryTilt μ X n) ≤ L) :
    (∫ ω, Y ω ∂boundaryConditionedMeasure μ {x | X x = 0}) ≤ L :=
  le_of_tendsto (tendsto_laplaceBoundaryTilt_integral hX h₀ hY hA) hBound

/-- A bound on the integrated conditional affine exponent gives the
same bound on the conditional probability of positive next-time variance.
The event A is measurable at the conditioning time. -/
theorem boundaryConditionalPositive_le_of_affine_bound [IsFiniteMeasure μ]
    {m₀ : MeasurableSpace Ω} (hm : m₀ ≤ m)
    {A : Set Ω} (hA : MeasurableSet[m₀] A) (hApos : 0 < μ A)
    {Y : Ω → ℝ} (hY : Measurable[m] Y) (hY₀ : ∀ᵐ ω ∂μ, 0 ≤ Y ω)
    {Ψ : ℕ → Ω → ℝ} {C : ℝ}
    (hAffine : ∀ n : ℕ, μ[laplaceBoundaryWeight Y n | m₀]
      =ᵐ[μ] fun ω => Real.exp (-Ψ n ω))
    (hΨ : ∀ n, Integrable (Ψ n) (μ.restrict A))
    (hBound : ∀ n, (∫ ω in A, Ψ n ω ∂μ) ≤ C * μ.real A) :
    (boundaryConditionedMeasure μ A).real {x | 0 < Y x} ≤ C := by
  let : MeasurableSpace Ω := m
  have hLap (n : ℕ) : (∫ ω in A, 1 - laplaceBoundaryWeight Y n ω ∂μ) ≤ C * μ.real A := by
    have hi := laplaceBoundaryWeight_integrable (μ := μ) hY hY₀ n
    have ha : μ[laplaceBoundaryWeight Y n | m₀]
        =ᵐ[μ.restrict A] fun ω => Real.exp (-Ψ n ω) :=
      (hAffine n).filter_mono (ae_mono Measure.restrict_le_self)
    have hf : Integrable (fun ω => Real.exp (-Ψ n ω)) (μ.restrict A) :=
      (integrable_condExp.restrict).congr ha
    have hEq : (∫ ω in A, laplaceBoundaryWeight Y n ω ∂μ) =
        ∫ ω in A, Real.exp (-Ψ n ω) ∂μ :=
      (setIntegral_condExp hm hi hA).symm.trans (integral_congr_ae ha)
    rw [integral_sub (integrable_const _) hi.restrict, hEq,
      ← integral_sub (integrable_const _) hf]
    refine (integral_mono ((integrable_const _).sub hf) (hΨ n) (fun ω => ?_)).trans (hBound n)
    change 1 - Real.exp (-Ψ n ω) ≤ Ψ n ω
    linarith [Real.add_one_le_exp (-Ψ n ω)]
  let Yp (ω : Ω) := max (Y ω) 0
  have hYp : Measurable Yp := hY.max measurable_const
  have heq : Yp =ᵐ[μ.restrict A] Y :=
    (hY₀.filter_mono (ae_mono Measure.restrict_le_self)).mono fun ω hω => max_eq_left hω
  have hLap' (n : ℕ) : (∫ ω in A, 1 - Real.exp (-(n : ℝ) * Yp ω) ∂μ) ≤ C * μ.real A := by
    have hc : (fun ω => 1 - Real.exp (-(n : ℝ) * Yp ω))
        =ᵐ[μ.restrict A] fun ω => 1 - laplaceBoundaryWeight Y n ω :=
      heq.mono fun ω hω => by
        change 1 - Real.exp (-(n : ℝ) * Yp ω) = 1 - laplaceBoundaryWeight Y n ω
        rw [hω, laplaceBoundaryWeight]
    exact (integral_congr_ae hc).trans_le (hLap n)
  have he := positive_probability_of_laplace_bounds (μ := μ.restrict A) hYp
    (fun _ => le_max_right _ _) hLap'
  have hset : {x | 0 < Yp x} = {x | 0 < Y x} := by
    ext x
    simp [Yp]
  rw [hset] at he
  rw [boundaryConditionedMeasure_real]
  exact (div_le_iff₀ (ENNReal.toReal_pos_iff.mpr ⟨hApos, measure_lt_top _ _⟩)).2 he

end RoughHeston

#print axioms RoughHeston.tendsto_laplaceBoundary_weighted_integral
#print axioms RoughHeston.laplaceBoundary_atom_of_affine_bound
#print axioms RoughHeston.boundaryConditionedMeasure_isProbability
#print axioms RoughHeston.tendsto_laplaceBoundaryTilt_integral
#print axioms RoughHeston.boundaryConditionalMean_le_of_laplaceTilt
#print axioms RoughHeston.boundaryConditionalPositive_le_of_affine_bound
#print axioms RoughHeston.laplaceBoundaryTilt_isProbability
#print axioms RoughHeston.integral_boundaryConditionedMeasure
