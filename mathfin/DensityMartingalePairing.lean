import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Expectation pairings with a density martingale, before its terminal time. -/

open MeasureTheory Filter
open scoped MeasureTheory ENNReal

namespace RoughHeston

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  [Preorder ι] {F : Filtration ι m} {D : ι → Ω → ℝ} {s t : ι}

/-- A past-measurable factor can be pulled out of the conditional
expectation of its product with the terminal martingale value. -/
theorem condExp_martingale_mul_past
    (hD : Martingale D F μ) (hst : s ≤ t) {X : Ω → ℝ}
    (hX : AEStronglyMeasurable[F s] X μ) (hMul : Integrable (D t * X) μ) :
    μ[D t * X | F s] =ᵐ[μ] D s * X :=
  (condExp_mul_of_aestronglyMeasurable_right hX hMul (hD.integrable t)).trans
    ((hD.condExp_ae_eq hst).mul (EventuallyEq.rfl))

/-- A past-measurable integrable payoff has the same expectation when
paired with the terminal density or its current martingale value. -/
theorem integral_martingale_mul_past [IsFiniteMeasure μ]
    (hD : Martingale D F μ) (hst : s ≤ t) {X : Ω → ℝ}
    (hX : AEStronglyMeasurable[F s] X μ) (hMul : Integrable (D t * X) μ) :
    (∫ ω, D t ω * X ω ∂μ) = ∫ ω, D s ω * X ω ∂μ := by
  calc
    _ = ∫ ω, μ[D t * X | F s] ω ∂μ := (integral_condExp (F.le s)).symm
    _ = _ := integral_congr_ae (condExp_martingale_mul_past hD hst hX hMul)

/-- The pairing identity applies in particular to square-integrable
past tests and terminal densities. -/
theorem integral_martingale_mul_past_of_memLp_two [IsFiniteMeasure μ]
    (hD : Martingale D F μ) (hst : s ≤ t) {X : Ω → ℝ}
    (hX : AEStronglyMeasurable[F s] X μ) (hX₂ : MemLp X 2 μ)
    (hDt₂ : MemLp (D t) 2 μ) :
    (∫ ω, D t ω * X ω ∂μ) = ∫ ω, D s ω * X ω ∂μ :=
  integral_martingale_mul_past hD hst hX (hDt₂.integrable_mul hX₂)

/-- A bounded terminal density and an integrable past payoff also
suffice for the pairing identity. -/
theorem integral_martingale_mul_past_of_bounded [IsFiniteMeasure μ]
    (hD : Martingale D F μ) (hst : s ≤ t) {X : Ω → ℝ}
    (hX : AEStronglyMeasurable[F s] X μ) (hXi : Integrable X μ)
    {C : ℝ} (hDt : ∀ᵐ ω ∂μ, ‖D t ω‖ ≤ C) :
    (∫ ω, D t ω * X ω ∂μ) = ∫ ω, D s ω * X ω ∂μ := by
  have hDtTop : MemLp (D t) ⊤ μ := memLp_top_of_bound
    (((hD.stronglyMeasurable t).mono (F.le t)).aestronglyMeasurable) C hDt
  have hProd : MemLp (D t * X) 1 μ := hDtTop.mul (memLp_one_iff_integrable.2 hXi)
  exact integral_martingale_mul_past hD hst hX (memLp_one_iff_integrable.1 hProd)

/-- The same replacement can be made inside an integral in time.
Joint integrability on the time-sample product is the Fubini condition. -/
theorem integral_time_weighted_martingale_pairing [IsFiniteMeasure μ]
    [MeasurableSpace ι] (ν : Measure ι) [SFinite ν]
    (hD : Martingale D F μ) (t : ι) {X : ι → Ω → ℝ} (w : ι → ℝ)
    (hPast : ∀ᵐ s ∂ν, s ≤ t ∧ AEStronglyMeasurable[F s] (X s) μ)
    (hProd : ∀ᵐ s ∂ν, Integrable (D t * X s) μ)
    (hJoint : Integrable (fun z : ι × Ω => D t z.2 * (w z.1 * X z.1 z.2)) (ν.prod μ)) :
    (∫ ω, D t ω * (∫ s, w s * X s ω ∂ν) ∂μ) =
      ∫ s, w s * (∫ ω, D s ω * X s ω ∂μ) ∂ν := by
  let f (s : ι) (ω : Ω) := D t ω * (w s * X s ω)
  have hf : Integrable (Function.uncurry f) (ν.prod μ) := hJoint
  calc
    _ = ∫ ω, ∫ s, f s ω ∂ν ∂μ := by
      apply integral_congr_ae
      filter_upwards with ω
      exact (integral_const_mul (D t ω) (fun s => w s * X s ω)).symm
    _ = ∫ s, ∫ ω, f s ω ∂μ ∂ν := (integral_integral_swap hf).symm
    _ = ∫ s, w s * (∫ ω, D t ω * X s ω ∂μ) ∂ν := by
      apply integral_congr_ae
      filter_upwards with s
      have he (ω : Ω) : f s ω = w s * (D t ω * X s ω) := by
        dsimp only [f]
        ring
      simp only [he, integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hPast, hProd] with s hs hi
      rw [integral_martingale_mul_past hD hs.1 hs.2 hi]

/-- A square-integrable terminal density and square-integrable past
payoffs supply each sectional product integrability condition. -/
theorem integral_time_weighted_martingale_pairing_of_memLp_two [IsFiniteMeasure μ]
    [MeasurableSpace ι] (ν : Measure ι) [SFinite ν]
    (hD : Martingale D F μ) (t : ι) {X : ι → Ω → ℝ} (w : ι → ℝ)
    (hPast : ∀ᵐ s ∂ν, s ≤ t ∧ AEStronglyMeasurable[F s] (X s) μ ∧ MemLp (X s) 2 μ)
    (hDt₂ : MemLp (D t) 2 μ)
    (hJoint : Integrable (fun z : ι × Ω => D t z.2 * (w z.1 * X z.1 z.2)) (ν.prod μ)) :
    (∫ ω, D t ω * (∫ s, w s * X s ω ∂ν) ∂μ) =
      ∫ s, w s * (∫ ω, D s ω * X s ω ∂μ) ∂ν :=
  integral_time_weighted_martingale_pairing ν hD t w
    (hPast.mono fun _ hs => ⟨hs.1, hs.2.1⟩)
    (hPast.mono fun _ hs => hDt₂.integrable_mul hs.2.2) hJoint

/-- Under the terminal density tilt, the expectation of a past test is
its pairing with the current density under the original measure. -/
theorem integral_densityTilt_past [IsFiniteMeasure μ]
    (hD : Martingale D F μ) (hst : s ≤ t)
    (hNonneg : ∀ᵐ ω ∂μ, 0 ≤ D t ω) {X : Ω → ℝ}
    (hX : AEStronglyMeasurable[F s] X μ) (hMul : Integrable (D t * X) μ) :
    (∫ ω, X ω ∂μ.withDensity (fun ω => ENNReal.ofReal (D t ω))) =
      ∫ ω, D s ω * X ω ∂μ := by
  have hd := ((hD.stronglyMeasurable t).mono (F.le t)).measurable.ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hd
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  calc
    _ = ∫ ω, D t ω * X ω ∂μ := by
      apply integral_congr_ae
      filter_upwards [hNonneg] with ω hω
      rw [ENNReal.toReal_ofReal hω, smul_eq_mul]
    _ = _ := integral_martingale_mul_past hD hst hX hMul

/-- A bounded terminal density preserves joint integrability of a
deterministically weighted payoff. -/
theorem integral_time_weighted_martingale_pairing_of_bounded [IsFiniteMeasure μ]
    [MeasurableSpace ι] (ν : Measure ι) [SFinite ν]
    (hD : Martingale D F μ) (t : ι) {X : ι → Ω → ℝ} (w : ι → ℝ)
    (hPast : ∀ᵐ s ∂ν, s ≤ t ∧ AEStronglyMeasurable[F s] (X s) μ ∧ Integrable (X s) μ)
    {C : ℝ} (hBound : ∀ᵐ ω ∂μ, ‖D t ω‖ ≤ C)
    (hJoint : Integrable (fun z : ι × Ω => w z.1 * X z.1 z.2) (ν.prod μ)) :
    (∫ ω, D t ω * (∫ s, w s * X s ω ∂ν) ∂μ) =
      ∫ s, w s * (∫ ω, D s ω * X s ω ∂μ) ∂ν := by
  have hDm : AEStronglyMeasurable (D t) μ := ((hD.stronglyMeasurable t).mono (F.le t)).aestronglyMeasurable
  have hSnd : QuasiMeasurePreserving (Prod.snd : ι × Ω → Ω) (ν.prod μ) μ :=
    Measure.quasiMeasurePreserving_snd
  refine integral_time_weighted_martingale_pairing ν hD t w
    (hPast.mono fun _ hs => ⟨hs.1, hs.2.1⟩) ?_ ?_
  · exact hPast.mono fun _ hs => hs.2.2.bdd_mul hDm hBound
  · exact hJoint.bdd_mul (hDm.comp_quasiMeasurePreserving hSnd) (hSnd.ae hBound)

/-- The expected time integral under the terminal tilt can use the
current density in each time section. -/
theorem integral_densityTilt_time_weighted_martingale_pairing_of_bounded [IsFiniteMeasure μ]
    [MeasurableSpace ι] (ν : Measure ι) [SFinite ν]
    (hD : Martingale D F μ) (t : ι) {X : ι → Ω → ℝ} (w : ι → ℝ)
    (hPast : ∀ᵐ s ∂ν, s ≤ t ∧ AEStronglyMeasurable[F s] (X s) μ ∧ Integrable (X s) μ)
    (hNonneg : ∀ᵐ ω ∂μ, 0 ≤ D t ω)
    {C : ℝ} (hBound : ∀ᵐ ω ∂μ, ‖D t ω‖ ≤ C)
    (hJoint : Integrable (fun z : ι × Ω => w z.1 * X z.1 z.2) (ν.prod μ)) :
    (∫ ω, (∫ s, w s * X s ω ∂ν) ∂μ.withDensity (fun ω => ENNReal.ofReal (D t ω))) =
      ∫ s, w s * (∫ ω, D s ω * X s ω ∂μ) ∂ν := by
  have hd := ((hD.stronglyMeasurable t).mono (F.le t)).measurable.ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hd
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  calc
    _ = ∫ ω, D t ω * (∫ s, w s * X s ω ∂ν) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hNonneg] with ω hω
      rw [ENNReal.toReal_ofReal hω, smul_eq_mul]
    _ = _ := integral_time_weighted_martingale_pairing_of_bounded ν hD t w hPast hBound hJoint

#print axioms condExp_martingale_mul_past
#print axioms integral_martingale_mul_past
#print axioms integral_martingale_mul_past_of_memLp_two
#print axioms integral_martingale_mul_past_of_bounded
#print axioms integral_time_weighted_martingale_pairing
#print axioms integral_time_weighted_martingale_pairing_of_memLp_two
#print axioms integral_densityTilt_past
#print axioms integral_time_weighted_martingale_pairing_of_bounded
#print axioms integral_densityTilt_time_weighted_martingale_pairing_of_bounded

end RoughHeston
