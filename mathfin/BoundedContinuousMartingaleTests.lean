import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory Filter Set
open scoped MeasureTheory ENNReal BoundedContinuousFunction

namespace RoughHeston

variable {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E] [MeasurableSpace E]
  [BorelSpace E] {μ : Measure Ω}

private theorem integral_withDensity_nonneg_mul {d : Ω → ℝ}
    (hd : Integrable d μ) (hdn : ∀ ω, 0 ≤ d ω) (f : Ω → ℝ) :
    (∫ ω, f ω ∂μ.withDensity (fun ω => ENNReal.ofReal (d ω))) =
      ∫ ω, d ω * f ω ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul₀ hd.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (hdn _), smul_eq_mul]

private theorem max_zero_sub_max_neg_zero (r : ℝ) :
    max r 0 - max (-r) 0 = r := by
  by_cases hr : 0 ≤ r
  · rw [max_eq_left hr, max_eq_right (neg_nonpos.mpr hr), sub_zero]
  · have h := le_of_not_ge hr
    rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), zero_sub, neg_neg]

/-- Bounded continuous tests of a measurable statistic determine the
real signed set integrals of an integrable increment on its past events. -/
theorem setIntegral_preimage_eq_of_boundedContinuous_tests
    {P : Ω → E} (hP : Measurable P) {X Y : Ω → ℝ}
    (hX : Integrable X μ) (hY : Integrable Y μ)
    (htest : ∀ f : E →ᵇ ℝ, (∫ ω, (Y ω - X ω) * f (P ω) ∂μ) = 0)
    {A : Set E} (hA : MeasurableSet A) :
    (∫ ω in P ⁻¹' A, X ω ∂μ) = ∫ ω in P ⁻¹' A, Y ω ∂μ := by
  let d := Y - X
  let dp (ω : Ω) := max (d ω) 0
  let dn (ω : Ω) := max (-d ω) 0
  have hd : Integrable d μ := hY.sub hX
  have hp : Integrable dp μ := hd.pos_part
  have hn : Integrable dn μ := hd.neg_part
  have hdp (ω : Ω) : 0 ≤ dp ω := le_max_right _ _
  have hdn (ω : Ω) : 0 ≤ dn ω := le_max_right _ _
  have he (ω : Ω) : dp ω - dn ω = d ω := max_zero_sub_max_neg_zero (d ω)
  let ρp := μ.withDensity fun ω => ENNReal.ofReal (dp ω)
  let ρn := μ.withDensity fun ω => ENNReal.ofReal (dn ω)
  let : IsFiniteMeasure ρp := isFiniteMeasure_withDensity_ofReal hp.hasFiniteIntegral
  let : IsFiniteMeasure ρn := isFiniteMeasure_withDensity_ofReal hn.hasFiniteIntegral
  have hmap : ρp.map P = ρn.map P := by
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    have hfm : AEStronglyMeasurable (fun ω => f (P ω)) μ :=
      (f.continuous.measurable.comp hP).aestronglyMeasurable
    have hfb : ∀ᵐ ω ∂μ, ‖f (P ω)‖ ≤ ‖f‖ :=
      Eventually.of_forall fun ω => f.norm_coe_le_norm (P ω)
    have hip : Integrable (fun ω => dp ω * f (P ω)) μ := hp.mul_bdd hfm hfb
    have hin : Integrable (fun ω => dn ω * f (P ω)) μ := hn.mul_bdd hfm hfb
    rw [integral_map_of_stronglyMeasurable hP f.continuous.measurable.stronglyMeasurable,
      integral_map_of_stronglyMeasurable hP f.continuous.measurable.stronglyMeasurable]
    change (∫ ω, f (P ω) ∂μ.withDensity (fun ω => ENNReal.ofReal (dp ω))) =
      ∫ ω, f (P ω) ∂μ.withDensity (fun ω => ENNReal.ofReal (dn ω))
    rw [integral_withDensity_nonneg_mul hp hdp, integral_withDensity_nonneg_mul hn hdn]
    apply sub_eq_zero.mp
    rw [← integral_sub hip hin]
    calc
      _ = ∫ ω, (Y ω - X ω) * f (P ω) ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        change dp ω * f (P ω) - dn ω * f (P ω) = d ω * f (P ω)
        rw [← sub_mul, he]
      _ = 0 := htest f
  have hPA : MeasurableSet (P ⁻¹' A) := hP hA
  have hmeasure : ρp (P ⁻¹' A) = ρn (P ⁻¹' A) := by
    have h := congrArg (fun ν : Measure E => ν A) hmap
    simpa only [Measure.map_apply hP hA] using h
  change (μ.withDensity fun ω => ENNReal.ofReal (dp ω)) (P ⁻¹' A) =
    (μ.withDensity fun ω => ENNReal.ofReal (dn ω)) (P ⁻¹' A) at hmeasure
  rw [withDensity_apply _ hPA, withDensity_apply _ hPA] at hmeasure
  have heq : (∫ ω in P ⁻¹' A, dp ω ∂μ) = ∫ ω in P ⁻¹' A, dn ω ∂μ := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hdp) hp.restrict.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hdn) hn.restrict.aestronglyMeasurable,
      hmeasure]
  have hzero : (∫ ω in P ⁻¹' A, d ω ∂μ) = 0 := by
    calc
      _ = ∫ ω in P ⁻¹' A, dp ω - dn ω ∂μ :=
        integral_congr_ae (Eventually.of_forall fun ω => (he ω).symm)
      _ = 0 := by rw [integral_sub hp.restrict hn.restrict, heq, sub_self]
  change (∫ ω in P ⁻¹' A, Y ω - X ω ∂μ) = 0 at hzero
  rw [integral_sub hY.restrict hX.restrict] at hzero
  exact (sub_eq_zero.mp hzero).symm

end RoughHeston

#print axioms RoughHeston.setIntegral_preimage_eq_of_boundedContinuous_tests
