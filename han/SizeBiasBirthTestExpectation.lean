import SizeBiasEnergy
import Mathlib.Analysis.SpecialFunctions.Exp

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston.GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 m} {Z : ℝ≥0 → Ω → ℝ} {b H : ℝ≥0} {ε : ℝ}

/-- A terminal size bias whose focal mass is deterministic at birth
leaves the expectation of every birth-measurable payoff unchanged. -/
theorem integral_sizeBiasedLaw_eq_at_birth (hZ : Martingale Z F P)
    (hε : 0<ε) (hZ₀ : ∀ t, ∀ᵐ ω ∂P, 0≤Z t ω) (hb : b≤H)
    (hZb : Z b =ᵐ[P] fun _ => ε)
    {g : Ω → ℝ} (hg : StronglyMeasurable[F b] g) :
    ∫ ω,g ω ∂sizeBiasedLaw P (Z H) ε = ∫ ω,g ω ∂P := by
  have hd : sizeBiasedLaw P (Z b) ε = P := by
    have he : (fun ω => ENNReal.ofReal (Z b ω / ε)) =ᵐ[P] (1 : Ω → ℝ≥0∞) := by
      filter_upwards [hZb] with ω hω
      simp only [hω,div_self hε.ne',ENNReal.ofReal_one,Pi.one_apply]
    rw [sizeBiasedLaw,withDensity_congr_ae he,withDensity_one]
  rw [integral_trim (μ:=sizeBiasedLaw P (Z H) ε) (F.le b) hg,
    sizeBiasedLaw_trim_eq hZ hε hZ₀ hb, hd, ← integral_trim (μ:=P) (F.le b) hg]

/-- The exact birth expectation needed by the transported point tests
is bounded by the old probability of positive competitor variance. -/
theorem point_test_birth_sizeBiasedLaw_le (hZ : Martingale Z F P)
    (hε : 0<ε) (hZ₀ : ∀ t, ∀ᵐ ω ∂P, 0≤Z t ω) (hb : b≤H)
    (hZb : Z b =ᵐ[P] fun _ => ε)
    {Y : Ω → ℝ} (hY : Measurable Y) (hY₀ : ∀ ω, 0≤Y ω) {q : ℝ} (hq : 0≤q) :
    (∫ ω,1-P[(fun ω => Real.exp (-q*Y ω))|F b] ω ∂sizeBiasedLaw P (Z H) ε) ≤
      P.real {ω | 0<Y ω} := by
  let f (ω : Ω) := Real.exp (-q*Y ω)
  let V := {ω | 0<Y ω}
  have hV : MeasurableSet V := measurableSet_lt measurable_const hY
  have hf (ω : Ω) : f ω≤1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq) (hY₀ ω))
  have hfi : Integrable f P := by
    have hm : Measurable f := (measurable_const.mul hY).exp
    exact Integrable.of_bound hm.aestronglyMeasurable 1
      (ae_of_all _ fun ω => by
        have h : 0≤f ω := (Real.exp_pos _).le
        rw [Real.norm_of_nonneg h]
        exact hf ω)
  have ha : StronglyMeasurable[F b] (fun ω => 1-P[f|F b] ω) :=
    stronglyMeasurable_const.sub stronglyMeasurable_condExp
  change (∫ ω,1-P[f|F b] ω ∂sizeBiasedLaw P (Z H) ε) ≤ P.real V
  rw [integral_sizeBiasedLaw_eq_at_birth hZ hε hZ₀ hb hZb ha,
    integral_sub (integrable_const 1) integrable_condExp, integral_condExp (F.le b),
    ← integral_sub (integrable_const 1) hfi]
  have hInt : Integrable (V.indicator fun _ => (1:ℝ)) P := (integrable_const 1).indicator hV
  have he : ∫ ω,V.indicator (fun _ => (1:ℝ)) ω ∂P = P.real V := by
    rw [integral_indicator hV, setIntegral_const, smul_eq_mul, mul_one]
  rw [← he]
  refine integral_mono ((integrable_const 1).sub hfi) hInt fun ω => ?_
  by_cases hω : ω∈V
  · rw [indicator_of_mem hω]
    exact sub_le_self _ (Real.exp_pos _).le
  · have ht : Y ω=0 := le_antisymm (le_of_not_gt hω) (hY₀ ω)
    simp [f,ht,indicator_of_notMem hω]

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.integral_sizeBiasedLaw_eq_at_birth
#print axioms RoughHeston.GirsanovPort.point_test_birth_sizeBiasedLaw_le
