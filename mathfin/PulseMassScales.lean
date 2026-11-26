import ClusterDenominator
import RectangularPulseMeasure

/-! Conversion of accumulated-variance tests to uniform bounds for the
density martingale on the early and late pulse blocks. -/

open MeasureTheory Set Filter
open scoped Topology

namespace RoughHeston

/-- The constants for a block with t≤k·s can be read directly from
the power kernel, with no dependence on the pulse scale. -/
theorem fractionalL_mul_age_power {α s k x : ℝ} (hs : 0 < s) (hk : 0 < k) :
    fractionalL α (k*s) * (x*s^(2*α)) =
      (k^(-α) / Real.Gamma (1-α))*x*s^α := by
  rw [fractionalL,ite_eq_right (not_le.mpr (mul_pos hk hs)),Real.mul_rpow hk.le hs.le]
  have h : s^(-α)*s^(2*α)=s^α := by rw [← Real.rpow_add hs]; ring_nf
  calc
    _ = k^(-α)/Real.Gamma (1-α)*x*(s^(-α)*s^(2*α)) := by ring
    _ = _ := by rw [h]

/-- In the first quarter of the pulse the unspent input alone bounds Z.
For older ages the same accrued variance J_(d/4) bounds all Z up to 4d. -/
theorem rectangular_focal_mass_early_block {α κ ε d x : ℝ} (hα : 0 < α) (hα' : α < 1)
    (hκ : 0 ≤ κ) (hd : 0 < d) (hε : ε = d^α)
    {U Z : ℝ → ℝ} (hc : Continuous U) (hn : ∀ t ∈ Icc 0 (4*d), 0 ≤ U t)
    (hz : ∀ t ∈ Icc 0 (4*d), Z t = ε - ε/d*min t d +
      volterraConvolution (fractionalL α) U t + κ*(∫ u in Ioc 0 t,U u))
    (hJ : x*(d/4)^(2*α) ≤ ∫ u in Ioc 0 (d/4), U u) :
    ∀ t ∈ Icc 0 (4*d),
      min (3/4) ((4:ℝ)^(-α)/Real.Gamma (1-α)*x/(4:ℝ)^(2*α)) * d^α ≤ Z t := by
  have hd' : 0 < d/4 := by positivity
  have hmon (v : ℝ) (hv : 0 ≤ v) (t : ℝ) (ht : v ≤ t) (htd : t ≤ 4*d) :
      fractionalL α (4*d)*(∫ u in Ioc 0 v,U u) ≤ volterraConvolution (fractionalL α) U t := by
    rcases hv.eq_or_lt with he|hh
    · subst v
      rw [Ioc_self,Measure.restrict_empty,integral_zero_measure,mul_zero]
      apply setIntegral_nonneg measurableSet_Ioc
      intro u hu
      apply mul_nonneg _ (hn u ⟨hu.1.le,hu.2.trans htd⟩)
      unfold fractionalL
      split
      · exact le_rfl
      · exact div_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hu.2) _)
          (Real.Gamma_pos_of_pos (sub_pos.mpr hα')).le
    · exact fractional_history_controls_accumulated_variance hα hα' hh ht htd hc
        (fun u hu => hn u ⟨hu.1,hu.2.trans htd⟩)
  intro t ht
  have hdα : 0 < d^α := Real.rpow_pos_of_pos hd _
  have heps : 0 < ε := by rwa [hε]
  have hA : ε/d * min t d ≤ ε := by
    calc _ ≤ (ε/d)*d := mul_le_mul_of_nonneg_left (min_le_right ..) (div_nonneg heps.le hd.le)
         _ = _ := div_mul_cancel₀ _ hd.ne'
  have hkJ := mul_nonneg hκ (setIntegral_nonneg (μ := volume) measurableSet_Ioc
    (fun u (hu : u ∈ Ioc 0 t) => hn u ⟨hu.1.le,hu.2.trans ht.2⟩))
  rw [hz t ht]
  by_cases he : t ≤ d/4
  · have hL := hmon 0 le_rfl t ht.1 ht.2
    simp only [Ioc_self,Measure.restrict_empty,integral_zero_measure,mul_zero] at hL
    have ht' : ε/d*min t d ≤ ε/4 := by
      calc _ ≤ ε/d*(d/4) := mul_le_mul_of_nonneg_left ((min_le_left ..).trans he) (div_nonneg heps.le hd.le)
           _ = _ := by field_simp
    have hl := mul_le_mul_of_nonneg_right (min_le_left (3/4:ℝ) ((4:ℝ)^(-α)/Real.Gamma (1-α)*x/(4:ℝ)^(2*α))) hdα.le
    linarith only [hL,hε,ht',hkJ,hl]
  · have hL := hmon _ hd'.le t (le_of_not_ge he) ht.2
    have hK : 0 ≤ fractionalL α (4*d) := by
      rw [fractionalL,ite_eq_right (not_le.mpr (by positivity : 0<4*d))]
      exact div_nonneg (Real.rpow_nonneg (by positivity) _) (Real.Gamma_pos_of_pos (sub_pos.mpr hα')).le
    have hbound := (mul_le_mul_of_nonneg_left hJ hK).trans hL
    rw [Real.div_rpow hd.le (by norm_num : (0:ℝ) ≤ 4)] at hbound
    have halg : fractionalL α (4*d)*(x*(d^(2*α)/(4:ℝ)^(2*α))) =
        ((4:ℝ)^(-α)/Real.Gamma (1-α)*x/(4:ℝ)^(2*α))*d^α := by
      calc _ = (fractionalL α (4*d)*(x*d^(2*α)))/(4:ℝ)^(2*α) := by ring
           _ = _ := by rw [fractionalL_mul_age_power hd (by norm_num : (0:ℝ)<4)]; ring
    rw [halg] at hbound
    have hl := mul_le_mul_of_nonneg_right (min_le_right (3/4:ℝ) ((4:ℝ)^(-α)/Real.Gamma (1-α)*x/(4:ℝ)^(2*α))) hdα.le
    linarith only [hl,hbound,hA,hkJ]

#print axioms fractionalL_mul_age_power
#print axioms rectangular_focal_mass_early_block

end RoughHeston
