import PositiveClusterMass

/-! A lower bound for the focal density throughout a dyadic block in terms
of the variance accumulated by the beginning of the block. -/

open MeasureTheory Set Filter
open scoped Topology

namespace RoughHeston

theorem fractional_history_controls_accumulated_variance
    {α s v S : ℝ} (hα : 0 < α) (hα' : α < 1)
    (hs : 0 < s) (hsv : s ≤ v) (hvS : v ≤ S)
    {U : ℝ → ℝ} (hc : Continuous U) (hn : ∀ t ∈ Icc 0 v, 0 ≤ U t) :
    fractionalL α S * (∫ u in Ioc 0 s, U u) ≤ volterraConvolution (fractionalL α) U v := by
  let f := fun u => fractionalL α (v-u)*U u
  have hi : IntegrableOn f (Ioc 0 v) :=
    (fractionalL_reflected_integrableOn_Ioc hα' (hs.le.trans hsv)).mul_continuousOn_of_subset
      hc.continuousOn measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self
  have hsub : Ioc (0:ℝ) s ⊆ Ioc 0 v := Ioc_subset_Ioc_right hsv
  have hS := (hs.trans_le hsv).trans_le hvS
  have hG := (Real.Gamma_pos_of_pos (sub_pos.mpr hα')).le
  calc
    fractionalL α S * _ = ∫ u in Ioc 0 s, fractionalL α S * U u := (integral_const_mul ..).symm
    _ ≤ ∫ u in Ioc 0 s, f u := by
      apply integral_mono_ae ((hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self).const_mul _)
        (hi.mono_set hsub)
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := 0) (b := s)),
        ae_mono (Measure.restrict_le_self (μ := volume) (s := Ioc 0 s)) (volume.ae_ne v)] with u hu hne
      have huv : 0 < v-u := sub_pos.mpr (lt_of_le_of_ne (hu.2.trans hsv) hne)
      apply mul_le_mul_of_nonneg_right _ (hn u ⟨hu.1.le,hu.2.trans hsv⟩)
      simp only [fractionalL, ite_eq_right (not_le.mpr huv), ite_eq_right (not_le.mpr hS)]
      exact div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_nonpos huv (by linarith [hu.1])
        (neg_nonpos.mpr hα.le)) hG
    _ ≤ _ := by
      apply setIntegral_mono_set hi _ (ae_of_all _ fun _ hu => hsub hu)
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := 0) (b := v))] with u hu
      apply mul_nonneg _ (hn u ⟨hu.1.le,hu.2⟩)
      unfold fractionalL
      split
      · exact le_rfl
      · exact div_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hu.2) _) hG

/-- For the inverse focal mass, Z_v on [s,2s] dominates L(2s) J_s,
including when part of the pulse is still to come. -/
theorem focal_mass_lower_on_block {α κ ε s v : ℝ} {U A Z : ℝ → ℝ}
    (hα : 0 < α) (hα' : α < 1) (hκ : 0 ≤ κ) (hs : 0 < s)
    (hsv : s ≤ v) (hv : v ≤ 2*s) (hc : Continuous U)
    (hn : ∀ t ∈ Icc 0 v, 0 ≤ U t) (hcap : A v ≤ ε)
    (hz : Z v = ε - A v + volterraConvolution (fractionalL α) U v +
      κ*(∫ u in Ioc 0 v, U u)) :
    fractionalL α (2*s) * (∫ u in Ioc 0 s, U u) ≤ Z v := by
  rw [hz]
  have hL := fractional_history_controls_accumulated_variance hα hα' hs hsv hv hc hn
  have hJ := setIntegral_nonneg (μ := volume) measurableSet_Ioc
    (fun u (hu : u ∈ Ioc 0 v) => hn u ⟨hu.1.le,hu.2⟩)
  linarith only [hL, hcap, mul_nonneg hκ hJ]

#print axioms fractional_history_controls_accumulated_variance
#print axioms focal_mass_lower_on_block

end RoughHeston
