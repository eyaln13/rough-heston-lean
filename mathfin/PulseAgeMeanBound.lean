import PulseMeanConvolution
import PhysicalResolventGlobalBound

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

/-- At an age at least twice the pulse duration, the deterministic mean
is bounded by the pulse mass times a kernel depending only on that age. -/
theorem translatedPulse_resolvent_mean_le {T α ε d r D : ℝ} {τ : ℝ≥0} {R : ℝ→ℝ}
    (hα : 0<α) (hα' : α<1) (hε : 0≤ε) (hd : 0<d) (hr : 0<r) (hdr : d≤r/2)
    (hs : (τ:ℝ)+r≤T) (hD : 0≤D) (hR : Measurable R) (hR0 : ∀ u≤0,R u=0)
    (hRb : ∀ u∈Ioc (0:ℝ) T,|R u|≤D*fractionalK α u) :
    volterraConvolution R (fun u => translatedPulseRate τ ε d u.toNNReal) ((τ:ℝ)+r) ≤
      (D*fractionalK α (r/2))*ε := by
  let k := (Ioc (0:ℝ) T).indicator R
  let K := D*fractionalK α (r/2)
  have hiR : IntegrableOn R (Ioc (0:ℝ) T) := by
    refine ((fractionalK_integrableOn_Ioc hα T).const_mul D).mono' hR.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    simpa only [Real.norm_eq_abs] using hRb u hu
  have hi : Integrable k := (integrable_indicator_iff measurableSet_Ioc).2 hiR
  have hval := translatedPulse_resolvent_value (τ := τ) hd
    (show (τ:ℝ)+r∈Icc (0:ℝ) T from ⟨add_nonneg (NNReal.coe_nonneg τ) hr.le,hs⟩) hR0 (ε := ε)
  rw [add_sub_cancel_left] at hval
  have hl (u : ℝ) (hu : u∈Icc (r-d) r) : k u≤K := by
    have hlow : r/2≤u := by linarith [hu.1]
    have hpos : 0<u := (half_pos hr).trans_le hlow
    have huT : u≤T := by linarith [hu.2,NNReal.coe_nonneg τ]
    have hu' : u∈Ioc (0:ℝ) T := ⟨hpos,huT⟩
    have hK : fractionalK α u≤fractionalK α (r/2) := by
      rw [fractionalK,ite_eq_right (not_le.mpr hpos),fractionalK,ite_eq_right (not_le.mpr (half_pos hr))]
      exact div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_nonpos (half_pos hr) hlow (by linarith))
        (Real.Gamma_pos_of_pos hα).le
    change (Ioc (0:ℝ) T).indicator R u≤D*fractionalK α (r/2)
    rw [Set.indicator_of_mem hu']
    exact (le_abs_self _).trans ((hRb u hu').trans (mul_le_mul_of_nonneg_left hK hD))
  have hb : (∫ u in r-d..r,k u)≤d*K := by
    have he := intervalIntegral.integral_mono_on
      (f := k) (g := fun _ => K) (sub_le_self _ hd.le) hi.intervalIntegrable intervalIntegrable_const hl
    simpa only [intervalIntegral.integral_const,sub_sub_cancel,smul_eq_mul] using he
  rw [hval]
  exact (mul_le_mul_of_nonneg_left hb (div_nonneg hε hd.le)).trans_eq (by
    dsimp [K]
    field_simp)

theorem fractionalK_nonnegative_on_positive {α t : ℝ} (hα : 0<α) (ht : 0<t) :
    0≤fractionalK α t := by
  rw [fractionalK,ite_eq_right (not_le.mpr ht)]
  exact div_nonneg (Real.rpow_nonneg ht.le _) (Real.Gamma_pos_of_pos hα).le

theorem fractionalSecondKindResolvent_causal (α κ : ℝ) (u : ℝ) (hu : u≤0) :
    fractionalSecondKindResolvent α κ u=0 := by
  simp [fractionalSecondKindResolvent,fractionalK,hu]

#print axioms translatedPulse_resolvent_mean_le

end RoughHeston
