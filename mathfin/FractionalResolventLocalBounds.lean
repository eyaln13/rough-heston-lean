import FractionalResolventProfile

/-! Uniform short-time comparison of the second-kind resolvent with the
rough Heston kernel, under bounded mean reversion. -/

open MeasureTheory Set Filter
open scoped Topology

namespace RoughHeston

theorem fractionalResolvent_uniform_local_comparison {α K : ℝ} (hα : 0 < α) (hK : 0 ≤ K) :
    ∃ r : ℝ, 0 < r ∧ ∀ κ t : ℝ, |κ| ≤ K → 0 < t → t ≤ r →
      (fractionalK α t)/2 ≤ fractionalSecondKindResolvent α κ t ∧
      fractionalSecondKindResolvent α κ t ≤ 2*fractionalK α t := by
  obtain ⟨C, hC, hLip⟩ := fractionalResolventProfile_lipschitz_on hα (by linarith : 1 ≤ 1+K)
  let c := 1/Real.Gamma α
  have hc : 0 < c := one_div_pos.mpr (Real.Gamma_pos_of_pos hα)
  let b := min 1 (c/(2*((C+1)*(K+1))))
  have hb : 0 < b := lt_min zero_lt_one (div_pos hc (by positivity))
  let r := b^(1/α)
  have hr : 0 < r := Real.rpow_pos_of_pos hb _
  have hpow : r^α=b := by
    dsimp [r]
    rw [← Real.rpow_mul hb.le,one_div,inv_mul_cancel₀ hα.ne',Real.rpow_one]
  refine ⟨r,hr,?_⟩
  intro κ t hκ ht htr
  have hta : 0 ≤ t^α := Real.rpow_nonneg ht.le _
  have htb : t^α ≤ b := hpow ▸ Real.rpow_le_rpow ht.le htr hα.le
  have ht1 : t^α ≤ 1 := htb.trans (min_le_left _ _)
  have ha : |(-κ)*t^α| ≤ K*t^α := by rw [abs_mul,abs_neg,abs_of_nonneg hta]; gcongr
  have hab : |(-κ)*t^α| ≤ 1+K :=
    ha.trans ((mul_le_of_le_one_right hK ht1).trans (by linarith))
  have hL := hLip (-κ*t^α) 0 hab (by simp; linarith)
  rw [sub_zero,fractionalResolventProfile_zero] at hL
  have herr : C*|(-κ)*t^α| ≤ c/2 := by
    have hsmall := (le_div_iff₀ (by positivity : 0 < 2*((C+1)*(K+1)))).mp
      (htb.trans (min_le_right ..))
    have hcK : C*K ≤ (C+1)*(K+1) := by nlinarith
    have h := (mul_le_mul_of_nonneg_left ha hC).trans
      (by simpa [mul_assoc] using (mul_le_mul_of_nonneg_right hcK hta))
    linarith only [h, hsmall]
  obtain ⟨hl,hu⟩ := abs_le.mp (hL.trans herr)
  rw [fractionalSecondKindResolvent_factor ht, fractionalK, ite_eq_right (not_le.mpr ht)]
  have htn := Real.rpow_nonneg ht.le (α-1)
  have hlow : c/2 ≤ fractionalResolventProfile α (-κ*t^α) := by dsimp [c] at *; linarith
  have hup : fractionalResolventProfile α (-κ*t^α) ≤ 2*c := by dsimp [c] at *; linarith
  constructor
  · calc _ = t^(α-1)*(c/2) := by dsimp [c]; ring
         _ ≤ _ := mul_le_mul_of_nonneg_left hlow htn
  · calc _ ≤ t^(α-1)*(2*c) := mul_le_mul_of_nonneg_left hup htn
         _ = _ := by dsimp [c]; ring

#print axioms fractionalResolvent_uniform_local_comparison

end RoughHeston
