import ClusterNoiseSplit
import ClusterResolventDifferenceProfile

open MeasureTheory Set Filter
open scoped NNReal

namespace RoughHeston.GirsanovPort

theorem pastResolventDifference_measurable {R : ℝ → ℝ} (hR : Measurable R) (a b : ℝ≥0) :
    Measurable (pastResolventDifference R a b) :=
  ((hR.comp (measurable_const.sub measurable_subtype_coe)).sub
    (hR.comp (measurable_const.sub measurable_subtype_coe))).indicator measurableSet_Ioc

theorem newResolventWeight_measurable {R : ℝ → ℝ} (hR : Measurable R) (a b : ℝ≥0) :
    Measurable (newResolventWeight R a b) :=
  (hR.comp (measurable_const.sub measurable_subtype_coe)).indicator measurableSet_Ioc

/-- The earlier Brownian row gains h^(2δ); the new row on (a,b]
retains the full fractional kernel exponent. -/
theorem cluster_resolvent_increment_row_bounds {R : ℝ → ℝ} {α δ A C H σ : ℝ}
    (ha : α≤1) (hd : 0≤δ) (hd' : δ≤1) (hA : 0≤A) (hC : 0≤C)
    (hpoint : ∀ x∈Ioc 0 H, |R x|≤A*x^(α-1))
    (hinc : ∀ x h, 0<x → 0≤h → x+h≤H → |R (x+h)-R x|≤C*x^(α-2)*h)
    {a b : ℝ≥0} (hab : a<b) (hb : (b:ℝ)≤H) :
    let h := (b:ℝ)-(a:ℝ)
    let β := 2*α-1
    (∀ u∈Ioo (0:ℝ≥0) a, (σ*pastResolventDifference R a b u)^2 ≤
      ((|σ| *(2*A+C))^2*h^(2*δ))*((a:ℝ)-(u:ℝ))^(β-2*δ-1)) ∧
    (∀ u∈Ioo a b, (σ*newResolventWeight R a b u)^2 ≤
      (|σ| *A)^2*((b:ℝ)-(u:ℝ))^(β-1)) := by
  dsimp only
  let h := (b:ℝ)-(a:ℝ)
  have hh : 0<h := sub_pos.mpr (show (a:ℝ)<(b:ℝ) from hab)
  constructor
  · intro u hu
    let x := (a:ℝ)-(u:ℝ)
    have hx : 0<x := sub_pos.mpr (show (u:ℝ)<(a:ℝ) from hu.2)
    have hxsum : x+h=(b:ℝ)-(u:ℝ) := by dsimp [x,h]; ring
    have hm := cluster_kernel_difference_power ha hd hd' hA hC hpoint hinc hx hh
      (show x+h≤H by rw [hxsum]; exact (sub_le_self _ u.coe_nonneg).trans hb)
    rw [hxsum] at hm
    have hterm := pow_le_pow_left₀ (mul_nonneg (abs_nonneg σ) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hm (abs_nonneg σ)) 2
    have hhp : (h^δ)^2=h^(2*δ) := by rw [←Real.rpow_mul_natCast hh.le]; congr 1; ring
    have hxp : (x^(α-1-δ))^2=x^(2*α-1-2*δ-1) := by rw [←Real.rpow_mul_natCast hx.le]; congr 1; ring
    rw [pastResolventDifference,indicator_of_mem (show u∈Ioc (0:ℝ≥0) a from ⟨hu.1,hu.2.le⟩)]
    change (σ*(R ((b:ℝ)-(u:ℝ))-R x))^2≤((|σ| *(2*A+C))^2*h^(2*δ))*x^(2*α-1-2*δ-1)
    rw [←hhp,←hxp]
    simp only [mul_pow, sq_abs] at hterm ⊢
    exact hterm.trans_eq (by ring)
  · intro u hu
    let x := (b:ℝ)-(u:ℝ)
    have hx : 0<x := sub_pos.mpr (show (u:ℝ)<(b:ℝ) from hu.2)
    have hm := hpoint x ⟨hx,(sub_le_self _ u.coe_nonneg).trans hb⟩
    have hterm := pow_le_pow_left₀ (mul_nonneg (abs_nonneg σ) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hm (abs_nonneg σ)) 2
    have hxp : (x^(α-1))^2=x^(2*α-1-1) := by rw [←Real.rpow_mul_natCast hx.le]; congr 1; ring
    rw [newResolventWeight,indicator_of_mem (show u∈Ioc a b from ⟨hu.1,hu.2.le⟩)]
    change (σ*R x)^2≤(|σ| *A)^2*x^(2*α-1-1)
    rw [←hxp]
    simp only [mul_pow, sq_abs] at hterm ⊢
    exact hterm.trans_eq (by ring)

#print axioms cluster_resolvent_increment_row_bounds

end RoughHeston.GirsanovPort
