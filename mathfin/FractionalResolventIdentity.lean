import FractionalResolventSeries
import FractionalKernelL1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Ring

open Set Filter MeasureTheory
open scoped Topology

namespace RoughHeston

private theorem fractionalK_nonneg_for_resolvent {a : ℝ} (ha : 0 < a) (t : ℝ) :
    0 ≤ fractionalK a t := by
  unfold fractionalK
  split
  · exact le_rfl
  · exact div_nonneg (Real.rpow_nonneg (le_of_lt (lt_of_not_ge ‹¬ t ≤ 0›)) _)
      (Real.Gamma_pos_of_pos ha).le

private theorem integrableOn_fractionalK_pair {a b t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ht : 0 < t) :
    IntegrableOn (fun s => fractionalK a (t-s) * fractionalK b s) (Ioc 0 t) := by
  have hi := (real_beta_weight_scaled (a := b) (b := a) hb ha ht).1
  rw [integrableOn_Ioc_iff_integrableOn_Ioo] at hi ⊢
  have hdiv : IntegrableOn (fun s => (s^(b-1)*(t-s)^(a-1)) /
      (Real.Gamma b * Real.Gamma a)) (Ioo 0 t) :=
    hi.div_const (Real.Gamma b * Real.Gamma a)
  refine hdiv.congr_fun ?_ measurableSet_Ioo
  intro s hs
  dsimp only
  rw [fractionalK, fractionalK, ite_eq_right (not_le.mpr (sub_pos.mpr hs.2)),
    ite_eq_right (not_le.mpr hs.1), div_mul_div_comm]
  ac_rfl

/-- The series of convolution powers solves the second-kind resolvent
equation. In the convolution, the series is integrable term by term. -/
theorem fractionalSecondKindResolvent_identity {α κ t : ℝ}
    (hα : 0 < α) (ht : 0 < t) :
    fractionalSecondKindResolvent α κ t =
      fractionalK α t - κ * volterraConvolution (fractionalK α)
        (fractionalSecondKindResolvent α κ) t := by
  by_cases hκ : κ = 0
  · rw [hκ, fractionalSecondKindResolvent, zero_mul, sub_zero, neg_zero, tsum_eq_single 0]
    · simp
    · intro n hn
      simp [zero_pow hn]
  let f (n : ℕ) (s : ℝ) := (-κ)^n * fractionalK (((n : ℝ)+1)*α) s
  let F (n : ℕ) (s : ℝ) := fractionalK α (t-s) * f n s
  have ho (n : ℕ) : (0 : ℝ) < ((n : ℝ)+1)*α := mul_pos (by positivity) hα
  have hi (n : ℕ) : IntegrableOn (F n) (Ioc 0 t) := by
    have hmul : IntegrableOn (fun s => (-κ)^n *
        (fractionalK α (t-s) * fractionalK (((n : ℝ)+1)*α) s)) (Ioc 0 t) :=
      (integrableOn_fractionalK_pair hα (ho n) ht).const_mul ((-κ)^n)
    refine hmul.congr_fun (fun s _ => ?_) measurableSet_Ioc
    dsimp [F, f]
    ring
  have hf (n : ℕ) : (∫ s in Ioc (0 : ℝ) t, F n s) =
      (-κ)^n * fractionalK ((((n+1 : ℕ) : ℝ)+1)*α) t := by
    have hre : (∫ s in Ioc (0 : ℝ) t, F n s) =
        (-κ)^n * volterraConvolution (fractionalK α) (fractionalK (((n : ℝ)+1)*α)) t := by
      unfold volterraConvolution
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s _
      dsimp [F, f]
      ring
    rw [hre, fractionalK_convolution_add hα (ho n) ht]
    congr 2
    push_cast
    ring
  have hnorm (n : ℕ) : (∫ s in Ioc (0 : ℝ) t, ‖F n s‖) =
      ‖f (n+1) t‖ / |κ| := by
    have hre : (∫ s in Ioc (0 : ℝ) t, ‖F n s‖) =
        |κ|^n * volterraConvolution (fractionalK α) (fractionalK (((n : ℝ)+1)*α)) t := by
      unfold volterraConvolution
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s _
      dsimp [F, f]
      rw [abs_mul, abs_mul, abs_pow, abs_neg,
        abs_of_nonneg (fractionalK_nonneg_for_resolvent hα _),
        abs_of_nonneg (fractionalK_nonneg_for_resolvent (ho n) _)]
      ring
    rw [hre, fractionalK_convolution_add hα (ho n) ht, show α + ((n : ℝ)+1)*α =
      (((n+1 : ℕ) : ℝ)+1)*α by push_cast; ring]
    change _ = ‖(-κ)^(n+1) * fractionalK ((((n+1 : ℕ) : ℝ)+1)*α) t‖ / |κ|
    rw [norm_mul, norm_pow, norm_neg, Real.norm_eq_abs κ,
      Real.norm_of_nonneg (fractionalK_nonneg_for_resolvent (ho (n+1)) _), pow_succ]
    field_simp [abs_ne_zero.2 hκ]
  have hsumNorm : Summable (fun n : ℕ => ‖f n t‖) :=
    fractionalSecondKindResolvent_norm_summable hα κ ht le_rfl
  have htailNorm : Summable (fun n : ℕ => ‖f (n+1) t‖) :=
    (summable_nat_add_iff 1).mpr hsumNorm
  have hsumI : Summable (fun n : ℕ => ∫ s in Ioc (0 : ℝ) t, ‖F n s‖) := by
    simp_rw [hnorm]
    exact htailNorm.div_const _
  have hK : volterraConvolution (fractionalK α) (fractionalSecondKindResolvent α κ) t =
      ∑' n : ℕ, (-κ)^n * fractionalK ((((n+1 : ℕ) : ℝ)+1)*α) t := by
    unfold volterraConvolution
    have hsumExt : (∫ s in Ioc (0 : ℝ) t,
          fractionalK α (t-s) * fractionalSecondKindResolvent α κ s) =
          ∫ s in Ioc (0 : ℝ) t, ∑' n : ℕ, F n s := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s _
      change fractionalK α (t-s) * (∑' n, f n s) = ∑' n, fractionalK α (t-s) * f n s
      rw [tsum_mul_left]
    rw [hsumExt, ← integral_tsum_of_summable_integral_norm hi hsumI]
    exact tsum_congr hf
  have hsplit := hsumNorm.of_norm.tsum_eq_zero_add
  change (∑' n, f n t) = f 0 t + ∑' n, f (n+1) t at hsplit
  rw [fractionalSecondKindResolvent, hK]
  change (∑' n, f n t) = _
  rw [hsplit]
  have hzero : f 0 t = fractionalK α t := by simp [f]
  rw [hzero, ← tsum_mul_left, sub_eq_add_neg, ← tsum_neg]
  congr 1
  apply tsum_congr
  intro n
  simp only [f, pow_succ]
  ring

end RoughHeston

#print axioms RoughHeston.fractionalSecondKindResolvent_identity
