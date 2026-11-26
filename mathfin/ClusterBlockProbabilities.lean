import FocalEnvelopeFailure
import PulseMassScales
import SizeBiasedBurst

/-! Failure probabilities of the numerator and denominator thresholds on
a single interval, in the focal size-biased law. -/

open MeasureTheory Set Filter
open scoped Topology

namespace RoughHeston

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]

/-- If w is the relative block length raised to γ, the selected
thresholds fail with probability at most (K/M+D√c)√w. -/
theorem cluster_block_failures {supU J : Ω → ℝ} {u j w c D K M : ℝ}
    (hu : 0 < u) (hj : 0 < j) (hw : 0 < w) (hw1 : w ≤ 1)
    (hc : 0 < c) (hc1 : c ≤ 1) (hM : 0 < M)
    (hn : ∀ᵐ ω ∂Q, 0 ≤ supU ω) (hi : Integrable supU Q)
    (he : (∫ ω, supU ω ∂Q) ≤ K*u)
    (hJ : ∀ x, 0 < x → x ≤ 1 → Q.real {ω | J ω ≤ x*j} ≤ D*Real.sqrt x) :
    Q.real ({ω | M*u/w < supU ω} ∪ {ω | J ω ≤ (c*w)*j}) ≤ (K/M+D*Real.sqrt c)*Real.sqrt w := by
  have hK : 0 ≤ K := nonneg_of_mul_nonneg_left ((integral_nonneg_of_ae hn).trans he) hu
  have hU : Q.real {ω | M*u/w < supU ω} ≤ K/M*w := by
    have hq := (mul_meas_ge_le_integral_of_nonneg hn hi (M*u/w)).trans he
    have hm : Q.real {ω | M*u/w < supU ω} ≤ Q.real {ω | M*u/w ≤ supU ω} :=
      measureReal_mono fun ω (hω : M*u/w < supU ω) => hω.le
    have hpos : 0 < M*u/w := div_pos (mul_pos hM hu) hw
    apply le_of_mul_le_mul_left _ hpos
    calc _ ≤ _ := mul_le_mul_of_nonneg_left hm hpos.le
         _ ≤ K*u := hq
         _ = _ := by field_simp
  have hJ' := hJ (c*w) (mul_pos hc hw) ((mul_le_mul_of_nonneg_right hc1 hw.le).trans (by simpa using hw1))
  rw [Real.sqrt_mul hc.le] at hJ'
  have hw' : w ≤ Real.sqrt w := by
    nlinarith [Real.sq_sqrt hw.le, Real.sqrt_nonneg w, mul_nonneg hw.le (sub_nonneg.mpr hw1),
      sq_nonneg (Real.sqrt w-w)]
  have hU' := hU.trans (mul_le_mul_of_nonneg_left hw' (div_nonneg hK hM.le))
  calc
    _ ≤ _ := (measureReal_union_le _ _).trans (add_le_add hU' hJ')
    _ = _ := by ring

/-- The square root of the weight on dyadic block j is the
(j+1)-th term of a convergent geometric series. -/
theorem cluster_dyadic_relative_weight {r γ : ℝ} (hr : 0 < r) (hγ : 0 < γ) (j : ℕ) :
    let s := clusterDyadicAge r j
    let q := (1/2:ℝ)^(γ/2)
    0 < q ∧ q < 1 ∧ 0 < (s/r)^γ ∧ (s/r)^γ ≤ 1 ∧
      Real.sqrt ((s/r)^γ) = q^(j+1) := by
  dsimp only
  have hhalf : (0:ℝ) < 1/2 := by norm_num
  have hlo : (1/2:ℝ) < 1 := by norm_num
  have e : clusterDyadicAge r j/r = (1/2:ℝ)^(j+1) := by
    unfold clusterDyadicAge
    field_simp
  rw [e]
  refine ⟨Real.rpow_pos_of_pos hhalf _, Real.rpow_lt_one hhalf.le hlo (by positivity),
    Real.rpow_pos_of_pos (pow_pos hhalf _) _, Real.rpow_le_one (pow_nonneg hhalf.le _)
    (pow_le_one₀ hhalf.le hlo.le) hγ.le, ?_⟩
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (pow_nonneg hhalf.le _),
    show γ*(1/2)=γ/2 by ring]
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hhalf.le, ← Real.rpow_mul hhalf.le]
  congr 1
  ring

#print axioms cluster_block_failures
#print axioms cluster_dyadic_relative_weight

end RoughHeston
