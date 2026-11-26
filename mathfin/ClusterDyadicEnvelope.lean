import ClusterDenominator
import Mathlib.Analysis.SpecificLimits.Normed

/-! Dyadic scales and control of the focal Girsanov drift between
observation times. -/

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston

noncomputable def clusterDyadicAge (r : ℝ) (j : ℕ) : ℝ := r * (1/2 : ℝ)^(j+1)

theorem exists_cluster_dyadic_block {t r : ℝ} (ht : 0 < t) (htr : t ≤ r) :
    ∃ j, clusterDyadicAge r j < t ∧ t ≤ 2 * clusterDyadicAge r j := by
  have hr := ht.trans_le htr
  obtain ⟨j,h1,h2⟩ := exists_nat_pow_near_of_lt_one (div_pos ht hr)
    ((div_le_one hr).mpr htr) (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
  refine ⟨j, ?_, ?_⟩
  · simpa [clusterDyadicAge,mul_comm] using (lt_div_iff₀ hr).mp h1
  · have h := (div_le_iff₀ hr).mp h2
    simpa [clusterDyadicAge,pow_succ] using (show t ≤ 2*(r*((1/2:ℝ)^j*(1/2))) by nlinarith only [h])

/-- The loss of three powers of the scale ratio comes from one upper
bound for U and two inverse factors of Z. The constant also covers the
initial pulse block with ages up to four times its reference age. -/
theorem cluster_drift_envelope_on_block {t s r α γ U Z m M σ : ℝ}
    (ht : 0 < t) (hs : 0 < s) (hr : 0 < r) (hts : t ≤ 4*s)
    (hγ : 0 ≤ γ) (hm : 0 < m) (hM : 0 ≤ M) (hU : 0 ≤ U)
    (hupper : U ≤ M*s^(2*α-1)*(r/s)^γ)
    (hlower : m*s^α*(s/r)^γ ≤ Z) :
    t^(1+3*γ)*σ^2*U/Z^2 ≤ 4^(1+3*γ)*σ^2*M/m^2*r^(3*γ) := by
  have hZ : 0 < m*s^α*(s/r)^γ := by positivity
  have hz := hZ.trans_le hlower
  have ht' : t^(1+3*γ) ≤ (4*s)^(1+3*γ) := Real.rpow_le_rpow ht.le hts (by linarith)
  have hratio : t^(1+3*γ)*σ^2*U/Z^2 ≤
      (4*s)^(1+3*γ)*σ^2*(M*s^(2*α-1)*(r/s)^γ)/(m*s^α*(s/r)^γ)^2 := by
    gcongr
  have hsα : s^(2*α-1) = (s^α)^2 / s := by
    rw [Real.rpow_sub hs, Real.rpow_one, mul_comm (2:ℝ) α, Real.rpow_mul hs.le,Real.rpow_two]
  have h3 (x : ℝ) (hx : 0 ≤ x) : x^(3*γ)=(x^γ)^3 := by
    rw [mul_comm (3:ℝ) γ, Real.rpow_mul hx, ← Nat.cast_ofNat (R := ℝ) (n := 3), Real.rpow_natCast]
  refine hratio.trans_eq ?_
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hs.le, Real.rpow_add hs,
    Real.rpow_one, hsα, Real.div_rpow hr.le hs.le, Real.div_rpow hs.le hr.le,
    h3 s hs.le,h3 r hr.le]
  field_simp [(Real.rpow_pos_of_pos hs α).ne', (Real.rpow_pos_of_pos hs γ).ne',
    (Real.rpow_pos_of_pos hr γ).ne', hs.ne', hm.ne']

/-- Countably many dyadic failures with geometrically decaying
probability cost at most A/(1−q), uniformly in the number of pulses. -/
theorem cluster_dyadic_failures_probability {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] (E : ℕ → Set Ω) {A q : ℝ}
    (hA : 0 ≤ A) (hq : 0 ≤ q) (hq' : q < 1)
    (hb : ∀ j, Q.real (E j) ≤ A*q^j) : Q.real (⋃ j, E j) ≤ A/(1-q) := by
  have hs := (summable_geometric_of_lt_one hq hq').mul_left A
  have h : Q (⋃ j, E j) ≤ ∑' j, ENNReal.ofReal (A*q^j) := by
    refine (measure_iUnion_le E).trans (ENNReal.tsum_le_tsum fun j => ?_)
    rw [← ofReal_measureReal (μ := Q) (s := E j)]
    exact ENNReal.ofReal_le_ofReal (hb j)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg hA (pow_nonneg hq j)) hs,
    tsum_mul_left,tsum_geometric_of_lt_one hq hq'] at h
  simpa [measureReal_def, div_eq_mul_inv, ENNReal.toReal_ofReal
    (mul_nonneg hA (inv_nonneg.mpr (sub_nonneg.mpr hq'.le)))] using
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top h)

#print axioms exists_cluster_dyadic_block
#print axioms cluster_drift_envelope_on_block
#print axioms cluster_dyadic_failures_probability

end RoughHeston
