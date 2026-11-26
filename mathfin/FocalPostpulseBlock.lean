import ClusterBlockProbabilities
import RectangularPulseLowerTail

/-! On dyadic ages after the immigration pulse, the lower-tail estimate
for J and an upper moment of the block supremum give both bounds in the
Girsanov envelope. -/

open Set MeasureTheory Filter
open scoped Topology

namespace RoughHeston

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]

theorem focal_postpulse_block {r α γ c M D K κ ε : ℝ}
    (hr : 0 < r) (hα : 0 < α) (hα' : α < 1) (hκ : 0 ≤ κ) (hγ : 0 < γ)
    (hc : 0 < c) (hc1 : c ≤ 1) (hM : 0 < M) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (i : ℕ) {U Z : ℝ → Ω → ℝ} {A : ℝ → ℝ} {S : Ω → ℝ}
    (huc : ∀ ω, Continuous (fun t => U t ω)) (hn : ∀ t ∈ Icc 0 r, ∀ ω, 0 ≤ U t ω)
    (hA : ∀ t ∈ Icc 0 r, A t ≤ ε)
    (hz : ∀ t ∈ Icc 0 r, ∀ ω, Z t ω = ε-A t+
      volterraConvolution (fractionalL α) (fun v => U v ω) t+
      κ*clusterAccumulatedVariance U t ω) :
    let s := clusterDyadicAge r i
    (∀ t ∈ Icc s (2*s), ∀ ω, U t ω ≤ S ω) → Integrable S Q →
    (∀ᵐ ω ∂Q, 0 ≤ S ω) → (∫ ω,S ω ∂Q) ≤ K*s^(2*α-1) →
    (∀ x, 0 < x → x ≤ 1 → Q.real {ω | clusterAccumulatedVariance U s ω ≤ x*s^(2*α)}
      ≤ D*Real.sqrt x) →
    ∃ E : Set Ω, Q.real E ≤ (K/M+D*Real.sqrt c)*((1/2:ℝ)^(γ/2))^i ∧
      ∀ ω ∉ E, ∀ t ∈ Ioc 0 r, t ∈ Icc s (2*s) →
        U t ω ≤ M*s^(2*α-1)*(r/s)^γ ∧
        ((2:ℝ)^(-α)/Real.Gamma (1-α)*c)*s^α*(s/r)^γ ≤ Z t ω := by
  dsimp only
  let s := clusterDyadicAge r i
  let w := (s/r)^γ
  let q := (1/2:ℝ)^(γ/2)
  have hs : 0 < s := by dsimp [s,clusterDyadicAge]; positivity
  obtain ⟨hq,hq1,hw,hw1,hroot⟩ := cluster_dyadic_relative_weight hr hγ i
  intro hsup hi hnon hmean hlower
  let low := {ω | clusterAccumulatedVariance U s ω ≤ (c*w)*s^(2*α)}
  let high := {ω | M*s^(2*α-1)/w < S ω}
  refine ⟨high ∪ low, ?_, ?_⟩
  · have h := cluster_block_failures (u := s^(2*α-1)) (j := s^(2*α))
      (Real.rpow_pos_of_pos hs _) (Real.rpow_pos_of_pos hs _) hw hw1 hc hc1 hM hnon hi hmean hlower
    rw [hroot] at h
    exact h.trans (mul_le_mul_of_nonneg_left (by rw [pow_succ]; exact mul_le_of_le_one_right (pow_nonneg hq.le _) hq1.le)
      (add_nonneg (div_nonneg hK hM.le) (mul_nonneg hD (Real.sqrt_nonneg _))))
  · intro ω he t ht hts
    have htop : S ω ≤ M*s^(2*α-1)/w := le_of_not_gt fun h => he (Or.inl h)
    have hlo : c*w*s^(2*α) ≤ clusterAccumulatedVariance U s ω :=
      (lt_of_not_ge (fun h => he (Or.inr h))).le
    have hw : w⁻¹=(r/s)^γ := by dsimp [w]; rw [← Real.inv_rpow (div_nonneg hs.le hr.le),inv_div]
    refine ⟨(hsup t hts ω).trans (by simpa [div_eq_mul_inv, hw] using htop), ?_⟩
    have hKern : 0 ≤ fractionalL α (2*s) := by
      rw [fractionalL,ite_eq_right (not_le.mpr (by positivity : 0 < 2*s))]
      exact div_nonneg (Real.rpow_nonneg (by positivity) _) (Real.Gamma_pos_of_pos (sub_pos.mpr hα')).le
    have h := (mul_le_mul_of_nonneg_left hlo hKern).trans
      (focal_mass_lower_on_block (U := fun u => U u ω) (A := A) (Z := fun u => Z u ω)
        hα hα' hκ hs hts.1 hts.2 (huc ω)
        (fun v hv => hn v ⟨hv.1,hv.2.trans ht.2⟩ ω) (hA t ⟨ht.1.le,ht.2⟩) (hz t ⟨ht.1.le,ht.2⟩ ω))
    rw [fractionalL_mul_age_power hs (by norm_num : (0:ℝ)<2)] at h
    dsimp only [s,w] at *
    linarith only [h]

#print axioms focal_postpulse_block

end RoughHeston
