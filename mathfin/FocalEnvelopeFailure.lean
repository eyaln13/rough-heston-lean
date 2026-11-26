import ClusterDyadicEnvelope
import StoppedClusterEnvelope

/-! From estimates on dyadic age blocks to the exit probability of the
actual Girsanov envelope stop. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]

theorem focal_envelope_failure_probability {r : ℝ≥0} {d α γ m M σ A q e : ℝ}
    (hr : 0 < r) (hd : 0 < d) (hγ : 0 ≤ γ) (hm : 0 < m) (hM : 0 ≤ M)
    (hA : 0 ≤ A) (hq : 0 ≤ q) (hq' : q < 1) {U Z : ℝ≥0 → Ω → ℝ}
    (hu : ∀ t ≤ r, ∀ ω, 0 ≤ U t ω) (early : Set Ω) (E : ℕ → Set Ω)
    (he : Q.real early ≤ e) (hprob : ∀ j, Q.real (E j) ≤ A*q^j)
    (hfirst : ∀ ω ∉ early, ∀ t ∈ Ioc (0:ℝ≥0) r, (t:ℝ) ≤ 4*d →
      U t ω ≤ M*d^(2*α-1)*((r:ℝ)/d)^γ ∧ m*d^α*(d/(r:ℝ))^γ ≤ Z t ω)
    (hblock : ∀ j, let s := clusterDyadicAge (r:ℝ) j
      2*d ≤ s → ∀ ω ∉ E j, ∀ t ∈ Ioc (0:ℝ≥0) r, (t:ℝ) ∈ Icc s (2*s) →
      U t ω ≤ M*s^(2*α-1)*((r:ℝ)/s)^γ ∧ m*s^α*(s/(r:ℝ))^γ ≤ Z t ω) :
    Q.real {ω | envelopeStop r (4^(1+3*γ)*σ^2*M/m^2*(r:ℝ)^(3*γ))
      (clusterEnvelopeValue 0 σ (1+3*γ) U Z) ω < r} ≤ e + A/(1-q) := by
  let C := 4^(1+3*γ)*σ^2*M/m^2*(r:ℝ)^(3*γ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hp : 0 < 1+3*γ := by linarith
  have hsub : {ω | envelopeStop r C (clusterEnvelopeValue 0 σ (1+3*γ) U Z) ω < r} ⊆
      early ∪ ⋃ j, E j := by
    intro ω hω
    by_contra h
    have hne : ω ∉ early := fun hω => h (Or.inl hω)
    have hn j : ω ∉ E j := fun hω => h (Or.inr (mem_iUnion.mpr ⟨j,hω⟩))
    obtain ⟨t,ht,habove⟩ := (envelopeStop_lt_horizon_iff r C _ ω).mp hω
    have ht0 : 0 < t := by
      apply lt_of_le_of_ne zero_le
      rintro e
      rw [← e] at habove
      simp [clusterEnvelopeValue, Real.zero_rpow hp.ne'] at habove
      exact habove.not_ge hC
    have htr : t ∈ Ioc (0:ℝ≥0) r := ⟨ht0,ht.le⟩
    obtain ⟨j,hj,htj⟩ := exists_cluster_dyadic_block (show (0:ℝ) < t from ht0)
      (show (t:ℝ) ≤ r from ht.le)
    let s := clusterDyadicAge (r:ℝ) j
    have hs : 0 < s := by dsimp [s,clusterDyadicAge]; positivity
    have htbound : (t:ℝ)^(1+3*γ)*σ^2*U t ω/(Z t ω)^2 ≤ C := by
      by_cases hds : 2*d ≤ s
      · obtain ⟨hU,hZ⟩ := hblock j hds ω (hn j) t htr ⟨hj.le,htj⟩
        exact cluster_drift_envelope_on_block (show 0 < (t:ℝ) from ht0) hs (show 0 < (r:ℝ) from hr)
          (by linarith only [htj,hs]) hγ hm hM (hu t ht.le ω) hU hZ
      · have htd : (t:ℝ) ≤ 4*d := by linarith only [htj,show clusterDyadicAge (r:ℝ) j < 2*d from lt_of_not_ge hds]
        obtain ⟨hU,hZ⟩ := hfirst ω hne t htr htd
        exact cluster_drift_envelope_on_block (show 0 < (t:ℝ) from ht0) hd (show 0 < (r:ℝ) from hr)
          htd hγ hm hM (hu t ht.le ω) hU hZ
    apply habove.not_ge
    simpa [clusterEnvelopeValue, max_eq_right t.coe_nonneg, mul_div_assoc, mul_assoc] using htbound
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans
    (add_le_add he (cluster_dyadic_failures_probability E hA hq hq' hprob)))

#print axioms focal_envelope_failure_probability

end RoughHeston
