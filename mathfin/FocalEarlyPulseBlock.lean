import FocalPostpulseBlock

/-! Control on the single initial block, including the ages before any
integrated-variance lower-tail estimate is needed. -/

open Set MeasureTheory Filter
open scoped Topology

namespace RoughHeston

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]

theorem focal_early_pulse_block {r d α γ c M D K κ ε : ℝ}
    (hd : 0 < d) (hdr : d ≤ r) (hα : 0 < α) (hα' : α < 1)
    (hκ : 0 ≤ κ) (hε : ε=d^α) (hγ : 0 ≤ γ) (hc : 0 < c) (hc1 : c ≤ 1)
    (hM : 0 < M) {U Z : ℝ → Ω → ℝ} {S : Ω → ℝ}
    (huc : ∀ ω, Continuous (fun t => U t ω)) (hn : ∀ t ∈ Icc 0 (4*d), ∀ ω, 0 ≤ U t ω)
    (hz : ∀ t ∈ Icc 0 (4*d), ∀ ω, Z t ω = ε-ε/d*min t d+
      volterraConvolution (fractionalL α) (fun v => U v ω) t+
      κ*clusterAccumulatedVariance U t ω)
    (hsup : ∀ t ∈ Icc 0 (4*d), ∀ ω, U t ω ≤ S ω)
    (hi : Integrable S Q) (hnon : ∀ᵐ ω ∂Q, 0 ≤ S ω) (hmean : (∫ ω,S ω ∂Q) ≤ K*d^(2*α-1))
    (hlower : ∀ x, 0 < x → x ≤ 1 →
      Q.real {ω | clusterAccumulatedVariance U (d/4) ω ≤ x*(d/4)^(2*α)} ≤ D*Real.sqrt x) :
    let m := min (3/4) ((4:ℝ)^(-α)/Real.Gamma (1-α)*c/(4:ℝ)^(2*α))
    ∃ E : Set Ω, Q.real E ≤ K/M+D*Real.sqrt c ∧
      ∀ ω ∉ E, ∀ t ∈ Icc 0 (4*d), U t ω ≤ M*d^(2*α-1)*(r/d)^γ ∧
        m*d^α*(d/r)^γ ≤ Z t ω := by
  dsimp only
  let low := {ω | clusterAccumulatedVariance U (d/4) ω ≤ c*(d/4)^(2*α)}
  let high := {ω | M*d^(2*α-1) < S ω}
  refine ⟨high ∪ low, ?_, ?_⟩
  · have h := cluster_block_failures (u := d^(2*α-1)) (j := (d/4)^(2*α))
      (Real.rpow_pos_of_pos hd _) (Real.rpow_pos_of_pos (by positivity) _)
      (w := 1) zero_lt_one le_rfl hc hc1 hM hnon hi hmean hlower
    simpa [high,low] using h
  · intro ω he t ht
    have htop : S ω ≤ M*d^(2*α-1) := le_of_not_gt fun h => he (Or.inl h)
    have hlo : c*(d/4)^(2*α) ≤ clusterAccumulatedVariance U (d/4) ω :=
      (lt_of_not_ge (fun h => he (Or.inr h))).le
    have hZ := rectangular_focal_mass_early_block hα hα' hκ hd hε (huc ω)
      (fun v hv => hn v hv ω) (fun v hv => hz v hv ω) hlo t ht
    have hrate : 1 ≤ (r/d)^γ := Real.one_le_rpow ((one_le_div hd).mpr hdr) hγ
    have hrate' : (d/r)^γ ≤ 1 :=
      Real.rpow_le_one (div_nonneg hd.le (hd.trans_le hdr).le) ((div_le_one (hd.trans_le hdr)).mpr hdr) hγ
    refine ⟨(hsup t ht ω).trans (htop.trans (le_mul_of_one_le_right (by positivity) hrate)), ?_⟩
    apply (mul_le_of_le_one_right _ hrate').trans hZ
    apply mul_nonneg _ (Real.rpow_nonneg hd.le _)
    exact le_min (by norm_num) (by
      have hG := (Real.Gamma_pos_of_pos (sub_pos.mpr hα')).le
      positivity)

#print axioms focal_early_pulse_block

end RoughHeston
