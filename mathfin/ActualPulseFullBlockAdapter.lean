import ActualPulseEnvelope

open MeasureTheory Set Filter
open scoped Topology NNReal

namespace RoughHeston

/-- A full past block controls the early and every late envelope
block, with one deterministic change of the upper-mean coefficient. -/
theorem actual_pulse_block_means_of_full
    {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} {U : ℝ → Ω → ℝ}
    {α K d r : ℝ} (hα : 1/2<α) (hK : 0≤K) (hd : 0<d) (hadr : 4*d≤r)
    (hFull : ∀ s, d≤s → 2*s≤r → Nonempty (PulseBlockUpperMean Q U 0 (2*s) s α K)) :
    let K' := K*(2:ℝ)^(2*α-1)
    0≤K' ∧
    Nonempty (PulseBlockUpperMean Q U 0 (4*d) d α K') ∧
    ∀ j, let s := clusterDyadicAge r j
      2*d≤s → Nonempty (PulseBlockUpperMean Q U s (2*s) s α K') := by
  let β := 2*α-1
  let K' := K*(2:ℝ)^β
  have hβ : 0≤β := by dsimp [β]; linarith
  have hK' : 0≤K' := mul_nonneg hK (by positivity)
  have hKK : K≤K' := by
    have hpow : 1≤(2:ℝ)^β := by
      simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num : (0:ℝ)≤1) (by norm_num) hβ
    exact le_mul_of_one_le_right hK hpow
  refine ⟨hK',?_,?_⟩
  · obtain ⟨E⟩ := hFull (2*d) (by linarith) (by linarith)
    refine ⟨⟨E.supU,?_,E.integrable,E.nonnegative,?_⟩⟩
    · intro t ht ω
      exact E.dominates t ⟨ht.1,by linarith [ht.2]⟩ ω
    · refine E.mean.trans_eq ?_
      change K*(2*d)^β=K'*d^β
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hd.le]
      dsimp [K']
      ring
  · intro j
    dsimp only
    intro hds
    let s := clusterDyadicAge r j
    change 2*d≤s at hds
    change Nonempty (PulseBlockUpperMean Q U s (2*s) s α K')
    have hr : 0≤r := (by positivity : 0≤4*d).trans hadr
    have hsr : 2*s≤r := by
      have hp : (1/2:ℝ)^j≤1 := pow_le_one₀ (by norm_num) (by norm_num)
      dsimp [s,clusterDyadicAge]
      rw [pow_succ]
      convert mul_le_of_le_one_right hr hp using 1
      ring
    have hs : 0≤s := by dsimp [s,clusterDyadicAge]; positivity
    obtain ⟨E⟩ := hFull s (by linarith [hd]) hsr
    refine ⟨⟨E.supU,?_,E.integrable,E.nonnegative,?_⟩⟩
    · exact fun t ht ω => E.dominates t ⟨hs.trans ht.1,ht.2⟩ ω
    · exact E.mean.trans (mul_le_mul_of_nonneg_right hKK (Real.rpow_nonneg hs _))

#print axioms actual_pulse_block_means_of_full

end RoughHeston
