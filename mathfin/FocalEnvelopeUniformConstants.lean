import FocalEarlyPulseBlock

/-! The simultaneous choice of upper and lower thresholds in all pulse
blocks. The constants are independent of the immigration mesh. -/

open Set MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston

theorem choose_focal_envelope_thresholds {K D q p : ℝ} (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hq : q < 1) (hp : 0 < p) :
    ∃ c M : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < M ∧
      (K/M+D*Real.sqrt c) + (K/M+D*Real.sqrt c)/(1-q) ≤ p := by
  let A := 1+(1-q)⁻¹
  have hA : 0 < A := by dsimp [A]; positivity
  let y := min 1 (p/(2*A*(D+1)))
  have hy : 0 < y := lt_min zero_lt_one (div_pos hp (by positivity))
  let M := 2*A*(K+1)/p
  have hM : 0 < M := div_pos (by positivity) hp
  refine ⟨y^2,M,sq_pos_of_pos hy,?_,hM,?_⟩
  · calc _ ≤ (1:ℝ)^2 := pow_le_pow_left₀ hy.le (min_le_left ..) _
         _ = _ := one_pow _
  rw [Real.sqrt_sq hy.le]
  have hy' := (le_div_iff₀ (by positivity : 0 < 2*A*(D+1))).mp
    (show y ≤ p/(2*A*(D+1)) from min_le_right ..)
  have hm : (K/M)*A ≤ p/2 := by
    change K/(2*A*(K+1)/p)*A ≤ p/2
    field_simp
    nlinarith
  have h := mul_nonneg hy.le hA.le
  calc _ = (K/M+D*y)*A := by dsimp [A]; ring
       _ ≤ p := by nlinarith only [hy',hm,h]

/-- Actual upper-envelope and accumulated-variance estimates on one
age block. The first observation time can be zero on the early block. -/
structure FocalBlockEstimate {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (U : ℝ → Ω → ℝ) (lo hi massAge reference α K D : ℝ) where
  supU : Ω → ℝ
  dominates : ∀ t ∈ Icc lo hi, ∀ ω, U t ω ≤ supU ω
  integrable : Integrable supU Q
  nonnegative : ∀ᵐ ω ∂Q, 0 ≤ supU ω
  mean : (∫ ω,supU ω ∂Q) ≤ K*reference^(2*α-1)
  tail : ∀ x, 0 < x → x ≤ 1 →
    Q.real {ω | clusterAccumulatedVariance U massAge ω ≤ x*massAge^(2*α)} ≤ D*Real.sqrt x

/-- The single-block estimates yield the required envelope probability
at any specified error level. The output coefficient is common to all
families with the prescribed constants K and D. -/
theorem uniform_focal_envelope_of_block_estimates {Ω : Type*} [MeasurableSpace Ω]
    {α γ K D p σ : ℝ} (hα : 0 < α) (hα' : α < 1) (hγ : 0 < γ)
    (hK : 0 ≤ K) (hD : 0 ≤ D) (hp : 0 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : Measure Ω) [IsProbabilityMeasure Q] (r : ℝ≥0)
      (d ε κ : ℝ) (U Z : ℝ≥0 → Ω → ℝ),
      0 < d → 4*d ≤ (r:ℝ) → ε = d^α → 0 ≤ κ →
      (∀ ω, Continuous (fun t => U t ω)) →
      (∀ t ≤ r, ∀ ω, 0 ≤ U t ω) →
      (∀ t ≤ r, ∀ ω, Z t ω = ε-ε/d*min (t:ℝ) d+
        volterraConvolution (fractionalL α) (fun s => U s.toNNReal ω) t+
        κ*clusterAccumulatedVariance (fun s => U s.toNNReal) t ω) →
      FocalBlockEstimate Q (fun t => U t.toNNReal) 0 (4*d) (d/4) d α K D →
      (∀ j, let s := clusterDyadicAge (r:ℝ) j
        2*d ≤ s → FocalBlockEstimate Q (fun t => U t.toNNReal) s (2*s) s s α K D) →
      Q.real {ω | envelopeStop r (C*(r:ℝ)^(3*γ))
        (clusterEnvelopeValue 0 σ (1+3*γ) U Z) ω < r} ≤ p := by
  let q := (1/2:ℝ)^(γ/2)
  have hq : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by positivity)
  obtain ⟨c,M,hc,hc1,hM,hcost⟩ := choose_focal_envelope_thresholds hK hD hq1 hp
  let m₁ := min (3/4) ((4:ℝ)^(-α)/Real.Gamma (1-α)*c/(4:ℝ)^(2*α))
  let m₂ := (2:ℝ)^(-α)/Real.Gamma (1-α)*c
  let m := min m₁ m₂
  have hG := Real.Gamma_pos_of_pos (sub_pos.mpr hα')
  have hm : 0 < m := by dsimp [m,m₁,m₂]; positivity
  refine ⟨4^(1+3*γ)*σ^2*M/m^2,by positivity,?_⟩
  intro Q hQ r d ε κ U Z hd hd4 hε hκ huc hn hz early late
  let U' (t : ℝ) := U t.toNNReal
  let Z' (t : ℝ) := Z t.toNNReal
  let A (t : ℝ) := ε/d*min t d
  have hdr : d ≤ (r:ℝ) := by linarith
  have hr : 0 < (r:ℝ) := hd.trans_le hdr
  have heps : 0 < ε := hε ▸ Real.rpow_pos_of_pos hd _
  have hU (ω : Ω) : Continuous (fun t => U' t ω) := (huc ω).comp continuous_real_toNNReal
  have hN (t : ℝ) (ht : t ∈ Icc (0:ℝ) (r:ℝ)) (ω : Ω) : 0 ≤ U' t ω :=
    hn t.toNNReal (Real.toNNReal_le_iff_le_coe.mpr ht.2) ω
  have hZ (t : ℝ) (ht : t ∈ Icc (0:ℝ) (r:ℝ)) (ω : Ω) : Z' t ω = ε - A t +
      volterraConvolution (fractionalL α) (fun v => U' v ω) t + κ*clusterAccumulatedVariance U' t ω := by
    simpa [U',Z',A,Real.coe_toNNReal t ht.1] using hz t.toNNReal (Real.toNNReal_le_iff_le_coe.mpr ht.2) ω
  have hA (t : ℝ) (_ : t ∈ Icc (0:ℝ) (r:ℝ)) : A t ≤ ε := by
    calc _ ≤ ε/d*d := mul_le_mul_of_nonneg_left (min_le_right ..) (div_nonneg heps.le hd.le)
         _ = ε := div_mul_cancel₀ _ hd.ne'
  obtain ⟨E,he,hfirst⟩ := focal_early_pulse_block (U := U') (Z := Z') hd hdr hα hα' hκ hε hγ.le hc hc1 hM hU
    (fun t ht => hN t ⟨ht.1,ht.2.trans hd4⟩)
    (fun t ht => hZ t ⟨ht.1,ht.2.trans hd4⟩)
    early.dominates early.integrable early.nonnegative early.mean early.tail
  let B := K/M+D*Real.sqrt c
  have hB : 0 ≤ B := add_nonneg (div_nonneg hK hM.le) (mul_nonneg hD (Real.sqrt_nonneg _))
  have hP (j : ℕ) : ∃ E : Set Ω, Q.real E ≤ B*q^j ∧
      ∀ ω ∉ E, ∀ t ∈ Ioc (0:ℝ≥0) r,
        let s := clusterDyadicAge (r:ℝ) j
        2*d ≤ s → (t:ℝ) ∈ Icc s (2*s) →
        U t ω ≤ M*s^(2*α-1)*((r:ℝ)/s)^γ ∧ m*s^α*(s/(r:ℝ))^γ ≤ Z t ω := by
    let s := clusterDyadicAge (r:ℝ) j
    have hs : 0 < s := by dsimp [s,clusterDyadicAge]; positivity
    by_cases hds : 2*d ≤ s
    · let data := late j hds
      obtain ⟨E,hprob,hgood⟩ := focal_postpulse_block (U := U') (Z := Z') hr hα hα' hκ hγ hc hc1 hM hD hK j
        hU hN hA hZ data.dominates data.integrable data.nonnegative data.mean data.tail
      refine ⟨E,hprob,?_⟩
      intro ω hω t ht
      dsimp only
      intro _ hts
      obtain ⟨h₁,h₂⟩ := hgood ω hω t ⟨ht.1,ht.2⟩ hts
      have h₂' : m₂*s^α*(s/(r:ℝ))^γ ≤ Z t ω := by simpa [m₂,s,Z'] using h₂
      refine ⟨by simpa [U',s] using h₁, le_trans ?_ h₂'⟩
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_right m₁ m₂)
        (Real.rpow_nonneg hs.le _)) (Real.rpow_nonneg (div_nonneg hs.le hr.le) _)
    · exact ⟨∅, by simp [mul_nonneg hB (pow_nonneg hq.le j)], by intro ω _ t ht; dsimp only; intro h; exact (hds h).elim⟩
  choose bad hbad hgood using hP
  apply (focal_envelope_failure_probability (Q := Q) (r := r) hr hd hγ.le hm hM.le
    hB hq.le hq1 hn E bad he hbad ?_ (fun j hds ω hω t ht hts => hgood j ω hω t ht hds hts)).trans hcost
  intro ω hω t ht htd
  obtain ⟨h₁,h₂⟩ := hfirst ω hω t ⟨t.coe_nonneg,htd⟩
  have h₂' : m₁*d^α*(d/(r:ℝ))^γ ≤ Z t ω := by simpa [m₁,Z'] using h₂
  exact ⟨by simpa [U'] using h₁,(mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (min_le_left m₁ m₂) (Real.rpow_nonneg hd.le _))
    (Real.rpow_nonneg (div_nonneg hd.le hr.le) _)).trans h₂'⟩

#print axioms choose_focal_envelope_thresholds
#print axioms uniform_focal_envelope_of_block_estimates

end RoughHeston
