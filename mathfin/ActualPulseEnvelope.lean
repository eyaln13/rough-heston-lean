import ActualPulseLowerTails
import FocalEnvelopeUniformConstants

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace RoughHeston

/-- An upper-variance estimate for a block. The affine transform
supplies the lower-mass tail separately. -/
structure PulseBlockUpperMean {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (U : ℝ → Ω → ℝ) (lo hi age α K : ℝ) where
  supU : Ω → ℝ
  dominates : ∀ t∈Icc lo hi, ∀ ω, U t ω≤supU ω
  integrable : Integrable supU Q
  nonnegative : ∀ᵐ ω ∂Q, 0≤supU ω
  mean : (∫ ω,supU ω ∂Q)≤K*age^(2*α-1)

private theorem envelopeStop_congr_path {Ω : Type*} {E F : ℝ≥0 → Ω → ℝ}
    (r : ℝ≥0) (c : ℝ) (ω : Ω) (h : ∀ t, E t ω=F t ω) :
    envelopeStop r c E ω=envelopeStop r c F ω := by
  have hS : {t : ℝ≥0 | ⊥≤t ∧ E t ω∈Ioi c}={t : ℝ≥0 | ⊥≤t ∧ F t ω∈Ioi c} := by
    ext t
    simp only [mem_ofPred_eq,h]
  have hE : (∃ t : ℝ≥0, ⊥≤t ∧ E t ω∈Ioi c) ↔ (∃ t : ℝ≥0, ⊥≤t ∧ F t ω∈Ioi c) := by
    constructor
    · rintro ⟨t,ht,he⟩
      exact ⟨t,ht,(h t) ▸ he⟩
    · rintro ⟨t,ht,he⟩
      exact ⟨t,ht,(h t).symm ▸ he⟩
  unfold envelopeStop leastGT hittingAfter
  by_cases he : ∃ t : ℝ≥0, ⊥≤t ∧ E t ω∈Ioi c
  · rw [ite_eq_left he,ite_eq_left (hE.mp he),hS]
  · rw [ite_eq_right he,ite_eq_right (he ∘ hE.mpr)]

/-- Denominator tails from the genuine pulse affine transform give
the uniform envelope. The coefficient precedes the law, filtration,
observation age, mesh mass, and block data. -/
theorem uniform_actual_pulse_envelope
    {Ω : Type*} {m : MeasurableSpace Ω}
    {α κ a C₀ γ K p σ : ℝ} {H : ℝ≥0}
    (hα : 1/2<α) (hα' : α<1) (hκ : 0≤κ) (ha : 0<a) (hH : 0<H) (hC₀ : 0<C₀)
    (hγ : 0<γ) (hK : 0≤K) (hp : 0<p) :
    ∃ Cenv : ℝ, 0≤Cenv ∧ ∀ (μ : Measure Ω) [IsProbabilityMeasure μ]
      (𝒢 : Filtration ℝ≥0 m) (r : ℝ≥0) (ε : ℝ) (M U C : ℝ≥0 → Ω → ℝ),
      let d := ε^(1/α)
      let Z := fractionalPulseMass ε M
      let Q := @sizeBiasedLaw Ω m μ (Z r) ε
      0<ε → r≤H → 4*d≤(r:ℝ) →
      FractionalPulseProcess μ 𝒢 H α κ a ε d M U C →
      (∫ ω,(Z (d/4).toNNReal ω)^2 ∂μ)≤C₀*ε^2 →
      Nonempty (@PulseBlockUpperMean Ω m Q (fun t => U t.toNNReal) 0 (4*d) d α K) →
      (∀ j, let s := clusterDyadicAge (r:ℝ) j
        2*d≤s → Nonempty (@PulseBlockUpperMean Ω m Q (fun t => U t.toNNReal) s (2*s) s α K)) →
      Q.real {ω | envelopeStop r (Cenv*(r:ℝ)^(3*γ))
        (clusterEnvelopeValue 0 σ (1+3*γ) U Z) ω<r}≤p := by
  let _ : MeasurableSpace Ω := m
  have hα₀ : 0<α := by linarith
  obtain ⟨D,hD,hTail⟩ := uniform_actual_fractional_pulse_mass_tails (Ω := Ω)
    (m := m) hα hα' hκ ha hH hC₀
  obtain ⟨Cenv,hCenv,hEnvelope⟩ := uniform_focal_envelope_of_block_estimates (Ω := Ω)
    (σ := σ) hα₀ hα' hγ hK hD.le hp
  refine ⟨Cenv,hCenv,?_⟩
  intro μ _ 𝒢 r ε M U C
  dsimp only
  intro hε hr hd4 hP hZ2 hEarly hLate
  let d := ε^(1/α)
  let Z := fractionalPulseMass ε M
  let Q := sizeBiasedLaw μ (Z r) ε
  have hd : 0<d := Real.rpow_pos_of_pos hε _
  have hεd : ε=d^α := by
    dsimp [d]
    rw [← Real.rpow_mul hε.le,one_div,inv_mul_cancel₀ hα₀.ne',Real.rpow_one]
  obtain ⟨hZm,hZn,hZi,hZmean,_⟩ := fractional_pulse_mass_data hα₀ hα' hκ hε hd hr hP
  let : IsProbabilityMeasure Q := sizeBiasedLaw_isProbabilityMeasure hε hZi hZn hZmean
  have hQμ : Q ≪ μ := withDensity_absolutelyContinuous μ _
  let good (ω : Ω) : Prop := ∀ s∈Icc (0:ℝ) (H:ℝ),
    Z s.toNNReal ω=ε-(ε/d)*min s d+volterraConvolution (fractionalL α)
      (fun u => U u.toNNReal ω) s+κ*clusterAccumulatedVariance (fun u => U u.toNNReal) s ω
  have hGood : ∀ᵐ ω ∂Q, good ω :=
    hQμ.ae_le (fractional_pulse_mass_identity hα₀ hα' hε.le hd hP)
  classical
  let U' (s : ℝ≥0) (ω : Ω) := if good ω then U s ω else 0
  let Z' (s : ℝ≥0) (ω : Ω) := if good ω then Z s ω else ε-(ε/d)*min (s:ℝ) d
  have hU'c (ω : Ω) : Continuous (fun t => U' t ω) := by
    by_cases hw : good ω
    · simpa only [U',ite_eq_left hw] using hP.variance_continuous ω
    · simpa only [U',ite_eq_right hw] using (continuous_const : Continuous (fun _ : ℝ≥0 => (0:ℝ)))
  have hU'n (s : ℝ≥0) (_ : s≤r) (ω : Ω) : 0≤U' s ω := by
    by_cases hw : good ω
    · simpa only [U',ite_eq_left hw] using hP.variance_nonnegative s ω
    · simp [U',hw]
  have hZ' (s : ℝ≥0) (hs : s≤r) (ω : Ω) :
      Z' s ω=ε-(ε/d)*min (s:ℝ) d+
        volterraConvolution (fractionalL α) (fun u => U' u.toNNReal ω) (s:ℝ)+
        κ*clusterAccumulatedVariance (fun u => U' u.toNNReal) (s:ℝ) ω := by
    by_cases hw : good ω
    · simpa only [U',Z',ite_eq_left hw,Real.toNNReal_coe,clusterAccumulatedVariance] using
        hw (s:ℝ) ⟨NNReal.coe_nonneg _, NNReal.coe_le_coe.mpr (hs.trans hr)⟩
    · simp [U',Z',hw,volterraConvolution,clusterAccumulatedVariance]
  have hMassTail := hTail μ 𝒢 r ε M U C hε hr (by linarith [hd4,hd]) hP hZ2
  have hBuild {lo hi massAge age : ℝ}
      (hSup : PulseBlockUpperMean Q (fun t => U t.toNNReal) lo hi age α K)
      (hMtail : ∀ x,0<x → x≤1 →
        Q.real {ω | clusterAccumulatedVariance (fun t => U t.toNNReal) massAge ω≤x*massAge^(2*α)}
          ≤D*Real.sqrt x) :
      FocalBlockEstimate Q (fun t => U' t.toNNReal) lo hi massAge age α K D := by
    let S (ω : Ω) := max (hSup.supU ω) 0
    have hSeq : hSup.supU =ᵐ[Q] S := hSup.nonnegative.mono fun ω hw =>
      (max_eq_left hw).symm
    refine ⟨S,?_,hSup.integrable.congr hSeq,ae_of_all _ (fun _ => le_max_right _ _),?_,?_⟩
    · intro t ht ω
      by_cases hw : good ω
      · have hh : U' t.toNNReal ω≤hSup.supU ω := by
          simpa only [U',ite_eq_left hw] using hSup.dominates t ht ω
        exact hh.trans (le_max_left _ _)
      · simp only [U',ite_eq_right hw]
        exact le_max_right _ _
    · rw [← integral_congr_ae hSeq]
      exact hSup.mean
    · intro x hx hx₁
      have hSets : {ω | clusterAccumulatedVariance (fun t => U' t.toNNReal) massAge ω≤x*massAge^(2*α)}
          =ᵐ[Q] {ω | clusterAccumulatedVariance (fun t => U t.toNNReal) massAge ω≤x*massAge^(2*α)} := by
        filter_upwards [hGood] with ω hw
        have hh : (fun t : ℝ => U' t.toNNReal ω)=(fun t : ℝ => U t.toNNReal ω) := by
          funext t
          simp [U',hw]
        change ((∫ t in Ioc 0 massAge,U' t.toNNReal ω)≤x*massAge^(2*α)) =
          ((∫ t in Ioc 0 massAge,U t.toNNReal ω)≤x*massAge^(2*α))
        rw [hh]
      exact (measureReal_congr hSets).trans_le (hMtail x hx hx₁)
  obtain ⟨hEarly⟩ := hEarly
  have he := hBuild hEarly hMassTail.1
  have hl (j : ℕ) (hds : 2*d≤clusterDyadicAge (r:ℝ) j) :
      let s := clusterDyadicAge (r:ℝ) j
      FocalBlockEstimate Q (fun t => U' t.toNNReal) s (2*s) s s α K D := by
    let s := clusterDyadicAge (r:ℝ) j
    have hs₀ : 0≤s := by dsimp [s,clusterDyadicAge]; positivity
    have hsr : s≤(r:ℝ) := by
      dsimp [s,clusterDyadicAge]
      exact mul_le_of_le_one_right (NNReal.coe_nonneg _) (pow_le_one₀ (by norm_num) (by norm_num))
    have hs : s.toNNReal≤r := Real.toNNReal_le_iff_le_coe.mpr hsr
    have hsc : (s.toNNReal:ℝ)=s := Real.coe_toNNReal s hs₀
    let hUpper := Classical.choice (hLate j hds)
    apply hBuild hUpper
    intro x hx hx₁
    have hds' : 2*d≤(s.toNNReal:ℝ) := by simpa only [hsc] using hds
    have hh := hMassTail.2 s.toNNReal hds' hs x hx hx₁
    rw [hsc] at hh
    exact hh
  have hEnvelopeBound := hEnvelope Q r d ε κ U' Z' hd hd4 hεd hκ hU'c hU'n hZ' he
    (fun j hj => hl j hj)
  have heq : {ω | envelopeStop r (Cenv*(r:ℝ)^(3*γ))
      (clusterEnvelopeValue 0 σ (1+3*γ) U Z) ω<r} =ᵐ[Q]
      {ω | envelopeStop r (Cenv*(r:ℝ)^(3*γ))
      (clusterEnvelopeValue 0 σ (1+3*γ) U' Z') ω<r} := by
    filter_upwards [hGood] with ω hw
    have hh := envelopeStop_congr_path (E := clusterEnvelopeValue 0 σ (1+3*γ) U Z)
      (F := clusterEnvelopeValue 0 σ (1+3*γ) U' Z') r (Cenv*(r:ℝ)^(3*γ)) ω
        (fun t => by simp [clusterEnvelopeValue,U',Z',hw])
    change (_<r) = (_<r)
    rw [hh]
  exact (measureReal_congr heq).trans_le hEnvelopeBound

#print axioms uniform_actual_pulse_envelope

end RoughHeston
