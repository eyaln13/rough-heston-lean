import ClusterBiasedBlockMean
import ActualBlockMassMoment
import FractionalPulseBiasPast
import ActualPulseEnvelope

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston

/-- An old-law block estimate gives an upper mean under the actual
terminal mass bias at every later observation age. -/
theorem actual_pulse_biased_block_of_old_sup
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {M U C : ℝ≥0 → Ω → ℝ}
    {α κ a ε d S K : ℝ} {H r : ℝ≥0} {m : ℕ} {R : ℝ → ℝ}
    (hα : 1/2<α) (hα' : α<1) (ha : 0≤a) (hκ : 0≤κ) (hd : 0<d) (hε : ε=d^α)
    (hdS : d≤S) (htr : (2*S).toNNReal≤r) (hr : r≤H) (hm : 0<m)
    (hP : FractionalPulseProcess P F H α κ a ε d M U C)
    (hU : ∀ t≤H, Integrable (U t) P) (hRm : Measurable R)
    (hR : ∀ x∈Ioc (0:ℝ) (H:ℝ), 0≤R x ∧ R x≤2*fractionalK α x)
    (hMean : ∀ x∈Ioc (0:ℝ) (H:ℝ), (∫ ω,U x.toNNReal ω ∂P)=
        volterraConvolution R (rectangularPulseRate ε d) x)
    (W : Ω → ℝ) (hWm : Measurable[F (2*S).toNNReal] W) (hW₀ : ∀ ω,0≤W ω)
    (hWd : ∀ t≤(2*S).toNNReal, ∀ ω,U t ω≤W ω)
    (hWi : Integrable (fun ω => W ω^(2*m)) P)
    (hWE : (∫ ω,W ω^(2*m) ∂P)≤ K*ε*S^(((2*m:ℕ):ℝ)*(2*α-1)-α)) :
    let Zc := 1+(2*a)*(4/α)*2^α/(Real.Gamma α*α)
    let Q := @sizeBiasedLaw Ω mΩ P (fractionalPulseMass ε M r) ε
    Nonempty (@PulseBlockUpperMean Ω mΩ Q (fun t => U t.toNNReal) 0 (2*S) S α
      (1+(Zc+K)/2)) := by
  let _ : MeasurableSpace Ω := mΩ
  let t := (2*S).toNNReal
  let Zc := 1+(2*a)*(4/α)*2^α/(Real.Gamma α*α)
  let β := 2*α-1
  have hS := hd.trans_le hdS
  have hε₀ : 0<ε := hε ▸ Real.rpow_pos_of_pos hd _
  have ht : (t:ℝ)=2*S := Real.coe_toNNReal _ (by positivity)
  have htH := htr.trans hr
  obtain ⟨hZm,hZpos,hZi,hZE,hZ₂⟩ := fractional_pulse_mass_data (by linarith) hα' hκ hε₀ hd htH hP
  have hQ := sizeBiasedLaw_isProbabilityMeasure hε₀ hZi hZpos hZE
  have hZm₂ := actual_block_mass_second_of_resolvent_mean (t:=t) (by linarith) hα' ha hκ hd hε
    hdS htH ht.le hP hU hRm hR hMean
  have he : S^(((2*m:ℕ):ℝ)*β-α) = (S^β)^(2*m)/S^α := by
    rw [Real.rpow_sub hS,← Real.rpow_mul_natCast hS.le,mul_comm ((2*m:ℕ):ℝ)]
  have hW' : (∫ ω,W ω^(2*m) ∂P) ≤ K*(ε/S^α)*(S^β)^(2*m) :=
    hWE.trans_eq (by change K*ε*S^(((2*m:ℕ):ℝ)*β-α)=_;rw [he];ring)
  obtain ⟨hi,heQ⟩ := GirsanovPort.sizeBiased_block_mean hm hε₀ (Real.rpow_pos_of_pos hS α)
    (Real.rpow_pos_of_pos hS β) hZm hZpos hZ₂ (hWm.mono (F.le _) le_rfl) hW₀ hZm₂ hWi hW' hQ
  obtain ⟨hI,hM⟩ := fractional_pulse_bias_past_integral (by linarith) hα' hκ hε₀ hd htr hr hP hWm.stronglyMeasurable
  refine ⟨⟨W,fun u hu ω => hWd u.toNNReal (Real.toNNReal_mono hu.2) ω,
    hI.mpr hi,ae_of_all _ hW₀,hM.le.trans (heQ.trans_eq (mul_comm _ _))⟩⟩

#print axioms actual_pulse_biased_block_of_old_sup

end RoughHeston
