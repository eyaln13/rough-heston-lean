import ActualPulseStoppedSeparation
import ActualPulseEarlyMassMoment
import ActualPulseFullBlockAdapter

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace RoughHeston

/-- The resolvent first moment supplies the early mass square, and a
full-block supremum bound supplies both envelope blocks. The resulting
separation keeps the reverse-law budgets and original birth event explicit. -/
theorem uniform_actual_pulse_separation_of_resolvent_mean
    {Ω : Type*} {m : MeasurableSpace Ω}
    {α κ a σ γ K p cU cZ cB η rCap : ℝ} {H : ℝ≥0} {L : ℝ → ℝ}
    (hα : 1/2<α) (hα' : α<1) (hκ : 0≤κ) (ha : 0<a) (hH : 0<H)
    (hγ : 0<γ) (hK : 0≤K) (hp : 0<p) (hcU : 0<cU) (hcZ : 0<cZ) (hcB : 0<cB)
    (hη : 0<η) (hrCap : 0<rCap)
    (hLm : Measurable L) (hL : ∀ t∈Ioc (0:ℝ) (H:ℝ),0≤L t ∧ L t≤2*fractionalK α t) :
    ∃ Cenv : ℝ, 0≤Cenv ∧ ∀ Cenergy Cocc : ℝ,
      ∃ (r : ℝ≥0) (ε₀ c : ℝ), 0<r ∧ r≤H ∧ (r:ℝ)<rCap ∧ 0<ε₀ ∧ ε₀=((r:ℝ)/8)^α ∧ 0<c ∧
      ∀ (P : Measure Ω) [IsProbabilityMeasure P] (𝒢 : Filtration ℝ≥0 m)
        (birth : Set Ω) (ε : ℝ) (M U C : ℝ≥0 → Ω → ℝ) (Y : Ω → ℝ),
        let μ := @boundaryConditionedMeasure Ω m P birth
        let d := ε^(1/α)
        let Z := fractionalPulseMass ε M
        let Q := @sizeBiasedLaw Ω m μ (Z r) ε
        let env := envelopeStop r (Cenv*(r:ℝ)^(3*γ)) (clusterEnvelopeValue 0 σ (1+3*γ) U Z)
        let δ := (r:ℝ)^(2*η/3)
        0<ε → ε≤ε₀ → cB≤P.real birth →
        FractionalPulseProcess μ 𝒢 H α κ a ε d M U C →
        (∀ t≤H, Integrable (U t) μ) →
        (∀ t∈Ioc (0:ℝ) (H:ℝ), (∫ ω,U t.toNNReal ω ∂μ)=
          volterraConvolution L (rectangularPulseRate ε d) t) →
        (∀ s, d≤s → 2*s≤(r:ℝ) →
          Nonempty (@PulseBlockUpperMean Ω m Q (fun t => U t.toNNReal) 0 (2*s) s α K)) →
        Measurable[m] Y → (∀ ω,0≤Y ω) →
        p≤Q.real {ω | cU*(r:ℝ)^(2*α-1)≤U r ω ∧ Z r ω≤cZ*(r:ℝ)^α} →
        (∀ (R : Measure Ω) [IsProbabilityMeasure R],
          @PulseStoppedLaw Ω m Q R r δ (Cenergy*(r:ℝ)^η) (Cocc*(r:ℝ)^η) env Y →
          c*ε≤P.real ({ω | cU*(r:ℝ)^(2*α-1)≤U r ω ∧ Y ω=0} ∩ birth)) := by
  let _ : MeasurableSpace Ω := m
  have hα₀ : 0<α := by linarith
  let K' := K*(2:ℝ)^(2*α-1)
  have hK' : 0≤K' := mul_nonneg hK (by positivity)
  let C₀ := 1+(2*a)*(4/(Real.Gamma α*α))/4
  have hC₀ : 0<C₀ := by
    dsimp [C₀]
    exact add_pos_of_pos_of_nonneg zero_lt_one (by positivity)
  obtain ⟨Cenv,hCenv,hSep⟩ := uniform_actual_pulse_stopped_separation
    (σ := σ) (m := m) hα hα' hκ ha hH hC₀ hγ hK' hp hcU hcZ hcB hη hrCap
  refine ⟨Cenv,hCenv,?_⟩
  intro Cenergy Cocc
  obtain ⟨r,ε₀,c,hr,hrH,hrCap,hε₀,hε₀Eq,hc,hData⟩ := hSep Cenergy Cocc
  refine ⟨r,ε₀,c,hr,hrH,hrCap,hε₀,hε₀Eq,hc,?_⟩
  intro P _ 𝒢 birth ε M U C Y
  dsimp only
  intro hε hcut hBirth hP hUi hMean hFull hYm hYn hBurst
  let d := ε^(1/α)
  have hd : 0<d := Real.rpow_pos_of_pos hε _
  have hεd : ε=d^α := by
    dsimp [d]
    rw [← Real.rpow_mul hε.le,one_div,inv_mul_cancel₀ hα₀.ne',Real.rpow_one]
  have hSmall : d≤(r:ℝ)/8 := by
    rw [hε₀Eq] at hcut
    have he := Real.rpow_le_rpow hε.le hcut (by positivity : 0≤1/α)
    rw [← Real.rpow_mul (by positivity : 0≤(r:ℝ)/8),one_div,
      mul_inv_cancel₀ hα₀.ne',Real.rpow_one] at he
    simpa only [d,one_div] using he
  have hd4 : 4*d≤(r:ℝ) := by linarith [NNReal.coe_nonneg r]
  have hdH : d/4≤(H:ℝ) := by
    linarith [NNReal.coe_le_coe.mpr hrH]
  let μ := boundaryConditionedMeasure P birth
  have hpos : 0<P birth := (ENNReal.toReal_pos_iff.mp (hcB.trans_le hBirth)).1
  let : IsProbabilityMeasure μ := boundaryConditionedMeasure_isProbability hpos
  have hZ₂ := actual_pulse_early_mass_second_of_resolvent_mean hα₀ hα' ha.le hd hεd hdH
    hP hUi hLm hL hMean
  obtain ⟨_,hEarly,hLate⟩ := actual_pulse_block_means_of_full hα hK hd hd4 hFull
  exact hData P 𝒢 birth ε M U C Y hε hcut hBirth hP hZ₂ hEarly hLate hYm hYn hBurst

#print axioms uniform_actual_pulse_separation_of_resolvent_mean

end RoughHeston
