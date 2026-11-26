import ActualPulseEnvelope
import SmallAgeSeparation

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace RoughHeston

/-- The quantitative reverse-tilt estimates used in the stopped
separation, with the cost and occupation budgets exposed. -/
structure PulseStoppedLaw {Ω : Type*} [MeasurableSpace Ω]
    (Q R : Measure Ω) (r : ℝ≥0) (δ mean occupation : ℝ) (env : Ω → ℝ≥0)
    (Y : Ω → ℝ) where
  stop : Ω → ℝ≥0
  energy : Ω → ℝ
  stop_measurable : Measurable stop
  energy_measurable : Measurable energy
  energy_nonnegative : ∀ᵐ ω ∂R, 0≤energy ω
  energy_integrable : Integrable energy R
  energy_mean : (∫ ω,energy ω ∂R)≤mean
  exit : ∀ ω, stop ω<r → r≤env ω → δ≤energy ω
  stopped_occupation : R.real {ω | r≤stop ω ∧ 0<Y ω}≤occupation
  total_variation : ∀ A, MeasurableSet A → |R.real A-Q.real A|≤Real.sqrt δ/2

/-- The envelope coefficient is fixed before the stopped law's
uniform cost coefficients. Then the observation age is fixed before
the mesh mass and birth event, giving a linear original-law bound. -/
theorem uniform_actual_pulse_stopped_separation
    {Ω : Type*} {m : MeasurableSpace Ω}
    {α κ a σ C₀ γ K p cU cZ cB η rCap : ℝ} {H : ℝ≥0}
    (hα : 1/2<α) (hα' : α<1) (hκ : 0≤κ) (ha : 0<a) (hH : 0<H) (hC₀ : 0<C₀)
    (hγ : 0<γ) (hK : 0≤K) (hp : 0<p) (_hcU : 0<cU) (hcZ : 0<cZ) (hcB : 0<cB)
    (hη : 0<η) (hrCap : 0<rCap) :
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
        (∫ ω,(Z (d/4).toNNReal ω)^2 ∂μ)≤C₀*ε^2 →
        Nonempty (@PulseBlockUpperMean Ω m Q (fun t => U t.toNNReal) 0 (4*d) d α K) →
        (∀ j, let s := clusterDyadicAge (r:ℝ) j
          2*d≤s → Nonempty (@PulseBlockUpperMean Ω m Q (fun t => U t.toNNReal) s (2*s) s α K)) →
        Measurable[m] Y → (∀ ω,0≤Y ω) →
        p≤Q.real {ω | cU*(r:ℝ)^(2*α-1)≤U r ω ∧ Z r ω≤cZ*(r:ℝ)^α} →
        (∀ (R : Measure Ω) [IsProbabilityMeasure R],
          @PulseStoppedLaw Ω m Q R r δ (Cenergy*(r:ℝ)^η) (Cocc*(r:ℝ)^η) env Y →
          c*ε≤P.real ({ω | cU*(r:ℝ)^(2*α-1)≤U r ω ∧ Y ω=0} ∩ birth)) := by
  let _ : MeasurableSpace Ω := m
  have hα₀ : 0<α := by linarith
  have hp4 : 0<p/4 := by positivity
  obtain ⟨Cenv,hCenv,hEnv⟩ := uniform_actual_pulse_envelope (σ := σ)
    (γ := γ) (m := m) hα hα' hκ ha hH hC₀ hγ hK hp4
  refine ⟨Cenv,hCenv,?_⟩
  intro Cenergy Cocc
  have hHr : 0<(H:ℝ) := NNReal.coe_pos.mpr hH
  have hNear : ∀ᶠ r in 𝓝[>] (0:ℝ), 0<r ∧ r<min (H:ℝ) rCap ∧
      p/2≤p-p/4-Cenergy*r^η/r^(2*η/3)-Cocc*r^η-Real.sqrt (r^(2*η/3))/2 := by
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds (lt_min hHr hrCap)),
      eventually_small_age_separation hη hp Cenergy Cocc] with r hr hl hs
    exact ⟨hr,hl,hs⟩
  obtain ⟨u,hu,huH,huSep⟩ := hNear.exists
  let r := u.toNNReal
  have hru : (r:ℝ)=u := Real.coe_toNNReal u hu.le
  have hr : 0<r := NNReal.coe_pos.mp (by simpa only [hru] using hu)
  have hrH : r≤H := NNReal.coe_le_coe.mp (by rw [hru]; exact huH.le.trans (min_le_left _ _))
  have hrC : (r:ℝ)<rCap := by rw [hru]; exact huH.trans_le (min_le_right _ _)
  let ε₀ := (u/8)^α
  let cap := cZ*(r:ℝ)^α
  have hcap : 0<cap := mul_pos hcZ (Real.rpow_pos_of_pos (NNReal.coe_pos.mpr hr) _)
  let c := cB*(p/2)/cap
  have hc : 0<c := div_pos (mul_pos hcB (by positivity)) hcap
  refine ⟨r,ε₀,c,hr,hrH,hrC,Real.rpow_pos_of_pos (by positivity) _,?_,hc,?_⟩
  · change (u/8)^α=((r:ℝ)/8)^α
    rw [hru]
  intro P _ 𝒢 birth ε M U C Y
  dsimp only
  intro hε hε₀ hBirth hP hZ₂ hEarly hLate hYm hY₀ hBurst R _ stopped
  let μ := boundaryConditionedMeasure P birth
  let Z := fractionalPulseMass ε M
  let Q := sizeBiasedLaw μ (Z r) ε
  let d := ε^(1/α)
  let δ := (r:ℝ)^(2*η/3)
  let env := envelopeStop r (Cenv*(r:ℝ)^(3*γ)) (clusterEnvelopeValue 0 σ (1+3*γ) U Z)
  have hB : 0<P birth := (ENNReal.toReal_pos_iff.mp (hcB.trans_le hBirth)).1
  let : IsProbabilityMeasure μ := boundaryConditionedMeasure_isProbability hB
  have hd : 0<d := Real.rpow_pos_of_pos hε _
  have hdR : d≤u/8 := by
    have hv := Real.rpow_le_rpow hε.le hε₀ (by positivity : 0≤1/α)
    dsimp [ε₀] at hv
    rw [← Real.rpow_mul (by positivity : 0≤u/8),one_div,mul_inv_cancel₀ hα₀.ne',
      Real.rpow_one] at hv
    simpa only [d,one_div] using hv
  have hd4 : 4*d≤(r:ℝ) := by rw [hru]; linarith
  have hδ : 0<δ := Real.rpow_pos_of_pos (NNReal.coe_pos.mpr hr) _
  obtain ⟨hZm,hZn,hZi,hZmean,_⟩ := fractional_pulse_mass_data hα₀ hα' hκ hε hd hrH hP
  let : IsProbabilityMeasure Q := sizeBiasedLaw_isProbabilityMeasure hε hZi hZn hZmean
  have hEnvelope : Q.real {ω | env ω<r}≤p/4 :=
    hEnv μ 𝒢 r ε M U C hε hrH hd4 hP hZ₂ hEarly hLate
  have hSep := stopped_burst_with_zero_probability hδ stopped.stop_measurable hYm hY₀
    stopped.energy_measurable stopped.energy_nonnegative stopped.energy_integrable
    stopped.energy_mean stopped.exit hEnvelope stopped.stopped_occupation stopped.total_variation hBurst
  have hSep' : p/2≤Q.real
      ({ω | cU*(r:ℝ)^(2*α-1)≤U r ω ∧ Z r ω≤cap} ∩ {ω | Y ω=0}) := by
    refine le_trans ?_ hSep
    simpa only [δ,hru] using huSep
  have hUm : Measurable (U r) := ((hP.variance_adapted r).mono (𝒢.le r)).measurable
  exact original_single_birth_burst hB hBirth hε hcap (by positivity) hUm hYm hZm hSep'

#print axioms uniform_actual_pulse_stopped_separation

end RoughHeston
