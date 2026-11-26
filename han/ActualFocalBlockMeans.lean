import RectangularPulseBlockSup
import ActualPulseBiasedBlock
import FocalPulseDynamics
import FocalPulseVerifiedBurst
import ClusterDominatedMean

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Interval

namespace RoughHeston.GirsanovPort

set_option maxHeartbeats 1400000 in
/-- A fractional pulse with its genuine square bracket and an orthogonal
auxiliary motion satisfies the full-block upper-mean hypothesis under its
terminal size bias, uniformly over all meshes and all laws. -/
theorem uniform_focal_biased_block_means_of_regular_inverse {α κ σ : ℝ} {H : ℝ≥0}
    (hα : 1/2<α) (hα' : α<1) (hκ : 0≤κ) (hσ : 0≤σ) (hH : 0<H)
    (hR : ∀ x∈Ioc 0 (H:ℝ), 0≤fractionalSecondKindResolvent α κ x ∧
      fractionalSecondKindResolvent α κ x≤2*fractionalK α x) :
    ∃ K : ℝ, 0≤K ∧ ∀ {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
      [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ} {U M C W : ℝ≥0 → Ω → ℝ}
      {ε d : ℝ}, 0<d → ε=d^α →
      (∀ N : Set Ω, MeasurableSet N → P N=0 → MeasurableSet[F 0] N) →
      FractionalPulseProcess P F H α κ (σ^2/2) ε d M U C →
      (∀ᵐ ω ∂P, ∀ t≤H, C t ω = ∫ s in (0:ℝ)..(t:ℝ), σ^2*U s.toNNReal ω) →
      FocalPulseRegularity P U →
      Martingale W F P → (∀ t, MemLp (W t) 2 P) → (∀ᵐ ω ∂P, Continuous (fun t => W t ω)) →
      Martingale (fun t ω => W t ω*W t ω-((min t H:ℝ≥0):ℝ)) F P →
      Martingale (fun t => W t*M t) F P →
      ∀ r : ℝ≥0, r≤H → ∀ S : ℝ, d≤S → 2*S≤(r:ℝ) →
      Nonempty (@PulseBlockUpperMean Ω mΩ (@sizeBiasedLaw Ω mΩ P (fractionalPulseMass ε M r) ε)
        (fun t => U t.toNNReal) 0 (2*S) S α K) := by
  obtain ⟨n,hn,K,hK,hSup⟩ := rectangularPulse_uniform_old_block_sup (κ:=κ) (σ:=σ) hα hα' hH
  let Kz := 1+(2*(σ^2/2))*(4/α)*2^α/(Real.Gamma α*α)
  have hapos : 0<α := by linarith
  have hg := Real.Gamma_pos_of_pos hapos
  have hz : 0≤Kz := by dsimp [Kz];positivity
  refine ⟨1+(Kz+K)/2,by positivity,?_⟩
  intro Ω mΩ P inst F U M C W ε d hd hε hnull hP hCe hReg hW hW₂ hWc hWsq hWM r hr S hdS hs
  have hε₀ : 0≤ε := hε ▸ Real.rpow_nonneg hd.le _
  have hU := hP.variance_adapted
  have hUm (t : ℝ≥0) : Measurable (U t) := (hU t).measurable.mono (F.le t) le_rfl
  have hUp : IsStronglyPredictable F U := hU.isStronglyPredictable_of_leftContinuous
    (fun ω t => (hP.variance_continuous ω).continuousAt.continuousWithinAt)
  have hUc : ∀ᵐ ω ∂P, Continuous (fun t => U t ω) := ae_of_all _ hP.variance_continuous
  have hUci : ∀ᵐ ω ∂P, ContinuousOn (fun t => U t ω) (Icc 0 H) :=
    hUc.mono (fun ω hw => hw.continuousOn)
  have hIc := hReg.mean_continuous
  obtain ⟨hUi,⟨_,hMean⟩,v,hvC,hvU⟩ := hReg
  obtain ⟨B,hB₂,hB,hB₀,hBc,hclock,hcut,_⟩ := focal_cluster_has_own_unit_clock_driver hσ
    hP.martingale hP.martingale_memLp (ae_of_all _ fun ω => (hP.martingale_continuous ω).continuousOn)
    hP.martingale_zero hP.compensated_square hCe hW hW₂ hWc hWsq hWM hUp hU hUci
    hP.variance_nonnegative hUi hMean
  have hEq := rectangularPulse_L2_equation_of_samplewise_inverse hα hα' hH hε₀ hd hσ
    hB₂ hB hclock hUp hU hUci hP.variance_nonnegative hUi hMean hcut v hvC.stronglyMeasurable
    hvC.continuousOn hvU (fractionalPulse_inverse_at hP)
  let t := (2*S).toNNReal
  have hS := hd.trans_le hdS
  have ht : 0<t := Real.toNNReal_pos.mpr (by positivity)
  have het : (t:ℝ)=2*S := Real.coe_toNNReal _ (by positivity)
  have htr : t≤r := Real.toNNReal_le_iff_le_coe.mpr hs
  obtain ⟨V,hVm,hV₀,hVd,hVi,hVE⟩ := hSup hd hε hnull hB₂ hB hBc hB₀ hclock hUp
    hP.variance_nonnegative hUi hMean hU hP.variance_continuous hP.variance_zero hIc hR
    v hvC.stronglyMeasurable hvC.continuousOn (fun x _ => hvU x) hEq t S ht (htr.trans hr) hdS het.le
  have hmean := rectangularPulse_resolvent_old_means_on_horizon hα hα'.le hB₂ hB hclock hUp
    hP.variance_nonnegative hUi hMean (fun s hx => by rw [abs_of_nonneg (hR s hx).1];exact (hR s hx).2)
    v hvC.stronglyMeasurable hvC.continuousOn (fun x _ => hvU x) hEq
  exact actual_pulse_biased_block_of_old_sup hα hα' (by positivity) hκ hd hε hdS htr hr hn hP
    (fun s _ => hUi s) (fractionalSecondKindResolvent_measurable α κ) hR hmean V hVm hV₀ hVd hVi hVE

theorem uniform_focal_biased_block_means_of_inverse {α κ σ : ℝ} {H : ℝ≥0}
    (hα : 1/2<α) (hα' : α<1) (hκ : 0≤κ) (hσ : 0≤σ) (hH : 0<H)
    (hR : ∀ x∈Ioc 0 (H:ℝ), 0≤fractionalSecondKindResolvent α κ x ∧
      fractionalSecondKindResolvent α κ x≤2*fractionalK α x) :
    ∃ K : ℝ, 0≤K ∧ ∀ {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
      [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ} {U M C W : ℝ≥0 → Ω → ℝ}
      {ε d : ℝ}, 0<d → ε=d^α →
      (∀ N : Set Ω, MeasurableSet N → P N=0 → MeasurableSet[F 0] N) →
      FractionalPulseProcess P F H α κ (σ^2/2) ε d M U C →
      (∀ᵐ ω ∂P, ∀ t≤H, C t ω = ∫ s in (0:ℝ)..(t:ℝ), σ^2*U s.toNNReal ω) →
      ∀ D : Ω → ℝ, MemLp D 2 P → (∀ᵐ ω ∂P, ∀ t, ‖U t ω‖≤‖D ω‖) →
      Martingale W F P → (∀ t, MemLp (W t) 2 P) → (∀ᵐ ω ∂P, Continuous (fun t => W t ω)) →
      Martingale (fun t ω => W t ω*W t ω-((min t H:ℝ≥0):ℝ)) F P →
      Martingale (fun t => W t*M t) F P →
      ∀ r : ℝ≥0, r≤H → ∀ S : ℝ, d≤S → 2*S≤(r:ℝ) →
      Nonempty (@PulseBlockUpperMean Ω mΩ (@sizeBiasedLaw Ω mΩ P (fractionalPulseMass ε M r) ε)
        (fun t => U t.toNNReal) 0 (2*S) S α K) := by
  obtain ⟨K,hK,hData⟩ := uniform_focal_biased_block_means_of_regular_inverse hα hα' hκ hσ hH hR
  refine ⟨K,hK,?_⟩
  intro Ω mΩ P inst F U M C W ε d hd hε hnull hP hCe D hD hDU
  have hReg := FocalPulseRegularity.of_dominated hD
    (fun t => (hP.variance_adapted t).measurable.mono (F.le t) le_rfl)
    (ae_of_all P hP.variance_continuous) hDU
  exact hData hd hε hnull hP hCe hReg

#print axioms uniform_focal_biased_block_means_of_regular_inverse
#print axioms uniform_focal_biased_block_means_of_inverse

end RoughHeston.GirsanovPort
