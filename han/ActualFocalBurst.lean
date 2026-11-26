import FocalPulseDynamics
import FocalPulseVerifiedBurst

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Interval

namespace RoughHeston.GirsanovPort

/-- The same positive burst probability and both thresholds work for every
birth law, pulse width and observation age in the local resolvent range. -/
theorem exists_focal_burst_constants {α κ σ : ℝ} {H : ℝ≥0}
    (hα : 1/2<α) (hα' : α<1) (hκ : 0≤κ) (hσ : 0<σ)
    (hcomp : ∀ x∈Ioc 0 (H:ℝ), fractionalK α x/2≤fractionalSecondKindResolvent α κ x ∧
      fractionalSecondKindResolvent α κ x≤2*fractionalK α x) :
    ∃ cU cZ p : ℝ, 0<cU ∧ 0<cZ ∧ 0<p ∧ ∀ {Ω : Type*} [mΩ : MeasurableSpace Ω]
      {P : Measure Ω} [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
      {M U C W : ℝ≥0 → Ω → ℝ} {ε d : ℝ} {r : ℝ≥0}, 0<d → ε=d^α → d≤(r:ℝ)/8 → r≤H →
      (∀ N : Set Ω, MeasurableSet N → P N=0 → MeasurableSet[F 0] N) →
      FocalPulseDynamics P F H α κ σ ε d M U C W →
      let Z := fractionalPulseMass ε M
      let Q := sizeBiasedLaw P (Z r) ε
      p≤Q.real {ω | cU*(r:ℝ)^(2*α-1)≤U r ω ∧ Z r ω≤cZ*(r:ℝ)^α} := by
  let D := 1+focalPulseMomentConstant α σ 2
  let a := σ^2/(16*(Real.Gamma α)^2)
  let z := 1+σ^2*(4/α)/(Real.Gamma α*α)
  let c := Real.sqrt (D*z)
  have hal : 0<α := by linarith
  have hg := Real.Gamma_pos_of_pos hal
  have hD₀ : 0<D := by dsimp [D];linarith [focalPulseMomentConstant_nonneg α σ 2]
  have ha : 0<a := by dsimp [a];positivity
  have hz : 0<z := by dsimp [z];positivity
  have hc : 0<c := Real.sqrt_pos.mpr (mul_pos hD₀ hz)
  refine ⟨a/2,8*c*(z+1)/a^2,a^2/(8*c),by positivity,by positivity,by positivity,?_⟩
  intro Ω mΩ P inst F M U C W ε d r hd hε hdr hr hnull h
  have hP := h.pulse
  have hUa := hP.variance_adapted
  have hUp := hUa.isStronglyPredictable_of_leftContinuous
    (fun ω t => (hP.variance_continuous ω).continuousAt.continuousWithinAt)
  have hε₀ : 0<ε := hε ▸ Real.rpow_pos_of_pos hd _
  have hM := martingale_freeze_at hP.martingale r
  have hCsq := martingale_freeze_at hP.compensated_square r
  have hW := martingale_freeze_at h.auxiliary r
  have hWM := martingale_freeze_at h.orthogonal r
  have hWs : Martingale (fun s ω => W (min s r) ω*W (min s r) ω-((min s r:ℝ≥0):ℝ)) F P := by
    simpa only [min_assoc,min_eq_left hr] using martingale_freeze_at h.auxiliary_clock r
  have hCe : ∀ᵐ ω ∂P,∀ s≤r, C (min s r) ω=∫ u in (0:ℝ)..(s:ℝ),σ^2*U u.toNNReal ω :=
    h.clock.mono fun ω hw s hs => by simpa only [min_eq_left hs] using hw s (hs.trans hr)
  obtain ⟨_,hZn,_,_,_⟩ := fractional_pulse_mass_data hal hα' hκ hε₀ hd hr hP
  have hb := rectangularPulse_uniform_burst_of_regular_inverse hα hα' hε₀ hd hdr hε hσ hnull hUp hUa
    (ae_of_all _ hP.variance_continuous) hP.variance_nonnegative h.regularity
    (fun s hs => hcomp s ⟨hs.1,hs.2.trans hr⟩) hM (fun s => hP.martingale_memLp (min s r))
    (ae_of_all P fun ω => ((hP.martingale_continuous ω).comp (continuous_id.min continuous_const)).continuousOn)
    (by change M (min 0 r) =ᵐ[P] 0; rw [min_eq_left (show (0:ℝ≥0)≤r from zero_le)]; exact hP.martingale_zero)
    hCsq hCe hW (fun s => h.auxiliary_memLp (min s r))
    (h.auxiliary_continuous.mono fun ω hw => hw.comp (continuous_id.min continuous_const)) hWs hWM
    (fun u hu => by simpa only [min_eq_left hu] using fractionalPulse_inverse_at hP u (hu.trans hr))
    (by simpa only [min_self,fractionalPulseMass] using hZn)
  dsimp only
  rw [show fractionalPulseMass ε M r = (fun ω => ε+M r ω) from rfl]
  simpa only [min_self,fractionalPulseMass,a,z,c,D] using hb.2

#print axioms exists_focal_burst_constants

end RoughHeston.GirsanovPort
