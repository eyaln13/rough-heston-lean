import ActualFractionalPulse
import ClusterFocalAmplitude
import ClusterPulseSamplewiseInverse
import ClusterPulseHorizonConsistency
import FocalPulseRegularity

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Interval

namespace RoughHeston.GirsanovPort

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {U M C W : ℝ≥0 → Ω → ℝ} {H : ℝ≥0} {α κ σ ε d : ℝ}

/-- Raw properties of a focal pulse and an orthogonal auxiliary martingale
on a single birth filtration. -/
structure FocalPulseDynamics (P : Measure Ω) (F : Filtration ℝ≥0 mΩ) (H : ℝ≥0)
    (α κ σ ε d : ℝ) (M U C W : ℝ≥0 → Ω → ℝ) : Prop where
  pulse : FractionalPulseProcess P F H α κ (σ^2/2) ε d M U C
  clock : ∀ᵐ ω ∂P, ∀ t≤H, C t ω = ∫ s in (0:ℝ)..(t:ℝ), σ^2*U s.toNNReal ω
  regularity : FocalPulseRegularity P U
  auxiliary : Martingale W F P
  auxiliary_memLp : ∀ t, MemLp (W t) 2 P
  auxiliary_continuous : ∀ᵐ ω ∂P, Continuous (fun t => W t ω)
  auxiliary_clock : Martingale (fun t ω => W t ω*W t ω-((min t H:ℝ≥0):ℝ)) F P
  orthogonal : Martingale (fun t => W t*M t) F P

theorem fractionalPulse_inverse_at {a : ℝ}
    (hP : FractionalPulseProcess P F H α κ a ε d M U C)
    (u : ℝ≥0) (hu : u≤H) :
      (fun ω => ∫ s in Ioc (0:ℝ) (u:ℝ), fractionalL α ((u:ℝ)-s)*U s.toNNReal ω) =ᵐ[P]
      fun ω => (∫ s in Ioc (0:ℝ) (u:ℝ), rectangularPulseRate ε d s-κ*U s.toNNReal ω)+M u ω := by
  rcases eq_or_lt_of_le (show (0:ℝ≥0)≤u from zero_le) with e|hp
  · subst u
    filter_upwards [hP.martingale_zero] with ω h
    simpa using h.symm
  · filter_upwards [hP.inverse] with ω hw
    have h := hw (u:ℝ) ⟨hp,hu⟩
    simp only [Real.toNNReal_coe,volterraConvolution] at h
    have he : (∫ s in Ioc (0:ℝ) (u:ℝ), rectangularPulseRate ε d s-κ*U s.toNNReal ω) =
        -(∫ s in Ioc (0:ℝ) (u:ℝ),κ*U s.toNNReal ω-rectangularPulseRate ε d s) := by
      rw [← integral_neg];congr 1;funext z;ring
    linarith

/-- The original-law first moment at every positive age follows from the
inverse pulse equation, on the actual filtered space of the cluster. -/
theorem FocalPulseDynamics.resolvent_mean
    (h : FocalPulseDynamics P F H α κ σ ε d M U C W)
    (hα : 1/2<α) (hα' : α<1) (hH : 0<H) (hε : 0≤ε) (hd : 0<d) (hσ : 0≤σ)
    (hLoc : ∀ s∈Ioc 0 (H:ℝ), |fractionalSecondKindResolvent α κ s|≤2*fractionalK α s) :
    (∀ s,Integrable (U s) P) ∧ ∀ s∈Ioc 0 (H:ℝ), (∫ ω,U s.toNNReal ω ∂P)=
      volterraConvolution (fractionalSecondKindResolvent α κ) (rectangularPulseRate ε d) s := by
  have hP := h.pulse
  have hU := hP.variance_adapted
  have hUm (t : ℝ≥0) : Measurable (U t) := (hU t).measurable.mono (F.le t) le_rfl
  have hUp := hU.isStronglyPredictable_of_leftContinuous
    (fun ω t => (hP.variance_continuous ω).continuousAt.continuousWithinAt)
  have hUc := ae_of_all P hP.variance_continuous
  have hUci := ae_of_all P fun ω => (hP.variance_continuous ω).continuousOn (s:=Icc 0 H)
  obtain ⟨hUi,⟨_,hMean⟩,v,hvC,hvU⟩ := h.regularity
  obtain ⟨B,hB₂,hB,hB₀,hBc,hclock,hcut,_⟩ := focal_cluster_has_own_unit_clock_driver hσ
    hP.martingale hP.martingale_memLp (ae_of_all _ fun ω => (hP.martingale_continuous ω).continuousOn)
    hP.martingale_zero hP.compensated_square h.clock h.auxiliary h.auxiliary_memLp h.auxiliary_continuous
    h.auxiliary_clock h.orthogonal hUp hU hUci hP.variance_nonnegative hUi hMean
  have hEq := rectangularPulse_L2_equation_of_samplewise_inverse hα hα' hH hε hd hσ hB₂ hB hclock
    hUp hU hUci hP.variance_nonnegative hUi hMean hcut v hvC.stronglyMeasurable hvC.continuousOn hvU
    (fractionalPulse_inverse_at hP)
  exact ⟨hUi,rectangularPulse_resolvent_old_means_on_horizon hα hα'.le hB₂ hB hclock hUp
    hP.variance_nonnegative hUi hMean hLoc v hvC.stronglyMeasurable hvC.continuousOn (fun s _ => hvU s) hEq⟩

#print axioms fractionalPulse_inverse_at
#print axioms FocalPulseDynamics.resolvent_mean

end RoughHeston.GirsanovPort
