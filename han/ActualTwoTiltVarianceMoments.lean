import CappedDriftDensityMoment
import TwoTiltVarianceMoments
import SizeBiasedBurst

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace RoughHeston.GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 m} {H b : ℝ≥0}
  {W N g Y : ℝ≥0 → Ω → ℝ} {Z : Ω → ℝ} {ε : ℝ}

local notation "Q" => sizeBiasedLaw P Z ε

/-- Exact terminal size bias and the actual capped reverse change give
the finite first moments needed for stochastic integration, without
requiring any uniform bound on the density as the pulse mass vanishes. -/
theorem actual_two_tilt_variance_first_moments
    (hε : 0<ε) (hZm : Measurable Z) (hZ₀ : ∀ᵐ ω ∂P, 0≤Z ω) (hZ₂ : MemLp Z 2 P)
    [IsProbabilityMeasure Q] {R : Measure Ω}
    (hW : MathFinBridge.BrownianOn Q F H W)
    (hnull : SHE.NullCompleteFiltration.ContainsNullSets F Q)
    (hW₂ : ∀ t, MemLp (W t) 2 Q) (hWm : Martingale W F Q)
    (hWclock : Martingale (fun t ω => W t ω ^ 2-((min t H : ℝ≥0):ℝ)) F Q)
    {δ : ℝ} (hδ : 0≤δ) (hc : IsStoppedDriftChange (F:=F) (H:=H) b δ g hW₂ R N)
    (hcap : ∀ᵐ ω ∂Q, (∫ t, g t ω ^ 2 ∂hestonTimeMeasure H)≤δ)
    (hY : ∀ t, Measurable (Y t))
    (hY₄ : ∀ t, Integrable (fun ω => Y t ω ^ 4) P)
    {K : ℝ} (hK : ∀ t, (∫ ω,Y t ω ^ 4 ∂P)≤K) :
    ∃ A₀ A₁ A₂ : ℝ,
      (∀ t, Integrable (Y t) P ∧ (∫ ω,Y t ω ∂P)≤A₀) ∧
      (∀ t, Integrable (Y t) Q ∧ (∫ ω,Y t ω ∂Q)≤A₁) ∧
      (∀ t, Integrable (Y t) R ∧ (∫ ω,Y t ω ∂R)≤A₂) := by
  obtain ⟨D,hDm,hD₀,hD₂,_,hR⟩ := stopped_drift_change_density_two hW hnull hW₂ hWm hWclock hδ hc hcap
  have hZp : ∀ᵐ ω ∂P, 0≤Z ω/ε := hZ₀.mono (fun _ hz => div_nonneg hz hε.le)
  exact uniform_necessary_moments_under_two_tilts (hZm.div_const ε) hDm hZp
    (by simpa only [div_eq_mul_inv] using hZ₂.mul_const ε⁻¹)
    rfl hR (ae_of_all _ hD₀) hD₂ hY hY₄ hK

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.actual_two_tilt_variance_first_moments
