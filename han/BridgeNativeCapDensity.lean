import SHEStochastic.NativeGirsanovTilt
import SHEStochastic.NativePastExponential
import StoppedDensityCost
import ProductKernelEnergy
import JointPredictableDensity

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace RoughHeston
namespace GirsanovPort

open SHEStochastic

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

local notation "ν" => FiniteScalarIto.inputMeasure F μ H

/-- Identify the native pathwise energy with the integral of any
representative over the physical time measure used by the model. -/
theorem nativeEnergy_ae_eq_hestonEnergy (u : Lp C 2 ν) (g : ℝ≥0 × Ω → C)
    (hg : u =ᵐ[jointPredictableMeasure F μ H] g) :
    NativeEnergy.energy u =ᵐ[μ]
      (fun ω => ∫ r, ‖g (r, ω)‖ ^ 2 ∂hestonTimeMeasure H) := by
  rw [hestonTimeMeasure_eq_horizon]
  exact NativeEnergy.energy_ae_of_ae u g hg

/-- The native stopped tilt preserves the complete past at its starting
time and obeys the event-probability estimate used in the coupling. -/
theorem nativeTilt_preserves_past_and_bounds_events
    (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (s : ℝ≥0) (hsH : s ≤ H) (u : Lp C 2 ν)
    (hus : ∀ᵐ p ∂ν, p.1 ≤ s → u p = 0) (δ : ℝ) (hδ : 0 ≤ δ)
    (hu : ∀ᵐ ω ∂μ, NativeEnergy.energy u ω ≤ δ) :
    let Q := NativeGirsanovTilt.measure P e u
    IsProbabilityMeasure Q ∧ (∀ A, MeasurableSet[F s] A → Q.real A = μ.real A) ∧
      (∀ A, MeasurableSet A → |Q.real A - μ.real A| ≤ Real.sqrt (Real.exp δ - 1) / 2) := by
  dsimp only
  let D := NativeExponential.density P e (-1) u
  let D₂ := NativeExponential.density P e (-2) u
  have hQ := NativeGirsanovTilt.probability P e u δ hδ hu
  letI := hQ
  obtain ⟨hD, hmean, _⟩ := NativeBoundedExponential.bounded_energy P e (-1) u δ hδ hu
  obtain ⟨hD₂, hmean₂, _⟩ := NativeBoundedExponential.bounded_energy P e (-2) u δ hδ hu
  have hfactor : ∀ᵐ ω ∂μ, D ω ^ 2 = Real.exp (NativeEnergy.energy u ω) * D₂ ω := by
    refine ae_of_all μ fun ω => ?_
    dsimp [D, D₂, NativeExponential.density]
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  refine ⟨hQ, ?_, ?_⟩
  · intro A hA
    have hcond := NativePastExponential.conditional_mean_one P e (-1) s hsH u hus δ hδ hu
    calc
      _ = ∫ ω in A, (1 : ℝ) ∂NativeGirsanovTilt.measure P e u :=
        setIntegral_one_eq_measureReal.symm
      _ = ∫ ω in A, D ω ∂μ := by
        simpa only [mul_one] using NativeGirsanovTilt.setIntegral_change P e u
          (fun _ => (1 : ℝ)) A (F.le s A hA)
      _ = ∫ ω in A, μ[D | F s] ω ∂μ :=
        (setIntegral_condExp (F.le s) (hD.integrable one_le_two) hA).symm
      _ = ∫ _ : Ω in A, (1 : ℝ) ∂μ := integral_congr_ae (ae_restrict_of_ae hcond)
      _ = _ := setIntegral_one_eq_measureReal
  · intro A hA
    exact event_probability_diff_le_stopped_density_cost hD.aestronglyMeasurable
      (ae_of_all μ fun _ => (Real.exp_pos _).le) hmean (hD₂.integrable one_le_two)
      (ae_of_all μ fun _ => (Real.exp_pos _).le) hmean₂.le hu hfactor hA

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.nativeEnergy_ae_eq_hestonEnergy
#print axioms RoughHeston.GirsanovPort.nativeTilt_preserves_past_and_bounds_events
