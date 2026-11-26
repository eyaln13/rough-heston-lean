import JointTimeEnergyProfile
import BridgeScalarNative
import SHEStochastic.NativeScalarBDG

/-! Han's even-moment estimate for the joint-filtration stochastic
integral used to define rough Heston solutions. -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace RoughHeston.GirsanovPort

open SHEStochastic

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 m} {H : ℝ≥0} {B : ℝ≥0 → Ω → ℝ}

theorem jointIto_power_two_estimate (hb : MathFinBridge.BrownianOn P F H B)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[F 0] A)
    (hB₂ : ∀ t, MemLp (B t) 2 P) (hB : Martingale B F P)
    (hclock : Martingale (fun t ω => B t ω^2-((min t H:ℝ≥0):ℝ)) F P)
    (k : ℕ) (u : Lp ℝ 2 (jointPredictableMeasure F P H)) :
    (∫⁻ ω, ENNReal.ofReal (‖jointItoIntegralCLM H hB₂ u ω‖^(2*(2^k))) ∂P) ≤
      (NativeScalarBDG.constant k : ℝ≥0∞) * ∫⁻ ω,
        (∫⁻ t, ENNReal.ofReal (‖u (t,ω)‖^2) ∂hestonTimeMeasure H)^(2^k:ℕ) ∂P := by
  obtain ⟨N, hN⟩ := exists_scalarNativeFamily_of_brownianOn hb hnull
  have hi := scalarNativeIntegral_eq_joint N.toCoordinates hB₂ hB hclock hN u
  let ν := (SHE.PredictableL2.energyMeasure P H).trim (SHE.PredictableL2.predictable_le_product F)
  have hν : ν = jointPredictableMeasure F P H := processMeasure_eq_joint
  have hu : MemLp (fun p => u p) 2 ν := by rw [hν]; exact Lp.memLp u
  let v : SHE.PredictableL2.Process (E := ℝ) F P H := hu.toLp _
  have hv : (fun p => v p) =ᵐ[jointPredictableMeasure F P H] u := by
    exact (congrArg (fun a => (fun p => v p) =ᵐ[a] (fun p => u p)) hν).mp hu.coeFn_toLp
  have htransport : FiniteCylindricalIto.processTransport v = u :=
    Lp.ext ((FiniteCylindricalIto.processTransport_ae v).trans hv)
  have he := NativeScalarBDG.power_two N scalarHilbertBasis k v
  change (∫⁻ ω, ENNReal.ofReal (‖FiniteCylindricalIto.rawIntegral N.toCoordinates
    scalarHilbertBasis (FiniteCylindricalIto.processTransport v) ω‖ ^ (2*(2^k))) ∂P) ≤
    _ * (∫⁻ ω, (∫⁻ t, ENNReal.ofReal (‖v (t,ω)‖^2) ∂SHE.PredictableL2.timeMeasure H)^(2^k:ℕ) ∂P) at he
  rw [htransport, hi] at he
  have ht : SHE.PredictableL2.timeMeasure H = hestonTimeMeasure H := by
    rw [hestonTimeMeasure_eq_horizon]; exact SHEStochastic.timeMeasure_eq H
  rw [ht] at he
  refine he.trans_eq (congrArg (fun a => (NativeScalarBDG.constant k : ℝ≥0∞)*a) ?_)
  apply lintegral_congr_ae
  filter_upwards [joint_predictable_ae_on_time_sections hv] with ω hω
  apply congrArg (fun a : ℝ≥0∞ => a^(2^k:ℕ))
  exact lintegral_congr_ae (hω.mono fun t h => congrArg (fun x : ℝ => ENNReal.ofReal (‖x‖^2)) h)

#print axioms jointIto_power_two_estimate

end RoughHeston.GirsanovPort
