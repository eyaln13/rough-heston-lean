import StoppedCompetitorGirsanov
import BridgeGirsanovDensityToJoint
import StoppedDensityCost

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace RoughHeston.GirsanovPort

open SHEStochastic

variable {Ω : Type*} [m : MeasurableSpace Ω] {Q R : Measure Ω} [IsProbabilityMeasure Q]
  {F : Filtration ℝ≥0 m} {H b : ℝ≥0} {W N g : ℝ≥0 → Ω → ℝ}

set_option maxHeartbeats 1500000 in
/-- The actual stopped reverse law has a square-integrable nonnegative
density with its second moment bounded by the exponential of the
pathwise energy budget. -/
theorem stopped_drift_change_density_two
    (hW : MathFinBridge.BrownianOn Q F H W)
    (hnull : SHE.NullCompleteFiltration.ContainsNullSets F Q)
    (hW₂ : ∀ t, MemLp (W t) 2 Q) (hWm : Martingale W F Q)
    (hWclock : Martingale (fun t ω => W t ω ^ 2 - ((min t H : ℝ≥0):ℝ)) F Q)
    {δ : ℝ} (hδ : 0≤δ) (hc : IsStoppedDriftChange (F:=F) (H:=H) b δ g hW₂ R N)
    (hcap : ∀ᵐ ω ∂Q, (∫ t, g t ω ^ 2 ∂hestonTimeMeasure H)≤δ) :
    ∃ D : Ω → ℝ, Measurable D ∧ (∀ ω, 0≤D ω) ∧ MemLp D 2 Q ∧
      (∫ ω,D ω ^ 2 ∂Q)≤Real.exp δ ∧ R=Q.withDensity (fun ω => ENNReal.ofReal (D ω)) := by
  obtain ⟨P,hP⟩ := exists_scalarNativeFamily_of_brownianOn hW (fun A _ hA => hnull 0 A hA)
  obtain ⟨_,_,_,_,_,_,_,u,_,_,_,hu,hR,_⟩ := hc
  let D := NativeExponential.density P scalarHilbertBasis (-1) u
  let D₂ := NativeExponential.density P scalarHilbertBasis (-2) u
  have he : ∀ᵐ ω ∂Q, NativeEnergy.energy u ω≤δ := by
    filter_upwards [nativeEnergy_ae_eq_hestonEnergy u (Function.uncurry g) hu,hcap] with ω h₁ h₂
    simpa only [h₁,Function.uncurry_apply_pair,Real.norm_eq_abs,sq_abs] using h₂
  obtain ⟨hD₂,hmean₂,_⟩ := NativeBoundedExponential.bounded_energy P scalarHilbertBasis (-2) u δ hδ he
  have hDm := (NativeExponential.stronglyMeasurable P scalarHilbertBasis (-1) u).measurable
  have hfactor : ∀ᵐ ω ∂Q, D ω ^ 2 = Real.exp (NativeEnergy.energy u ω) * D₂ ω := by
    refine ae_of_all _ fun ω => ?_
    dsimp [D,D₂,NativeExponential.density]
    rw [pow_two,←Real.exp_add,←Real.exp_add]
    congr 1
    ring
  obtain ⟨hD,hdbd⟩ := density_sq_le_exp_of_energy_cap hDm.aestronglyMeasurable
    (hD₂.integrable one_le_two) (ae_of_all _ fun _ => (Real.exp_pos _).le) hmean₂.le he hfactor
  refine ⟨D,hDm,fun _ => (Real.exp_pos _).le,hD,hdbd,?_⟩
  exact hR.trans (nativeScalarTilt_eq_jointWithDensity P hW₂ hWm hWclock hP u (Function.uncurry g) hu).symm

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.stopped_drift_change_density_two
