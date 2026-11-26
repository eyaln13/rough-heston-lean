import BridgeScalarNative
import BridgeNativeCapDensity

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace RoughHeston
namespace GirsanovPort

open SHEStochastic

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} {H : ℝ≥0} {M : ℝ≥0 → Ω → ℝ}

/-- The native scalar density is the exponential of the actual joint
Itô integral and the physical pathwise time energy. -/
theorem nativeScalarDensity_ae_eq_joint (P : FiniteScalarIto.Family F μ H Unit)
    (hM₂ : ∀ u, MemLp (M u) 2 μ) (hM : Martingale M F μ)
    (hclock : Martingale (fun u ω => M u ω ^ 2 - ((min u H : ℝ≥0) : ℝ)) F μ)
    (hagree : ∀ u ≤ H, P.W () u =ᵐ[μ] M u)
    (u : Lp ℝ 2 (jointPredictableMeasure F μ H)) (g : ℝ≥0 × Ω → ℝ)
    (hg : u =ᵐ[jointPredictableMeasure F μ H] g) (a : ℝ) :
    NativeExponential.density P scalarHilbertBasis a u =ᵐ[μ]
      (fun ω => Real.exp (a * jointItoIntegralCLM H hM₂ u ω -
        a ^ 2 * (∫ t, g (t, ω) ^ 2 ∂hestonTimeMeasure H) / 2)) := by
  have hi := scalarNativeIntegral_eq_joint P.toCoordinates hM₂ hM hclock hagree u
  filter_upwards [nativeEnergy_ae_eq_hestonEnergy u g hg] with ω hω
  simp only [Real.norm_eq_abs, sq_abs] at hω
  change Real.exp (a * FiniteCylindricalIto.rawIntegral P.toCoordinates scalarHilbertBasis u ω -
    a ^ 2 * NativeEnergy.energy u ω / 2) = _
  rw [hi, hω]

/-- Native scalar Girsanov and the model use the same change of measure,
with the sign that adds the drift to the Brownian driver. -/
theorem nativeScalarTilt_eq_jointWithDensity (P : FiniteScalarIto.Family F μ H Unit)
    (hM₂ : ∀ u, MemLp (M u) 2 μ) (hM : Martingale M F μ)
    (hclock : Martingale (fun u ω => M u ω ^ 2 - ((min u H : ℝ≥0) : ℝ)) F μ)
    (hagree : ∀ u ≤ H, P.W () u =ᵐ[μ] M u)
    (u : Lp ℝ 2 (jointPredictableMeasure F μ H)) (g : ℝ≥0 × Ω → ℝ)
    (hg : u =ᵐ[jointPredictableMeasure F μ H] g) :
    NativeGirsanovTilt.measure P scalarHilbertBasis u =
      μ.withDensity (fun ω => ENNReal.ofReal (Real.exp (-jointItoIntegralCLM H hM₂ u ω -
        (∫ t, g (t, ω) ^ 2 ∂hestonTimeMeasure H) / 2))) := by
  change (μ.withDensity fun ω => ENNReal.ofReal (NativeExponential.density P scalarHilbertBasis (-1) u ω)) = _
  apply withDensity_congr_ae
  filter_upwards [nativeScalarDensity_ae_eq_joint P hM₂ hM hclock hagree u g hg (-1)] with ω hω
  simp only [hω, neg_one_mul, neg_one_sq, one_mul]

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.nativeScalarDensity_ae_eq_joint
#print axioms RoughHeston.GirsanovPort.nativeScalarTilt_eq_jointWithDensity
