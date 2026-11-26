import AffineDensityPerturbation
import BridgeGirsanovDensityToJoint
import SHEStochastic.NativeExponentialSubprobability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston.GirsanovPort

open SHEStochastic

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} {H : ℝ≥0} {B : ℝ≥0 → Ω → ℝ}

local notation "ν" => jointPredictableMeasure F μ H
local notation "τ" => hestonTimeMeasure H

set_option maxHeartbeats 800000 in
/-- Pair a normalized bounded stochastic exponential with any joint
Brownian integral, by testing the native exponential in both directions. -/
theorem native_exponential_pairing_joint
    (P : FiniteScalarIto.Family F μ H Unit)
    (hB₂ : ∀ u, MemLp (B u) 2 μ) (hB : Martingale B F μ)
    (hClock : Martingale (fun u ω => B u ω ^ 2 - ((min u H : ℝ≥0) : ℝ)) F μ)
    (hAgree : ∀ u ≤ H, P.W () u =ᵐ[μ] B u)
    (u v : Lp ℝ 2 ν)
    {K : ℝ}
    (hBound : ∀ᵐ ω ∂μ, ‖NativeExponential.density P scalarHilbertBasis 1 u ω‖ ≤ K)
    (hMean : (∫ ω, NativeExponential.density P scalarHilbertBasis 1 u ω ∂μ) = 1) :
    let D := NativeExponential.density P scalarHilbertBasis 1 u
    (∫ ω, D ω * jointItoIntegralCLM H hB₂ v ω ∂μ) =
      ∫ ω, D ω * (∫ t, u (t, ω) * v (t, ω) ∂τ) ∂μ := by
  have : IsFiniteMeasure τ := by rw [hestonTimeMeasure_eq_horizon]; infer_instance
  let D := NativeExponential.density P scalarHilbertBasis 1 u
  let I := jointItoIntegralCLM (𝒢 := F) H hB₂
  let E (z : Lp ℝ 2 ν) (ω : Ω) := ∫ t, z (t, ω)^2 ∂τ
  let C (ω : Ω) := ∫ t, u (t, ω) * v (t, ω) ∂τ
  let L (ω : Ω) := I v ω - C ω
  have hD₀ : 0 ≤ᵐ[μ] D := ae_of_all _ fun _ => (Real.exp_pos _).le
  have hDi := (NativeExponentialSubprobability.integrable_and_le_one P scalarHilbertBasis 1 u).1
  have hp (z : Lp ℝ 2 ν) : MemLp (fun p => z p) 2 (Measure.prod τ μ) := by
    rw [hestonTimeMeasure_eq_horizon]
    exact NativeEnergy.product_memLp z
  have huv := (hp u).integrable_mul (hp v)
  have hu := (hp u).integrable_sq
  have hv := (hp v).integrable_sq
  have hCi : Integrable C μ := huv.integral_prod_right
  have hEi : Integrable (E v) μ := hv.integral_prod_right
  have hIi : Integrable (⇑(I v)) μ := (Lp.memLp (I v)).integrable one_le_two
  have hmul {f : Ω → ℝ} (hf : Integrable f μ) : Integrable (fun ω => D ω * f ω) μ := by
    refine (hf.norm.const_mul K).mono' (hDi.aestronglyMeasurable.mul hf.aestronglyMeasurable) ?_
    filter_upwards [hBound] with ω hω
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hω (norm_nonneg _)
  have hDφ (c : ℝ) : NativeExponential.density P scalarHilbertBasis 1 (u + c • v) =ᵐ[μ]
      fun ω => D ω * Real.exp (c * L ω - c^2 * E v ω / 2) := by
    have hPlus : ⇑(u + c • v) =ᵐ[ν] fun p => u p + c * v p := by
      filter_upwards [Lp.coeFn_add u (c • v), Lp.coeFn_smul c v] with p hp hq
      rw [hp, Pi.add_apply, hq, Pi.smul_apply, smul_eq_mul]
    have hID : (⇑(I (u + c • v)) : Ω → ℝ) =ᵐ[μ] fun ω => I u ω + c * I v ω := by
      rw [map_add, map_smul]
      filter_upwards [Lp.coeFn_add (I u) (c • I v), Lp.coeFn_smul c (I v)] with ω hw hz
      rw [hw, Pi.add_apply, hz, Pi.smul_apply, smul_eq_mul]
    have he : (fun ω => ∫ t, (u (t, ω)+c*v (t, ω))^2 ∂τ) =ᵐ[μ]
        fun ω => E u ω + 2*c*C ω + c^2*E v ω := by
      filter_upwards [hu.prod_left_ae, hv.prod_left_ae, huv.prod_left_ae] with ω hU hV hUV
      have h1 : (fun t => (u (t, ω) + c*v (t, ω))^2) =
          fun t => (u (t, ω)^2 + (2*c)*(u (t, ω)*v (t, ω))) + c^2*v (t, ω)^2 := by
        funext t
        ring
      have hUV' : Integrable (fun t => u (t, ω) * v (t, ω)) τ := hUV
      have hA : Integrable (fun t => u (t, ω)^2 + (2*c)*(u (t, ω)*v (t, ω))) τ :=
        hU.add (hUV'.const_mul (2*c))
      rw [h1, integral_add hA (hV.const_mul (c^2)),
        integral_add hU (hUV'.const_mul (2*c)), integral_const_mul, integral_const_mul]
    filter_upwards [nativeScalarDensity_ae_eq_joint P hB₂ hB hClock hAgree (u + c • v) _ hPlus 1,
      nativeScalarDensity_ae_eq_joint P hB₂ hB hClock hAgree u _ EventuallyEq.rfl 1, hID, he] with
      ω hω hDω hIω hEω
    rw [hω, hIω, hEω, show D ω = _ from hDω, ← Real.exp_add]
    congr 1
    dsimp [L]
    ring
  have hEx (c : ℝ) := NativeExponentialSubprobability.integrable_and_le_one P scalarHilbertBasis 1 (u+c • v)
  have hLi : Integrable L μ := hIi.sub hCi
  have hDMean : (∫ ω, D ω ∂μ) = 1 := hMean
  have hzero : (∫ ω, D ω * L ω ∂μ) = 0 :=
    integral_linear_perturbation_zero hDi hD₀ (hmul hLi) (hmul hEi)
      (fun c => (hEx c).1.congr (hDφ c)) (fun c => by
        rw [← integral_congr_ae (hDφ c), hDMean]
        exact (hEx c).2)
  have hz : (∫ ω, D ω * I v ω ∂μ) - (∫ ω, D ω*C ω ∂μ) = 0 := by
    rw [← integral_sub (hmul hIi) (hmul hCi)]
    simpa only [L, mul_sub] using hzero
  exact sub_eq_zero.mp hz

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.native_exponential_pairing_joint
