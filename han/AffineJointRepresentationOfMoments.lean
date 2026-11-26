import BridgeScalarNative
import TiltingItoPairing
import HestonFubiniKernel
import SHEStochastic.NativeEnergy

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston.GirsanovPort

open SHEStochastic

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} {H : ℝ≥0} {B : ℝ≥0 → Ω → ℝ}

local notation "ν" => jointPredictableMeasure F μ H
local notation "τ" => hestonTimeMeasure H

set_option maxHeartbeats 500000 in
/-- A normalized density equals the candidate joint integral plus one
when the covariance and second-moment estimate saturate its projection. -/
theorem joint_exp_representation_of_moment_pairing {D : Ω → ℝ}
    (hB₂ : ∀ u, MemLp (B u) 2 μ) (hB : Martingale B F μ)
    (hClock : Martingale (fun u ω => B u ω ^ 2 - ((min u H : ℝ≥0) : ℝ)) F μ)
    (r : Lp ℝ 2 ν) (hD₂ : MemLp D 2 μ) (hMean : (∫ ω, D ω ∂μ) = 1)
    (hPair : (∫ ω, D ω * jointItoIntegralCLM H hB₂ r ω ∂μ) = ∫ p, (r p)^2 ∂ν)
    (hSq : (∫ ω, (D ω)^2 ∂μ) ≤ 1 + ∫ p, (r p)^2 ∂ν) :
    D =ᵐ[μ] fun ω => 1 + jointItoIntegralCLM H hB₂ r ω := by
  let I := jointItoIntegralCLM (𝒢 := F) H hB₂ r
  let P (ω : Ω) := D ω - 1
  let X (ω : Ω) := P ω - I ω
  have hP : MemLp P 2 μ := hD₂.sub (memLp_const 1)
  have hI : MemLp (⇑I : Ω → ℝ) 2 μ := Lp.memLp _
  have hX : MemLp X 2 μ := hP.sub hI
  have hiSq : (∫ ω, (I ω)^2 ∂μ) = ∫ p, (r p)^2 ∂ν := by
    simp only [pow_two]
    exact integral_jointItoIntegralCLM_product H hB₂ hB hClock r r
  have hiM : (∫ ω, I ω ∂μ) = 0 := integral_jointItoIntegralCLM_eq_zero H hB₂ hB hClock r
  have hPSq : (∫ ω, (P ω)^2 ∂μ) = (∫ ω, (D ω)^2 ∂μ) - 1 := by
    change (∫ ω, (D ω - 1)^2 ∂μ) = _
    simp_rw [show ∀ x : ℝ, (x-1)^2 = (x^2 - 2*x) + 1 from fun x => by ring]
    have hJ : Integrable (fun ω => D ω^2 - 2*D ω) μ :=
      hD₂.integrable_sq.sub ((hD₂.integrable one_le_two).const_mul 2)
    rw [integral_add hJ (integrable_const 1),
      integral_sub hD₂.integrable_sq ((hD₂.integrable one_le_two).const_mul 2), integral_const_mul,hMean]
    simp
    ring
  have hPI : (∫ ω, P ω * I ω ∂μ) = ∫ p, (r p)^2 ∂ν := by
    change (∫ ω, (D ω-1) * I ω ∂μ) = _
    simp_rw [sub_mul, one_mul]
    have hJ : Integrable (fun ω => D ω * I ω) μ := hD₂.integrable_mul hI
    change (∫ ω, D ω * I ω ∂μ) = _ at hPair
    rw [integral_sub hJ (hI.integrable one_le_two), hPair, hiM, sub_zero]
  have hXle : (∫ ω, (X ω)^2 ∂μ) ≤ 0 := by
    change (∫ ω, (P ω - I ω)^2 ∂μ) ≤ _
    simp_rw [show ∀ x y : ℝ, (x-y)^2 = (x^2-2*(x*y))+y^2 from fun x y => by ring]
    have hJ : Integrable (fun ω => P ω * I ω) μ := hP.integrable_mul hI
    have hJ' : Integrable (fun ω => P ω^2 - 2*(P ω * I ω)) μ :=
      hP.integrable_sq.sub (hJ.const_mul 2)
    rw [integral_add hJ' hI.integrable_sq, integral_sub hP.integrable_sq (hJ.const_mul 2),
      integral_const_mul, hPSq, hPI, hiSq]
    linarith
  have hX0 := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _)
    hX.integrable_sq).mp (le_antisymm hXle (integral_nonneg fun _ => sq_nonneg _))
  filter_upwards [hX0] with ω hω
  change (D ω-1-I ω)^2 = 0 at hω
  have hh : D ω-1-I ω = 0 := by simpa only [pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)] using hω
  linarith

set_option maxHeartbeats 800000 in
/-- Conditional expectation moves the terminal density inside the
physical-time pairing with the two predictable rows. -/
theorem joint_exponential_pairing_of_conditional_density {D : Ω → ℝ} {d : ℝ≥0 → Ω → ℝ}
    (hDi : Integrable D μ) {K : ℝ} (hBound : ∀ᵐ ω ∂μ, ‖D ω‖ ≤ K)
    (hCond : ∀ t ≤ H, μ[D | F t] =ᵐ[μ] d t)
    (u v r : Lp ℝ 2 ν)
    (hr : ⇑r =ᵐ[ν] fun p => d p.1 p.2 * u p) :
    (∫ ω, D ω * (∫ t, u (t, ω) * v (t, ω) ∂τ) ∂μ) = ∫ p, r p * v p ∂ν := by
  have : IsFiniteMeasure τ := by rw [hestonTimeMeasure_eq_horizon]; infer_instance
  have hp (z : Lp ℝ 2 ν) : MemLp (fun p => z p) 2 (Measure.prod τ μ) := by
    rw [hestonTimeMeasure_eq_horizon]
    exact NativeEnergy.product_memLp z
  have hUv := (hp u).integrable_mul (hp v)
  have hRv : Integrable (fun p => r p * v p) (Measure.prod τ μ) := (hp r).integrable_mul (hp v)
  let J (p : ℝ≥0 × Ω) := (u p * v p) * D p.2
  have hDprod : AEStronglyMeasurable (fun p : ℝ≥0 × Ω => D p.2) (Measure.prod τ μ) :=
    hDi.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hJ : Integrable J (Measure.prod τ μ) := by
    refine (hUv.norm.mul_const K).mono' (hUv.aestronglyMeasurable.mul hDprod) ?_
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hBound] with p hp
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hp (norm_nonneg _)
  have hFn (t : ℝ≥0) : StronglyMeasurable[F t] (fun ω => u (t, ω) * v (t, ω)) :=
    ((show IsStronglyPredictable F (fun (t : ℝ≥0) (ω : Ω) => u (t, ω)) from
      Lp.stronglyMeasurable u).stronglyAdapted t).mul
    ((show IsStronglyPredictable F (fun (t : ℝ≥0) (ω : Ω) => v (t, ω)) from
      Lp.stronglyMeasurable v).stronglyAdapted t)
  have hrp : ⇑r =ᵐ[Measure.prod τ μ] fun p => d p.1 p.2 * u p := by
    rw [hestonTimeMeasure_eq_horizon]
    exact ae_eq_of_ae_eq_trim (hm := F.predictable_le_prod) hr
  have hInt : (∫ p, J p ∂(Measure.prod τ μ)) = ∫ p, r p * v p ∂(Measure.prod τ μ) := by
    rw [integral_prod _ hJ, integral_prod _ hRv]
    apply integral_congr_ae
    filter_upwards [ae_time_lt_hestonTimeMeasure H, hJ.prod_right_ae,
      Measure.ae_ae_of_ae_prod hrp] with t ht hJω hrω
    have he := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℝ) (hFn t) hJω hDi
    change μ[(fun ω => u (t, ω) * v (t, ω) * D ω) | F t] =ᵐ[μ]
      fun ω => u (t, ω) * v (t, ω) * μ[D | F t] ω at he
    rw [← integral_condExp (F.le t) (f := fun ω => J (t, ω)), integral_congr_ae he]
    apply integral_congr_ae
    filter_upwards [hCond t ht.le, hrω] with ω h₁ h₂
    rw [h₁, h₂]
    ring
  calc
    _ = ∫ p, J p ∂(Measure.prod τ μ) := by
      rw [integral_prod_symm _ hJ]
      apply integral_congr_ae
      exact ae_of_all _ fun ω => by dsimp [J]; rw [integral_mul_const, mul_comm]
    _ = _ := by
      rw [hInt, hestonTimeMeasure_eq_horizon]
      exact integral_trim F.predictable_le_prod ((Lp.stronglyMeasurable r).mul (Lp.stronglyMeasurable v))

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.joint_exp_representation_of_moment_pairing
#print axioms RoughHeston.GirsanovPort.joint_exponential_pairing_of_conditional_density
