import BridgeScalarNative
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston.GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} {ν : Measure ℝ≥0} [IsFiniteMeasure ν]

set_option maxHeartbeats 650000 in
/-- The doubled submartingale bound controls the second moment of the
ordinary density by its instantaneous squared row. -/
theorem second_moment_le_of_doubled_density {H : ℝ≥0} {D L : ℝ≥0 → Ω → ℝ}
    {G W : ℝ≥0 × Ω → ℝ}
    (hL : Integrable (L H) μ) (hL₀ : 0 ≤ᵐ[μ] L H) (hLmean : (∫ ω, L H ω ∂μ) ≤ 1)
    (hD₂ : Integrable (fun ω => (D H ω)^2) μ)
    (hG : Measurable G) (hG₀ : ∀ z, 0 ≤ G z)
    (hGa : ∀ t, StronglyMeasurable[F t] (fun ω => G (t, ω)))
    (hGω : ∀ᵐ ω ∂μ, Integrable (fun t => G (t, ω)) ν)
    (hEnd : ∀ᵐ ω ∂μ, (D H ω)^2 = L H ω + L H ω * (∫ t, G (t, ω) ∂ν))
    (hT : ∀ᵐ t ∂ν, t ≤ H)
    (hCond : ∀ t ≤ H, μ[L H | F t] ≤ᵐ[μ] L t)
    (hW : Integrable W (ν.prod μ))
    (hGcomp : ∀ t ≤ H, (fun ω => G (t, ω) * L t ω) =ᵐ[μ] fun ω => W (t, ω)) :
    (∫ ω, (D H ω)^2 ∂μ) ≤ 1 + (∫ z, W z ∂ν.prod μ) := by
  let J (z : ℝ≥0 × Ω) := G z * L H z.2
  have hJm : AEStronglyMeasurable J (ν.prod μ) :=
    hG.aestronglyMeasurable.mul (hL.aestronglyMeasurable.comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_snd)
  have hA : Integrable (fun ω => L H ω * ∫ t, G (t, ω) ∂ν) μ := by
    refine (hD₂.sub hL).congr ?_
    filter_upwards [hEnd] with ω hω
    change (D H ω)^2 - L H ω = _
    rw [hω, add_sub_cancel_left]
  have hJ : Integrable J (ν.prod μ) := by
    refine (integrable_prod_iff' hJm).2 ⟨?_, ?_⟩
    · filter_upwards [hGω] with ω hω using hω.mul_const (L H ω)
    · refine hA.congr ?_
      filter_upwards [hL₀] with ω hω
      change L H ω * (∫ t, G (t, ω) ∂ν) = ∫ t, ‖G (t, ω) * L H ω‖ ∂ν
      simp only [Real.norm_of_nonneg (mul_nonneg (hG₀ _) hω)]
      rw [integral_mul_const, mul_comm]
  have hJle : (∫ z, J z ∂ν.prod μ) ≤ ∫ z, W z ∂ν.prod μ := by
    rw [integral_prod _ hJ, integral_prod _ hW]
    refine integral_mono_ae hJ.integral_prod_left hW.integral_prod_left ?_
    filter_upwards [hT, hJ.prod_right_ae, hW.prod_right_ae] with t ht hti hWi
    have he := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℝ)
      (hGa t) hti hL
    change μ[(fun ω => G (t, ω) * L H ω) | F t] =ᵐ[μ]
      (fun ω => G (t, ω) * μ[L H | F t] ω) at he
    have hi : Integrable (fun ω => G (t, ω) * μ[L H | F t] ω) μ :=
      integrable_condExp.congr he
    have hle := integral_mono_ae hi hWi ?_
    · rw [← integral_congr_ae he, integral_condExp (F.le t)] at hle
      exact hle
    · filter_upwards [hCond t ht, hGcomp t ht] with ω hco hc
      rw [← hc]
      exact mul_le_mul_of_nonneg_left hco (hG₀ _)
  have he : (∫ ω, (D H ω)^2 ∂μ) = (∫ ω, L H ω ∂μ) + ∫ z, J z ∂ν.prod μ := by
    rw [integral_congr_ae hEnd, integral_add hL hA, integral_prod_symm _ hJ]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun ω => by dsimp [J]; rw [integral_mul_const, mul_comm]
  rw [he]
  exact add_le_add hLmean hJle

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.second_moment_le_of_doubled_density
