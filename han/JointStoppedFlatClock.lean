import SHEStochastic.StoppedSquareZero
import BrownianMotion.StochasticIntegral.OptionalSampling

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston.GirsanovPort

open SHEStochastic

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} [Approximable F μ]

set_option maxHeartbeats 700000 in
/-- A continuous martingale with no remaining compensator after a
bounded stopping time equals its stopped observation at the horizon. -/
theorem martingale_terminal_eq_stopped_of_flat_clock {H : ℝ≥0}
    {M A : ℝ≥0 → Ω → ℝ}
    (hnull : SHE.NullCompleteFiltration.ContainsNullSets F μ)
    (hM : Martingale M F μ) (hMc : ∀ ω, Continuous (fun t => M t ω))
    (hM₂ : MemLp (M H) 2 μ)
    (hC : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
    (hAc : ∀ᵐ ω ∂μ, Continuous (fun t => A t ω))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) (hτH : ∀ ω, τ ω ≤ H)
    (hAH : Integrable (A H) μ)
    (hFlat : stoppedProcess A τ H =ᵐ[μ] A H) :
    M H =ᵐ[μ] stoppedProcess M τ H := by
  let C (t : ℝ≥0) (ω : Ω) := M t ω ^ 2 - A t ω
  let S := stoppedProcess M τ H
  let D := stoppedProcess C τ H
  have hCC : ∀ᵐ ω ∂μ, Continuous (fun t => C t ω) :=
    hAc.mono fun ω hω => ((hMc ω).pow 2).sub hω
  have hCs := StoppedSquareZero.stopped_martingale μ F hnull C hC hCC τ hτ
  have hC0 : stoppedProcess C τ 0 = C 0 := by
    funext ω
    exact stoppedProcess_eq_of_le (i := 0) (ω := ω) (by simp)
  have hm {Z : ℝ≥0 → Ω → ℝ} (hZ : Martingale Z F μ) :
      (∫ ω, Z H ω ∂μ) = ∫ ω, Z 0 ω ∂μ :=
    (integral_condExp (F.le 0)).symm.trans (integral_congr_ae (hZ.condExp_ae_eq zero_le))
  have hDmean : (∫ ω, D ω ∂μ) = ∫ ω, C H ω ∂μ := by
    calc
      _ = ∫ ω, stoppedProcess C τ 0 ω ∂μ := hm hCs
      _ = ∫ ω, C 0 ω ∂μ := by rw [hC0]
      _ = _ := (hm hC).symm
  have hST : (fun ω => S ω ^ 2) =ᵐ[μ] fun ω => D ω + A H ω := by
    filter_upwards [hFlat] with ω hω
    change S ω ^ 2 = S ω ^ 2 - stoppedProcess A τ H ω + A H ω
    rw [hω, sub_add_cancel]
  have hSsquare : Integrable (fun ω => S ω ^ 2) μ := ((hCs.integrable H).add hAH).congr hST.symm
  have hτm := hτ.measurableSpace_le
  have hScond : S =ᵐ[μ] μ[M H | hτ.measurableSpace] := by
    have he := hM.stoppedValue_ae_eq_condExp_of_le_const' (fun ω _ => (hMc ω).continuousAt.continuousWithinAt)
      hτ hτH
    filter_upwards [he] with ω hω
    change M (min (H : WithTop ℝ≥0) (τ ω)).untopA ω = _
    rw [min_eq_right (hτH ω)]
    exact hω
  have hSad : AEStronglyMeasurable[hτ.measurableSpace] S μ :=
    stronglyMeasurable_condExp.aestronglyMeasurable.congr hScond.symm
  have hS₂ : MemLp S 2 μ :=
    (memLp_two_iff_integrable_sq (hSad.mono hτm)).2 hSsquare
  have hSs : (∫ ω, S ω ^ 2 ∂μ) = ∫ ω, M H ω ^ 2 ∂μ := by
    have hE : (fun ω => C H ω + A H ω) = fun ω => M H ω ^ 2 := by
      funext ω
      exact sub_add_cancel _ _
    rw [integral_congr_ae hST, integral_add (hCs.integrable H) hAH,
      hDmean, ← integral_add (hC.integrable H) hAH, hE]
  have hPi : Integrable (fun ω => M H ω * S ω) μ := hM₂.integrable_mul hS₂
  have hPS : (∫ ω, M H ω * S ω ∂μ) = ∫ ω, S ω ^ 2 ∂μ := by
    have he := condExp_mul_of_aestronglyMeasurable_right hSad hPi (hM.integrable H)
    calc
      _ = ∫ ω, μ[(fun ω => M H ω * S ω) | hτ.measurableSpace] ω ∂μ := (integral_condExp hτm).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [he, hScond] with ω h₁ h₂
        change μ[M H * S | hτ.measurableSpace] ω = _
        rw [h₁, Pi.mul_apply, ← h₂, pow_two]
  have hi : Integrable (fun ω => (M H ω - S ω)^2) μ := (hM₂.sub hS₂).integrable_sq
  have hzero : (∫ ω, (M H ω - S ω)^2 ∂μ) = 0 := by
    have hExp (ω : Ω) : (M H ω - S ω)^2 = (M H ω ^ 2 - 2*(M H ω*S ω)) + S ω^2 := by ring
    have hMid : Integrable (fun ω => M H ω ^ 2 - 2*(M H ω*S ω)) μ :=
      hM₂.integrable_sq.sub (hPi.const_mul 2)
    simp_rw [hExp]
    rw [integral_add hMid hSsquare, integral_sub hM₂.integrable_sq (hPi.const_mul 2),
      integral_const_mul, hPS, hSs]
    ring
  have hh := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hi).mp hzero
  exact hh.mono fun ω hω => sub_eq_zero.mp (sq_eq_zero_iff.mp hω)

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.martingale_terminal_eq_stopped_of_flat_clock
