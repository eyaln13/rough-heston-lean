import AffineNativeConditionalSubprobability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston.GirsanovPort

open SHEStochastic

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} {H : ℝ≥0}

local notation "ν" => FiniteScalarIto.inputMeasure F μ H

set_option maxHeartbeats 600000 in
/-- As a terminal relative exponential, a native density has
conditional expectation at most its elapsed exponential. -/
theorem native_density_condExp_le_prior
    (P : FiniteScalarIto.Family F μ H Unit) (a : ℝ) (t : ℝ≥0) (ht : t ≤ H)
    (u : Lp ℝ 2 ν) :
    μ[NativeExponential.density P scalarHilbertBasis a u | F t] ≤ᵐ[μ]
      NativeExponential.density P scalarHilbertBasis a (NativeTimeCut.prior t u) := by
  let e := scalarHilbertBasis
  let D := NativeExponential.density P e a u
  let d := NativeExponential.density P e a (NativeTimeCut.prior t u)
  let p := NativeExponential.density P e a (NativeTimeCut.after t u)
  have hh := native_after_density_condExp_le_one P a t ht u
  have hd := NativeExponentialMartingale.density_prior_adapted P e a t u
  let f := hd.mk d
  have hf : StronglyMeasurable[F t] f := hd.stronglyMeasurable_mk
  have hfp : (fun ω => f ω * p ω) =ᵐ[μ] D := by
    filter_upwards [hd.ae_eq_mk, NativeExponentialMartingale.density_split P e a t u] with ω hdω hDω
    change d ω = f ω at hdω
    rw [← hdω]
    exact hDω.symm
  have hD := (NativeExponentialSubprobability.integrable_and_le_one P e a u).1
  have hP := (NativeExponentialSubprobability.integrable_and_le_one P e a (NativeTimeCut.after t u)).1
  have he := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℝ) hf
    (hD.congr hfp.symm) hP
  change μ[(fun ω => f ω * p ω) | F t] =ᵐ[μ] fun ω => f ω * μ[p | F t] ω at he
  have hc := (condExp_congr_ae (m := F t) hfp).symm.trans he
  filter_upwards [hc, hd.ae_eq_mk, hh] with ω h₁ h₂ h₃
  change μ[D | F t] ω ≤ d ω
  change d ω = f ω at h₂
  rw [h₁, ← h₂]
  have hn : 0 ≤ d ω := (Real.exp_pos _).le
  have hlo : μ[p | F t] ω ≤ 1 := h₃
  exact (mul_le_mul_of_nonneg_left hlo hn).trans_eq (mul_one _)

/-- Doubling a parameter changes the square of the unit exponential
by the ordinary elapsed energy factor. -/
theorem native_density_sq_eq_doubled_energy
    (P : FiniteScalarIto.Family F μ H Unit) (u : Lp ℝ 2 ν) (ω : Ω) :
    (NativeExponential.density P scalarHilbertBasis 1 u ω)^2 =
      NativeExponential.density P scalarHilbertBasis 2 u ω * Real.exp (NativeEnergy.energy u ω) := by
  simp only [NativeExponential.density, one_mul, pow_two, ← Real.exp_add]
  congr 1
  ring

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.native_density_condExp_le_prior
#print axioms RoughHeston.GirsanovPort.native_density_sq_eq_doubled_energy
