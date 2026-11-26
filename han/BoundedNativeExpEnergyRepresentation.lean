import AffineNativeProjectionPairing
import AffineNativeDoubled
import AffineJointRepresentationOfMoments
import AffineDensityEnergy
import AffineContinuousEnergyClock

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston.GirsanovPort

open SHEStochastic

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} {H : ℝ≥0} {B : ℝ≥0 → Ω → ℝ}

local notation "ν" => jointPredictableMeasure F μ H
local notation "τ" => hestonTimeMeasure H

set_option maxHeartbeats 1200000 in
/-- A bounded normalized exponential is represented by its joint Brownian
integral when its pathwise energy satisfies the exponential chain rule. -/
theorem bounded_native_exp_joint_representation_of_energy_identity
    (P : FiniteScalarIto.Family F μ H Unit)
    (hB₂ : ∀ u, MemLp (B u) 2 μ) (hB : Martingale B F μ)
    (hClock : Martingale (fun u ω => B u ω ^ 2 - ((min u H : ℝ≥0) : ℝ)) F μ)
    (hAgree : ∀ u ≤ H, P.W () u =ᵐ[μ] B u)
    (u : Lp ℝ 2 ν) {g D : ℝ≥0 → Ω → ℝ}
    (hg : IsStronglyPredictable F g)
    (hGad : ∀ t, StronglyMeasurable[F t] (fun ω => Real.exp (affineEnergyClock g t ω) * (g t ω)^2))
    (hGm : Measurable (fun p : ℝ≥0 × Ω => Real.exp (affineEnergyClock g p.1 p.2) * (g p.1 p.2)^2))
    (hGω : ∀ᵐ ω ∂μ, let Φ := fun t => Real.exp (affineEnergyClock g t ω) * (g t ω)^2
      Integrable Φ τ ∧ Real.exp (affineEnergyClock g H ω) = 1 + ∫ t, Φ t ∂τ)
    (hu : ⇑u =ᵐ[ν] Function.uncurry g)
    (hD : IsStronglyPredictable F D) {K : ℝ} (hK : 0 ≤ K)
    (hDbd : ∀ t ω, ‖D t ω‖ ≤ K)
    (hDnative : ∀ t ≤ H, D t =ᵐ[μ]
      NativeExponential.density P scalarHilbertBasis 1 (NativeTimeCut.prior t u))
    (hDmean : (∫ ω, D H ω ∂μ) = 1)
    (hCond : ∀ t ≤ H, μ[D H | F t] =ᵐ[μ] D t) :
    ∃ r : Lp ℝ 2 ν, (⇑r =ᵐ[ν] fun p => D p.1 p.2 * g p.1 p.2) ∧
      D H =ᵐ[μ] fun ω => 1 + jointItoIntegralCLM H hB₂ r ω := by
  have : IsFiniteMeasure τ := by rw [hestonTimeMeasure_eq_horizon]; infer_instance
  have hFull : NativeTimeCut.prior H u = u := by
    apply Lp.ext
    filter_upwards [NativeTimeCut.prior_ae H u,
      ae_fst_mem_Ioo_jointPredictableMeasure (𝒢 := F) (μ := μ) H] with p h hp
    rw [h, ite_eq_right (not_lt_of_ge hp.2.le)]
  let e := scalarHilbertBasis
  let L (t : ℝ≥0) := NativeExponential.density P e 2 (NativeTimeCut.prior t u)
  let G (p : ℝ≥0 × Ω) := Real.exp (affineEnergyClock g p.1 p.2) * (g p.1 p.2)^2
  let W (p : ℝ≥0 × Ω) := (D p.1 p.2 * g p.1 p.2)^2
  let f (p : ℝ≥0 × Ω) := D p.1 p.2 * g p.1 p.2
  have hfm : StronglyMeasurable[F.predictable] f := hD.mul hg
  have hf : MemLp f 2 ν := by
    refine ((Lp.memLp u).const_mul K).mono hfm.aestronglyMeasurable ?_
    filter_upwards [hu] with p hp
    change ‖D p.1 p.2 * g p.1 p.2‖ ≤ ‖K * u p‖
    rw [norm_mul, norm_mul, Real.norm_of_nonneg hK, hp]
    exact mul_le_mul_of_nonneg_right (hDbd _ _) (norm_nonneg _)
  let r : Lp ℝ 2 ν := hf.toLp f
  have hr : ⇑r =ᵐ[ν] f := hf.coeFn_toLp
  refine ⟨r, hr, ?_⟩
  have HD : MemLp (D H) 2 μ := (memLp_const K).mono
    ((hD.stronglyAdapted H).mono (F.le H)).aestronglyMeasurable
    (ae_of_all _ fun ω => by rw [Real.norm_of_nonneg hK]; exact hDbd H ω)
  have hDn : D H =ᵐ[μ] NativeExponential.density P e 1 u := by
    simpa only [hFull] using hDnative H le_rfl
  have hL : Integrable (L H) μ ∧ (∫ ω, L H ω ∂μ) ≤ 1 := by
    simpa only [L, hFull] using NativeExponentialSubprobability.integrable_and_le_one P e 2 u
  have hLcond (t : ℝ≥0) (ht : t ≤ H) : μ[L H | F t] ≤ᵐ[μ] L t := by
    simpa only [L, hFull] using native_density_condExp_le_prior P 2 t ht u
  have hG₀ (p : ℝ≥0 × Ω) : 0 ≤ G p := mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hFact (t : ℝ≥0) (ht : t ≤ H) :
      ∀ᵐ ω ∂μ, (D t ω)^2 = L t ω * Real.exp (affineEnergyClock g t ω) := by
    filter_upwards [hDnative t ht, affineEnergyClock_prior_eq u hg hu ht] with ω h₁ h₂
    rw [h₁, native_density_sq_eq_doubled_energy, h₂]
  have hEnd : ∀ᵐ ω ∂μ, (D H ω)^2 = L H ω + L H ω * (∫ t, G (t, ω) ∂τ) := by
    filter_upwards [hFact H le_rfl,hGω] with ω hω hEnergy
    rw [hω, hEnergy.2, mul_add, mul_one]
  have hGcomp (t : ℝ≥0) (ht : t ≤ H) :
      (fun ω => G (t, ω) * L t ω) =ᵐ[μ] fun ω => W (t, ω) := by
    filter_upwards [hFact t ht] with ω hω
    change _ = (D t ω * g t ω)^2
    rw [mul_pow, hω]
    dsimp [G]
    ring
  have hW : Integrable W (Measure.prod τ μ) := by
    rw [hestonTimeMeasure_eq_horizon]
    exact (memLp_of_memLp_trim F.predictable_le_prod hf).integrable_sq
  have hSq := second_moment_le_of_doubled_density hL.1 (ae_of_all _ fun _ => (Real.exp_pos _).le)
    hL.2 HD.integrable_sq hGm hG₀ hGad (hGω.mono fun _ h => h.1) hEnd
    ((ae_time_lt_hestonTimeMeasure H).mono fun _ h => h.le) hLcond hW hGcomp
  have hWmean : (∫ p, W p ∂(Measure.prod τ μ)) = ∫ p, (r p)^2 ∂ν := by
    have hWM : StronglyMeasurable[F.predictable] W := hfm.pow 2
    rw [hestonTimeMeasure_eq_horizon, integral_trim F.predictable_le_prod hWM]
    exact integral_congr_ae (hr.symm.mono fun _ h => congrArg (fun x : ℝ => x^2) h)
  rw [hWmean] at hSq
  have hPairNative := native_exponential_pairing_joint P hB₂ hB hClock hAgree u r
    (hDn.symm.mono fun _ hω => by rw [hω]; exact hDbd H _)
    (by rwa [← integral_congr_ae hDn])
  have hPair :
      (∫ ω, D H ω * jointItoIntegralCLM H hB₂ r ω ∂μ) = ∫ p, (r p)^2 ∂ν := by
    calc
      _ = ∫ ω, NativeExponential.density P e 1 u ω * jointItoIntegralCLM H hB₂ r ω ∂μ :=
        integral_congr_ae (hDn.mul EventuallyEq.rfl)
      _ = ∫ ω, NativeExponential.density P e 1 u ω *
          (∫ t, u (t, ω) * r (t, ω) ∂τ) ∂μ := hPairNative
      _ = ∫ ω, D H ω * (∫ t, u (t, ω) * r (t, ω) ∂τ) ∂μ :=
        integral_congr_ae (hDn.symm.mul EventuallyEq.rfl)
      _ = _ := by
        have hr' : ⇑r =ᵐ[ν] fun p => D p.1 p.2 * u p := by
          filter_upwards [hr, hu] with p h₁ h₂
          rw [h₁, h₂]
          rfl
        simpa only [pow_two] using joint_exponential_pairing_of_conditional_density
          (HD.integrable one_le_two) (ae_of_all _ (hDbd H)) hCond u r r hr'
  exact joint_exp_representation_of_moment_pairing hB₂ hB hClock r HD hDmean hPair hSq

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.bounded_native_exp_joint_representation_of_energy_identity
