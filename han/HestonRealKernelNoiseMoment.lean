import HestonKernelNoiseMoment
import ClusterRealMomentTransfer

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace RoughHeston.GirsanovPort

open SHEStochastic

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 m} {H : ℝ≥0} {B : ℝ≥0 → Ω → ℝ}

theorem heston_sqrt_row_real_moment (hb : MathFinBridge.BrownianOn P F H B)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[F 0] A)
    (hB₂ : ∀ t, MemLp (B t) 2 P) (hB : Martingale B F P)
    (hclock : Martingale (fun t ω => B t ω^2-((min t H:ℝ≥0):ℝ)) F P)
    (n : ℕ) {σ : ℝ} {K : ℝ≥0 → ℝ} (hK : Measurable K)
    {U : ℝ≥0 → Ω → ℝ} (hU : Measurable (Function.uncurry U))
    (hn : ∀ t ω, 0 ≤ U t ω)
    (u : Lp ℝ 2 (jointPredictableMeasure F P H))
    (hu : u =ᵐ[jointPredictableMeasure F P H] (fun z => σ*K z.1*Real.sqrt (U z.1 z.2)))
    {c : ℝ≥0 → ℝ}
    (hprev : ∀ᵐ t ∂hestonTimeMeasure H,
      Integrable (fun ω => U t ω^(2^n:ℕ)) P ∧ (∫ ω, U t ω^(2^n:ℕ) ∂P) ≤ c t)
    (hw : Integrable (fun t => (σ*K t)^2) (hestonTimeMeasure H))
    (hwc : Integrable (fun t => (σ*K t)^2*c t) (hestonTimeMeasure H)) :
    let N := jointItoIntegralCLM H hB₂ u
    MemLp (fun ω => N ω) ((2*2^n:ℕ):ℝ≥0∞) P ∧
      (∫ ω, ‖N ω‖^(2*2^n:ℕ) ∂P) ≤
      (NativeScalarBDG.constant n : ℝ) *
        ((∫ t, (σ*K t)^2 ∂hestonTimeMeasure H)^(((2^n:ℕ):ℝ)-1) *
          ∫ t, (σ*K t)^2*c t ∂hestonTimeMeasure H) := by
  let w (t : ℝ≥0) := (σ*K t)^2
  let d : ℝ := ((2^n:ℕ):ℝ)-1
  have hd : 0 ≤ d := sub_nonneg.mpr (by exact_mod_cast Nat.one_le_pow n 2 (by decide))
  have hn' : ∀ᵐ ω ∂P, ∀ᵐ t ∂hestonTimeMeasure H, 0 ≤ U t ω :=
    ae_of_all _ fun ω => ae_of_all _ fun t => hn t ω
  have hc' : ∀ᵐ t ∂hestonTimeMeasure H, 0 ≤ c t := by
    filter_upwards [hprev] with t h
    exact (integral_nonneg fun ω => pow_nonneg (hn t ω) _).trans h.2
  have hp : ∀ᵐ t ∂hestonTimeMeasure H,
      (∫⁻ ω, (ENNReal.ofReal (U t ω))^(2^n:ℕ) ∂P) ≤ ENNReal.ofReal (c t) := by
    filter_upwards [hprev] with t ht
    simpa only [ofReal_integral_eq_lintegral_ofReal ht.1
      (ae_of_all _ fun ω => pow_nonneg (hn t ω) _), ENNReal.ofReal_pow (hn t _)] using
        ENNReal.ofReal_le_ofReal ht.2
  have h := heston_sqrt_row_moment_time_profile hb hnull hB₂ hB hclock n hK hU hn' u hu hp
  have hs := weighted_time_profile_ofReal hw hwc (ae_of_all _ fun t => sq_nonneg (σ*K t)) hc' hd
  rw [hs] at h
  have he (x : ℝ≥0) : (x : ℝ≥0∞) = ENNReal.ofReal (x:ℝ) := by simp
  rw [he (NativeScalarBDG.constant n), ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)] at h
  have hi : 0 ≤ ∫ t, (σ*K t)^2*c t ∂hestonTimeMeasure H :=
    integral_nonneg_of_ae (hc'.mono fun t ht => mul_nonneg (sq_nonneg _) ht)
  exact memLp_and_integral_norm_pow_of_lintegral (by positivity)
    (Lp.stronglyMeasurable _).measurable
    (mul_nonneg (NNReal.coe_nonneg _) (mul_nonneg (Real.rpow_nonneg
      (integral_nonneg fun t => sq_nonneg (σ*K t)) _) hi)) h

#print axioms heston_sqrt_row_real_moment

end RoughHeston.GirsanovPort
