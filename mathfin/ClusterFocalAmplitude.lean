import RankOneCompensators
import FixedHestonHorizon
import HestonFubiniKernel

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Interval

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {B M C U W : ℝ≥0 → Ω → ℝ}

/-- The focal amplitude terminal integral has the exact predictable
representative used in the cluster moment pairing. -/
theorem focal_amplitude_terminal_jointIto {T : ℝ≥0} {σ : ℝ}
    (hσ : 0 ≤ σ)
    (hB₂ : ∀ t, MemLp (B t) 2 P) (hB : Martingale B F P)
    (hBclock : Martingale (fun t ω => B t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) F P)
    (hUp : IsStronglyPredictable F U) (hUa : StronglyAdapted F U)
    (hUc : ∀ᵐ ω ∂P, ContinuousOn (fun t => U t ω) (Icc 0 T))
    (hU₀ : ∀ t ω, 0 ≤ U t ω) (hUi : ∀ t, Integrable (U t) P)
    {A : ℝ} (hMean : ∀ t, (∫ ω, U t ω ∂P) ≤ A)
    (hcut : HasAmplitudeCutoffIntegral F P T B M (fun t ω => σ * Real.sqrt (U t ω))) :
    ∃ g : Lp ℝ 2 (jointPredictableMeasure F P T),
      (⇑g =ᵐ[jointPredictableMeasure F P T] fun p => σ * Real.sqrt (U p.1 p.2)) ∧
      M T =ᵐ[P] jointItoIntegralCLM T hB₂ g := by
  let a (t : ℝ≥0) (ω : Ω) := σ * Real.sqrt (U t ω)
  have ha₂ : MemLp (Function.uncurry a) 2 (jointPredictableMeasure F P T) :=
    (sqrt_variance_memLp_joint T hUp hU₀ hUi hMean).const_mul σ
  have haa : StronglyAdapted F a := fun t => ((hUa t).measurable.sqrt.const_mul σ).stronglyMeasurable
  have hasm : StronglyMeasurable[F.predictable] (Function.uncurry a) :=
    (hUp.measurable.sqrt.const_mul σ).stronglyMeasurable
  have hac : ∀ᵐ ω ∂P, ContinuousOn (fun t => a t ω) (Icc 0 T) :=
    hUc.mono fun ω hω => continuous_const.continuousOn.mul (Real.continuous_sqrt.comp_continuousOn hω)
  have ha₀ (t : ℝ≥0) (ω : Ω) : 0 ≤ a t ω := mul_nonneg hσ (Real.sqrt_nonneg _)
  let g := jointAmplitudeSectionLp T ha₂
  have hg : ⇑g =ᵐ[jointPredictableMeasure F P T] fun p => a p.1 p.2 := by
    refine (jointAmplitudeSectionLp_ae T ha₂).trans ?_
    filter_upwards [ae_fst_mem_Ioo_jointPredictableMeasure (𝒢 := F) (μ := P) T] with p hp
    have hp' : p ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) :=
      ⟨⟨hp.1, hp.2.le⟩, mem_univ _⟩
    simp only [indicator_of_mem hp', Function.uncurry]
  exact ⟨g, hg, hcut.ae_eq_jointIto_fixed_horizon le_rfl hB hB₂ hBclock haa hasm hac ha₀ ha₂⟩

/-- Normalizing the focal martingale against the orthogonal auxiliary
driver yields its dedicated unit-clock driver on the existing filtration. -/
theorem focal_cluster_has_own_unit_clock_driver {T : ℝ≥0} {σ : ℝ}
    (hσ : 0 ≤ σ) (hM : Martingale M F P) (hM₂ : ∀ t, MemLp (M t) 2 P)
    (hMc : ∀ᵐ ω ∂P, ContinuousOn (fun t => M t ω) (Iic T))
    (hM₀ : M 0 =ᵐ[P] 0) (hC : Martingale (fun t => M t * M t - C t) F P)
    (hCe : ∀ᵐ ω ∂P, ∀ t ≤ T, C t ω = ∫ s in (0 : ℝ)..(t : ℝ), σ ^ 2 * U s.toNNReal ω)
    (hW : Martingale W F P) (hW₂ : ∀ t, MemLp (W t) 2 P)
    (hWc : ∀ᵐ ω ∂P, Continuous (fun t => W t ω))
    (hWsq : Martingale (fun t ω => W t ω * W t ω - ((min t T : ℝ≥0) : ℝ)) F P)
    (hWM : Martingale (fun t => W t * M t) F P)
    (hUp : IsStronglyPredictable F U) (hUa : StronglyAdapted F U)
    (hUc : ∀ᵐ ω ∂P, ContinuousOn (fun t => U t ω) (Icc 0 T))
    (hU₀ : ∀ t ω, 0 ≤ U t ω) (hUi : ∀ t, Integrable (U t) P)
    {A : ℝ} (hMean : ∀ t, (∫ ω, U t ω ∂P) ≤ A) :
    ∃ (B : ℝ≥0 → Ω → ℝ) (hB₂ : ∀ t, MemLp (B t) 2 P),
      Martingale B F P ∧
      (B 0 =ᵐ[P] 0) ∧ (∀ᵐ ω ∂P, Continuous (fun t => B t ω)) ∧
      Martingale (fun t ω => B t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) F P ∧
      HasAmplitudeCutoffIntegral F P T B M (fun t ω => σ * Real.sqrt (U t ω)) ∧
      ∃ g : Lp ℝ 2 (jointPredictableMeasure F P T),
        (⇑g =ᵐ[jointPredictableMeasure F P T] fun p => σ * Real.sqrt (U p.1 p.2)) ∧
        M T =ᵐ[P] jointItoIntegralCLM T hB₂ g := by
  let a (t : ℝ≥0) (ω : Ω) := σ * Real.sqrt (U t ω)
  have haa : StronglyAdapted F a := fun t => ((hUa t).measurable.sqrt.const_mul σ).stronglyMeasurable
  have hac : ∀ᵐ ω ∂P, ContinuousOn (fun t => a t ω) (Icc 0 T) :=
    hUc.mono fun ω hω => continuous_const.continuousOn.mul (Real.continuous_sqrt.comp_continuousOn hω)
  have ha₀ (t : ℝ≥0) (ω : Ω) : 0 ≤ a t ω := mul_nonneg hσ (Real.sqrt_nonneg _)
  have hCe' : ∀ᵐ ω ∂P, ∀ t ≤ T, C t ω = ∫ s in (0 : ℝ)..(t : ℝ), a s.toNNReal ω ^ 2 := by
    filter_upwards [hCe] with ω hω t ht
    simpa only [a, mul_pow, Real.sq_sqrt (hU₀ _ _)] using hω t ht
  have hCT : Integrable (C T) P := by
    have hMm := ((hM₂ T).mul (hM₂ T) : MemLp (M T * M T) 1 P).integrable le_rfl
    simpa only [sub_sub_cancel] using hMm.sub (hC.integrable T)
  have hAi : Integrable (fun ω => ∫ s in (0 : ℝ)..(T : ℝ), a s.toNNReal ω ^ 2) P :=
    hCT.congr (hCe'.mono fun ω hω => hω T le_rfl)
  have ham := amplitude_mass_integrable_of_energy haa hac hAi
  obtain ⟨B, hB, hB₂, hB₀, hBc, hBclock, hcut, -⟩ := rank_one_pair_has_common_driver T
    hM hM hW hM₂ hM₂ hW₂ hMc hMc hWc hM₀ hM₀ hC hC hC hWM hWM hWsq
    haa haa hac hac ha₀ ha₀ hCe' (by simpa only [pow_two] using hCe') hCe' ham ham
  exact ⟨B, hB₂, hB, hB₀, hBc, hBclock, hcut,
    focal_amplitude_terminal_jointIto hσ hB₂ hB hBclock hUp hUa hUc hU₀ hUi hMean hcut⟩

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.focal_amplitude_terminal_jointIto
#print axioms RoughHeston.GirsanovPort.focal_cluster_has_own_unit_clock_driver
