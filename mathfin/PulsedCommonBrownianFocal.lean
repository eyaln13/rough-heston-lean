import PulsedFocalCompensator

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Interval Topology

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

/-- The aggregate Brownian driver and the focal mixed compensator
can be selected on the same filtered space. The focal density is the
actual normalized cluster contribution, including at aggregate zeros. -/
theorem pulsed_pair_has_common_brownian_with_focal [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} (T : ℝ≥0)
    {M N W Cmm Cmn Cnn a b : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M 𝒢 μ) (hN : Martingale N 𝒢 μ) (hW : Martingale W 𝒢 μ)
    (hM₂ : ∀ t, MemLp (M t) 2 μ) (hN₂ : ∀ t, MemLp (N t) 2 μ)
    (hW₂ : ∀ t, MemLp (W t) 2 μ)
    (hMc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => M t ω) (Iic T))
    (hNc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => N t ω) (Iic T))
    (hWc : ∀ᵐ ω ∂μ, Continuous (fun t => W t ω))
    (hM₀ : M 0 =ᵐ[μ] 0) (hN₀ : N 0 =ᵐ[μ] 0)
    (hmm : Martingale (fun t => M t * M t - Cmm t) 𝒢 μ)
    (hmn : Martingale (fun t => M t * N t - Cmn t) 𝒢 μ)
    (hnn : Martingale (fun t => N t * N t - Cnn t) 𝒢 μ)
    (hwm : Martingale (fun t => W t * M t) 𝒢 μ)
    (hwn : Martingale (fun t => W t * N t) 𝒢 μ)
    (hWsq : Martingale (fun t ω => W t ω * W t ω - ((min t T : ℝ≥0) : ℝ)) 𝒢 μ)
    (haa : StronglyAdapted 𝒢 a) (hba : StronglyAdapted 𝒢 b)
    (hac : ∀ᵐ ω ∂μ, ContinuousOn (fun t => a t ω) (Icc 0 T))
    (hbc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => b t ω) (Icc 0 T))
    (ha : ∀ t ω, 0 ≤ a t ω) (hb : ∀ t ω, 0 ≤ b t ω)
    (hcmm : ∀ᵐ ω ∂μ, ∀ t ≤ T, Cmm t ω = ∫ s in (0 : ℝ)..(t : ℝ), a s.toNNReal ω ^ 2)
    (hcmn : ∀ᵐ ω ∂μ, ∀ t ≤ T, Cmn t ω =
      ∫ s in (0 : ℝ)..(t : ℝ), a s.toNNReal ω * b s.toNNReal ω)
    (hcnn : ∀ᵐ ω ∂μ, ∀ t ≤ T, Cnn t ω = ∫ s in (0 : ℝ)..(t : ℝ), b s.toNNReal ω ^ 2)
    (ham : Integrable (fun ω => ∫ s in (0 : ℝ)..(T : ℝ), |a s.toNNReal ω|) μ)
    (hbm : Integrable (fun ω => ∫ s in (0 : ℝ)..(T : ℝ), |b s.toNNReal ω|) μ)
    {X Y U J Cx Cy : ℝ≥0 → Ω → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (haX : a = varianceAmplitude σ X) (hbY : b = varianceAmplitude σ Y)
    (hJ : Martingale J 𝒢 μ) (hJ₂ : ∀ t, MemLp (J t) 2 μ)
    (hJc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => J t ω) (Iic T)) (hJ₀ : J 0 =ᵐ[μ] 0)
    (hXJ : Martingale (fun t => M t * J t - Cx t) 𝒢 μ)
    (hYJ : Martingale (fun t => N t * J t - Cy t) 𝒢 μ)
    (hWJ : Martingale (fun t => W t * J t) 𝒢 μ)
    (hCx : ∀ᵐ ω ∂μ, ∀ t ≤ T, Cx t ω = ∫ s in (0 : ℝ)..(t : ℝ), σ ^ 2 * U s.toNNReal ω)
    (hCy : ∀ᵐ ω ∂μ, ∀ t ≤ T, Cy t ω = ∫ s in (0 : ℝ)..(t : ℝ),
      σ ^ 2 * U s.toNNReal ω * Real.sqrt (Y s.toNNReal ω) / Real.sqrt (X s.toNNReal ω))
    (hXm : Measurable (Function.uncurry X)) (hUm : Measurable (Function.uncurry U))
    (hXc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => X t ω) (Icc 0 T))
    (hYc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => Y t ω) (Icc 0 T))
    (hUc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => U t ω) (Icc 0 T))
    (hParts : ∀ᵐ ω ∂μ, ∀ t ≤ T, 0 ≤ U t ω ∧ U t ω ≤ X t ω)
    (hNull : ∀ E : Set Ω, MeasurableSet E → μ E = 0 → MeasurableSet[𝒢 0] E) :
    ∃ B Cf : ℝ≥0 → Ω → ℝ,
      MathFinBridge.BrownianOn μ 𝒢 T B ∧ Martingale B 𝒢 μ ∧ (∀ t, MemLp (B t) 2 μ) ∧
      Martingale (fun t ω => B t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) 𝒢 μ ∧
      HasAmplitudeCutoffIntegral 𝒢 μ T B M a ∧ HasAmplitudeCutoffIntegral 𝒢 μ T B N b ∧
      Martingale (fun t => B t * J (min t T) - Cf t) 𝒢 μ ∧
      (∀ t ≤ T, Cf t =ᵐ[μ] fun ω => ∫ s in (0 : ℝ)..(t : ℝ),
        focalBracketDensity σ U X s.toNNReal ω) := by
  subst a b
  obtain ⟨B, hB, hB₂, hB₀, hBc, hBsq, hMX, hNY, hTest⟩ :=
    rank_one_pair_has_common_driver_with_tests T hM hN hW hM₂ hN₂ hW₂ hMc hNc hWc hM₀ hN₀
      hmm hmn hnn hwm hwn hWsq haa hba hac hbc ha hb hcmm hcmn hcnn ham hbm
  obtain ⟨hC, hD, hQcont, hQzero, hDint, hQint⟩ := pulsed_focal_normalized_test
    hσ hM₂ hN₂ hJ₂ hXJ hYJ hCx hCy hXm hUm hXc hYc hUc hParts ham
  obtain ⟨Cf, hCf, hCross⟩ := hTest J (Cx + Cy) (focalBracketDensity σ U X)
    hJ hJ₂ hJc hJ₀ hC hWJ hD hQcont hQzero hDint hQint
  obtain ⟨W', hW', hEq⟩ := MathFinBridge.brownianOn_modification_of_measurable_nulls hNull hB hBsq hBc hB₀
  have hJf : Martingale (fun t => J (min t T)) 𝒢 μ := martingale_freeze_at hJ T
  have hCfAd := adapted_compensator_of_compensated_product hB.stronglyAdapted hJf.stronglyAdapted hCross
  have transfer {R S : ℝ≥0 → Ω → ℝ} (hR : Martingale R 𝒢 μ) (hS : StronglyAdapted 𝒢 S)
      (he : ∀ t, S t =ᵐ[μ] R t) : Martingale S 𝒢 μ := by
    refine ⟨hS, fun s t hst => ?_⟩
    exact (condExp_congr_ae (he t)).trans ((hR.condExp_ae_eq hst).trans (he s).symm)
  refine ⟨W', Cf, hW', transfer hB hW'.adapted hEq, fun t => (hB₂ t).ae_eq (hEq t).symm, ?_,
    hMX.congr_driver (fun t => (hEq t).symm), hNY.congr_driver (fun t => (hEq t).symm), ?_, ?_⟩
  · apply transfer hBsq (fun t => ((hW'.adapted t).pow 2).sub stronglyMeasurable_const)
    exact fun t => (hEq t).mono fun ω hw => congrArg (fun x : ℝ => x ^ 2 - ((min t T : ℝ≥0) : ℝ)) hw
  · apply transfer hCross (fun t => ((hW'.adapted t).mul (hJf.stronglyAdapted t)).sub (hCfAd t))
    exact fun t => ((hEq t).mul EventuallyEq.rfl).sub EventuallyEq.rfl
  · intro t ht
    filter_upwards [hCf t] with ω hw
    rw [hw]
    change (∫ s in (0 : ℝ)..(min t T : ℝ≥0), focalBracketDensity σ U X s.toNNReal ω) = _
    rw [min_eq_left ht]

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.pulsed_pair_has_common_brownian_with_focal
