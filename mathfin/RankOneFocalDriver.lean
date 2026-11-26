import RankOneCompensators
import CommonBrownianDriver

open MeasureTheory Filter Set
open scoped BigOperators MeasureTheory ProbabilityTheory Topology NNReal ENNReal Interval

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

/-- The same normalized driver that represents the two aggregate
martingales also carries every compatible compensated cross product.
This retains the test-martingale property of the dyadic construction
used by `rank_one_pair_has_common_driver`. -/
theorem rank_one_pair_has_common_driver_with_tests [IsProbabilityMeasure μ]
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
    (hbm : Integrable (fun ω => ∫ s in (0 : ℝ)..(T : ℝ), |b s.toNNReal ω|) μ) :
    ∃ B : ℝ≥0 → Ω → ℝ, Martingale B 𝒢 μ ∧ (∀ t, MemLp (B t) 2 μ) ∧
      (B 0 =ᵐ[μ] 0) ∧ (∀ᵐ ω ∂μ, Continuous (fun t => B t ω)) ∧
      Martingale (fun t ω => B t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) 𝒢 μ ∧
      HasAmplitudeCutoffIntegral 𝒢 μ T B M a ∧ HasAmplitudeCutoffIntegral 𝒢 μ T B N b ∧
      ∀ (V Csv q : ℝ≥0 → Ω → ℝ),
        Martingale V 𝒢 μ → (∀ t, MemLp (V t) 2 μ) →
        (∀ᵐ ω ∂μ, ContinuousOn (fun t => V t ω) (Iic T)) → (V 0 =ᵐ[μ] 0) →
        Martingale (fun t => (M + N) t * V t - Csv t) 𝒢 μ →
        Martingale (fun t => W t * V t) 𝒢 μ →
        (∀ᵐ ω ∂μ, ∀ t ≤ T, Csv t ω =
          ∫ s in (0 : ℝ)..(t : ℝ), (a s.toNNReal ω + b s.toNNReal ω) * q s.toNNReal ω) →
        (∀ᵐ ω ∂μ, ContinuousOn (fun t => q t ω) (Icc 0 T)) →
        (∀ᵐ ω ∂μ, ∀ t ≤ T, a t ω + b t ω = 0 → q t ω = 0) →
        Integrable (fun ω => ∫ s in (0 : ℝ)..(T : ℝ), |(a s.toNNReal ω + b s.toNNReal ω) * q s.toNNReal ω|) μ →
        Integrable (fun ω => ∫ s in (0 : ℝ)..(T : ℝ), |q s.toNNReal ω|) μ →
        ∃ Cq : ℝ≥0 → Ω → ℝ,
          (∀ t, Cq t =ᵐ[μ] driverDensityIntegral T (fun s ω => q s.toNNReal ω) t) ∧
          Martingale (fun t => B t * V (min t T) - Cq t) 𝒢 μ := by
  let F (P : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) := P (min t T)
  let A := a + b
  obtain ⟨hss, hsm, hsn, hsw, hcss, hcsm, hcsn⟩ :=
    rank_one_aggregate_compensators hmm hmn hnn hwm hwn hac hbc hcmm hcmn hcnn
  have intComp {X Y C : ℝ≥0 → Ω → ℝ} (hX : ∀ t, MemLp (X t) 2 μ)
      (hY : ∀ t, MemLp (Y t) 2 μ)
      (hC : Martingale (fun t => X t * Y t - C t) 𝒢 μ) (t : ℝ≥0) :
      Integrable (C t) μ := by
    have hp := ((hX t).mul (hY t) : MemLp (X t * Y t) 1 μ).integrable le_rfl
    simpa only [sub_sub_cancel] using hp.sub (hC.integrable t)
  have intDensity {C : ℝ≥0 → Ω → ℝ} {D : ℝ → Ω → ℝ}
      (hC : Integrable (C T) μ)
      (he : ∀ᵐ ω ∂μ, ∀ t ≤ T, C t ω = ∫ s in (0 : ℝ)..(t : ℝ), D s ω) :
      Integrable (fun ω => ∫ s in (0 : ℝ)..(T : ℝ), D s ω) μ :=
    hC.congr (he.mono fun ω hω => hω T le_rfl)
  have freezeDensity {C : ℝ≥0 → Ω → ℝ} {D : ℝ → Ω → ℝ}
      (he : ∀ᵐ ω ∂μ, ∀ t ≤ T, C t ω = ∫ s in (0 : ℝ)..(t : ℝ), D s ω) :
      ∀ᵐ ω ∂μ, ∀ t ≤ T, F C t ω = ∫ s in (0 : ℝ)..(t : ℝ), D s ω :=
    he.mono fun _ hω t ht => by simpa only [F, min_eq_left ht] using hω t ht
  have hS₂ : ∀ t, MemLp ((M + N) t) 2 μ := fun t => (hM₂ t).add (hN₂ t)
  have hSc : ∀ᵐ ω ∂μ, Continuous (fun t => F (M + N) t ω) := by
    filter_upwards [hMc, hNc] with ω h₁ h₂
    exact (h₁.add h₂).comp_continuous (continuous_id.min continuous_const)
      (fun t => Set.mem_Iic.mpr (min_le_right t T))
  have hAc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => A t ω) (Icc 0 T) := by
    filter_upwards [hac, hbc] with ω h₁ h₂ using h₁.add h₂
  have hA (t : ℝ≥0) (ω : Ω) : 0 ≤ A t ω := add_nonneg (ha t ω) (hb t ω)
  have hCssMono (s t : ℝ≥0) (hst : s ≤ t) :
      F (Cmm + Cmn + Cmn + Cnn) s ≤ᵐ[μ] F (Cmm + Cmn + Cmn + Cnn) t := by
    filter_upwards [hcss, hAc] with ω he hω
    change ((Cmm + Cmn + Cmn + Cnn) (min s T)) ω ≤ _
    have hsT := min_le_right s T
    have htT := min_le_right t T
    rw [he _ hsT, show F (Cmm + Cmn + Cmn + Cnn) t ω = _ from he _ htT]
    have hrt : ((min s T : ℝ≥0) : ℝ) ≤ ((min t T : ℝ≥0) : ℝ) := by
      exact_mod_cast min_le_min_right T hst
    apply intervalIntegral.integral_mono_interval le_rfl (NNReal.coe_nonneg _) hrt
      (Eventually.of_forall fun r => sq_nonneg (A r.toNNReal ω))
    refine ContinuousOn.intervalIntegrable_of_Icc (NNReal.coe_nonneg _) ?_
    apply (hω.comp continuous_real_toNNReal.continuousOn ?_).pow
    intro r hr
    refine ⟨zero_le, ?_⟩
    have hrT : (r.toNNReal : ℝ) ≤ (T : ℝ) := by
      rw [Real.coe_toNNReal r hr.1]
      exact hr.2.trans (by exact_mod_cast htT)
    exact_mod_cast hrT
  obtain ⟨B, hB, hB₂, hB₀, hBc, hBsq, hComp⟩ := exists_normalized_driver T
    (martingale_freeze_at (hM.add hN) T) (martingale_freeze_at hW T)
    (fun t => hS₂ (min t T)) (fun t => hW₂ (min t T)) hSc
    (hWc.mono fun _ hc => hc.comp (continuous_id.min continuous_const))
    (martingale_freeze_at hss T)
    (by simpa only [F, min_assoc, min_self] using martingale_freeze_at hWsq T)
    (martingale_freeze_at hsw T) (fun t => intComp hS₂ hS₂ hss (min t T)) hCssMono
    (freezeDensity hcss) (intDensity (intComp hS₂ hS₂ hss T) hcss) (haa.add hba) hAc hA
  have recover {V Cv Csv u : ℝ≥0 → Ω → ℝ}
      (hV : Martingale V 𝒢 μ) (hV₂ : ∀ t, MemLp (V t) 2 μ)
      (hVc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => V t ω) (Iic T))
      (hV₀ : V 0 =ᵐ[μ] 0)
      (hVsq : Martingale (fun t => V t * V t - Cv t) 𝒢 μ)
      (hSV : Martingale (fun t => (M + N) t * V t - Csv t) 𝒢 μ)
      (hWV : Martingale (fun t => W t * V t) 𝒢 μ)
      (hVe : ∀ᵐ ω ∂μ, ∀ t ≤ T, Cv t ω = ∫ s in (0 : ℝ)..(t : ℝ), u s.toNNReal ω ^ 2)
      (hSe : ∀ᵐ ω ∂μ, ∀ t ≤ T, Csv t ω =
        ∫ s in (0 : ℝ)..(t : ℝ), A s.toNNReal ω * u s.toNNReal ω)
      (hua : StronglyAdapted 𝒢 u) (huc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => u t ω) (Icc 0 T))
      (hu : ∀ t ω, 0 ≤ u t ω) (huz : ∀ t ω, A t ω = 0 → u t ω = 0)
      (hum : Integrable (fun ω => ∫ s in (0 : ℝ)..(T : ℝ), |u s.toNNReal ω|) μ) :
      HasAmplitudeCutoffIntegral 𝒢 μ T B V u := by
    have hFu : ∀ᵐ ω ∂μ, ContinuousOn (fun t => F V t ω) (Iic T) := by
      filter_upwards [hVc] with ω hω
      exact (hω.comp_continuous (continuous_id.min continuous_const)
        (fun t => Set.mem_Iic.mpr (min_le_right t T))).continuousOn
    have hF₀ : F V 0 =ᵐ[μ] 0 := by simpa only [F, min_eq_left (zero_le)] using hV₀
    have hF := martingale_freeze_at hV T
    have hF₂ (t : ℝ≥0) : MemLp (F V t) 2 μ := hV₂ _
    have hEi := intDensity (intComp hV₂ hV₂ hVsq T) hVe
    have hSi : Integrable (fun ω => ∫ s in (0 : ℝ)..(T : ℝ), |A s.toNNReal ω * u s.toNNReal ω|) μ := by
      simpa only [abs_of_nonneg (mul_nonneg (hA _ _) (hu _ _))] using
        intDensity (intComp hS₂ hV₂ hSV T) hSe
    obtain ⟨C, hCe, hBm⟩ := hComp (F V) (F Csv) u hF hF₂ hFu hF₀
      (martingale_freeze_at hSV T) (martingale_freeze_at hWV T)
      (freezeDensity hSe) huc (Eventually.of_forall fun ω t _ => huz t ω) hSi hum
    have hBC : Martingale (fun t => B t * F V t - C t) 𝒢 μ := by
      simpa only [F, min_assoc, min_self] using hBm
    have hCt (t : ℝ≥0) (ht : t ≤ T) : C t =ᵐ[μ] fun ω =>
        ∫ s in (0 : ℝ)..(t : ℝ), u s.toNNReal ω := by
      filter_upwards [hCe t] with ω hω
      rw [hω]
      change (∫ s in (0 : ℝ)..((min t T : ℝ≥0) : ℝ), u s.toNNReal ω) =
        ∫ s in (0 : ℝ)..(t : ℝ), u s.toNNReal ω
      rw [min_eq_left ht]
    simpa only [HasAmplitudeCutoffIntegral, F, min_assoc, min_self] using
      recover_martingale_from_driver T hB hF hB₂ hF₂ hBc hFu hF₀ hBsq
        (martingale_freeze_at hVsq T) hBC (freezeDensity hVe) hCt hEi hum hua huc hu
  refine ⟨B, hB, hB₂, hB₀, hBc, hBsq, ?_, ?_, ?_⟩
  · exact recover hM hM₂ hMc hM₀ hmm hsm hwm hcmm hcsm haa hac ha
      (fun t ω hz => by change a t ω + b t ω = 0 at hz; linarith [ha t ω, hb t ω]) ham
  · exact recover hN hN₂ hNc hN₀ hnn hsn hwn hcnn hcsn hba hbc hb
      (fun t ω hz => by change a t ω + b t ω = 0 at hz; linarith [ha t ω, hb t ω]) hbm
  · intro V Csv q hV hV₂ hVc hV₀ hSV hWV hSe hqc hqz hSi hqi
    have hFv : ∀ᵐ ω ∂μ, ContinuousOn (fun t => F V t ω) (Iic T) := by
      filter_upwards [hVc] with ω hω
      exact (hω.comp_continuous (continuous_id.min continuous_const)
        (fun t => Set.mem_Iic.mpr (min_le_right t T))).continuousOn
    have hF₀ : F V 0 =ᵐ[μ] 0 := by simpa only [F, min_eq_left (zero_le)] using hV₀
    obtain ⟨Cq, hCqe, hCqm⟩ := hComp (F V) (F Csv) q (martingale_freeze_at hV T)
      (fun t => hV₂ _) hFv hF₀ (martingale_freeze_at hSV T) (martingale_freeze_at hWV T)
      (freezeDensity hSe) hqc hqz hSi hqi
    exact ⟨Cq, hCqe, by simpa only [F, min_assoc, min_self] using hCqm⟩

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.rank_one_pair_has_common_driver_with_tests
