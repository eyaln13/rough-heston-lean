import CommonDriverConstruction
import Mathlib.MeasureTheory.Integral.Prod

/-!
Compensators for the aggregate of a pair of martingales when their
covariance density is the outer product of their amplitudes.
-/

open MeasureTheory Filter Set
open scoped MeasureTheory ProbabilityTheory Topology NNReal ENNReal

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

/-- The compensated products of the sum and its two components follow
by polarization of the three original compensated products. -/
theorem rank_one_aggregate_compensators [IsFiniteMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} {T : ℝ≥0}
    {M N W Cmm Cmn Cnn a b : ℝ≥0 → Ω → ℝ}
    (hmm : Martingale (fun t => M t * M t - Cmm t) 𝒢 μ)
    (hmn : Martingale (fun t => M t * N t - Cmn t) 𝒢 μ)
    (hnn : Martingale (fun t => N t * N t - Cnn t) 𝒢 μ)
    (hwm : Martingale (fun t => W t * M t) 𝒢 μ)
    (hwn : Martingale (fun t => W t * N t) 𝒢 μ)
    (ha : ∀ᵐ ω ∂μ, ContinuousOn (fun t => a t ω) (Icc 0 T))
    (hb : ∀ᵐ ω ∂μ, ContinuousOn (fun t => b t ω) (Icc 0 T))
    (hcmm : ∀ᵐ ω ∂μ, ∀ t ≤ T, Cmm t ω = ∫ s in (0 : ℝ)..(t : ℝ), a s.toNNReal ω ^ 2)
    (hcmn : ∀ᵐ ω ∂μ, ∀ t ≤ T, Cmn t ω =
      ∫ s in (0 : ℝ)..(t : ℝ), a s.toNNReal ω * b s.toNNReal ω)
    (hcnn : ∀ᵐ ω ∂μ, ∀ t ≤ T, Cnn t ω = ∫ s in (0 : ℝ)..(t : ℝ), b s.toNNReal ω ^ 2) :
    let S := M + N
    let Css := Cmm + Cmn + Cmn + Cnn
    let Csm := Cmm + Cmn
    let Csn := Cmn + Cnn
    Martingale (fun t => S t * S t - Css t) 𝒢 μ ∧
    Martingale (fun t => S t * M t - Csm t) 𝒢 μ ∧
    Martingale (fun t => S t * N t - Csn t) 𝒢 μ ∧
    Martingale (fun t => S t * W t) 𝒢 μ ∧
    (∀ᵐ ω ∂μ, ∀ t ≤ T, Css t ω =
      ∫ s in (0 : ℝ)..(t : ℝ), (a s.toNNReal ω + b s.toNNReal ω) ^ 2) ∧
    (∀ᵐ ω ∂μ, ∀ t ≤ T, Csm t ω =
      ∫ s in (0 : ℝ)..(t : ℝ), (a s.toNNReal ω + b s.toNNReal ω) * a s.toNNReal ω) ∧
    (∀ᵐ ω ∂μ, ∀ t ≤ T, Csn t ω =
      ∫ s in (0 : ℝ)..(t : ℝ), (a s.toNNReal ω + b s.toNNReal ω) * b s.toNNReal ω) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · convert ((hmm.add hmn).add hmn).add hnn using 1
    ext t ω
    simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
    ring
  · convert hmm.add hmn using 1
    ext t ω
    simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
    ring
  · convert hmn.add hnn using 1
    ext t ω
    simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
    ring
  · convert hwm.add hwn using 1
    ext t ω
    simp only [Pi.add_apply, Pi.mul_apply]
    ring
  rw [← eventually_and, ← eventually_and]
  filter_upwards [ha, hb, hcmm, hcmn, hcnn] with ω haω hbω hcmmω hcmnω hcnnω
  have equalities (t : ℝ≥0) (ht : t ≤ T) :
      (Cmm + Cmn + Cmn + Cnn) t ω =
        (∫ s in (0 : ℝ)..(t : ℝ), (a s.toNNReal ω + b s.toNNReal ω) ^ 2) ∧
      (Cmm + Cmn) t ω =
        (∫ s in (0 : ℝ)..(t : ℝ), (a s.toNNReal ω + b s.toNNReal ω) * a s.toNNReal ω) ∧
      (Cmn + Cnn) t ω =
        ∫ s in (0 : ℝ)..(t : ℝ), (a s.toNNReal ω + b s.toNNReal ω) * b s.toNNReal ω := by
    have preimage (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (t : ℝ)) : s.toNNReal ∈ Icc 0 T := by
      refine ⟨zero_le, ?_⟩
      have h : (s.toNNReal : ℝ) ≤ (T : ℝ) := by
        rw [Real.coe_toNNReal s hs.1]
        exact hs.2.trans (by exact_mod_cast ht)
      exact_mod_cast h
    have hac : ContinuousOn (fun s : ℝ => a s.toNNReal ω) (Icc (0 : ℝ) (t : ℝ)) :=
      haω.comp continuous_real_toNNReal.continuousOn preimage
    have hbc : ContinuousOn (fun s : ℝ => b s.toNNReal ω) (Icc (0 : ℝ) (t : ℝ)) :=
      hbω.comp continuous_real_toNNReal.continuousOn preimage
    have hi₁ : IntervalIntegrable (fun s : ℝ => a s.toNNReal ω ^ 2) volume 0 (t : ℝ) :=
      (hac.pow 2).intervalIntegrable_of_Icc (NNReal.coe_nonneg t)
    have hi₂ : IntervalIntegrable (fun s : ℝ => a s.toNNReal ω * b s.toNNReal ω) volume 0 (t : ℝ) :=
      (hac.mul hbc).intervalIntegrable_of_Icc (NNReal.coe_nonneg t)
    have hi₃ : IntervalIntegrable (fun s : ℝ => b s.toNNReal ω ^ 2) volume 0 (t : ℝ) :=
      (hbc.pow 2).intervalIntegrable_of_Icc (NNReal.coe_nonneg t)
    simp only [Pi.add_apply, hcmmω t ht, hcmnω t ht, hcnnω t ht]
    refine ⟨?_, ?_, ?_⟩
    · rw [← intervalIntegral.integral_add hi₁ hi₂,
        ← intervalIntegral.integral_add (hi₁.add hi₂) hi₂,
        ← intervalIntegral.integral_add ((hi₁.add hi₂).add hi₂) hi₃]
      congr 1
      funext s
      ring
    · rw [← intervalIntegral.integral_add hi₁ hi₂]
      congr 1
      funext s
      ring
    · rw [← intervalIntegral.integral_add hi₂ hi₃]
      congr 1
      funext s
      ring
  exact ⟨fun t ht => (equalities t ht).1, fun t ht => (equalities t ht).2.1,
    fun t ht => (equalities t ht).2.2⟩


/-- On a finite horizon, an adapted amplitude with continuous paths
almost surely has integrable total absolute amplitude if its energy
has finite expectation. -/
theorem amplitude_mass_integrable_of_energy [IsFiniteMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} {T : ℝ≥0} {b : ℝ≥0 → Ω → ℝ}
    (hba : StronglyAdapted 𝒢 b)
    (hbc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => b t ω) (Icc 0 T))
    (henergy : Integrable (fun ω => ∫ s in (0 : ℝ)..(T : ℝ), b s.toNNReal ω ^ 2) μ) :
    Integrable (fun ω => ∫ s in (0 : ℝ)..(T : ℝ), |b s.toNNReal ω|) μ := by
  classical
  obtain ⟨bad, hbad, hmBad, hzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hbc)
  let G := badᶜ
  have hmG : MeasurableSet G := hmBad.compl
  have hG : ∀ᵐ ω ∂μ, ω ∈ G := ae_iff.mpr (by simpa [G] using hzero)
  have hgood (ω : Ω) (hω : ω ∈ G) : ContinuousOn (fun t => b t ω) (Icc 0 T) :=
    by_contra fun hn => hω (hbad hn)
  let f (s : ℝ) : Ω → ℝ := G.indicator (fun ω => |b (min s.toNNReal T) ω|)
  have hclamp (s : ℝ) : min s.toNNReal T ∈ Icc 0 T := ⟨zero_le, min_le_right _ _⟩
  have hcont (ω : Ω) : Continuous (fun s => f s ω) := by
    by_cases hω : ω ∈ G
    · have hc := (hgood ω hω).comp_continuous
        (continuous_real_toNNReal.min continuous_const) hclamp
      simpa only [f, indicator_of_mem hω, Function.comp_def] using hc.abs
    · simpa only [f, indicator_of_notMem hω] using
        (continuous_const : Continuous fun _ : ℝ => (0 : ℝ))
  have hmeas (s : ℝ) : StronglyMeasurable (f s) :=
    (continuous_abs.comp_stronglyMeasurable ((hba _).mono (𝒢.le _))).indicator hmG
  have hfu := stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hcont hmeas
  have hfm := hfu.integral_prod_left' (μ := volume.restrict (Ioc (0 : ℝ) (T : ℝ)))
  have hT : 0 ≤ (T : ℝ) := NNReal.coe_nonneg T
  have hpreimage (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (T : ℝ)) : s.toNNReal ∈ Icc 0 T := by
    refine ⟨zero_le, ?_⟩
    have hsT : (s.toNNReal : ℝ) ≤ (T : ℝ) := by
      rw [Real.coe_toNNReal s hs.1]
      exact hs.2
    exact_mod_cast hsT
  have hmassMeas : AEStronglyMeasurable (fun ω => ∫ s in (0 : ℝ)..(T : ℝ), |b s.toNNReal ω|) μ := by
    refine hfm.aestronglyMeasurable.congr ?_
    filter_upwards [hG] with ω hω
    change (∫ s in Ioc (0 : ℝ) (T : ℝ), f s ω) = ∫ s in (0 : ℝ)..(T : ℝ), |b s.toNNReal ω|
    rw [intervalIntegral.integral_of_le hT]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    have hsT := (hpreimage s ⟨hs.1.le, hs.2⟩).2
    simp only [f, indicator_of_mem hω, min_eq_left hsT]
  refine (henergy.add (integrable_const (T : ℝ))).mono' hmassMeas ?_
  filter_upwards [hbc] with ω hω
  have hb' := hω.comp continuous_real_toNNReal.continuousOn hpreimage
  have habs : IntervalIntegrable (fun s : ℝ => |b s.toNNReal ω|) volume 0 (T : ℝ) :=
    hb'.abs.intervalIntegrable_of_Icc hT
  have hsq : IntervalIntegrable (fun s : ℝ => b s.toNNReal ω ^ 2) volume 0 (T : ℝ) :=
    (hb'.pow 2).intervalIntegrable_of_Icc hT
  rw [Real.norm_eq_abs, abs_of_nonneg (intervalIntegral.integral_nonneg_of_forall hT
    (fun _ => abs_nonneg _))]
  have hdom (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (T : ℝ)) :
      |b s.toNNReal ω| ≤ b s.toNNReal ω ^ 2 + 1 := by
    nlinarith [sq_nonneg (|b s.toNNReal ω| - 1 / 2), sq_abs (b s.toNNReal ω)]
  have h := intervalIntegral.integral_mono_on hT habs
    (hsq.add (intervalIntegrable_const (c := (1 : ℝ)))) hdom
  rw [intervalIntegral.integral_add hsq intervalIntegrable_const] at h
  simpa only [Pi.add_apply, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] using h

/-- The dyadic integrals of the bounded amplitude cutoffs converge in
mean square to the recovered martingale at every observation time. -/
def HasAmplitudeCutoffIntegral (𝒢 : Filtration ℝ≥0 m) (μ : Measure Ω)
    (T : ℝ≥0) (B V b : ℝ≥0 → Ω → ℝ) : Prop :=
  ∃ J : ℕ → ℝ≥0 → Ω → ℝ, (∀ n, Martingale (J n) 𝒢 μ) ∧
    (∀ n t, MemLp (J n t) 2 μ) ∧
    (∀ (n : ℕ) t, t ≤ T → Tendsto (fun j => eLpNorm
      (gridIntegralProcess ((uniformDyadicGrids T).grid j)
        (fun k ω => min (b ((uniformDyadicGrids T).grid j k) ω) (n : ℝ))
        B (2 ^ j) t - J n t) 2 μ) atTop (𝓝 0)) ∧
    ∀ t, Tendsto (fun n => eLpNorm (J n t - V (min t T)) 2 μ) atTop (𝓝 0)

set_option maxHeartbeats 1000000 in
/-- Two square-integrable martingales on one filtered space, with
rank-one covariance and an orthogonal auxiliary martingale of unit
clock up to the horizon, have one driver for both amplitude integrals. -/
theorem rank_one_pair_has_common_driver [IsProbabilityMeasure μ]
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
      HasAmplitudeCutoffIntegral 𝒢 μ T B M a ∧ HasAmplitudeCutoffIntegral 𝒢 μ T B N b := by
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
  refine ⟨B, hB, hB₂, hB₀, hBc, hBsq, ?_, ?_⟩
  · exact recover hM hM₂ hMc hM₀ hmm hsm hwm hcmm hcsm haa hac ha
      (fun t ω hz => by change a t ω + b t ω = 0 at hz; linarith [ha t ω, hb t ω]) ham
  · exact recover hN hN₂ hNc hN₀ hnn hsn hwn hcnn hcsn hba hbc hb
      (fun t ω hz => by change a t ω + b t ω = 0 at hz; linarith [ha t ω, hb t ω]) hbm

end RoughHeston

#print axioms RoughHeston.rank_one_aggregate_compensators
#print axioms RoughHeston.amplitude_mass_integrable_of_energy
#print axioms RoughHeston.rank_one_pair_has_common_driver
