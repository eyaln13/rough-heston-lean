import FocalBracketRatio
import RankOneFocalDriver
import FiniteHorizonLevy

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Interval Topology

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {F : Filtration ℝ≥0 m} {T : ℝ≥0} {σ : ℝ}
  {X Y U M N J Cx Cy : ℝ≥0 → Ω → ℝ}

noncomputable def varianceAmplitude (σ : ℝ) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  σ * Real.sqrt (X t ω)

noncomputable def focalBracketDensity (σ : ℝ) (U X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  σ * U t ω / Real.sqrt (X t ω)

theorem focalBracketDensity_predictable
    (hU : IsStronglyPredictable F U) (hX : IsStronglyPredictable F X) :
    IsStronglyPredictable F (focalBracketDensity σ U X) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact ((hU.measurable.const_mul σ).div (Real.continuous_sqrt.measurable.comp hX.measurable)).stronglyMeasurable

private theorem realClock_continuousOn {f : ℝ≥0 → ℝ} (hf : ContinuousOn f (Icc 0 T)) :
    ContinuousOn (fun r : ℝ => f r.toNNReal) (Icc (0 : ℝ) (T : ℝ)) := by
  apply hf.comp continuous_real_toNNReal.continuousOn
  intro r hr
  refine ⟨zero_le, ?_⟩
  have he : (r.toNNReal : ℝ) = r := Real.coe_toNNReal _ hr.1
  have hh : (r.toNNReal : ℝ) ≤ (T : ℝ) := he.trans_le hr.2
  exact_mod_cast hh

/-- The two focal cross brackets in the pulsed limit are precisely the
compatibility data for testing its common normalized Brownian driver. -/
theorem pulsed_focal_normalized_test [IsFiniteMeasure μ]
    (hσ : 0 < σ)
    (hM₂ : ∀ t, MemLp (M t) 2 μ) (hN₂ : ∀ t, MemLp (N t) 2 μ) (hJ₂ : ∀ t, MemLp (J t) 2 μ)
    (hXJ : Martingale (fun t => M t * J t - Cx t) F μ)
    (hYJ : Martingale (fun t => N t * J t - Cy t) F μ)
    (hCx : ∀ᵐ ω ∂μ, ∀ t ≤ T, Cx t ω = ∫ s in (0 : ℝ)..(t : ℝ), σ ^ 2 * U s.toNNReal ω)
    (hCy : ∀ᵐ ω ∂μ, ∀ t ≤ T, Cy t ω = ∫ s in (0 : ℝ)..(t : ℝ),
      σ ^ 2 * U s.toNNReal ω * Real.sqrt (Y s.toNNReal ω) / Real.sqrt (X s.toNNReal ω))
    (hXm : Measurable (Function.uncurry X)) (hUm : Measurable (Function.uncurry U))
    (hXc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => X t ω) (Icc 0 T))
    (hYc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => Y t ω) (Icc 0 T))
    (hUc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => U t ω) (Icc 0 T))
    (hParts : ∀ᵐ ω ∂μ, ∀ t ≤ T, 0 ≤ U t ω ∧ U t ω ≤ X t ω)
    (hMass : Integrable (fun ω => ∫ s in (0 : ℝ)..(T : ℝ), |varianceAmplitude σ X s.toNNReal ω|) μ) :
    let a := varianceAmplitude σ X
    let b := varianceAmplitude σ Y
    let q := focalBracketDensity σ U X
    let D (s : ℝ) (ω : Ω) := (a s.toNNReal ω + b s.toNNReal ω) * q s.toNNReal ω
    Martingale (fun t => (M + N) t * J t - (Cx + Cy) t) F μ ∧
      (∀ᵐ ω ∂μ, ∀ t ≤ T, (Cx + Cy) t ω = ∫ s in (0 : ℝ)..(t : ℝ), D s ω) ∧
      (∀ᵐ ω ∂μ, ContinuousOn (fun t => q t ω) (Icc 0 T)) ∧
      (∀ᵐ ω ∂μ, ∀ t ≤ T, a t ω + b t ω = 0 → q t ω = 0) ∧
      Integrable (fun ω => ∫ s in (0 : ℝ)..(T : ℝ), |D s ω|) μ ∧
      Integrable (fun ω => ∫ s in (0 : ℝ)..(T : ℝ), |q s.toNNReal ω|) μ := by
  let a := varianceAmplitude σ X
  let b := varianceAmplitude σ Y
  let q := focalBracketDensity σ U X
  let D (s : ℝ) (ω : Ω) := (a s.toNNReal ω + b s.toNNReal ω) * q s.toNNReal ω
  have hqC : ∀ᵐ ω ∂μ, ContinuousOn (fun t => q t ω) (Icc 0 T) := by
    filter_upwards [hXc, hUc, hParts] with ω hx hu hp
    exact continuousOn_focalBracketRatio hu hx hσ.le (fun t ht => hp t ht.2)
  have hqZero : ∀ᵐ ω ∂μ, ∀ t ≤ T, a t ω + b t ω = 0 → q t ω = 0 := by
    refine ae_of_all _ fun ω t _ hw => ?_
    change σ * Real.sqrt (X t ω) + σ * Real.sqrt (Y t ω) = 0 at hw
    exact focalBracketRatio_eq_zero_of_totalAmplitude_zero (u := U t ω) (y := Y t ω) hσ (by rwa [mul_add])
  have hYamp : ∀ᵐ ω ∂μ, ContinuousOn (fun t => b t ω) (Icc 0 T) :=
    hYc.mono fun ω hω => continuousOn_const.mul (Real.continuous_sqrt.comp_continuousOn hω)
  have hXamp : ∀ᵐ ω ∂μ, ContinuousOn (fun t => a t ω) (Icc 0 T) :=
    hXc.mono fun ω hω => continuousOn_const.mul (Real.continuous_sqrt.comp_continuousOn hω)
  have hDensity : ∀ᵐ ω ∂μ, ∀ t ≤ T, (Cx + Cy) t ω = ∫ s in (0 : ℝ)..(t : ℝ), D s ω := by
    filter_upwards [hCx, hCy, hUc, hYamp, hqC, hParts] with ω hx hy hu hya hqc hp
    intro t ht
    have hR : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast ht
    have hsub : Icc (0 : ℝ) (t : ℝ) ⊆ Icc (0 : ℝ) (T : ℝ) := Icc_subset_Icc le_rfl hR
    have hI (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (0 : ℝ) (T : ℝ))) :
        IntervalIntegrable f volume (0 : ℝ) (t : ℝ) :=
      (hf.mono hsub).intervalIntegrable_of_Icc (NNReal.coe_nonneg _)
    have hUI : IntervalIntegrable (fun s : ℝ => σ ^ 2 * U s.toNNReal ω) volume 0 (t : ℝ) :=
      hI _ (continuousOn_const.mul (realClock_continuousOn hu))
    have hYI : IntervalIntegrable (fun s : ℝ => σ ^ 2 * U s.toNNReal ω *
        Real.sqrt (Y s.toNNReal ω) / Real.sqrt (X s.toNNReal ω)) volume 0 (t : ℝ) := by
      have h := hI _ ((realClock_continuousOn hya).mul (realClock_continuousOn hqc))
      convert h using 1
      funext s
      dsimp [a, b, q, varianceAmplitude, focalBracketDensity]
      ring
    change Cx t ω + Cy t ω = _
    rw [hx t ht, hy t ht, ← intervalIntegral.integral_add hUI hYI]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (NNReal.coe_nonneg t)] at hs
    have hr : s.toNNReal ≤ T := by
      have he : (s.toNNReal : ℝ) = s := Real.coe_toNNReal _ hs.1
      have hr : (s.toNNReal : ℝ) ≤ (T : ℝ) := he.trans_le (hs.2.trans hR)
      exact_mod_cast hr
    obtain ⟨hU, hUX⟩ := hp _ hr
    symm
    simpa only [D, a, b, q, varianceAmplitude, focalBracketDensity, mul_add] using
      (focalBracketSum_eq (σ := σ) (y := Y s.toNNReal ω) hU hUX)
  have hCsum : Martingale (fun t => (M + N) t * J t - (Cx + Cy) t) F μ := by
    convert hXJ.add hYJ using 1
    ext t ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring
  have hCint : Integrable ((Cx + Cy) T) μ := by
    have hp : Integrable ((M + N) T * J T) μ := ((hM₂ T).add (hN₂ T)).integrable_mul (hJ₂ T)
    simpa only [sub_sub_cancel] using hp.sub (hCsum.integrable T)
  have hDabs : Integrable (fun ω => ∫ s in (0 : ℝ)..(T : ℝ), |D s ω|) μ := by
    refine hCint.congr ?_
    filter_upwards [hDensity, hParts] with ω hω hp
    rw [hω T le_rfl]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (NNReal.coe_nonneg T)] at hs
    have hsT : s.toNNReal ≤ T := by
      have hr : (s.toNNReal : ℝ) ≤ (T : ℝ) := (Real.coe_toNNReal _ hs.1).trans_le hs.2
      exact_mod_cast hr
    have ha : 0 ≤ a s.toNNReal ω := mul_nonneg hσ.le (Real.sqrt_nonneg _)
    have hb : 0 ≤ b s.toNNReal ω := mul_nonneg hσ.le (Real.sqrt_nonneg _)
    exact (abs_of_nonneg (mul_nonneg (add_nonneg ha hb) (focalBracketRatio_nonneg hσ.le (hp _ hsT).1))).symm
  have hqMass : Integrable (fun ω => ∫ s in (0 : ℝ)..(T : ℝ), |q s.toNNReal ω|) μ := by
    have hqMeas : Measurable (fun p : ℝ × Ω => |q p.1.toNNReal p.2|) := by
      have hp : Measurable (fun p : ℝ × Ω => (p.1.toNNReal, p.2)) :=
        (continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd
      exact (((hUm.comp hp).const_mul σ).div (Real.continuous_sqrt.measurable.comp (hXm.comp hp))).abs
    have hR : (0 : ℝ) ≤ (T : ℝ) := NNReal.coe_nonneg T
    refine hMass.mono' ?_ ?_
    · simp only [intervalIntegral.integral_of_le hR]
      exact (hqMeas.stronglyMeasurable.integral_prod_left' (μ := volume.restrict (Ioc (0 : ℝ) (T : ℝ)))).aestronglyMeasurable
    · filter_upwards [hParts, hqC, hXamp] with ω hp hqc hax
      rw [Real.norm_eq_abs, abs_of_nonneg (intervalIntegral.integral_nonneg hR (fun _ _ => abs_nonneg _))]
      apply intervalIntegral.integral_mono_on hR
        ((realClock_continuousOn hqc).abs.intervalIntegrable_of_Icc hR)
        ((realClock_continuousOn hax).abs.intervalIntegrable_of_Icc hR)
      intro s hs
      have hsT : s.toNNReal ≤ T := by
        have h : (s.toNNReal : ℝ) ≤ (T : ℝ) := (Real.coe_toNNReal _ hs.1).trans_le hs.2
        exact_mod_cast h
      have hu := hp _ hsT
      change |σ * U s.toNNReal ω / Real.sqrt (X s.toNNReal ω)| ≤ |σ * Real.sqrt (X s.toNNReal ω)|
      rw [abs_of_nonneg (focalBracketRatio_nonneg hσ.le hu.1),
        abs_of_nonneg (mul_nonneg hσ.le (Real.sqrt_nonneg (X s.toNNReal ω)))]
      exact focalBracketRatio_le_sqrt hσ.le hu.1 hu.2
  exact ⟨hCsum, hDensity, hqC, hqZero, hDabs, hqMass⟩

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.pulsed_focal_normalized_test
