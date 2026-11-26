import LocalizedEntropyEnergy
import LocalizedGridBDG
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Interval Topology

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {F : Filtration ℝ≥0 m} {H : ℝ≥0}

omit m in
private theorem stoppedProcess_finite_eq {X : ℝ≥0 → Ω → ℝ}
    {τ : Ω → WithTop ℝ≥0} {ω : Ω} (hτ : τ ω ≠ ⊤) (t : ℝ≥0) :
    stoppedProcess X τ t ω = X (min t (τ ω).untopA) ω :=
  stoppedProcess_of_eq_coe t (WithTop.coe_untopA hτ).symm

omit m in
private theorem stoppedProcess_first_norm_bound {X : ℝ≥0 → Ω → ℝ}
    (hX : ∀ ω, Continuous (fun t => X t ω)) {K : ℝ} (hK : 0 ≤ K)
    {ω : Ω} (hω : X 0 ω = 0) (t : ℝ≥0) :
    ‖stoppedProcess X (leastGE (fun t ω => ‖X t ω‖) K) t ω‖ ≤ K := by
  let τ := leastGE (fun t ω => ‖X t ω‖) K
  by_cases hb : τ ω = ⊥
  · have hτ : τ ω = ((0 : ℝ≥0) : WithTop ℝ≥0) := hb
    rw [stoppedProcess_of_eq_coe t hτ, min_eq_right (zero_le : 0 ≤ t), hω, norm_zero]
    exact hK
  have hw : ω ∈ {ω | ⊥ < leastGE (fun t ω => ‖X t ω‖) K ω} := bot_lt_iff_ne_bot.mpr hb
  have he : stoppedAtNorm X K t ω = stoppedProcess X τ t ω := by
    rw [stoppedAtNorm, stoppedProcess_indicator_comm, Set.indicator_of_mem hw]
    rfl
  have h := stoppedAtNorm_le_add_jump (fun a => (hX a).isCadlag) t ω hK
  have hj (r : ℝ≥0) : Function.jump (fun s => X s ω) r = 0 := by
    rcases (zero_le : 0 ≤ r).eq_or_lt with hr | hr
    · subst r
      exact jump_bot
    · exact (hX ω).continuousAt.jump_eq_zero (nhdsLT_neBot_of_exists_lt ⟨0, hr⟩).ne'
  rwa [hj _, norm_zero, add_zero, he] at h

private theorem integral_stopped_density {d : ℝ → ℝ} (t u : ℝ≥0) :
    (∫ r in 0..(t : ℝ), if r ≤ (u : ℝ) then d r else 0) =
      ∫ r in 0..(min t u : ℝ≥0), d r := by
  have hmin : ((min t u : ℝ≥0) : ℝ) ∈ Icc (0 : ℝ) (t : ℝ) :=
    ⟨(min t u).2, by exact_mod_cast min_le_left _ _⟩
  rw [← intervalIntegral.integral_indicator hmin]
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.2)] at hr
  have he : r ≤ ((min t u : ℝ≥0) : ℝ) ↔ r ≤ (u : ℝ) := by
    rw [NNReal.coe_min, le_min_iff]
    exact and_iff_right hr.2
  change (if r ≤ (u : ℝ) then d r else 0) = (if r ≤ ((min t u : ℝ≥0) : ℝ) then d r else 0)
  simp only [he]

/-- Entropy localization proves integrability of the instantaneous
bracket density divided by a strictly positive continuous martingale. -/
theorem integrable_bracket_ratio_of_continuous_martingale
    [F.IsComplete μ] [F.IsRightContinuous]
    {Z C : ℝ≥0 → Ω → ℝ} {ε : ℝ}
    (hZ : Martingale Z F μ) (hC : Martingale (fun t => Z t * Z t - C t) F μ)
    (hStart : Z 0 =ᵐ[μ] fun _ => ε) (hZ₂ : MemLp (Z H) 2 μ)
    (hZcont : ∀ ω, Continuous (fun t => Z t ω))
    (hCcont : ∀ ω, Continuous (fun t => C t ω))
    (hPos : ∀ᵐ ω ∂μ, ∀ t ≤ H, 0 < Z t ω)
    (hMono : ∀ᵐ ω ∂μ, Monotone (fun t => C t ω))
    (hZmeas : Measurable (Function.uncurry Z))
    {d : ℝ → Ω → ℝ} (hdMeas : Measurable (Function.uncurry d))
    (hdInt : Integrable (Function.uncurry d) ((volume.restrict (Ioc (0 : ℝ) (H : ℝ))).prod μ))
    (hdNN : 0 ≤ᵐ[(volume.restrict (Ioc (0 : ℝ) (H : ℝ))).prod μ] Function.uncurry d)
    (hDensity : ∀ᵐ ω ∂μ, ∀ t ≤ H, C t ω = ∫ r in (0 : ℝ)..(t : ℝ), d r ω) :
    Integrable (fun p : ℝ × Ω => d p.1 p.2 / Z p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (H : ℝ))).prod μ) := by
  let X (t : ℝ≥0) (ω : Ω) := Z t ω - ε
  let V (t : ℝ≥0) (ω : Ω) := ‖X t ω‖
  let τ (n : ℕ) := leastGE V ((n + 1 : ℕ) : ℝ)
  let σ (n : ℕ) (ω : Ω) := min (τ n ω) (H : WithTop ℝ≥0)
  let cut (n : ℕ) (ω : Ω) := (σ n ω).untopA
  let Zn (n : ℕ) := stoppedProcess Z (σ n)
  let Cn (n : ℕ) := stoppedProcess C (σ n)
  let dn (n : ℕ) (r : ℝ) (ω : Ω) := if r ≤ (cut n ω : ℝ) then d r ω else 0
  have hXc (ω : Ω) : Continuous (fun t => X t ω) := (hZcont ω).sub continuous_const
  have hAdV : StronglyAdapted F V := fun t => ((hZ.stronglyMeasurable t).sub stronglyMeasurable_const).norm
  have hLocal : IsLocalizingSequence F (fun n => leastGE V (n : ℝ)) μ :=
    isLocalizingSequence_leastGE F hAdV (fun ω => (continuous_norm.comp (hXc ω)).isCadlag)
  have hτ (n : ℕ) : IsStoppingTime F (τ n) := hLocal.isStoppingTime (n + 1)
  have hσ (n : ℕ) : IsStoppingTime F (σ n) := (hτ n).min (isStoppingTime_const F H)
  have hσH (n : ℕ) (ω : Ω) : σ n ω ≤ (H : WithTop ℝ≥0) := min_le_right _ _
  have hσf (n : ℕ) (ω : Ω) : σ n ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (hσH n ω)
  have hσeq (n : ℕ) (ω : Ω) : (cut n ω : WithTop ℝ≥0) = σ n ω := WithTop.coe_untopA (hσf n ω)
  have hcH (n : ℕ) (ω : Ω) : cut n ω ≤ H := WithTop.coe_le_coe.mp ((hσeq n ω).le.trans (hσH n ω))
  have hCutMeas (n : ℕ) : Measurable (cut n) := (hσ n).measurable'.untopA
  have hZn (n : ℕ) (t : ℝ≥0) (ω : Ω) : Zn n t ω = Z (min t (cut n ω)) ω :=
    stoppedProcess_finite_eq (hσf n ω) t
  have hCn (n : ℕ) (t : ℝ≥0) (ω : Ω) : Cn n t ω = C (min t (cut n ω)) ω :=
    stoppedProcess_finite_eq (hσf n ω) t
  have hRight (ω : Ω) : IsRightContinuous (fun t => Z t ω) := (hZcont ω).isRightContinuous
  have hRight₂ (ω : Ω) : IsRightContinuous (fun t => (Z t * Z t - C t) ω) :=
    (((hZcont ω).mul (hZcont ω)).sub (hCcont ω)).isRightContinuous
  have hZm (n : ℕ) : Martingale (Zn n) F μ := hZ.stoppedProcess hRight (hσ n)
  have hCm (n : ℕ) : Martingale (fun t => Zn n t * Zn n t - Cn n t) F μ :=
    hC.stoppedProcess hRight₂ (hσ n)
  have hMonoCn (n : ℕ) (s t : ℝ≥0) (hst : s ≤ t) : Cn n s ≤ᵐ[μ] Cn n t := by
    filter_upwards [hMono] with ω hw
    change Cn n s ω ≤ Cn n t ω
    rw [hCn, hCn]
    exact hw (min_le_min_right _ hst)
  have hNonnegZn (n : ℕ) (t : ℝ≥0) : ∀ᵐ ω ∂μ, 0 ≤ Zn n t ω := by
    filter_upwards [hPos] with ω hw
    rw [hZn]
    exact (hw _ ((min_le_right _ _).trans (hcH n ω))).le
  have hZnCont (n : ℕ) : ∀ᵐ ω ∂μ, ContinuousOn (fun t => Zn n t ω) (Icc 0 H) :=
    ae_of_all _ fun ω => ((hZcont ω).stoppedProcess (σ n)).continuousOn
  have hZnMeas (n : ℕ) : Measurable (Function.uncurry (Zn n)) := by
    have hpair : Measurable (fun p : ℝ≥0 × Ω => (min p.1 (cut n p.2), p.2)) :=
      (measurable_fst.min ((hCutMeas n).comp measurable_snd)).prodMk measurable_snd
    convert hZmeas.comp hpair using 1
    funext p
    exact hZn n p.1 p.2
  have hBand (n : ℕ) : MeasurableSet {p : ℝ × Ω | p.1 ≤ (cut n p.2 : ℝ)} :=
    measurableSet_le measurable_fst
      (NNReal.continuous_coe.measurable.comp ((hCutMeas n).comp measurable_snd))
  have hDnMeas (n : ℕ) : Measurable (Function.uncurry (dn n)) := hdMeas.indicator (hBand n)
  have hDnInt (n : ℕ) : Integrable (Function.uncurry (dn n)) ((volume.restrict (Ioc (0 : ℝ) (H : ℝ))).prod μ) :=
    hdInt.indicator (hBand n)
  have hDnNN (n : ℕ) : 0 ≤ᵐ[(volume.restrict (Ioc (0 : ℝ) (H : ℝ))).prod μ] Function.uncurry (dn n) := by
    filter_upwards [hdNN] with p hp
    change 0 ≤ d p.1 p.2 at hp
    change 0 ≤ if p.1 ≤ (cut n p.2 : ℝ) then d p.1 p.2 else 0
    split
    · exact hp
    · exact le_rfl
  have hDnDensity (n : ℕ) (t : ℝ≥0) (ht : t ≤ H) :
      Cn n t =ᵐ[μ] fun ω => ∫ r in (0 : ℝ)..(t : ℝ), dn n r ω := by
    filter_upwards [hDensity] with ω hw
    rw [hCn, hw _ ((min_le_left _ _).trans ht)]
    exact (integral_stopped_density t (cut n ω)).symm
  have hBound (n : ℕ) : ∃ K : ℝ, ∀ t, ∀ᵐ ω ∂μ, ‖Zn n t ω‖ ≤ K := by
    refine ⟨((n + 1 : ℕ) : ℝ) + ‖ε‖, fun t => ?_⟩
    filter_upwards [hStart] with ω hw
    have hX0 : X 0 ω = 0 := sub_eq_zero.mpr hw
    have hXτ := stoppedProcess_first_norm_bound hXc (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ))
      hX0 (min t H)
    have he : stoppedProcess X (τ n) (min t H) ω = X (min t (cut n ω)) ω := by
      change X ((min ((min t H : ℝ≥0) : WithTop ℝ≥0) (τ n ω)).untopA) ω = _
      have heq : min ((min t H : ℝ≥0) : WithTop ℝ≥0) (τ n ω) = ((min t (cut n ω) : ℝ≥0) : WithTop ℝ≥0) := by
        calc
          _ = min (min (t : WithTop ℝ≥0) (H : WithTop ℝ≥0)) (τ n ω) := by rw [WithTop.coe_min]
          _ = min (t : WithTop ℝ≥0) (min (τ n ω) (H : WithTop ℝ≥0)) := by ac_rfl
          _ = _ := by rw [WithTop.coe_min, hσeq]
      rw [heq]
      rfl
    rw [he] at hXτ
    rw [hZn]
    have hp : Z (min t (cut n ω)) ω = X (min t (cut n ω)) ω + ε := by simp [X]
    rw [hp]
    exact (norm_add_le _ _).trans (add_le_add_left hXτ _)
  have hMoment (n : ℕ) : (∫ ω, Zn n H ω ^ 2 ∂μ) + (∫ ω, Zn n 0 ω ^ 2 ∂μ) ≤
      (∫ ω, Z H ω ^ 2 ∂μ) + ∫ ω, Z 0 ω ^ 2 ∂μ := by
    have hStop := hZ.stoppedValue_ae_eq_condExp_of_le_const' hRight (hσ n) (hσH n)
    have he : Zn n H =ᵐ[μ] μ[Z H | (hσ n).measurableSpace] := by
      apply hStop.mono
      intro ω hw
      rw [hZn, min_eq_right (hcH n ω)]
      exact hw
    have hNorm := integral_norm_condExp_rpow_le (m := (hσ n).measurableSpace) (p := (2 : ℝ))
      (by norm_num) (f := Z H) (by simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using hZ₂.integrable_sq)
    simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs] at hNorm
    have hz₀ : Zn n 0 = Z 0 := funext fun ω => by rw [hZn, min_eq_left zero_le]
    rw [hz₀]
    apply add_le_add_left
    calc
      _ = ∫ ω, μ[Z H | (hσ n).measurableSpace] ω ^ 2 ∂μ :=
        integral_congr_ae (he.mono fun ω hw => congrArg (fun x : ℝ => x ^ 2) hw)
      _ ≤ _ := hNorm
  let θ := volume.restrict (Ioc (0 : ℝ) (H : ℝ))
  have hθ : ∀ᵐ r ∂θ, r ∈ Ioc (0 : ℝ) (H : ℝ) := ae_restrict_mem measurableSet_Ioc
  have hRhs (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) (H : ℝ)) : r.toNNReal ≤ H := by
    have hc : (r.toNNReal : ℝ) ≤ (H : ℝ) := (Real.coe_toNNReal _ hr.1.le).trans_le hr.2
    exact_mod_cast hc
  have hProdR : ∀ᵐ p ∂θ.prod μ, p.1 ∈ Ioc (0 : ℝ) (H : ℝ) := by
    exact (Measure.quasiMeasurePreserving_fst (μ := θ) (ν := μ)).ae hθ
  have hProdZ : ∀ᵐ p ∂θ.prod μ, ∀ t ≤ H, 0 < Z t p.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := θ) (ν := μ)).ae hPos
  have hCutH : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, cut n ω = H := by
    filter_upwards [hLocal.tendsto_top] with ω hw
    have hlim : Tendsto (fun n => τ n ω) atTop (𝓝 ⊤) := hw.comp (tendsto_add_atTop_nat 1)
    have h : ∀ᶠ n in atTop, (H : WithTop ℝ≥0) < τ n ω :=
      hlim (Ioi_mem_nhds (show (H : WithTop ℝ≥0) < ⊤ from WithTop.coe_lt_top _))
    filter_upwards [h] with n hn
    change (min (τ n ω) (H : WithTop ℝ≥0)).untopA = H
    rw [min_eq_right hn.le]
    rfl
  have hProdCut : ∀ᵐ p ∂θ.prod μ, ∀ᶠ n in atTop, cut n p.2 = H :=
    (Measure.quasiMeasurePreserving_snd (μ := θ) (ν := μ)).ae hCutH
  have hzMeas : Measurable (fun p : ℝ × Ω => Z p.1.toNNReal p.2) :=
    hZmeas.comp ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)
  refine integrable_bracket_ratio_of_localized_martingales hZm hCm hMonoCn hBound hNonnegZn hZnCont
    hDnDensity hZnMeas hDnMeas hDnInt hDnNN hMoment hzMeas hdMeas ?_ hdNN ?_
  · exact (hProdR.and hProdZ).mono fun p hp => hp.2 _ (hRhs _ hp.1)
  · filter_upwards [hProdR, hProdCut] with p hp hcut
    filter_upwards [hcut] with n hn
    exact ⟨by rw [hZn, hn, min_eq_left (hRhs _ hp)], by simp [dn, hn, hp.2]⟩

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.integrable_bracket_ratio_of_continuous_martingale
