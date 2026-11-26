import LocalizedGridBDG
import MathFin.Probability.Brownian.ExitTime

/-! Upper even moments in the original continuous-time filtration.
This adapts the localization in `LocalizedGridBDG` using MathFin's
closed-hit-time theorem, which applies to any filtration. -/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace RoughHeston

private theorem continuous_jump_nnreal_eq_zero {f : ℝ≥0 → ℝ} (hf : Continuous f) (r : ℝ≥0) :
    Function.jump f r = 0 := by
  rcases (zero_le : 0 ≤ r).eq_or_lt with hr | hr
  · subst r
    exact jump_bot
  · exact (hf.continuousAt (x := r)).jump_eq_zero
      (nhdsLT_neBot_of_exists_lt ⟨0, hr⟩).ne'

private theorem stoppedProcess_leastGE_norm_le {Ω : Type*} {X : ℝ≥0 → Ω → ℝ}
    (hX : ∀ ω, Continuous (fun t => X t ω)) (r : ℝ) (hr : 0 ≤ r)
    (ω : Ω) (hzero : X 0 ω = 0) (t : ℝ≥0) :
    ‖stoppedProcess X (leastGE (fun t ω => ‖X t ω‖) r) t ω‖ ≤ r := by
  let τ := leastGE (fun t ω => ‖X t ω‖) r
  by_cases h : τ ω = ⊥
  · have hz : τ ω = ((0 : ℝ≥0) : WithTop ℝ≥0) := h
    change ‖stoppedProcess X τ t ω‖ ≤ r
    rw [stoppedProcess_of_eq_coe t hz, min_eq_right (zero_le : 0 ≤ t), hzero, norm_zero]
    exact hr
  have hw : ω ∈ {ω | ⊥ < leastGE (fun t ω => ‖X t ω‖) r ω} :=
    bot_lt_iff_ne_bot.mpr h
  have he : stoppedAtNorm X r t ω = stoppedProcess X τ t ω := by
    rw [stoppedAtNorm, stoppedProcess_indicator_comm, Set.indicator_of_mem hw]
    rfl
  have hbound := stoppedAtNorm_le_add_jump (fun ω => (hX ω).isCadlag) t ω hr
  rw [continuous_jump_nnreal_eq_zero (hX ω), norm_zero, add_zero, he] at hbound
  exact hbound

private theorem monotone_stoppedProcess_on_path {Ω : Type*} {C : ℝ≥0 → Ω → ℝ}
    (τ : Ω → WithTop ℝ≥0) {ω : Ω} (hC : Monotone (fun t => C t ω)) :
    Monotone (fun t => stoppedProcess C τ t ω) := by
  intro s t hst
  change stoppedProcess C τ s ω ≤ stoppedProcess C τ t ω
  by_cases htop : τ ω = ⊤
  · rw [stoppedProcess_of_eq_top s htop, stoppedProcess_of_eq_top t htop]
    exact hC hst
  · let r := (τ ω).untopA
    have hr : τ ω = ((r : ℝ≥0) : WithTop ℝ≥0) := (WithTop.coe_untopA htop).symm
    rw [stoppedProcess_of_eq_coe s hr, stoppedProcess_of_eq_coe t hr]
    exact hC (min_le_min_right r hst)

private theorem stoppedProcess_le_on_monotone_path {Ω : Type*} {C : ℝ≥0 → Ω → ℝ}
    (τ : Ω → WithTop ℝ≥0) {ω : Ω} (hC : Monotone (fun t => C t ω)) (t : ℝ≥0) :
    stoppedProcess C τ t ω ≤ C t ω := by
  by_cases htop : τ ω = ⊤
  · rw [stoppedProcess_of_eq_top t htop]
  · let r := (τ ω).untopA
    have hr : τ ω = ((r : ℝ≥0) : WithTop ℝ≥0) := (WithTop.coe_untopA htop).symm
    rw [stoppedProcess_of_eq_coe t hr]
    exact hC (min_le_left _ _)

private theorem stoppedProcess_nnreal_zero {Ω : Type*} (Y : ℝ≥0 → Ω → ℝ)
    (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    stoppedProcess Y τ 0 ω = Y 0 ω :=
  stoppedProcess_eq_of_le (show ((0 : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω from bot_le)

/-- The upper even-moment bound for a continuous, zero-start martingale
with a continuous nondecreasing square compensator. Localizing at the
first norm crossing leaves both stopped martingale identities valid.
Fatou's lemma removes the localization bound. -/
theorem continuous_raw_martingale_even_power_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {X C : ℝ≥0 → Ω → ℝ}
    (hX : Martingale X F μ) (hX0 : X 0 =ᵐ[μ] 0)
    (hXcont : ∀ ω, Continuous (fun t => X t ω))
    (hC : Martingale (fun t => X t * X t - C t) F μ)
    (hCcont : ∀ ω, Continuous (fun t => C t ω))
    (hCmono : ∀ᵐ ω ∂μ, Monotone (fun t => C t ω))
    (T : ℝ≥0) (m : ℕ) (hm : 2 ≤ m) :
    (∫⁻ ω, ‖X T ω‖ₑ ^ (2 * m : ℕ) ∂μ) ≤
      boundedMartingaleEvenPowerConstant m *
        (∫⁻ ω, ENNReal.ofReal (C T ω - C 0 ω) ^ m ∂μ) := by
  let V (t : ℝ≥0) (ω : Ω) := ‖X t ω‖
  let τ (n : ℕ) := leastGE V ((n + 1 : ℕ) : ℝ)
  let Xn (n : ℕ) := stoppedProcess X (τ n)
  let Cn (n : ℕ) := stoppedProcess C (τ n)
  have hLocal : IsLocalizingSequence F (fun n => leastGE V (n : ℝ)) μ := by
    have he : (fun n : ℕ => leastGE V (n : ℝ)) = MathFin.exitTime X := by
      funext n ω
      rfl
    rw [he]
    exact MathFin.isLocalizingSequence_exitTime_of_measurable
      (fun t => (hX.stronglyMeasurable t).measurable) hXcont
  have hτ (n : ℕ) : IsStoppingTime F (τ n) := hLocal.isStoppingTime (n + 1)
  have hτlim : ∀ᵐ ω ∂μ, Tendsto (fun n => τ n ω) atTop (𝓝 ⊤) :=
    hLocal.tendsto_top.mono fun ω hω => hω.comp (tendsto_add_atTop_nat 1)
  have hRCX (ω : Ω) : IsRightContinuous (fun t => X t ω) := (hXcont ω).isRightContinuous
  have hRCC (ω : Ω) : IsRightContinuous (fun t => (X t * X t - C t) ω) :=
    (((hXcont ω).mul (hXcont ω)).sub (hCcont ω)).isRightContinuous
  have hXn (n : ℕ) : Martingale (Xn n) F μ := hX.stoppedProcess hRCX (hτ n)
  have hCn (n : ℕ) : Martingale (fun t => Xn n t * Xn n t - Cn n t) F μ := by
    change Martingale (stoppedProcess (fun t => X t * X t - C t) (τ n)) F μ
    exact hC.stoppedProcess hRCC (hτ n)
  have hCmonoN (n : ℕ) (s t : ℝ≥0) (hst : s ≤ t) : Cn n s ≤ᵐ[μ] Cn n t :=
    hCmono.mono fun ω hω => monotone_stoppedProcess_on_path (τ n) hω hst
  have hX0N (n : ℕ) : Xn n 0 =ᵐ[μ] 0 := by
    filter_upwards [hX0] with ω hω
    change stoppedProcess X (τ n) 0 ω = 0
    rw [stoppedProcess_nnreal_zero]
    exact hω
  have hXnBound (n : ℕ) : ∀ᵐ ω ∂μ, ∀ t, ‖Xn n t ω‖ ≤ ((n + 1 : ℕ) : ℝ) := by
    filter_upwards [hX0] with ω hω
    intro t
    exact stoppedProcess_leastGE_norm_le hXcont _ (by positivity) ω hω t
  have hXnCont (n : ℕ) (ω : Ω) : Continuous (fun t => Xn n t ω) :=
    (hXcont ω).stoppedProcess (τ n)
  have hdomC (n : ℕ) : ∀ᵐ ω ∂μ, Cn n T ω - Cn n 0 ω ≤ C T ω - C 0 ω := by
    filter_upwards [hCmono] with ω hω
    change stoppedProcess C (τ n) T ω - stoppedProcess C (τ n) 0 ω ≤ _
    rw [stoppedProcess_nnreal_zero]
    exact sub_le_sub_right (stoppedProcess_le_on_monotone_path (τ n) hω T) _
  let U (n : ℕ) (ω : Ω) := ‖Xn n T ω‖ₑ ^ (2 * m : ℕ)
  let M := boundedMartingaleEvenPowerConstant m *
    (∫⁻ ω, ENNReal.ofReal (C T ω - C 0 ω) ^ m ∂μ)
  have hUn (n : ℕ) : Measurable (U n) :=
    ((((hXn n).stronglyMeasurable T).mono (F.le T)).measurable.enorm).pow_const _
  have hUbd (n : ℕ) : (∫⁻ ω, U n ω ∂μ) ≤ M := by
    have hb := bounded_martingale_even_power_le T (hXn n) (hX0N n) (hCn n)
      (hCmonoN n) (B := ((n + 1 : ℕ) : ℝ)) (by positivity)
      (fun t => (hXnBound n).mono fun _ hω => hω t)
      ((hXnBound n).mono fun _ hω t _ => hω t)
      (Eventually.of_forall fun ω => (hXnCont n ω).continuousOn) m hm
    refine hb.trans (mul_right_mono (lintegral_mono_ae ?_))
    exact (hdomC n).mono fun ω hω =>
      pow_le_pow_left₀ zero_le (ENNReal.ofReal_le_ofReal hω) m
  have he : (fun ω => ‖X T ω‖ₑ ^ (2 * m : ℕ)) =ᵐ[μ]
      (fun ω => liminf (fun n => U n ω) atTop) := by
    filter_upwards [hτlim] with ω hω
    have hnear : ∀ᶠ n : ℕ in atTop, (T : WithTop ℝ≥0) < τ n ω :=
      hω.eventually (Ioi_mem_nhds (WithTop.coe_lt_top T))
    have hEq : (fun n => U n ω) =ᶠ[atTop] (fun _ => ‖X T ω‖ₑ ^ (2 * m : ℕ)) := by
      filter_upwards [hnear] with n hn
      change ‖stoppedProcess X (τ n) T ω‖ₑ ^ (2 * m : ℕ) = _
      rw [stoppedProcess_eq_of_le hn.le]
    exact ((tendsto_const_nhds (x := ‖X T ω‖ₑ ^ (2 * m : ℕ))).congr' hEq.symm).liminf_eq.symm
  calc
    _ = ∫⁻ ω, liminf (fun n => U n ω) atTop ∂μ := lintegral_congr_ae he
    _ ≤ liminf (fun n => ∫⁻ ω, U n ω ∂μ) atTop := lintegral_liminf_le hUn
    _ ≤ liminf (fun _ : ℕ => M) atTop := liminf_le_liminf (Eventually.of_forall hUbd)
    _ = M := liminf_const M

#print axioms RoughHeston.continuous_raw_martingale_even_power_le

end RoughHeston
