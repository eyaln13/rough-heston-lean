import GridItoPowerLimit
import BrownianMotion.Auxiliary.StoppedProcess
import BrownianMotion.Auxiliary.Martingale
import BrownianMotion.StochasticIntegral.LocalizingLeastGE
import BrownianMotion.StochasticIntegral.OptionalSampling

/-! Stopping-time localization of the upper even-moment bound. -/

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
theorem continuous_martingale_even_power_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} [F.IsComplete μ] [F.IsRightContinuous]
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
  have hLocal : IsLocalizingSequence F (fun n => leastGE V (n : ℝ)) μ :=
    isLocalizingSequence_leastGE F (fun t => (hX.stronglyMeasurable t).norm)
      (fun ω => (continuous_norm.comp (hXcont ω)).isCadlag)
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

/-- The same moment estimate when continuity is initially specified almost
surely. The complete filtration makes the exceptional path set measurable
already at the initial time. -/
theorem ae_continuous_martingale_even_power_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} [F.IsComplete μ] [F.IsRightContinuous]
    {X C : ℝ≥0 → Ω → ℝ}
    (hX : Martingale X F μ) (hX0 : X 0 =ᵐ[μ] 0)
    (hXcont : ∀ᵐ ω ∂μ, Continuous (fun t => X t ω))
    (hC : Martingale (fun t => X t * X t - C t) F μ)
    (hCcont : ∀ᵐ ω ∂μ, Continuous (fun t => C t ω))
    (hCmono : ∀ᵐ ω ∂μ, Monotone (fun t => C t ω))
    (T : ℝ≥0) (m : ℕ) (hm : 2 ≤ m) :
    (∫⁻ ω, ‖X T ω‖ₑ ^ (2 * m : ℕ) ∂μ) ≤
      boundedMartingaleEvenPowerConstant m *
        (∫⁻ ω, ENNReal.ofReal (C T ω - C 0 ω) ^ m ∂μ) := by
  classical
  let S : Set Ω := {ω | Continuous (fun t => X t ω) ∧ Continuous (fun t => C t ω)}
  let Y (t : ℝ≥0) := S.indicator (X t)
  let D (t : ℝ≥0) := S.indicator (C t)
  have hSae : ∀ᵐ ω ∂μ, ω ∈ S := hXcont.and hCcont
  have hNull : μ Sᶜ = 0 := hSae
  have hS : MeasurableSet[F ⊥] S :=
    (Filtration.IsComplete.measurableSet_of_null (𝓕 := F) hNull ⊥).of_compl
  have hY : Martingale Y F μ := hX.indicator hS
  have hD : Martingale (fun t => Y t * Y t - D t) F μ := by
    have he : (fun t => Y t * Y t - D t) = fun t => S.indicator (X t * X t - C t) := by
      ext t ω
      by_cases hs : ω ∈ S <;> simp [Y, D, Set.indicator, hs]
    rw [he]
    exact hC.indicator hS
  have hY0 : Y 0 =ᵐ[μ] 0 :=
    (hSae.and hX0).mono fun ω hω => by simpa only [Y, Set.indicator_of_mem hω.1] using hω.2
  have hYcont (ω : Ω) : Continuous (fun t => Y t ω) := by
    by_cases hs : ω ∈ S
    · simpa only [Y, Set.indicator_of_mem hs] using hs.1
    · simpa only [Y, Set.indicator_of_notMem hs] using (continuous_const (y := (0 : ℝ)))
  have hDcont (ω : Ω) : Continuous (fun t => D t ω) := by
    by_cases hs : ω ∈ S
    · simpa only [D, Set.indicator_of_mem hs] using hs.2
    · simpa only [D, Set.indicator_of_notMem hs] using (continuous_const (y := (0 : ℝ)))
  have hDmono : ∀ᵐ ω ∂μ, Monotone (fun t => D t ω) :=
    (hSae.and hCmono).mono fun ω hω => by
      simpa only [D, Set.indicator_of_mem hω.1] using hω.2
  have hP := continuous_martingale_even_power_le hY hY0 hYcont hD hDcont hDmono T m hm
  have heY : (∫⁻ ω, ‖Y T ω‖ₑ ^ (2 * m : ℕ) ∂μ) = ∫⁻ ω, ‖X T ω‖ₑ ^ (2 * m : ℕ) ∂μ :=
    lintegral_congr_ae (hSae.mono fun ω hω => by simp only [Y, Set.indicator_of_mem hω])
  have heD : (∫⁻ ω, ENNReal.ofReal (D T ω - D 0 ω) ^ m ∂μ) =
      ∫⁻ ω, ENNReal.ofReal (C T ω - C 0 ω) ^ m ∂μ :=
    lintegral_congr_ae (hSae.mono fun ω hω => by simp only [D, Set.indicator_of_mem hω])
  rwa [heY, heD] at hP

#print axioms ProbabilityTheory.isLocalizingSequence_leastGE
#print axioms MeasureTheory.Martingale.stoppedProcess
#print axioms continuous_martingale_even_power_le
#print axioms ae_continuous_martingale_even_power_le

end RoughHeston
