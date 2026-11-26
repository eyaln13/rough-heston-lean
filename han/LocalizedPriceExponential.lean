import StoppedJointStochasticExponential
import StoppedClusterEnvelope

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston.GirsanovPort

open SHEStochastic SHE SHE.PredictableL2

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} [Approximable F μ] {H : ℝ≥0} {B N : ℝ≥0 → Ω → ℝ}

local notation "ν" => jointPredictableMeasure F μ H

set_option maxHeartbeats 1000000 in
/-- The same predictable stopped exponential row represents every
prefix, including the value at the random stop. -/
theorem stopped_joint_stochastic_exponential_prefix
    (P : FiniteScalarIto.Family F μ H Unit)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hB₂ : ∀ t, MemLp (B t) 2 μ) (hB : Martingale B F μ)
    (hBclock : Martingale (fun t ω => B t ω ^ 2 - ((min t H : ℝ≥0) : ℝ)) F μ)
    (hAgree : ∀ t ≤ H, P.W () t =ᵐ[μ] B t)
    (hN : StronglyAdapted F N) (hNc : ∀ ω, Continuous (fun t => N t ω))
    {g : ℝ≥0 → Ω → ℝ} (hg : IsStronglyPredictable F g) (hgc : ∀ ω, Continuous (fun t => g t ω))
    (u : Lp ℝ 2 ν) (hu : ⇑u =ᵐ[ν] Function.uncurry g)
    (hRep : ∀ t, N t =ᵐ[μ] jointItoIntegralCLM H hB₂ (NativeTimeCut.prior t u))
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτH : ∀ ω, τ ω ≤ H) {K E : ℝ} (hK : 0 ≤ K) (hE : 0 ≤ E)
    (hbd : ∀ ω t, t ≤ τ ω → |jointStochasticExponential N g t ω| ≤ K)
    (hCap : ∀ ω t, t ≤ τ ω → affineEnergyClock g t ω ≤ E) :
    ∃ r : Lp ℝ 2 ν, (⇑r =ᵐ[ν] fun p =>
      controlThrough (fun t ω => jointStochasticExponential N g t ω * g t ω) τ p.1 p.2) ∧
      ∀ t, (fun ω => jointStochasticExponential N g (min t (τ ω)) ω) =ᵐ[μ]
        (fun ω => 1 + jointItoIntegralCLM H hB₂ (NativeTimeCut.prior t r) ω) := by
  obtain ⟨r,hr,_⟩ := stopped_joint_stochastic_exponential P hnull hB₂ hB hBclock hAgree hN hNc
    hg hgc u hu hRep hτ hτH hK hE hbd (fun ω => hCap ω _ le_rfl)
  refine ⟨r,hr,?_⟩
  intro t
  let τ' (ω : Ω) := min t (τ ω)
  have hτ' : IsStoppingTime F (fun ω => (τ' ω : WithTop ℝ≥0)) := by
    simpa only [τ', WithTop.coe_min] using (isStoppingTime_const F t).min hτ
  obtain ⟨v,hv,he⟩ := stopped_joint_stochastic_exponential P hnull hB₂ hB hBclock hAgree hN hNc
    hg hgc u hu hRep hτ' (fun ω => (min_le_right _ _).trans (hτH ω)) hK hE
    (fun ω s hs => hbd ω s (hs.trans (min_le_right _ _)))
    (fun ω => hCap ω _ (min_le_right _ _))
  have hrow : v = NativeTimeCut.prior t r := by
    apply Lp.ext
    filter_upwards [hv, hr, NativeTimeCut.prior_ae t r] with p hp hq hw
    rw [hp,hw,hq]
    simp only [τ', controlThrough, le_min_iff]
    by_cases ht : p.1 ≤ t
    · simp [ht, not_lt.mpr ht]
    · simp [ht, lt_of_not_ge ht]
  rwa [hrow] at he

omit m [IsProbabilityMeasure μ] [Approximable F μ] in
theorem affineEnergyClock_nonneg (g : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    0 ≤ affineEnergyClock g t ω := by
  rw [affineEnergyClock, intervalIntegral.integral_of_le t.coe_nonneg]
  exact integral_nonneg fun _ => sq_nonneg _

omit m in
private theorem coe_envelopeStop_for_price (H : ℝ≥0) (C : ℝ) (E : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    (envelopeStop H C E ω : WithTop ℝ≥0) = min (H : WithTop ℝ≥0) (leastGT E C ω) := by
  unfold envelopeStop
  cases h : leastGT E C ω with
  | top => rw [min_eq_left (le_top : (H : WithTop ℝ≥0) ≤ ⊤)]; rfl
  | coe t => rw [← WithTop.coe_min]; rfl

omit m in
private theorem envelopeStop_mono_threshold (E : ℝ≥0 → Ω → ℝ) (ω : Ω)
    {c d : ℝ} (hcd : c ≤ d) : envelopeStop H c E ω ≤ envelopeStop H d E ω := by
  by_contra! hn
  have h : (envelopeStop H d E ω : WithTop ℝ≥0) < (envelopeStop H c E ω : WithTop ℝ≥0) :=
    WithTop.coe_lt_coe.mpr hn
  rw [coe_envelopeStop_for_price H d E ω] at h
  have hHor : (envelopeStop H c E ω : WithTop ℝ≥0) ≤ (H : WithTop ℝ≥0) :=
    WithTop.coe_le_coe.mpr (envelopeStop_le H c E ω)
  have hd := (min_lt_iff.mp h).resolve_left (not_lt_of_ge hHor)
  obtain ⟨t, ht, he⟩ := leastGT_lt_iff.mp hd
  have hc : leastGT E c ω < (envelopeStop H c E ω : WithTop ℝ≥0) :=
    leastGT_lt_iff.mpr ⟨t, ht, hcd.trans_lt he⟩
  rw [coe_envelopeStop_for_price H c E ω] at hc
  exact (not_lt_of_ge (min_le_right _ _)) hc

/-- Explicit meaning of a local Brownian integral on the fixed joint
filtration. Each stopped row belongs to the ordinary Hilbert-space
Itô integral, and its continuous process agrees simultaneously with
`I` at every time through the stop. On every path the stops eventually
reach the horizon. -/
def HasLocalizedJointBrownianIntegral (H : ℝ≥0) (F : Filtration ℝ≥0 m) (μ : Measure Ω) [IsFiniteMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB₂ : ∀ t, MemLp (B t) 2 μ) (a I : ℝ≥0 → Ω → ℝ) : Prop :=
  ∃ τ : ℕ → Ω → ℝ≥0, (∀ n, IsStoppingTime F (fun ω => (τ n ω : WithTop ℝ≥0))) ∧
    (∀ n ω, τ n ω ≤ H) ∧ (∀ ω, Monotone (fun n => τ n ω)) ∧
    (∀ ω, ∃ n₀, ∀ n ≥ n₀, τ n ω = H) ∧
    ∀ n, ∃ r : Lp ℝ 2 (jointPredictableMeasure F μ H),
      (⇑r =ᵐ[jointPredictableMeasure F μ H] Function.uncurry (controlThrough a (τ n))) ∧
      ∃ Iₙ : ℝ≥0 → Ω → ℝ, StronglyAdapted F Iₙ ∧ (∀ ω, Continuous (fun t => Iₙ t ω)) ∧
        (∀ t, Iₙ t =ᵐ[μ] jointItoIntegralCLM H hB₂ (NativeTimeCut.prior t r)) ∧
        ∀ t ω, I (min t (τ n ω)) ω = Iₙ t ω

set_option maxHeartbeats 1100000 in
/-- The actual stochastic exponential solves the price equation with
one Brownian driver in the original usual filtration. Only the log
integrand is square-integrable. The price integrand is localized. -/
theorem localized_joint_price_exponential
    [F.IsComplete μ] [F.IsRightContinuous]
    (P : FiniteScalarIto.Family F μ H Unit)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hB₂ : ∀ t, MemLp (B t) 2 μ) (hB : Martingale B F μ)
    (hBclock : Martingale (fun t ω => B t ω ^ 2 - ((min t H : ℝ≥0) : ℝ)) F μ)
    (hAgree : ∀ t ≤ H, P.W () t =ᵐ[μ] B t)
    (hN : StronglyAdapted F N) (hNc : ∀ ω, Continuous (fun t => N t ω))
    (hN₀ : ∀ ω, N 0 ω = 0)
    {g : ℝ≥0 → Ω → ℝ} (hg : IsStronglyPredictable F g) (hgc : ∀ ω, Continuous (fun t => g t ω))
    (u : Lp ℝ 2 ν) (hu : ⇑u =ᵐ[ν] Function.uncurry g)
    (hRep : ∀ t, N t =ᵐ[μ] jointItoIntegralCLM H hB₂ (NativeTimeCut.prior t u))
    {s₀ : ℝ} (hs₀ : 0 < s₀) :
    let S := fun t ω => s₀ * jointStochasticExponential N g t ω
    IsStronglyPredictable F S ∧ (∀ ω, Continuous (fun t => S t ω)) ∧
      (∀ ω, S 0 ω = s₀) ∧ (∀ t ω, 0 < S t ω) ∧
      HasLocalizedJointBrownianIntegral H F μ hB₂ (fun t ω => S t ω * g t ω) (fun t ω => S t ω - s₀) := by
  let D := jointStochasticExponential N g
  let S := fun t ω => s₀ * D t ω
  have hDa : StronglyAdapted F D := jointStochasticExponential_adapted hN hg.stronglyAdapted hgc
  have hDc := jointStochasticExponential_continuous hNc hgc
  have hSa : StronglyAdapted F S := fun t => stronglyMeasurable_const.mul (hDa t)
  have hSc (ω : Ω) : Continuous (fun t => S t ω) := continuous_const.mul (hDc ω)
  refine ⟨hSa.isStronglyPredictable_of_leftContinuous (fun ω _ => (hSc ω).continuousWithinAt),hSc,?_,fun _ _ => mul_pos hs₀ (Real.exp_pos _),?_⟩
  · intro ω
    simp [jointStochasticExponential,affineEnergyClock,hN₀ ω]
  let E (t : ℝ≥0) (ω : Ω) := |N t ω| + affineEnergyClock g t ω
  have hEad : StronglyAdapted F E := fun t => (continuous_abs.comp_stronglyMeasurable (hN t)).add
     (affineEnergyClock_stronglyAdapted hg.stronglyAdapted hgc t)
  have hEc (ω : Ω) : Continuous (fun t => E t ω) := (hNc ω).abs.add (affineEnergyClock_continuous hgc ω)
  have hE := hEad.isStronglyPredictable_of_leftContinuous (fun ω _ => (hEc ω).continuousWithinAt)
  let K (n : ℕ) : ℝ := n + 1
  let τ (n : ℕ) (ω : Ω) := envelopeStop H (K n) E ω
  have hτ (n : ℕ) : IsStoppingTime F (fun ω => (τ n ω : WithTop ℝ≥0)) :=
    envelopeStop_isStoppingTime μ H (K n) hE
  have hτH (n : ℕ) (ω : Ω) : τ n ω ≤ H := envelopeStop_le H (K n) E ω
  have hK (n : ℕ) : 0 ≤ K n := by dsimp [K]; positivity
  have hEz (n : ℕ) (ω : Ω) : E 0 ω ≤ K n := by
    simpa [E,hN₀ ω,affineEnergyClock] using hK n
  have hLoc (n : ℕ) (ω : Ω) (t : ℝ≥0) (ht : t ≤ τ n ω) : E t ω ≤ K n :=
    le_threshold_through_envelopeStop ω (hEc ω).continuousOn (hEz n ω) t ht
  refine ⟨τ,hτ,hτH,?_,?_,?_⟩
  · intro ω i j hij
    apply envelopeStop_mono_threshold E ω
    dsimp only [K]
    exact add_le_add_left (Nat.cast_le.mpr hij) 1
  · intro ω
    have hCompact : ContinuousOn (fun t => E t ω) (Icc 0 H) := (hEc ω).continuousOn
    obtain ⟨M,hM⟩ := isCompact_Icc.bddAbove_image hCompact
    obtain ⟨n,hn⟩ := exists_nat_ge M
    refine ⟨n, fun j hj => le_antisymm (hτH j ω) (le_of_not_gt fun h => ?_)⟩
    obtain ⟨t,ht,htE⟩ := (envelopeStop_lt_horizon_iff H (K j) E ω).mp h
    have hEt : E t ω ≤ M := hM ⟨t, ⟨zero_le,ht.le⟩, rfl⟩
    have hMK : M ≤ K j := hn.trans ((Nat.cast_le.mpr hj).trans (by dsimp [K]; linarith))
    exact (not_lt_of_ge (hEt.trans hMK)) htE
  · intro n
    have hNbd (ω : Ω) (t : ℝ≥0) (ht : t ≤ τ n ω) : |D t ω| ≤ Real.exp (K n) := by
      have hA := affineEnergyClock_nonneg g t ω
      have habs := le_abs_self (N t ω)
      change |Real.exp (N t ω - affineEnergyClock g t ω / 2)| ≤ Real.exp (K n)
      rw [abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have hl := hLoc n ω t ht
      dsimp [E] at hl
      linarith
    have hAbd (ω : Ω) (t : ℝ≥0) (ht : t ≤ τ n ω) : affineEnergyClock g t ω ≤ K n :=
      (le_add_of_nonneg_left (abs_nonneg _)).trans (hLoc n ω t ht)
    obtain ⟨r,hr,hI⟩ := stopped_joint_stochastic_exponential_prefix P hnull hB₂ hB hBclock hAgree hN hNc
      hg hgc u hu hRep (hτ n) (hτH n) (Real.exp_pos _).le (hK n) hNbd hAbd
    let r' := s₀ • r
    have hr' : ⇑r' =ᵐ[ν] Function.uncurry (controlThrough (fun t ω => S t ω * g t ω) (τ n)) := by
      filter_upwards [Lp.coeFn_smul s₀ r,hr] with p h₁ h₂
      rw [h₁]
      change s₀ * r p = _
      rw [h₂]
      by_cases h : p.1 ≤ τ n p.2
      · simp [Function.uncurry,controlThrough,h,S,D,mul_assoc]
      · simp [Function.uncurry,controlThrough,h]
    let Iₙ (t : ℝ≥0) (ω : Ω) := S (min t (τ n ω)) ω - s₀
    have hIₙadapt : StronglyAdapted F Iₙ := by
      have h := (hSa.isStronglyProgressive_of_continuous hSc).stronglyAdapted_stoppedProcess (hτ n)
      intro t
      have ht : StronglyMeasurable[F t] (fun ω => stoppedProcess S (fun x => (τ n x : WithTop ℝ≥0)) t ω - s₀) :=
        (h t).sub stronglyMeasurable_const
      convert ht using 1
      funext ω
      simp only [Iₙ, stoppedProcess, ← WithTop.coe_min, WithTop.untopA_eq_untop WithTop.coe_ne_top,
        WithTop.untop_coe]
    have hIₙc (ω : Ω) : Continuous (fun t => Iₙ t ω) :=
      ((hSc ω).comp (continuous_id.min continuous_const)).sub continuous_const
    refine ⟨r',hr',Iₙ,hIₙadapt,hIₙc,?_,fun _ _ => rfl⟩
    intro t
    have hp : NativeTimeCut.prior t r' = s₀ • NativeTimeCut.prior t r := by
      apply Lp.ext
      filter_upwards [NativeTimeCut.prior_ae t r',NativeTimeCut.prior_ae t r,Lp.coeFn_smul s₀ r,
        Lp.coeFn_smul s₀ (NativeTimeCut.prior t r)] with p h₁ h₂ h₃ h₄
      rw [h₁,h₄]
      change (if t < p.1 then 0 else (r' : ℝ≥0 × Ω → ℝ) p) = s₀ * (NativeTimeCut.prior t r) p
      rw [h₂,h₃]
      change (if t < p.1 then 0 else s₀ * r p) = s₀ * (if t < p.1 then 0 else r p)
      by_cases ht : t < p.1 <;> simp [ht]
    rw [hp,map_smul]
    filter_upwards [hI t,Lp.coeFn_smul s₀ (jointItoIntegralCLM H hB₂ (NativeTimeCut.prior t r))] with ω h₁ h₂
    rw [h₂]
    change s₀ * jointStochasticExponential N g (min t (τ n ω)) ω - s₀ = s₀ * _
    rw [h₁]
    ring

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.stopped_joint_stochastic_exponential_prefix
#print axioms RoughHeston.GirsanovPort.localized_joint_price_exponential
