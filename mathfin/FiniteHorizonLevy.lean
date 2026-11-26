/-
Finite-horizon adaptation of MathFin.Probability.Brownian.LevyCharacterization.
Upstream copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under the Apache License, Version 2.0, in the accompanying LICENSE file.
The adaptation allows the compensator to remain constant after the horizon
and includes the Brownian modification on a filtration containing null sets.
-/
import MathFin.Probability.Brownian.LevyCharacterization
import MathFin.Probability.Brownian.Girsanov.GirsanovFiltered
import MathFin.Probability.Brownian.Ito.StochasticFubiniIto

/-!
Compatibility check for the public MathFin revision on Lean 4.35.
This finite-horizon record is the Brownian part of the theorem statement
with StronglyAdapted, the newer name for the adaptedness predicate.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MathFinBridge

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

structure BrownianOn (P : Measure Ω) (𝓕 : Filtration ℝ≥0 m)
    (T : ℝ≥0) (M : ℝ≥0 → Ω → ℝ) : Prop where
  adapted : StronglyAdapted 𝓕 M
  zero_at_start : M 0 =ᵐ[P] 0
  continuous_paths : ∀ᵐ ω ∂P, ContinuousOn (fun t => M t ω) (Set.Icc 0 T)
  normal_increment : ∀ s t, s ≤ t → t ≤ T →
    Measure.map (fun ω => M t ω - M s ω) P = gaussianReal 0 (t - s)
  independent_of_past : ∀ s t, s ≤ t → t ≤ T →
    Indep (MeasurableSpace.comap (fun ω => M t ω - M s ω) (borel ℝ)) (𝓕 s) P

theorem brownianOn_of_expMartingale [IsProbabilityMeasure P]
    (h : MathFin.IsExpQMartingale P 𝓕 M T)
    (hcts : ∀ᵐ ω ∂P, ContinuousOn (fun t => M t ω) (Set.Icc 0 T)) :
    BrownianOn P 𝓕 T M :=
  ⟨h.adapted, h.zero_start, hcts,
    fun _ _ hst ht => MathFin.increment_map_eq_gaussianReal_of_expMartingale h hst ht,
    fun _ _ hst ht => MathFin.indep_increment_of_expMartingale h hst ht⟩

theorem brownianOn_of_global_compensated_local_martingale [IsProbabilityMeasure P]
    (hadapt : StronglyAdapted 𝓕 M) (hcts : ∀ ω, Continuous (fun t => M t ω))
    (h0 : ∀ ω, M 0 ω = 0) (hM : IsLocalMartingale M 𝓕 P)
    (hM2 : IsLocalMartingale (fun t ω => M t ω ^ 2 - (t : ℝ)) 𝓕 P) :
    BrownianOn P 𝓕 T M :=
  brownianOn_of_expMartingale
    (MathFin.LevyCharacterization.isExpQMartingale_of_localMartingale hadapt hcts h0 hM hM2 T)
    (ae_of_all _ fun ω => (hcts ω).continuousOn)

end MathFinBridge

#print axioms MathFinBridge.brownianOn_of_expMartingale
#print axioms MathFinBridge.brownianOn_of_global_compensated_local_martingale
#print axioms MathFin.LevyCharacterization.isFilteredPreBrownian_of_localMartingale
#print axioms MathFin.StochasticFubini.stochFubini_ofCLM
#print axioms MathFin.Btheta_isFilteredPreBrownian_predictable_of_bdd

/-!
Finite-horizon specialization of the localization argument in
MathFin.Probability.Brownian.LevyCharacterization (Apache-2.0 source).
Here the compensator can be frozen at the terminal time. The public
slow-clock exponential theorem and its L² limit tools do the analytic
work.
-/

open Filter Topology
open scoped Topology

namespace MathFinBridge

open MathFin MathFin.LevyCharacterization MathFin.LevyQuadraticSums
open MathFin.LevyExpMartingale

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 m} {M A : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

private theorem slowClock_stopped (hA : IsSlowClock A) (ρ : Ω → WithTop ℝ≥0) :
    IsSlowClock (stoppedProcess A ρ) where
  zero ω := by simp [stoppedProcess, hA.zero]
  sub_nonneg p q hpq ω := by
    apply hA.sub_nonneg
    exact_mod_cast (sub_nonneg.mp (stoppedClock_sub (ρ ω) hpq).1)
  sub_le p q hpq ω := by
    have h := stoppedClock_sub (ρ ω) hpq
    have hmon : (min (p : WithTop ℝ≥0) (ρ ω)).untopA ≤
        (min (q : WithTop ℝ≥0) (ρ ω)).untopA := by
      exact_mod_cast (sub_nonneg.mp h.1)
    exact (hA.sub_le hmon ω).trans h.2

private theorem exponential_martingale_after_exit [IsProbabilityMeasure P]
    (hM : Martingale M 𝓕 P)
    (hM2 : Martingale (fun t ω => M t ω ^ 2 - A t ω) 𝓕 P)
    (hcts : ∀ ω, Continuous (fun t => M t ω))
    (hAc : ∀ ω, Continuous (fun t => A t ω)) (hA : IsSlowClock A)
    (hM0 : ∀ ω, M 0 ω = 0) (n : ℕ) (a : ℝ) :
    let ρ := exitTime M (n + 1)
    Martingale (fun t ω => Real.exp
      (a * stoppedProcess M ρ t ω - a ^ 2 * stoppedProcess A ρ t ω / 2)) 𝓕 P := by
  let ρ := exitTime M (n + 1)
  let X := stoppedProcess M ρ
  let C := stoppedProcess A ρ
  let U := fun t ω => M t ω ^ 2 - A t ω
  have hρ : IsStoppingTime 𝓕 ρ := isStoppingTime_exitTime_of_measurable
    (fun t => (hM.1 t).measurable) hcts (n + 1)
  have hpos := bot_lt_exitTime hcts hM0 n
  have hX (t : ℝ≥0) (ω : Ω) : |X t ω| ≤ ((n + 1 : ℕ) : ℝ) :=
    abs_stoppedProcess_le hcts hM0 n t ω
  have hCs : IsSlowClock C := slowClock_stopped hA ρ
  have hUcts ω : Continuous (fun t => U t ω) := ((hcts ω).pow 2).sub (hAc ω)
  have hlocalM := Martingale.IsLocalMartingale hM (fun ω => (hcts ω).isCadlag)
  have hlocalU := Martingale.IsLocalMartingale hM2 (fun ω => (hUcts ω).isCadlag)
  have hMX : Martingale X 𝓕 P := martingale_stoppedProcess_of_locally_bounded
    hlocalM hM.1 hcts hρ hpos (fun _ => ⟨_, fun t _ ω => by
      simpa only [Real.norm_eq_abs] using hX t ω⟩)
  have hMU : Martingale (fun t ω => X t ω ^ 2 - C t ω) 𝓕 P := by
    apply martingale_stoppedProcess_of_locally_bounded hlocalU hM2.1 hUcts hρ hpos
    intro R
    refine ⟨((n + 1 : ℕ) : ℝ) ^ 2 + R, fun t ht ω => ?_⟩
    change ‖X t ω ^ 2 - C t ω‖ ≤ _
    rw [Real.norm_eq_abs, abs_le]
    have hsq : X t ω ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ 2 :=
      sq_le_sq' (abs_le.mp (hX t ω)).1 (abs_le.mp (hX t ω)).2
    have hT : (t : ℝ) ≤ R := ht
    have hC0 := hCs.apply_nonneg t ω
    have hCt := hCs.apply_le t ω
    have hR : 0 ≤ (R : ℝ) := R.coe_nonneg
    constructor <;> nlinarith [sq_nonneg (X t ω), sq_nonneg (((n : ℝ) + 1))]
  exact martingale_exp hCs hMX hMU hX (continuous_stoppedProcess hcts _) a

/-- Lévy's exponential test with a bracket clock equal to physical time
up to T. The process and its compensated square may both be frozen
after T. -/
theorem expMartingale_on_horizon_of_clock [IsProbabilityMeasure P]
    (hM : Martingale M 𝓕 P)
    (hM2 : Martingale (fun t ω => M t ω ^ 2 - A t ω) 𝓕 P)
    (hcts : ∀ ω, Continuous (fun t => M t ω))
    (hAc : ∀ ω, Continuous (fun t => A t ω))
    (hA : IsSlowClock A) (hAT : ∀ t ≤ T, ∀ ω, A t ω = (t : ℝ))
    (hM0 : ∀ ω, M 0 ω = 0) :
    MathFin.IsExpQMartingale P 𝓕 M T := by
  let ρ (n : ℕ) := exitTime M (n + 1)
  let X (n : ℕ) := stoppedProcess M (ρ n)
  let C (n : ℕ) := stoppedProcess A (ρ n)
  let E (n : ℕ) (a : ℝ) (t : ℝ≥0) (ω : Ω) :=
    Real.exp (a * X n t ω - a ^ 2 * C n t ω / 2)
  have hCs (n : ℕ) : IsSlowClock (C n) := slowClock_stopped hA (ρ n)
  have hEm (n : ℕ) (a : ℝ) : Martingale (E n a) 𝓕 P :=
    exponential_martingale_after_exit hM hM2 hcts hAc hA hM0 n a
  have hmean (n : ℕ) (a : ℝ) (t : ℝ≥0) : ∫ ω, E n a t ω ∂P = 1 := by
    have h := (hEm n a).setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ t)
      (MeasurableSet.univ : MeasurableSet[𝓕 0] Set.univ)
    simp only [Measure.restrict_univ] at h
    rw [← h]
    have hzero (ω : Ω) : E n a 0 ω = 1 := by
      have hX0 : X n 0 ω = 0 := by simp [X, stoppedProcess, hM0]
      simp [E, hX0, (hCs n).zero]
    simp [hzero]
  have hsq (n : ℕ) (a : ℝ) (t : ℝ≥0) :
      ∫ ω, (E n a t ω) ^ 2 ∂P ≤ Real.exp (a ^ 2 * (t : ℝ)) := by
    calc
      _ ≤ ∫ ω, Real.exp (a ^ 2 * (t : ℝ)) * E n (2 * a) t ω ∂P := by
        refine integral_mono_of_nonneg (.of_forall fun ω => sq_nonneg _)
          (((hEm n (2 * a)).integrable t).const_mul _) (.of_forall fun ω => ?_)
        dsimp only [E]
        rw [sq, ← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.2
        nlinarith [mul_le_mul_of_nonneg_left ((hCs n).apply_le t ω) (sq_nonneg a)]
      _ = _ := by rw [integral_const_mul, hmean, mul_one]
  have hlimit (a : ℝ) (t : ℝ≥0) (ht : t ≤ T) (S : Set Ω) :
      Tendsto (fun n => ∫ ω in S, E n a t ω ∂P) atTop
        (𝓝 (∫ ω in S, Real.exp (a * M t ω - a ^ 2 * (t : ℝ) / 2) ∂P)) := by
    have hf (n : ℕ) : Measurable (E n a t) :=
      (((hEm n a).1 t).mono (𝓕.le t)).measurable
    have hmem (n : ℕ) : MemLp (E n a t) 2 P := by
      refine (MemLp.of_bound (hf n).aestronglyMeasurable (Real.exp (|a| * ((n + 1 : ℕ) : ℝ))) ?_).mono_exponent le_top
      refine .of_forall fun ω => ?_
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact exp_le_exp_abs_mul (hCs n) (abs_stoppedProcess_le hcts hM0 n) a t ω
    let F := fun ω => Real.exp (a * M t ω - a ^ 2 * (t : ℝ) / 2)
    have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => E n a t ω) atTop (𝓝 (F ω)) := by
      refine .of_forall fun ω => ?_
      have hr : ∀ᶠ n : ℕ in atTop, (t : WithTop ℝ≥0) < ρ n ω :=
        (WithTop.tendsto_nhds_top_iff _).1
          ((exitTime_tendsto_top hcts ω).comp (tendsto_add_atTop_nat 1)) t
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hr] with n hn
      have hmin : min (t : WithTop ℝ≥0) (ρ n ω) = t := min_eq_left hn.le
      simp only [E, X, C, F, stoppedProcess, hmin, coe_untopA, hAT t ht]
    have hg : MemLp F 1 P :=
      MemLp.mono_exponent
        (memLp_two_of_subseq_ae_of_sq_bound hmem hf (fun n => hsq n a t) ⟨id, hlim⟩) (by norm_num)
    exact tendsto_setIntegral_of_subseq_ae_of_sq_bound hmem (fun n => hsq n a t) hg
      (fun ns hns => ⟨id, hlim.mono fun ω h => h.comp hns⟩) S
  refine ⟨hM.1, .of_forall hM0, fun a s t hst ht S hS => ?_⟩
  apply tendsto_nhds_unique (hlimit a t ht S)
  refine (hlimit a s (hst.trans ht) S).congr (fun n => ?_)
  exact (hEm n a).setIntegral_eq hst hS

/-- A continuous martingale with the compensated square martingale
on a finite horizon is Brownian on that horizon, with independence
from the given filtration. The hypotheses are stated for the frozen
martingales on the half-line. -/
theorem brownianOn_of_frozen_compensated_martingales [IsProbabilityMeasure P]
    (hM : Martingale M 𝓕 P)
    (hM2 : Martingale (fun t ω => M t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) 𝓕 P)
    (hcts : ∀ ω, Continuous (fun t => M t ω)) (hM0 : ∀ ω, M 0 ω = 0) :
    BrownianOn P 𝓕 T M := by
  let A := fun (t : ℝ≥0) (_ : Ω) => ((min t T : ℝ≥0) : ℝ)
  have hA : IsSlowClock A := by
    have heq : stoppedProcess (fun (t : ℝ≥0) (_ : Ω) => (t : ℝ))
          (fun _ : Ω => (T : WithTop ℝ≥0)) = A := by
      funext t ω
      change ((min (t : WithTop ℝ≥0) (T : WithTop ℝ≥0)).untopA : ℝ) = (min t T : ℝ≥0)
      rw [← WithTop.coe_min, coe_untopA]
    exact heq ▸ isSlowClock_stoppedProcess (fun _ : Ω => (T : WithTop ℝ≥0))
  have hAc : ∀ ω, Continuous (fun t => A t ω) :=
    fun _ => NNReal.continuous_coe.comp (continuous_id.min continuous_const)
  exact brownianOn_of_expMartingale
    (expMartingale_on_horizon_of_clock hM hM2 hcts hAc hA
      (fun t ht _ => by simp only [min_eq_left ht]) hM0)
    (.of_forall fun ω => (hcts ω).continuousOn)

end MathFinBridge

#print axioms MathFinBridge.brownianOn_of_frozen_compensated_martingales

namespace MathFinBridge

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

/-- On a filtration containing the probability-null sets at time zero,
one can impose continuity and the initial value everywhere before
applying the finite-horizon compensated-square characterization. -/
theorem brownianOn_modification_of_measurable_nulls [IsProbabilityMeasure P]
    (hnull : ∀ N : Set Ω, MeasurableSet N → P N = 0 → MeasurableSet[𝓕 0] N)
    (hM : Martingale M 𝓕 P)
    (hM2 : Martingale (fun t ω => M t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) 𝓕 P)
    (hcts : ∀ᵐ ω ∂P, Continuous (fun t => M t ω)) (h0 : M 0 =ᵐ[P] 0) :
    ∃ B : ℝ≥0 → Ω → ℝ, BrownianOn P 𝓕 T B ∧ ∀ t, B t =ᵐ[P] M t := by
  classical
  have hgood : ∀ᵐ ω ∂P, Continuous (fun t => M t ω) ∧ M 0 ω = 0 :=
    hcts.and h0
  obtain ⟨N, hcover, hNm, hNnull⟩ := exists_measurable_superset_of_null (ae_iff.mp hgood)
  let G : Set Ω := Nᶜ
  have hG : ∀ᵐ ω ∂P, ω ∈ G := ae_iff.mpr (by simpa [G] using hNnull)
  have hgood_on {ω : Ω} (hω : ω ∈ G) : Continuous (fun t => M t ω) ∧ M 0 ω = 0 := by
    by_contra hb
    exact hω (hcover hb)
  have hG0 : MeasurableSet[𝓕 0] G := (hnull N hNm hNnull).compl
  let B (t : ℝ≥0) : Ω → ℝ := G.indicator (M t)
  have hB (t : ℝ≥0) : B t =ᵐ[P] M t :=
    hG.mono (fun _ hω => Set.indicator_of_mem hω _)
  have hBm : Martingale B 𝓕 P := hM.indicator hG0
  have hB2 : Martingale (fun t ω => B t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) 𝓕 P := by
    refine ⟨fun t => ((hBm.1 t).pow 2).sub stronglyMeasurable_const, fun s t hst => ?_⟩
    have hE (r : ℝ≥0) : (fun ω => B r ω ^ 2 - ((min r T : ℝ≥0) : ℝ)) =ᵐ[P]
        fun ω => M r ω ^ 2 - ((min r T : ℝ≥0) : ℝ) :=
      (hB r).mono (fun ω hω => by dsimp only; rw [hω])
    exact (condExp_congr_ae (hE t)).trans ((hM2.condExp_ae_eq hst).trans (hE s).symm)
  have hBcts (ω : Ω) : Continuous (fun t => B t ω) := by
    by_cases hω : ω ∈ G
    · simpa only [B, Set.indicator_of_mem hω] using (hgood_on hω).1
    · simp only [B, Set.indicator_of_notMem hω]
      exact continuous_const
  have hB0 (ω : Ω) : B 0 ω = 0 := by
    by_cases hω : ω ∈ G
    · simpa only [B, Set.indicator_of_mem hω] using (hgood_on hω).2
    · exact Set.indicator_of_notMem hω _
  exact ⟨B, brownianOn_of_frozen_compensated_martingales hBm hB2 hBcts hB0, hB⟩


theorem brownianOn_modification_of_frozen_compensated_martingales [IsProbabilityMeasure P]
    (hnull : ∀ N : Set Ω, P N = 0 → MeasurableSet[𝓕 0] N)
    (hM : Martingale M 𝓕 P)
    (hM2 : Martingale (fun t ω => M t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) 𝓕 P)
    (hcts : ∀ᵐ ω ∂P, Continuous (fun t => M t ω)) (h0 : M 0 =ᵐ[P] 0) :
    ∃ B : ℝ≥0 → Ω → ℝ, BrownianOn P 𝓕 T B ∧ ∀ t, B t =ᵐ[P] M t :=
  brownianOn_modification_of_measurable_nulls (fun N _ => hnull N) hM hM2 hcts h0

end MathFinBridge

#print axioms MathFinBridge.brownianOn_modification_of_measurable_nulls
#print axioms MathFinBridge.brownianOn_modification_of_frozen_compensated_martingales

namespace MathFinBridge

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

/-- Finite-horizon Lévy characterization on the joint filtration.
Outside a null set the martingale is recovered up to the horizon as
a Brownian motion relative to that same filtration. -/
theorem brownianOn_of_martingales_up_to_horizon [IsProbabilityMeasure P]
    (hnull : ∀ N : Set Ω, P N = 0 → MeasurableSet[𝓕 0] N)
    (hM : Martingale (fun t => M (min t T)) 𝓕 P)
    (hM2 : Martingale (fun t ω => M (min t T) ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) 𝓕 P)
    (hcts : ∀ᵐ ω ∂P, ContinuousOn (fun t => M t ω) (Set.Icc 0 T))
    (h0 : M 0 =ᵐ[P] 0) :
    ∃ B : ℝ≥0 → Ω → ℝ, BrownianOn P 𝓕 T B ∧ ∀ t ≤ T, B t =ᵐ[P] M t := by
  let X := fun t => M (min t T)
  have hXc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω) := by
    filter_upwards [hcts] with ω hω
    have hc : Continuous (fun t : ℝ≥0 => min t T) := continuous_id.min continuous_const
    have hm : ∀ t, min t T ∈ Set.Icc 0 T := fun t => ⟨zero_le, min_le_right _ _⟩
    exact hω.comp_continuous hc hm
  have hX0 : X 0 =ᵐ[P] 0 := by simpa [X] using h0
  obtain ⟨B, hB, hBver⟩ :=
    brownianOn_modification_of_frozen_compensated_martingales hnull hM hM2 hXc hX0
  exact ⟨B, hB, fun t ht => by simpa only [X, min_eq_left ht] using hBver t⟩

end MathFinBridge

#print axioms MathFinBridge.brownianOn_of_martingales_up_to_horizon
