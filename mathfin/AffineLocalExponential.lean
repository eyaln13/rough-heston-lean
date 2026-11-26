import MathFin.Probability.Brownian.LevyCharacterization
import AffineDensityMartingale

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℝ≥0 m} {N A b : ℝ≥0 → Ω → ℝ}

/-- The stochastic exponential of a continuous local martingale whose
bracket has a continuous nonnegative density is a local martingale in
the given filtration. Exit times bound both the martingale and the
bracket rate so the verified slow-clock theorem applies. -/
theorem affine_exp_isLocalMartingale_of_bracket_rate [IsProbabilityMeasure μ]
    (hNad : StronglyAdapted 𝒢 N) (hAad : StronglyAdapted 𝒢 A)
    (hbad : StronglyAdapted 𝒢 b)
    (hNc : ∀ ω, Continuous fun t => N t ω)
    (hAc : ∀ ω, Continuous fun t => A t ω)
    (hbc : ∀ ω, Continuous fun t => b t ω)
    (hN : IsLocalMartingale N 𝒢 μ)
    (hN₂ : IsLocalMartingale (fun t ω => N t ω^2-A t ω) 𝒢 μ)
    (hA₀ : ∀ ω, A 0 ω = 0) (hAmon : ∀ ω, Monotone fun t => A t ω)
    (hb₀ : ∀ t ω, 0 ≤ b t ω)
    {K : ℝ} (hstart : ∀ ω, |N 0 ω|+b 0 ω ≤ K)
    (hinc : ∀ ω {s t : ℝ≥0}, s ≤ t → ∀ {D : ℝ}, 0 ≤ D →
      (∀ u ∈ Icc s t, b u ω ≤ D) → A t ω-A s ω ≤ D*((t:ℝ)-(s:ℝ))) :
    IsLocalMartingale (fun t ω => Real.exp (-N t ω-A t ω/2)) 𝒢 μ := by
  let R (t : ℝ≥0) (ω : Ω) := |N t ω|+b t ω
  have hRc (ω : Ω) : Continuous (fun t => R t ω) := (hNc ω).abs.add (hbc ω)
  have hRm (t : ℝ≥0) : Measurable[𝒢 t] (R t) := by
    let _ : MeasurableSpace Ω := 𝒢 t
    exact ((hNad t).measurable.abs).add ((hbad t).measurable)
  have hR₀ (t : ℝ≥0) (ω : Ω) : 0 ≤ R t ω := add_nonneg (abs_nonneg _) (hb₀ t ω)
  have hBase := MathFin.isLocalizingSequence_exitTime_of_measurable (μ := μ) hRm hRc
  obtain ⟨k,hk⟩ := exists_nat_gt (max 1 K)
  let nLevel (n : ℕ) := n+k
  let τ (n : ℕ) := MathFin.exitTime R (nLevel n)
  have hτ : IsLocalizingSequence 𝒢 τ μ := by
    refine ⟨⟨fun n => hBase.isStoppingTime (nLevel n), ?_⟩, ?_⟩
    · filter_upwards [hBase.tendsto_top] with ω hω
      exact hω.comp (tendsto_add_atTop_nat k)
    · filter_upwards [hBase.mono] with ω hω
      exact hω.comp (fun _ _ h => Nat.add_le_add_right h k)
  have hLevel (n : ℕ) : max 1 K < (nLevel n : ℝ) :=
    hk.trans_le (by exact_mod_cast (Nat.le_add_left k n))
  have hτpos (n : ℕ) (ω : Ω) : ⊥ < τ n ω := by
    refine lt_of_not_ge fun h => ?_
    obtain ⟨s,hs,hR⟩ := (MathFin.exitTime_le_iff hRc (nLevel n) 0 ω).mp h
    have hsz : s=0 := le_antisymm hs.2 hs.1
    subst s
    rw [abs_of_nonneg (hR₀ 0 ω)] at hR
    exact (not_le_of_gt (hLevel n)) (hR.trans ((hstart ω).trans (le_max_right _ _)))
  let sTime (n : ℕ) (t : ℝ≥0) (ω : Ω) :=
    (min (t:WithTop ℝ≥0) (τ n ω)).untopA
  have hTτ (n : ℕ) (t : ℝ≥0) (ω : Ω) : (sTime n t ω : WithTop ℝ≥0) ≤ τ n ω := by
    exact (le_of_eq (MathFin.coe_untopA_min t (τ n ω))).trans (min_le_right _ _)
  have hRB (n : ℕ) (t : ℝ≥0) (ω : Ω)
      (ht : (t : WithTop ℝ≥0) ≤ τ n ω) : R t ω ≤ (nLevel n:ℝ) := by
    have h := MathFin.abs_le_of_le_exitTime hRc (hτpos n ω) ht
    rwa [abs_of_nonneg (hR₀ t ω)] at h
  let Nτ (n : ℕ) := stoppedProcess N (τ n)
  let Aτ (n : ℕ) := stoppedProcess A (τ n)
  have hBoundN (n : ℕ) (t : ℝ≥0) (ω : Ω) : |Nτ n t ω| ≤ (nLevel n:ℝ) := by
    change |N (sTime n t ω) ω| ≤ _
    exact (le_add_of_nonneg_right (hb₀ _ _)).trans (hRB n _ ω (hTτ n t ω))
  have hAτ₀ (n : ℕ) (ω : Ω) : Aτ n 0 ω = 0 := by
    simp [Aτ,stoppedProcess,hA₀]
  have hAτinc (n : ℕ) {s t : ℝ≥0} (hst : s ≤ t) (ω : Ω) :
      0 ≤ Aτ n t ω-Aτ n s ω ∧
        Aτ n t ω-Aτ n s ω ≤ (nLevel n:ℝ)*((t:ℝ)-(s:ℝ)) := by
    let s' := sTime n s ω
    let t' := sTime n t ω
    have hs't' : s' ≤ t' := by
      apply WithTop.coe_le_coe.mp
      calc
        (s' : WithTop ℝ≥0) = min (s:WithTop ℝ≥0) (τ n ω) :=
          MathFin.coe_untopA_min s (τ n ω)
        _ ≤ min (t:WithTop ℝ≥0) (τ n ω) := min_le_min_right _ (WithTop.coe_le_coe.mpr hst)
        _ = (t' : WithTop ℝ≥0) := (MathFin.coe_untopA_min t (τ n ω)).symm
    have hRate (u : ℝ≥0) (hu : u ∈ Icc s' t') : b u ω ≤ (nLevel n:ℝ) := by
      have huτ : (u:WithTop ℝ≥0) ≤ τ n ω :=
        (WithTop.coe_le_coe.mpr hu.2).trans (hTτ n t ω)
      exact (le_add_of_nonneg_left (abs_nonneg _)).trans (hRB n u ω huτ)
    have hClock := (MathFin.LevyCharacterization.stoppedClock_sub (τ n ω) hst).2
    change (t':ℝ)-(s':ℝ) ≤ (t:ℝ)-(s:ℝ) at hClock
    change 0 ≤ A t' ω-A s' ω ∧ A t' ω-A s' ω ≤ _
    exact ⟨sub_nonneg.mpr (hAmon ω hs't'),
      (hinc ω hs't' (Nat.cast_nonneg _) hRate).trans
        (mul_le_mul_of_nonneg_left hClock (Nat.cast_nonneg _))⟩
  have hAτBound (n : ℕ) (t : ℝ≥0) (ω : Ω) :
      0 ≤ Aτ n t ω ∧ Aτ n t ω ≤ (nLevel n:ℝ)*(t:ℝ) := by
    simpa only [hAτ₀,sub_zero,NNReal.coe_zero] using hAτinc n (zero_le : 0≤t) ω
  have hNτ (n : ℕ) : Martingale (Nτ n) 𝒢 μ :=
    MathFin.martingale_stoppedProcess_of_locally_bounded hN hNad hNc
      (hτ.isStoppingTime n) (hτpos n)
      (fun _ => ⟨(nLevel n:ℝ),fun t _ ω => by simpa only [Real.norm_eq_abs] using hBoundN n t ω⟩)
  have hCompAd : StronglyAdapted 𝒢 (fun t ω => N t ω^2-A t ω) :=
    fun t => ((hNad t).pow 2).sub (hAad t)
  have hCompC (ω : Ω) : Continuous (fun t => N t ω^2-A t ω) :=
    ((hNc ω).pow 2).sub (hAc ω)
  have hComp (n : ℕ) : Martingale (fun t ω => Nτ n t ω^2-Aτ n t ω) 𝒢 μ := by
    refine MathFin.martingale_stoppedProcess_of_locally_bounded hN₂ hCompAd hCompC
      (hτ.isStoppingTime n) (hτpos n) (fun T => ?_)
    refine ⟨(nLevel n:ℝ)^2+(nLevel n:ℝ)*(T:ℝ),fun t ht ω => ?_⟩
    change ‖Nτ n t ω^2 - Aτ n t ω‖ ≤ _
    have hsq : Nτ n t ω^2 ≤ (nLevel n:ℝ)^2 := by
      rw [← sq_abs (Nτ n t ω)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hBoundN n t ω) 2
    refine (norm_sub_le _ _).trans ?_
    rw [Real.norm_of_nonneg (sq_nonneg _),Real.norm_of_nonneg (hAτBound n t ω).1]
    exact add_le_add hsq ((hAτBound n t ω).2.trans
      (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr ht) (Nat.cast_nonneg _)))
  refine ⟨τ,hτ,fun n => ?_⟩
  rw [MathFin.stoppedProcess_indicator_eq (hτpos n)]
  let L : ℝ := nLevel n
  have hL₁ : 1 ≤ L := (le_max_left _ _).trans (hLevel n).le
  have hL : 0 < L := zero_lt_one.trans_le hL₁
  let U (t : ℝ≥0) (ω : Ω) := Nτ n t ω/L
  let C (t : ℝ≥0) (ω : Ω) := Aτ n t ω/L^2
  have hU : Martingale U 𝒢 μ := by
    have he : U = L⁻¹ • Nτ n := by
      funext t ω
      change Nτ n t ω/L = L⁻¹*Nτ n t ω
      exact div_eq_inv_mul _ _
    rw [he]
    exact (hNτ n).smul L⁻¹
  have hUC : Martingale (fun t ω => U t ω^2-C t ω) 𝒢 μ := by
    convert (hComp n).smul ((L^2)⁻¹) using 1
    funext t ω
    change (Nτ n t ω/L)^2-Aτ n t ω/L^2 = (L^2)⁻¹*(Nτ n t ω^2-Aτ n t ω)
    field_simp
  have hUbound (t : ℝ≥0) (ω : Ω) : |U t ω| ≤ 1 := by
    dsimp [U]
    rw [abs_div,abs_of_nonneg hL.le]
    exact (div_le_one hL).mpr (hBoundN n t ω)
  have hUc (ω : Ω) : Continuous (fun t => U t ω) :=
    (MathFin.continuous_stoppedProcess hNc (τ n) ω).div_const L
  have hSlow : MathFin.LevyQuadraticSums.IsSlowClock C := by
    constructor
    · intro ω
      simp [C,hAτ₀]
    · intro s t hst ω
      change 0 ≤ Aτ n t ω/L^2-Aτ n s ω/L^2
      rw [← sub_div]
      exact div_nonneg (hAτinc n hst ω).1 (sq_nonneg _)
    · intro s t hst ω
      change Aτ n t ω/L^2-Aτ n s ω/L^2 ≤ _
      rw [← sub_div]
      apply (div_le_iff₀ (sq_pos_of_pos hL)).mpr
      have hh : L ≤ L^2 := by nlinarith [mul_nonneg hL.le (sub_nonneg.mpr hL₁)]
      exact (hAτinc n hst ω).2.trans
        ((mul_le_mul_of_nonneg_right hh (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst))).trans_eq (mul_comm _ _))
  have hExp := MathFin.LevyExpMartingale.martingale_exp hSlow hU hUC hUbound hUc (-L)
  constructor
  · convert hExp using 1
    funext t ω
    change Real.exp (-Nτ n t ω-Aτ n t ω/2) =
      Real.exp ((-L)*(Nτ n t ω/L)-(-L)^2*(Aτ n t ω/L^2)/2)
    congr 1
    field_simp
  · intro ω
    exact (MathFin.continuous_stoppedProcess (fun ω => by
      exact Real.continuous_exp.comp ((hNc ω).neg.sub ((hAc ω).div_const 2))) (τ n) ω).isCadlag

#print axioms affine_exp_isLocalMartingale_of_bracket_rate

end RoughHeston
