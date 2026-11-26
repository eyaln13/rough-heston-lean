import ExplicitLebesgueAggregateTightness
import CenteredCanonicalApproximationProof
import CanonicalPairVarianceMomentTests

/-! Final mesh-to-zero limit for the literal pulsed laws. The uniform
separation probability is the sole stochastic input from the burst proof. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

open GirsanovPort
set_option maxHeartbeats 2600000

variable {T : ℝ≥0} {α κ θ σ b v₀ : ℝ}
local notation "Ω₂" => CanonicalPath T (ℝ × ℝ)

/-- A deterministic mesh-to-zero sequence of the actual fractional pulse
laws yields the original pathwise nonuniqueness witnesses from one uniform
separation probability on the same laws. -/
theorem regular_heston_of_explicitLebesguePulseLaws
    (hT : 0 < T) (hα : 1/2 < α) (hα' : α < 1) (hκ : 0 ≤ κ) (hσ : 0 < σ)
    (hb : 0 < b) (hbθ : κ*θ = b) (hv₀ : 0 ≤ v₀)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hε₁ : ∀ n, ε n ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0))
    (hdΔ : ∀ n, lebesguePulseDuration α (ε n) ≤ ε n/b)
    (L : ∀ n, FractionalFixedMeshLaw T α κ σ (lebesgueMeshInitial T b (ε n) v₀)
        (lebesgueMeshInput T α b (ε n)))
    {ℓ : ℝ} (hℓ : 0 < ℓ) {pstar : ℝ≥0∞} (hpstar : 0 < pstar)
    (hgap : ∀ n, pstar ≤ ((L n).pairLaw : Measure Ω₂) {p | ℓ ≤ canonicalPairGap T p}) :
    RegularHestonPair T α v₀ κ θ σ := by
  have hα₀ : 0 < α := by linarith
  let Pn := fun n => (L n).pairLaw
  let C := lebesgueAggregateDeterministicCap α T b v₀
  let width (n : ℕ) := lebesguePulseDuration α (ε n)
  have hwide (n : ℕ) : 0 < width n := Real.rpow_pos_of_pos (hε n) _
  let center (n : ℕ) := explicitPulsedCanonicalCenter T hα₀ (hε n) hb (hwide n)
  have hW0 : Tendsto width atTop (𝓝 0) := hε0.rpow_const_nhds_zero (by positivity : 0 < 1/α)
  have hCenter := tendsto_explicitPulsedCanonicalCenter T hα hα' hb hε hwide hdΔ
    (fun n => lebesguePulseDuration_pow_eq_mass hα₀ (hε n)) hε0 hW0
  have hα₁ : 0 < 2*α-1 := by linarith
  obtain ⟨k,hk⟩ := exists_nat_gt (1/(2*α-1))
  let j := k+1
  have hkPow : (k:ℝ) < ((2^j:ℕ):ℝ) := by exact_mod_cast (Nat.lt_succ_self k).trans j.lt_two_pow_self
  let q : ℝ := ((2*2^j:ℕ):ℝ)
  let e : ℝ := (2*α-1)*((2^j:ℕ):ℝ)
  have he : 1 < e := by
    dsimp [e]
    rw [mul_comm]
    exact (div_lt_iff₀ hα₁).mp (hk.trans hkPow)
  have hq : 2 ≤ q := by
    have h : 1 ≤ (2:ℕ)^j := Nat.one_le_pow _ _ (by decide)
    have hh : 2 ≤ 2*(2:ℕ)^j := by omega
    change (2:ℝ) ≤ ((2*2^j:ℕ):ℝ)
    exact_mod_cast hh
  let D := 2*fractionalCenteredIncrementCap σ α κ T C j
  have hD : D ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top (fractionalCenteredIncrementCap_ne_top _ _ _ _ _ _)
  have hEst (n : ℕ) := lebesguePulse_pairLaw_fourth_and_centered_increment (L n) hT hα hα'
    hκ hσ.le hb (hε n) (hε₁ n) (hdΔ n) hv₀ j
  have hInc (n : ℕ) (s t : CanonicalPathTime T) :
      (∫⁻ p : Ω₂, edist (p s) (p t)^q ∂((Pn n).map (fun p => p-center n) : Measure Ω₂)) ≤ D*edist s t^e :=
    (hEst n).2 s t
  have hStart (n : ℕ) : ((Pn n).map (fun p => p-center n) : Measure Ω₂)
      {f | ‖(v₀,v₀)‖ < ‖f (canonicalEvalTime T 0)‖} = 0 := by
    have hC0 : center n (canonicalEvalTime T 0) = 0 := by
      have hti : ((canonicalEvalTime T 0).val:ℝ) = 0 := by
        change ((min (0:ℝ≥0) T : ℝ≥0):ℝ) = 0
        simp
      simp [center,explicitPulsedCanonicalCenter,hti,volterraConvolution,
        constantImmigrationConvolution,Real.zero_rpow hα₀.ne']
    have hI := (L n).pairLaw_initial (lebesgueMeshInitial_cluster_sum T b (ε n) v₀) rfl
    have hM : Measurable (fun p : Ω₂ => p-center n) := (continuous_id.sub continuous_const).measurable
    have hSet : MeasurableSet {f : Ω₂ | ‖(v₀,v₀)‖ < ‖f (canonicalEvalTime T 0)‖} :=
      (isOpen_lt continuous_const ((continuous_eval_const (canonicalEvalTime T 0)).norm)).measurableSet
    change Measure.map (fun p : Ω₂ => p-center n) (Pn n : Measure Ω₂) _ = 0
    rw [Measure.map_apply hM hSet]
    have ha : ∀ᵐ p : Ω₂ ∂(Pn n : Measure Ω₂), ¬ ‖(v₀,v₀)‖ <
        ‖p (canonicalEvalTime T 0)-center n (canonicalEvalTime T 0)‖ := by
      filter_upwards [hI] with p hp
      rw [hC0, sub_zero]
      exact not_lt.mpr (le_of_eq (congrArg norm hp))
    simpa only [Set.preimage_setOf_eq, ContinuousMap.sub_apply, not_not] using ae_iff.mp ha
  let rate (n : ℕ) := fun s : ℝ≥0 => ∑ i : FixedMeshClusterIndex (T:ℝ) b (ε n),
    lebesgueMeshInput T α b (ε n) (some i) s
  let d (n : ℕ) := canonicalImmigrationShift T b (rate n)
  have hRate (n : ℕ) : rate n = fun s : ℝ≥0 => explicitPulsedRate T b (ε n) (width n) s := by
    funext s
    have h := explicitPulsedRate_eq_lebesgueMeshInput_sum (α := α) (T := (T:ℝ)) hb (hε n) s.coe_nonneg
    simpa only [rate,width,Real.toNNReal_coe] using h.symm
  have hd (t : ℝ≥0) : Tendsto (fun n => d n t) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hε0
    unfold d
    rw [hRate n]
    exact norm_explicitPulsed_canonicalImmigrationShift_le T (hε n) hb (hwide n) (hdΔ n) t
  have hZeroShift (n : ℕ) (t : ℝ≥0) : canonicalImmigrationShift T b
      (lebesgueMeshInput (T:ℝ) α b (ε n) none) t = 0 := by
    unfold canonicalImmigrationShift
    simp only [lebesgueMeshInput,intervalIntegral.integral_const,sub_zero,smul_eq_mul]
    ring
  have hMart (n : ℕ) := by
    have hInv := ae_canonicalAggregatePair_martingale_pullback (θ := θ) hα'
      (lebesgueMeshInitial (T:ℝ) b (ε n) v₀) (lebesgueMeshInput T α b (ε n))
      (lebesgueMeshInitial_cluster_sum T b (ε n) v₀) rfl
      (lebesgueMeshInput_measurable T α b (ε n)) (lebesgueMeshInput_norm_le T α b (ε n))
      (L n).inverse (L n).nonnegative
    have h := canonicalAggregatePairLaw_martingales hα' (d n) (fun _ => 0) (L n).law
      (L n).residualMartingale (L n).productMartingale (L n).nonnegative (by
        filter_upwards [hInv] with p hp t
        simpa only [hbθ, hZeroShift, d, rate] using hp t)
    exact h
  let C₄ := ENNReal.ofReal (fractionalAggregateMomentCap σ α T C 2)
  have hC₄ : C₄ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hFourX (n : ℕ) (t : ℝ≥0) (ht : t ≤ T) :
      (∫⁻ p, ‖canonicalFirstVariance (canonicalPathEval T t p)‖ₑ^4 ∂(Pn n : Measure Ω₂)) ≤ C₄ :=
    ((hEst n).1 t ht).1
  have hFourY (n : ℕ) (t : ℝ≥0) (ht : t ≤ T) :
      (∫⁻ p, ‖canonicalSecondVariance (canonicalPathEval T t p)‖ₑ^4 ∂(Pn n : Measure Ω₂)) ≤ C₄ :=
    ((hEst n).1 t ht).2
  have hX := uniformCanonicalSecondMoment_varianceMartingale_of_variance_fourth (v₀ := v₀) (κ := κ) (θ := θ)
    hα' Pn canonicalFirstVariance hC₄ hFourX
  have hY := uniformCanonicalSecondMoment_varianceMartingale_of_variance_fourth (v₀ := v₀) (κ := κ) (θ := θ)
    hα' Pn canonicalSecondVariance hC₄ hFourY
  have hXX := uniformCanonicalSecondMoment_compensatedProduct_of_variance_fourth
    (v₀ := v₀) (κ := κ) (θ := θ) (σ := σ) hα' Pn canonicalFirstVariance canonicalFirstVariance
    (fun _ => le_max_left _ _) (fun _ => le_max_left _ _) hC₄ hFourX hFourX
  have hXY := uniformCanonicalSecondMoment_compensatedProduct_of_variance_fourth
    (v₀ := v₀) (κ := κ) (θ := θ) (σ := σ) hα' Pn canonicalFirstVariance canonicalSecondVariance
    (fun _ => le_max_left _ _) (fun _ => le_max_left _ _) hC₄ hFourX hFourY
  have hYY := uniformCanonicalSecondMoment_compensatedProduct_of_variance_fourth
    (v₀ := v₀) (κ := κ) (θ := θ) (σ := σ) hα' Pn canonicalSecondVariance canonicalSecondVariance
    (fun _ => le_max_left _ _) (fun _ => le_max_left _ _) hC₄ hFourY hFourY
  exact regular_heston_of_centered_canonical_increment_moments (Pn := Pn) (v₀ := v₀) (κ := κ)
    (θ := θ) hT hα hα' hσ (q := q) (β := e) (A := ‖(v₀,v₀)‖) (C := D) (bn := center)
    (d := d) (e := fun _ _ => 0) hq he hD hCenter hStart hInc
    (fun n => (L n).pairLaw_nonnegative) hℓ hpstar hgap hd (fun _ => tendsto_const_nhds)
    (fun n => (hMart n).1) (fun n => (hMart n).2.1) (fun n => (hMart n).2.2.1)
    (fun n => (hMart n).2.2.2.1) (fun n => (hMart n).2.2.2.2) hX hY hXX hXY hYY

theorem separated_heston_of_explicitLebesguePulseLaws
    (hT : 0 < T) (hα : 1/2 < α) (hα' : α < 1) (hκ : 0 ≤ κ) (hσ : 0 < σ)
    (hb : 0 < b) (hbθ : κ*θ = b) (hv₀ : 0 ≤ v₀)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hε₁ : ∀ n, ε n ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0))
    (hdΔ : ∀ n, lebesguePulseDuration α (ε n) ≤ ε n/b)
    (L : ∀ n, FractionalFixedMeshLaw T α κ σ (lebesgueMeshInitial T b (ε n) v₀)
        (lebesgueMeshInput T α b (ε n)))
    {ℓ : ℝ} (hℓ : 0 < ℓ) {pstar : ℝ≥0∞} (hpstar : 0 < pstar)
    (hgap : ∀ n, pstar ≤ ((L n).pairLaw : Measure Ω₂) {p | ℓ ≤ canonicalPairGap T p}) :
    ∃ (Ω : Type) (m : MeasurableSpace Ω) (μ : @Measure Ω m)
      (F : Filtration ℝ≥0 m) (B X Y : ℝ≥0 → Ω → ℝ),
      IsProbabilityMeasure μ ∧ IsBrownianOn μ F T B ∧
        IsHestonVarianceSolution μ F T α v₀ κ θ σ B X ∧
        IsHestonVarianceSolution μ F T α v₀ κ θ σ B Y ∧
        0 < μ {p | ∃ t ≤ T, X t p ≠ Y t p} := by
  exact (regular_heston_of_explicitLebesguePulseLaws hT hα hα' hκ hσ hb hbθ hv₀
    hε hε₁ hε0 hdΔ L hℓ hpstar hgap).variance

#print axioms RoughHeston.regular_heston_of_explicitLebesguePulseLaws
#print axioms RoughHeston.separated_heston_of_explicitLebesguePulseLaws

end RoughHeston
