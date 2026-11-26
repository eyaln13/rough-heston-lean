import CanonicalFourthIncrementEnergy

/-! Uniform fourth moments for the cutoff laws of linear-growth coefficients. -/

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston

open MathFin.ItoIntegralCLM

theorem norm_add_one_pow_four_le {u : ℝ} (hu : 0 ≤ u) :
    (1+u)^4 ≤ 8 * (1+u^4) := by
  have h1 : (1+u)^2 ≤ 2*(1+u^2) := by nlinarith [sq_nonneg (1-u)]
  have h2 : (1+u^2)^2 ≤ 2*(1+u^4) := by nlinarith [sq_nonneg (1-u^2)]
  nlinarith [pow_le_pow_left₀ (sq_nonneg (1+u)) h1 2]

theorem growth_fourth_le {ι : Type*} [Fintype ι] {L z : ℝ} {y : ι → ℝ}
    (hy : ‖z‖ ≤ L * (1+‖y‖)) :
    z^4 ≤ 8*L^4*(1+(Fintype.card ι : ℝ)) * (1+∑ i, (y i)^4) := by
  have hY : ‖y‖^4 ≤ (Fintype.card ι : ℝ) * (∑ i, (y i)^4) := by
    have h := pow_le_pow_left₀ (sq_nonneg ‖y‖) (norm_sq_pi_real_le_sum y) 2
    have hs := pow_sum_le_card_mul_sum_pow (s := (Finset.univ : Finset ι))
      (f := fun i => (y i)^2) (fun _ _ => sq_nonneg _) 1
    have he (i : ι) : ((y i)^2)^2 = (y i)^4 := by ring
    simp only [Finset.card_univ, pow_one, he, Nat.reduceAdd] at hs
    nlinarith [h.trans hs]
  have hp := pow_le_pow_left₀ (norm_nonneg z) hy 4
  rw [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity : 0 ≤ z^4), mul_pow] at hp
  calc
    _ ≤ L^4 * (1+‖y‖)^4 := hp
    _ ≤ L^4 * (8*(1+‖y‖^4)) :=
      mul_le_mul_of_nonneg_left (norm_add_one_pow_four_le (norm_nonneg _)) (by positivity)
    _ ≤ _ := by
      have hs : 0 ≤ ∑ i, (y i)^4 := Finset.sum_nonneg fun _ _ => by positivity
      have hp := mul_le_mul_of_nonneg_left hY (show 0 ≤ L^4 by positivity)
      nlinarith [mul_nonneg (show 0 ≤ L^4 by positivity) hs,
        mul_nonneg (show 0 ≤ L^4 by positivity) (show 0 ≤ (Fintype.card ι : ℝ) by positivity)]

/-- Total fourth moment in finite-dimensional real coordinates. -/
noncomputable def canonicalEulerStateFourthMoment {ι : Type*} [Fintype ι]
    (T : ℝ≥0) (μ : Measure (CanonicalPath T (ι → ℝ))) (r : ℝ≥0) : ℝ :=
  ∑ i, ∫ p, (canonicalPathEval T r p i)^4 ∂μ

theorem measurable_canonicalEulerStateFourthMoment {ι : Type*} [Fintype ι]
    (T : ℝ≥0) (μ : Measure (CanonicalPath T (ι → ℝ))) [IsProbabilityMeasure μ] :
    Measurable (canonicalEulerStateFourthMoment T μ) := by
  unfold canonicalEulerStateFourthMoment
  apply Finset.measurable_sum
  intro i _
  have h : Continuous (fun z : ℝ≥0 × CanonicalPath T (ι → ℝ) =>
      (canonicalPathEval T z.1 z.2 i)^4) :=
    ((continuous_apply i).comp (continuous_joint_pathEval T)).pow 4
  exact h.stronglyMeasurable.integral_prod_right'.measurable

/-- Integrating conditional state bounds gives an exact bound in terms
of the time integral of the canonical fourth moment. -/
theorem integral_slice_mean_le_of_state_fourth {ι : Type*} [Fintype ι]
    (T : ℝ≥0) {c : ℝ≥0 → (ι → ℝ) → ℝ} (hc : Continuous (Function.uncurry c))
    {B Q : ℝ} (hB : ∀ r y, ‖c r y‖ ≤ B)
    (hGrowth : ∀ r y, c r y ≤ Q * (1+∑ i, (y i)^4))
    (μ : Measure (CanonicalPath T (ι → ℝ))) [IsProbabilityMeasure μ]
    (h4 : ∀ r i, Integrable (fun p : CanonicalPath T (ι → ℝ) => (canonicalPathEval T r p i)^4) μ)
    {U : ℝ} (hU : ∀ r, canonicalEulerStateFourthMoment T μ r ≤ U)
    (ν : Measure ℝ≥0) [IsFiniteMeasure ν] :
    (∫ r, ∫ p, c r (canonicalPathEval T r p) ∂μ ∂ν) ≤
      Q * (ν.real univ + ∫ r, canonicalEulerStateFourthMoment T μ r ∂ν) := by
  let P := CanonicalPath T (ι → ℝ)
  let F (r : ℝ≥0) (p : P) := c r (canonicalPathEval T r p)
  let G := canonicalEulerStateFourthMoment T μ
  let Z (r : ℝ≥0) (p : P) := ∑ i, (canonicalPathEval T r p i)^4
  let mean (r : ℝ≥0) := ∫ p, F r p ∂μ
  have hG₀ (r : ℝ≥0) : 0 ≤ G r := Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => by positivity
  have hGi : Integrable G ν :=
    (integrable_const U).mono' (measurable_canonicalEulerStateFourthMoment T μ).stronglyMeasurable.aestronglyMeasurable
      (Eventually.of_forall fun r => by rw [Real.norm_of_nonneg (hG₀ r)]; exact hU r)
  have hFc : Continuous (Function.uncurry F) := hc.comp (continuous_fst.prodMk (continuous_joint_pathEval T))
  have hI : Integrable mean ν :=
    (integrable_const B).mono' hFc.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      (Eventually.of_forall fun r => by
        have h := norm_integral_le_of_norm_le_const (μ := μ) (f := F r)
          (Eventually.of_forall fun p => hB r (canonicalPathEval T r p))
        simpa [mean, measureReal_def] using h)
  have hBound (r : ℝ≥0) : mean r ≤ Q * (1+G r) := by
    have hF : Integrable (F r) μ := (integrable_const B).mono'
      (hFc.comp (continuous_const.prodMk continuous_id)).stronglyMeasurable.aestronglyMeasurable
      (Eventually.of_forall fun p => hB r (canonicalPathEval T r p))
    have hZ : Integrable (Z r) μ := integrable_finsetSum _ fun i _ => h4 r i
    have h1 : Integrable (fun p => 1+Z r p) μ := (integrable_const _).add hZ
    have hEq : (∫ p, Z r p ∂μ) = G r := by
      dsimp only [Z, G, canonicalEulerStateFourthMoment]
      rw [integral_finsetSum _ (fun i _ => h4 r i)]
    calc
      _ ≤ ∫ p : P, Q * (1+Z r p) ∂μ :=
        integral_mono hF (h1.const_mul _) (fun p => hGrowth r (canonicalPathEval T r p))
      _ = _ := by
        rw [integral_const_mul, integral_add (integrable_const (1 : ℝ)) hZ, hEq]
        simp
  calc
    _ ≤ ∫ r, Q*(1+G r) ∂ν :=
      integral_mono hI (((integrable_const (1 : ℝ)).add hGi).const_mul _) hBound
    _ = _ := by
      rw [integral_const_mul, integral_add (integrable_const (1 : ℝ)) hGi, integral_const, smul_eq_mul, mul_one]

/-- The bounded canonical martingale problem has a crude fourth-moment
bound. The crude bound is used only to initialize Grönwall. -/
theorem bounded_canonicalEulerStateFourthMoment
    {ι κ : Type*} [Fintype ι] [Fintype κ] {T : ℝ≥0}
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    {x : ι → ℝ} {μ : Measure (CanonicalPath T (ι → ℝ))} [IsProbabilityMeasure μ]
    (hInit : μ {p | canonicalPathEval T 0 p = x} = 1)
    (hb : ∀ i, Continuous (fun z : ℝ≥0 × (ι → ℝ) => b z.1 z.2 i))
    (hσ : ∀ i j, Continuous (fun z : ℝ≥0 × (ι → ℝ) => σ z.1 z.2 i j))
    {B C : ℝ} (hB : ∀ r y i, ‖b r y i‖ ≤ B) (hC₀ : 0 ≤ C)
    (hC : ∀ r y i j, ‖σ r y i j‖ ≤ C)
    (hM : ∀ i, Martingale (canonicalEulerMartingaleCoordinate T b x i)
      (canonicalPathNaturalFiltration T) μ)
    (hQ : ∀ i, Martingale (canonicalEulerCompensatedProduct T b σ x i i)
      (canonicalPathNaturalFiltration T) μ) :
    (∀ r i, Integrable (fun p : CanonicalPath T (ι → ℝ) => (canonicalPathEval T r p i)^4) μ) ∧
    ∃ U : ℝ, ∀ r, canonicalEulerStateFourthMoment T μ r ≤ U := by
  let P := CanonicalPath T (ι → ℝ)
  let K := (boundedMartingaleEvenPowerConstant 2).toReal
  let J := (Fintype.card κ : ℝ) * C^2
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  let U := 8 * ((T : ℝ)^4 * B^4 + K * (T : ℝ)^2 * J^2)
  have hAE : ∀ᵐ p ∂μ, canonicalPathEval T 0 p = x := by
    apply ae_iff.2
    change μ {p | canonicalPathEval T 0 p = x}ᶜ = 0
    have hS : MeasurableSet {p | canonicalPathEval T 0 p = x} :=
      (isClosed_eq (continuous_canonicalPathEval T 0) continuous_const).measurableSet
    rw [measure_compl hS (measure_ne_top _ _), hInit, measure_univ, tsub_self]
  have hAt (r : ℝ≥0) (i : ι) :
      MemLp (fun p : P => canonicalPathEval T r p i - x i) 4 μ ∧
      (∫ p : P, (canonicalPathEval T r p i - x i)^4 ∂μ) ≤ U := by
    have h := integral_fourth_canonicalEulerState_sub_le_energy hInit hb hσ hB hC₀ hC i (hM i) (hQ i)
      (s := 0) (t := r) zero_le
    let ν := eulerTimeSlice 0 (min r T)
    have hMass : ν.real univ = (↑(min r T) : ℝ) := by
      simpa only [NNReal.coe_zero, sub_zero] using eulerTimeSlice_mass 0 (min r T) zero_le
    have hν : ν.real univ ≤ (T : ℝ) := hMass.trans_le (NNReal.coe_le_coe.mpr (min_le_right _ _))
    have hCalc (p : P) (p0 : canonicalPathEval T 0 p = x) :
        canonicalPathEval T r p i - canonicalPathEval T 0 p i = canonicalPathEval T r p i - x i := by
      rw [p0]
    have hAfter := integral_congr_ae (hAE.mono fun p hp => congrArg (· ^ (4 : ℕ)) (hCalc p hp))
    have hRow (d : ℝ≥0 → (ι → ℝ) → ℝ) (B' : ℝ) (hD : ∀ r y, ‖d r y‖ ≤ B') (n : ℕ) :
        (∫ s, ∫ p : P, (d s (canonicalPathEval T s p))^n ∂μ ∂ν) ≤ (B')^n * (T : ℝ) := by
      have hPt (s : ℝ≥0) : ‖∫ p : P, (d s (canonicalPathEval T s p))^n ∂μ‖ ≤ (B')^n := by
        have h := norm_integral_le_of_norm_le_const (μ := μ)
          (f := fun p : P => (d s (canonicalPathEval T s p))^n)
          (Eventually.of_forall fun p => by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hD _ _) n)
        simpa [measureReal_def] using h
      have h := norm_integral_le_of_norm_le_const (μ := ν) (Eventually.of_forall hPt)
      refine (le_abs_self _).trans (h.trans ?_)
      exact mul_le_mul_of_nonneg_left hν (by
        have hpos : 0 ≤ B' := (norm_nonneg (d 0 (fun _ => 0))).trans (hD _ _)
        positivity)
    refine ⟨MemLp.ae_eq (hAE.mono hCalc) h.1, ?_⟩
    rw [← hAfter]
    simp only [zero_min, NNReal.coe_zero, sub_zero] at h
    refine h.2.trans ?_
    have hb2 := hRow (fun r y => b r y i) B (fun r y => hB r y i) 4
    have hc2 := hRow (eulerCovarianceCoefficient σ i i) J (norm_eulerCovarianceCoefficient_le hC₀ hC i i) 2
    have hrt : (↑(min r T) : ℝ) ≤ (T : ℝ) := NNReal.coe_le_coe.mpr (min_le_right _ _)
    have hb3 := mul_le_mul (pow_le_pow_left₀ (NNReal.coe_nonneg _) hrt 3) hb2
      (integral_nonneg fun _ => integral_nonneg fun _ => by positivity) (by positivity : 0 ≤ (T : ℝ)^3)
    have hc3 := mul_le_mul hrt hc2 (integral_nonneg fun _ => integral_nonneg fun _ => by positivity) T.coe_nonneg
    have hK : 0 ≤ K := ENNReal.toReal_nonneg
    have hh := add_le_add hb3 (mul_le_mul_of_nonneg_left hc3 hK)
    rw [mul_assoc (boundedMartingaleEvenPowerConstant 2).toReal]
    exact (mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ 8 by norm_num)).trans_eq (by dsimp [U, K]; ring)
  have hX (r : ℝ≥0) (i : ι) : MemLp (fun p : P => canonicalPathEval T r p i) 4 μ := by
    have h := (hAt r i).1.add (memLp_const (x i))
    convert h using 1
    funext p
    simp
  refine ⟨fun r i => integrable_pow_four_of_memLp (hX r i), ?_⟩
  refine ⟨∑ i, 8*(U + (x i)^4), fun r => Finset.sum_le_sum fun i _ => ?_⟩
  have h := integral_pow_four_add_le (hAt r i).1 (memLp_const (x i) : MemLp (fun _ : P => x i) 4 μ)
  simp only [sub_add_cancel, integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_left (add_le_add (hAt r i).2 le_rfl) (by norm_num))

/-- A row covariance squared is controlled by the common linear growth
constant and the fourth-power state energy. -/
theorem covariance_sq_le_of_growth {ι κ : Type*} [Fintype ι] [Fintype κ]
    {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ} {L : ℝ}
    (hCG : ∀ r y i j, ‖σ r y i j‖ ≤ L * (1+‖y‖)) (i : ι) (r : ℝ≥0) (y : ι → ℝ) :
    (eulerCovarianceCoefficient σ i i r y)^2 ≤
      (Fintype.card κ : ℝ)^2 * (8*L^4*(1+(Fintype.card ι : ℝ))) * (1+∑ i, (y i)^4) := by
  let a (j : κ) := σ r y i j
  let Q := 8*L^4*(1+(Fintype.card ι : ℝ))
  have h := pow_sum_le_card_mul_sum_pow (s := (Finset.univ : Finset κ))
    (f := fun j => (a j)^2) (fun _ _ => sq_nonneg _) 1
  have he (j : κ) : ((a j)^2)^2 = (a j)^4 := by ring
  simp only [Finset.card_univ, pow_one, he, Nat.reduceAdd] at h
  change (∑ j, a j * a j)^2 ≤ _
  simp_rw [← pow_two]
  refine h.trans ?_
  have hSum : ∑ j, (a j)^4 ≤ ∑ _j : κ, Q * (1+∑ i, (y i)^4) :=
    Finset.sum_le_sum fun j _ => growth_fourth_le (hCG r y i j)
  exact (mul_le_mul_of_nonneg_left hSum (by positivity)).trans_eq
    (by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Q]; ring)

/-- Radius-independent uniform fourth moment of the bounded canonical
laws sharing a linear-growth constant. -/
theorem canonicalEulerStateFourthMoment_le_linear_growth
    {ι κ : Type*} [Fintype ι] [Fintype κ] {T : ℝ≥0}
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    {x : ι → ℝ} {μ : Measure (CanonicalPath T (ι → ℝ))} [IsProbabilityMeasure μ]
    (hInit : μ {p | canonicalPathEval T 0 p = x} = 1)
    (hb : ∀ i, Continuous (fun z : ℝ≥0 × (ι → ℝ) => b z.1 z.2 i))
    (hσ : ∀ i j, Continuous (fun z : ℝ≥0 × (ι → ℝ) => σ z.1 z.2 i j))
    {B C L : ℝ} (hB : ∀ r y i, ‖b r y i‖ ≤ B) (hC₀ : 0 ≤ C)
    (hC : ∀ r y i j, ‖σ r y i j‖ ≤ C)
    (hBG : ∀ r y i, ‖b r y i‖ ≤ L * (1+‖y‖))
    (hCG : ∀ r y i j, ‖σ r y i j‖ ≤ L * (1+‖y‖))
    (hM : ∀ i, Martingale (canonicalEulerMartingaleCoordinate T b x i)
      (canonicalPathNaturalFiltration T) μ)
    (hQ : ∀ i, Martingale (canonicalEulerCompensatedProduct T b σ x i i)
      (canonicalPathNaturalFiltration T) μ) (t : ℝ≥0) :
    let Q := 8*L^4*(1+(Fintype.card ι : ℝ))
    let C₄ := (boundedMartingaleEvenPowerConstant 2).toReal
    let K := 64*(Fintype.card ι : ℝ)*Q*((T : ℝ)^3 + C₄*(T : ℝ)*(Fintype.card κ : ℝ)^2)
    let A := 8*(∑ i, (x i)^4) + K*(T : ℝ)
    canonicalEulerStateFourthMoment T μ t ≤ 2*A*Real.exp ((2*K+1)*(T : ℝ)) := by
  dsimp only
  let P := CanonicalPath T (ι → ℝ)
  let G := canonicalEulerStateFourthMoment T μ
  let Q := 8*L^4*(1+(Fintype.card ι : ℝ))
  let C₄ := (boundedMartingaleEvenPowerConstant 2).toReal
  let J := (Fintype.card κ : ℝ)
  let K := 64*(Fintype.card ι : ℝ)*Q*((T : ℝ)^3 + C₄*(T : ℝ)*J^2)
  let A := 8*(∑ i, (x i)^4) + K*(T : ℝ)
  have hQn : 0 ≤ Q := by dsimp [Q]; positivity
  have hC₄ : 0 ≤ C₄ := ENNReal.toReal_nonneg
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hAn : 0 ≤ A := by
    dsimp only [A]
    exact add_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => by positivity))
      (mul_nonneg hK T.coe_nonneg)
  obtain ⟨h4, U, hU⟩ := bounded_canonicalEulerStateFourthMoment hInit hb hσ hB hC₀ hC hM hQ
  have hGN (r : ℝ≥0) : 0 ≤ G r := Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => by positivity
  have hAE : ∀ᵐ p ∂μ, canonicalPathEval T 0 p = x := by
    apply ae_iff.2
    change μ {p | canonicalPathEval T 0 p = x}ᶜ = 0
    have hS : MeasurableSet {p | canonicalPathEval T 0 p = x} :=
      (isClosed_eq (continuous_canonicalPathEval T 0) continuous_const).measurableSet
    rw [measure_compl hS (measure_ne_top _ _), hInit, measure_univ, tsub_self]
  have hLe (r : ℝ≥0) (hr : r ≤ T) :
      G r ≤ A + K*(∫ q in (0 : ℝ)..(r : ℝ), G q.toNNReal) := by
    let ν := timeMeasureHorizon r
    let Δ := (r : ℝ) + (∫ q, G q ∂ν)
    have hΔ : 0 ≤ Δ := add_nonneg r.coe_nonneg (integral_nonneg hGN)
    let H := 64*Q*((T : ℝ)^3 + C₄*(T : ℝ)*J^2)
    have hRow (i : ι) : (∫ p : P, (canonicalPathEval T r p i)^4 ∂μ) ≤ 8*(x i)^4 + H*Δ := by
      let f (p : P) := canonicalPathEval T r p i - canonicalPathEval T 0 p i
      let m := (∫ p, (f p)^4 ∂μ)
      have hInc := integral_fourth_canonicalEulerState_sub_le_energy hInit hb hσ hB hC₀ hC i (hM i) (hQ i)
        (s := 0) (t := r) zero_le
      have hEq : f =ᵐ[μ] fun p => canonicalPathEval T r p i - x i := hAE.mono fun p hp => by simp [f, hp]
      have hPow := integral_pow_four_add_le (MemLp.ae_eq hEq hInc.1)
        (memLp_const (x i) : MemLp (fun _ : P => x i) 4 μ)
      have he : (fun p : P => (f p)^4) =ᵐ[μ] fun p =>
          (canonicalPathEval T r p i - x i)^4 :=
        hEq.mono fun p hp => congrArg (· ^ (4 : ℕ)) hp
      have hm : (∫ p : P, (canonicalPathEval T r p i)^4 ∂μ) ≤ 8*(m + (x i)^4) := by
        rw [← integral_congr_ae he] at hPow
        simpa only [m, sub_add_cancel, integral_const, measureReal_def, measure_univ,
          ENNReal.toReal_one, smul_eq_mul, one_mul] using hPow
      have hb4 (u : ℝ≥0) (y : ι → ℝ) : ‖(b u y i)^4‖ ≤ B^4 := by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hB _ _ _) 4
      have hCov2 (u : ℝ≥0) (y : ι → ℝ) :
          ‖(eulerCovarianceCoefficient σ i i u y)^2‖ ≤ (J*C^2)^2 := by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_eulerCovarianceCoefficient_le hC₀ hC i i u y) 2
      have hbGr := integral_slice_mean_le_of_state_fourth T ((hb i).pow 4) hb4
        (fun u y => growth_fourth_le (hBG u y i)) μ h4 hU ν
      have hcGr := integral_slice_mean_le_of_state_fourth T
        ((continuous_eulerCovarianceCoefficient hσ i i).pow 2) hCov2
        (covariance_sq_le_of_growth hCG i) μ h4 hU ν
      have hν : ν.real univ = (r : ℝ) := euler_timeMeasureHorizon_mass r
      rw [hν] at hbGr hcGr
      change (∫ q, ∫ p : P, (b q (canonicalPathEval T q p) i)^4 ∂μ ∂ν) ≤ Q * Δ at hbGr
      change (∫ q, ∫ p : P, (eulerCovarianceCoefficient σ i i q (canonicalPathEval T q p))^2 ∂μ ∂ν) ≤
        J^2 * Q * Δ at hcGr
      have hInc4 := hInc.2
      simp only [zero_min, NNReal.coe_zero, sub_zero, min_eq_left hr,
        mul_assoc (boundedMartingaleEvenPowerConstant 2).toReal] at hInc4
      have hrT : (r : ℝ) ≤ (T : ℝ) := NNReal.coe_le_coe.mpr hr
      have hbMul := mul_le_mul (pow_le_pow_left₀ r.coe_nonneg hrT 3) hbGr
        (integral_nonneg fun _ => integral_nonneg fun _ => by positivity)
        (by positivity : 0 ≤ (T : ℝ)^3)
      have hcMul := mul_le_mul hrT hcGr
        (integral_nonneg fun _ => integral_nonneg fun _ => by positivity) T.coe_nonneg
      have hh := add_le_add hbMul (mul_le_mul_of_nonneg_left hcMul hC₄)
      have hIncBound := hInc4.trans (mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ 8 by norm_num))
      refine hm.trans ?_
      dsimp only [H, m]
      nlinarith [hIncBound]
    have hJoin : G r ≤ 8*(∑ i, (x i)^4) + K*Δ := by
      unfold G canonicalEulerStateFourthMoment
      calc
        _ ≤ ∑ i, (8*(x i)^4 + H*Δ) := Finset.sum_le_sum fun i _ => hRow i
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          dsimp only [K, H]
          ring
    have hBound := mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr hr) hK
    have hMap : (∫ q, G q ∂ν) = ∫ q in (0 : ℝ)..(r : ℝ), G q.toNNReal :=
      integral_timeMeasureHorizon_eq_intervalIntegral (measurable_canonicalEulerStateFourthMoment T μ) r
    dsimp only [Δ] at hJoin
    rw [hMap] at hJoin
    dsimp only [A]
    linarith
  let g (r : ℝ) := G r.toNNReal
  have hg : Measurable g := (measurable_canonicalEulerStateFourthMoment T μ).comp continuous_real_toNNReal.measurable
  have hGr (r : ℝ) (hr : r ∈ Icc (0 : ℝ) (T : ℝ)) : g r ≤ A + K*(∫ q in (0 : ℝ)..r, g q) := by
    have hRT : r.toNNReal ≤ T := by
      apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal _ hr.1]
      exact hr.2
    have h := hLe _ hRT
    rw [Real.coe_toNNReal _ hr.1] at h
    exact h
  let r := min t T
  have hGT : G t = G r := by
    have he : canonicalEvalTime T t = canonicalEvalTime T r :=
      Subtype.ext (min_eq_left (min_le_right t T)).symm
    simp only [G, canonicalEulerStateFourthMoment, canonicalPathEval, he]
  rw [show canonicalEulerStateFourthMoment T μ t = G t from rfl, hGT]
  have hBnd := le_uniform_exp_of_bounded_measurable_integral_inequality hg hAn hK T.coe_nonneg
    (fun u _ => ⟨hGN u.toNNReal, hU u.toNNReal⟩) hGr (r : ℝ)
    ⟨r.coe_nonneg, NNReal.coe_le_coe.mpr (min_le_right _ _)⟩
  simpa only [g, Real.toNNReal_coe] using hBnd

#print axioms RoughHeston.growth_fourth_le
#print axioms RoughHeston.canonicalEulerStateFourthMoment_le_linear_growth
#print axioms RoughHeston.integral_slice_mean_le_of_state_fourth
#print axioms RoughHeston.bounded_canonicalEulerStateFourthMoment

end RoughHeston
