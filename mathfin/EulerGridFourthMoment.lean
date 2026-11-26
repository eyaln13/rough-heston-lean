import EulerGridMoments
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Probability.Distributions.Gaussian.Real

/-! A discrete fourth moment estimate for blocks of Euler noise. -/

open MeasureTheory ProbabilityTheory Filter
open scoped MeasureTheory NNReal ENNReal

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

private theorem memLp_four_integrable_pow_four {X : Ω → ℝ}
    (hX : MemLp X 4 μ) : Integrable (fun ω => X ω ^ 4) μ := by
  have h := hX.integrable_norm_pow (p := 4) (by decide)
  convert h using 1
  ext ω
  rw [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity : 0 ≤ X ω ^ 4)]

private theorem integrable_monomial_four {X Y : Ω → ℝ}
    (hX : MemLp X 4 μ) (hY : MemLp Y 4 μ)
    (p q : ℕ) (hpq : p + q = 4) :
    Integrable (fun ω => X ω ^ p * Y ω ^ q) μ := by
  have hSum : Integrable (fun ω => X ω ^ 4 + Y ω ^ 4) μ :=
    (memLp_four_integrable_pow_four hX).add (memLp_four_integrable_pow_four hY)
  refine hSum.mono' ((hX.aestronglyMeasurable.pow p).mul (hY.aestronglyMeasurable.pow q)) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_pow]
  have hPow (x : ℝ) : |x| ^ p * |x| ^ q = x ^ 4 := by
    rw [← pow_add, hpq, ← abs_pow, abs_of_nonneg (by positivity : 0 ≤ x ^ 4)]
  by_cases h : |X ω| ≤ |Y ω|
  · calc
      _ ≤ |Y ω| ^ p * |Y ω| ^ q :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) h _) (by positivity)
      _ = Y ω ^ 4 := hPow _
      _ ≤ _ := le_add_of_nonneg_left (by positivity)
  · calc
      _ ≤ |X ω| ^ p * |X ω| ^ q :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (le_of_not_ge h) _) (by positivity)
      _ = X ω ^ 4 := hPow _
      _ ≤ _ := le_add_of_nonneg_right (by positivity)

private theorem integral_mul_eq_integral_mul_condExp [IsFiniteMeasure μ] {F : MeasurableSpace Ω}
    (hF : F ≤ m) {X Y : Ω → ℝ} (hX : StronglyMeasurable[F] X)
    (hY : Integrable Y μ) (hXY : Integrable (X * Y) μ) :
    (∫ ω, X ω * Y ω ∂μ) = ∫ ω, X ω * μ[Y | F] ω ∂μ :=
  (integral_condExp hF).symm.trans <|
    integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hX hXY hY)

private theorem integral_mul_zero_of_condExp_zero [IsFiniteMeasure μ] {F : MeasurableSpace Ω}
    (hF : F ≤ m) {X Y : Ω → ℝ} (hX : StronglyMeasurable[F] X)
    (hY : Integrable Y μ) (hXY : Integrable (X * Y) μ)
    (hZero : μ[Y | F] =ᵐ[μ] 0) :
    (∫ ω, X ω * Y ω ∂μ) = 0 := by
  rw [integral_mul_eq_integral_mul_condExp hF hX hY hXY]
  simpa using integral_congr_ae (EventuallyEq.rfl.mul hZero : X * μ[Y | F] =ᵐ[μ] X * 0)

/-- A centered martingale step with bounded conditional variance has a
fourth-moment increment controlled by the second moment of the current value
and the fourth moment of the step. -/
theorem integral_add_fourth_le_of_conditional_variance [IsFiniteMeasure μ]
    {F : MeasurableSpace Ω} (hF : F ≤ m) {X Y : Ω → ℝ} {v : ℝ}
    (hX : StronglyMeasurable[F] X) (hX₄ : MemLp X 4 μ) (hY₄ : MemLp Y 4 μ)
    (hZero : μ[Y | F] =ᵐ[μ] 0)
    (hVar : ∀ᵐ ω ∂μ, μ[(fun x => Y x ^ 2) | F] ω ≤ v) :
    (∫ ω, (X ω + Y ω) ^ 4 ∂μ) ≤
      (∫ ω, X ω ^ 4 ∂μ) + 8 * v * (∫ ω, X ω ^ 2 ∂μ) + 3 * (∫ ω, Y ω ^ 4 ∂μ) := by
  have hX₂ : MemLp X 2 μ := hX₄.mono_exponent (by norm_num)
  have hY₂ : MemLp Y 2 μ := hY₄.mono_exponent (by norm_num)
  have hX4 := memLp_four_integrable_pow_four hX₄
  have hY4 := memLp_four_integrable_pow_four hY₄
  have h31 : Integrable (fun ω => X ω ^ 3 * Y ω) μ := by
    simpa using integrable_monomial_four hX₄ hY₄ 3 1 (by decide)
  have h22 : Integrable (fun ω => X ω ^ 2 * Y ω ^ 2) μ :=
    integrable_monomial_four hX₄ hY₄ 2 2 (by decide)
  have hI31 : (∫ ω, X ω ^ 3 * Y ω ∂μ) = 0 :=
    integral_mul_zero_of_condExp_zero hF (hX.pow 3) (hY₂.integrable one_le_two) h31 hZero
  have hEq : μ[(fun ω => X ω ^ 2 * Y ω ^ 2) | F] =ᵐ[μ]
      fun ω => X ω ^ 2 * μ[(fun x => Y x ^ 2) | F] ω :=
    condExp_mul_of_stronglyMeasurable_left (hX.pow 2) h22 hY₂.integrable_sq
  have hI22 : (∫ ω, X ω ^ 2 * Y ω ^ 2 ∂μ) ≤ v * (∫ ω, X ω ^ 2 ∂μ) := by
    have hI := integral_mul_eq_integral_mul_condExp hF (hX.pow 2) hY₂.integrable_sq h22
    change (∫ ω, X ω ^ 2 * Y ω ^ 2 ∂μ) =
      ∫ ω, X ω ^ 2 * μ[(fun x => Y x ^ 2) | F] ω ∂μ at hI
    rw [hI, ← integral_const_mul]
    exact integral_mono_ae (integrable_condExp.congr hEq)
      (hX₂.integrable_sq.const_mul v)
      (hVar.mono fun ω hw => by
        change X ω ^ 2 * μ[(fun x => Y x ^ 2) | F] ω ≤ v * X ω ^ 2
        rw [mul_comm v]
        exact mul_le_mul_of_nonneg_left hw (sq_nonneg _))
  have hPoint (ω : Ω) :
      (X ω + Y ω) ^ 4 ≤
        X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) + 8 * (X ω ^ 2 * Y ω ^ 2) + 3 * Y ω ^ 4 := by
    nlinarith [sq_nonneg (X ω * Y ω - Y ω ^ 2)]
  have hS1 : Integrable (fun ω => X ω ^ 4 + 4 * (X ω ^ 3 * Y ω)) μ :=
    hX4.add (h31.const_mul 4)
  have hS2 : Integrable (fun ω => X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) + 8 * (X ω ^ 2 * Y ω ^ 2)) μ :=
    hS1.add (h22.const_mul 8)
  calc
    _ ≤ ∫ ω, X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) + 8 * (X ω ^ 2 * Y ω ^ 2) + 3 * Y ω ^ 4 ∂μ :=
      integral_mono (memLp_four_integrable_pow_four (hX₄.add hY₄))
        (hS2.add (hY4.const_mul 3)) hPoint
    _ = (∫ ω, X ω ^ 4 ∂μ) + 8 * (∫ ω, X ω ^ 2 * Y ω ^ 2 ∂μ) +
        3 * (∫ ω, Y ω ^ 4 ∂μ) := by
      rw [integral_add hS2 (hY4.const_mul 3), integral_add hS1 (h22.const_mul 8),
        integral_add hX4 (h31.const_mul 4)]
      simp [integral_const_mul, hI31]
    _ ≤ _ := by linarith

private theorem integral_add_sq_le_of_conditional_variance [IsProbabilityMeasure μ]
    {F : MeasurableSpace Ω} (hF : F ≤ m) {X Y : Ω → ℝ} {v : ℝ}
    (hX : StronglyMeasurable[F] X) (hX₂ : MemLp X 2 μ) (hY₂ : MemLp Y 2 μ)
    (hZero : μ[Y | F] =ᵐ[μ] 0)
    (hVar : ∀ᵐ ω ∂μ, μ[(fun x => Y x ^ 2) | F] ω ≤ v) :
    (∫ ω, (X ω + Y ω) ^ 2 ∂μ) ≤ (∫ ω, X ω ^ 2 ∂μ) + v := by
  have hXY : Integrable (fun ω => X ω * Y ω) μ := hX₂.integrable_mul hY₂
  have hXYi := integral_mul_zero_of_condExp_zero hF hX (hY₂.integrable one_le_two) hXY hZero
  have hYi : (∫ ω, Y ω ^ 2 ∂μ) ≤ v := by
    rw [← integral_condExp hF]
    exact (integral_mono_ae integrable_condExp (integrable_const v) hVar).trans_eq (by simp)
  have hSum : Integrable (fun ω => X ω ^ 2 + 2 * (X ω * Y ω)) μ :=
    hX₂.integrable_sq.add (hXY.const_mul 2)
  calc
    _ = ∫ ω, X ω ^ 2 + 2 * (X ω * Y ω) + Y ω ^ 2 ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun ω => by ring
    _ = (∫ ω, X ω ^ 2 ∂μ) + ∫ ω, Y ω ^ 2 ∂μ := by
      rw [integral_add hSum hY₂.integrable_sq, integral_add hX₂.integrable_sq (hXY.const_mul 2)]
      simp [integral_const_mul, hXYi]
    _ ≤ _ := add_le_add (le_refl _) hYi

/-- On any block of a deterministic Euler grid, centered martingale
increments with conditional variance at most `L Δ` and fourth moments
at most `G Δ²` give a noise fourth moment at most `(4L²+3G) Δ²`. -/
theorem integral_runningSum_sub_fourth_le [IsProbabilityMeasure μ]
    (grid : ℕ →o ℝ≥0) {F : Filtration ℕ m} {d : ℕ → Ω → ℝ}
    (hd : ∀ n, StronglyMeasurable[F (n + 1)] (d n)) (hd₄ : ∀ n, MemLp (d n) 4 μ)
    (hZero : ∀ n, μ[d n | F n] =ᵐ[μ] 0)
    {L G : ℝ} (hL : 0 ≤ L) (hG : 0 ≤ G)
    (hVar : ∀ n, ∀ᵐ ω ∂μ, μ[(fun x => d n x ^ 2) | F n] ω ≤
      L * ((grid (n + 1) : ℝ) - (grid n : ℝ)))
    (hFourth : ∀ n, (∫ ω, d n ω ^ 4 ∂μ) ≤ G * ((grid (n + 1) : ℝ) - (grid n : ℝ)) ^ 2)
    {a b : ℕ} (hab : a ≤ b) :
    (∫ ω, (runningSum d b ω - runningSum d a ω) ^ 4 ∂μ) ≤
      (4 * L ^ 2 + 3 * G) * ((grid b : ℝ) - (grid a : ℝ)) ^ 2 := by
  let X (n : ℕ) := runningSum d n - runningSum d a
  let t (n : ℕ) := (grid n : ℝ) - (grid a : ℝ)
  let K := 4 * L ^ 2 + 3 * G
  have hA := adapted_runningSum hd
  have hXm {n : ℕ} (hn : a ≤ n) : StronglyMeasurable[F n] (X n) :=
    (hA n).sub ((hA a).mono (F.mono hn))
  have hX₄ (n : ℕ) : MemLp (X n) 4 μ := (memLp_runningSum hd₄ n).sub (memLp_runningSum hd₄ a)
  have h₂₄ (n : ℕ) (hn : a ≤ n) :
      (∫ ω, X n ω ^ 2 ∂μ) ≤ L * t n ∧
      (∫ ω, X n ω ^ 4 ∂μ) ≤ K * (t n)^2 := by
    induction n, hn using Nat.le_induction with
    | base => simp [X, t, Pi.sub_apply]
    | succ n hn ih =>
      let Δ := (grid (n + 1) : ℝ) - (grid n : ℝ)
      have hΔ : 0 ≤ Δ := sub_nonneg.mpr (NNReal.coe_le_coe.mpr (grid.monotone n.le_succ))
      have ht : 0 ≤ t n := sub_nonneg.mpr (NNReal.coe_le_coe.mpr (grid.monotone hn))
      have htS : t (n + 1) = t n + Δ := by dsimp [t, Δ]; ring
      have hXS (ω : Ω) : X (n + 1) ω = X n ω + d n ω := by
        simp only [X, runningSum_succ, Pi.add_apply, Pi.sub_apply]
        ring
      have hCurrent := hXm hn
      have hSecond := integral_add_sq_le_of_conditional_variance (F.le n) hCurrent
        ((hX₄ n).mono_exponent (show (2 : ℝ≥0∞) ≤ 4 by norm_num))
        ((hd₄ n).mono_exponent (show (2 : ℝ≥0∞) ≤ 4 by norm_num)) (hZero n) (hVar n)
      have hFourthStep := integral_add_fourth_le_of_conditional_variance (F.le n) hCurrent
        (hX₄ n) (hd₄ n) (hZero n) (hVar n)
      simp_rw [hXS]
      rw [htS]
      constructor
      · exact hSecond.trans (by
          have h := ih.1
          change _ ≤ _ + L * Δ at hSecond
          rw [mul_add]
          exact add_le_add h le_rfl)
      · refine hFourthStep.trans ?_
        have hJoin :
            (∫ ω, X n ω ^ 4 ∂μ) + 8 * (L * Δ) * (∫ ω, X n ω ^ 2 ∂μ) +
                3 * (∫ ω, d n ω ^ 4 ∂μ) ≤
              K * (t n)^2 + 8 * (L * Δ) * (L * t n) + 3 * (G * Δ^2) :=
          add_le_add (add_le_add ih.2 (mul_le_mul_of_nonneg_left ih.1 (by positivity)))
            (mul_le_mul_of_nonneg_left (hFourth n) (by norm_num))
        apply hJoin.trans
        dsimp only [K]
        nlinarith [sq_nonneg L, sq_nonneg Δ, mul_nonneg (sq_nonneg L) (sq_nonneg Δ),
          mul_nonneg hG (mul_nonneg ht hΔ)]
  exact (h₂₄ b hab).2

/-- The fixed standard Gaussian moment needed for the grid estimate. -/
noncomputable def standardGaussianFourthMoment : ℝ :=
  ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1

theorem standardGaussianFourthMoment_nonneg : 0 ≤ standardGaussianFourthMoment :=
  integral_nonneg (fun _ => by positivity)

/-- A centered real Gaussian of variance `v` has fourth moment given by
the standard Gaussian fourth moment times `v²`. -/
theorem integral_fourth_of_hasLaw_gaussianReal {Z : Ω → ℝ} {v : ℝ≥0}
    (hZ : HasLaw Z (gaussianReal 0 v) μ) :
    (∫ ω, Z ω ^ 4 ∂μ) = (v : ℝ)^2 * standardGaussianFourthMoment := by
  let c := Real.sqrt (v : ℝ)
  have hc : c ^ 2 = (v : ℝ) := Real.sq_sqrt v.coe_nonneg
  have hv : (⟨c^2, sq_nonneg c⟩ : ℝ≥0) = v := Subtype.ext hc
  have hMap : (gaussianReal 0 1).map (fun x : ℝ => c * x) = gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    exact congrArg (gaussianReal 0) hv
  have hPower : AEStronglyMeasurable (fun x : ℝ => x^4) (gaussianReal 0 v) :=
    (continuous_id.pow 4).stronglyMeasurable.aestronglyMeasurable
  calc
    _ = ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v := hZ.integral_comp hPower
    _ = ∫ x : ℝ, (c * x) ^ 4 ∂gaussianReal 0 1 := by
      rw [← hMap]
      exact integral_map_of_stronglyMeasurable
        (show Measurable (fun x : ℝ => c * x) from (continuous_const.mul continuous_id).measurable)
        (show StronglyMeasurable (fun x : ℝ => x^4) from (continuous_id.pow 4).stronglyMeasurable)
    _ = _ := by
      simp_rw [mul_pow]
      rw [integral_const_mul]
      have hc4 : c^4 = (v : ℝ)^2 := calc
        _ = (c^2)^2 := by ring
        _ = _ := by rw [hc]
      rw [hc4]
      rfl

/-- A bounded random row maps vector increments with uniform fourth
moments to a scalar increment with a uniform fourth moment. This estimate
does not require independence of the components. -/
theorem memLp_and_integral_weighted_sum_fourth_le {κ : Type*} [Fintype κ]
    {a d : κ → Ω → ℝ} {C H : ℝ}
    (ha : ∀ j, AEStronglyMeasurable (a j) μ)
    (hC : ∀ j ω, |a j ω| ≤ C) (hd₄ : ∀ j, MemLp (d j) 4 μ)
    (hH : ∀ j, (∫ ω, d j ω ^ 4 ∂μ) ≤ H) :
    MemLp (fun ω => ∑ j, a j ω * d j ω) 4 μ ∧
      (∫ ω, (∑ j, a j ω * d j ω)^4 ∂μ) ≤ (Fintype.card κ : ℝ)^4 * C^4 * H := by
  have hA (j : κ) : MemLp (a j) ⊤ μ :=
    memLp_top_of_bound (ha j) C (Eventually.of_forall (hC j))
  have hF : MemLp (fun ω => ∑ j, a j ω * d j ω) 4 μ :=
    memLp_finsetSum Finset.univ fun j _ => (hA j).mul (hd₄ j)
  refine ⟨hF, ?_⟩
  let K := (Fintype.card κ : ℝ)^3 * C^4
  have hKi : 0 ≤ K := by dsimp [K]; positivity
  have hPoint (ω : Ω) :
      (∑ j, a j ω * d j ω)^4 ≤ K * ∑ j, d j ω ^ 4 := by
    let v (j : κ) := |a j ω * d j ω|
    have hPow (r : ℝ) : |r|^4 = r^4 := by
      rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ r^4)]
    calc
      _ = |∑ j, a j ω * d j ω|^4 := (hPow _).symm
      _ ≤ (∑ j, v j)^4 := pow_le_pow_left₀ (abs_nonneg _)
        (Finset.abs_sum_le_sum_abs (fun j => a j ω * d j ω) _) _
      _ ≤ (Fintype.card κ : ℝ)^3 * ∑ j, (v j)^4 := by
        simpa using pow_sum_le_card_mul_sum_pow (s := (Finset.univ : Finset κ))
          (f := v) (fun j _ => abs_nonneg _) 3
      _ ≤ (Fintype.card κ : ℝ)^3 * ∑ j, C^4 * (d j ω)^4 := by
        gcongr with j
        dsimp only [v]
        rw [abs_mul, mul_pow, hPow (d j ω)]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hC j ω) _) (by positivity)
      _ = _ := by rw [← Finset.mul_sum, ← mul_assoc]
  have hI : Integrable (fun ω => ∑ j, d j ω ^ 4) μ :=
    integrable_finsetSum Finset.univ fun j _ => memLp_four_integrable_pow_four (hd₄ j)
  calc
    _ ≤ ∫ ω, K * ∑ j, d j ω ^ 4 ∂μ :=
      integral_mono (memLp_four_integrable_pow_four hF) (hI.const_mul K) hPoint
    _ = K * ∑ j, ∫ ω, d j ω ^ 4 ∂μ := by
      rw [integral_const_mul,
        integral_finsetSum Finset.univ (fun j _ => memLp_four_integrable_pow_four (hd₄ j))]
    _ ≤ K * ∑ _j : κ, H := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hH j) hKi
    _ = _ := by dsimp [K]; simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- The actual noise of a bounded Euler row has a uniform fourth
moment on every grid block. The Gaussian component laws provide the
single-step fourth moments and the conditional covariance supplies the
variance bound. -/
theorem integral_eulerGridNoise_sub_fourth_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] [IsProbabilityMeasure μ] {𝒢 : Filtration ℝ≥0 m}
    (grid : ℕ →o ℝ≥0) {b : ℝ≥0 → (ι → ℝ) → ι → ℝ}
    {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ} {W : κ → ℝ≥0 → Ω → ℝ} (x : ι → ℝ) (i : ι)
    (hb : ∀ t i, Measurable (fun y => b t y i))
    (hσ : ∀ t i j, Measurable (fun y => σ t y i j))
    (hW : ∀ j, Martingale (W j) 𝒢 μ) (hW₂ : ∀ j t, MemLp (W j t) 2 μ)
    {C : ℝ} (hC₀ : 0 ≤ C) (hC : ∀ t y i j, ‖σ t y i j‖ ≤ C)
    (hGaussian : ∀ n j, HasLaw (W j (grid (n + 1)) - W j (grid n))
      (gaussianReal 0 (grid (n + 1) - grid n)) μ)
    (hCov : ∀ n j k, μ[(W j (grid (n + 1)) - W j (grid n)) *
        (W k (grid (n + 1)) - W k (grid n)) | 𝒢 (grid n)] =ᵐ[μ]
      fun _ => if j = k then ((grid (n + 1) : ℝ) - (grid n : ℝ)) else 0)
    {a z : ℕ} (haz : a ≤ z) :
    (∫ ω, (eulerGridNoise grid b σ W x i z ω - eulerGridNoise grid b σ W x i a ω)^4 ∂μ) ≤
      (4 * ((Fintype.card κ : ℝ) * C^2)^2 +
        3 * ((Fintype.card κ : ℝ)^4 * C^4 * standardGaussianFourthMoment)) *
        ((grid z : ℝ) - (grid a : ℝ))^2 := by
  let F := gridFiltration 𝒢 grid
  let d := eulerGridNoiseIncrement grid b σ W x i
  let N := eulerGridNoise grid b σ W x i
  let L := (Fintype.card κ : ℝ) * C^2
  let G := (Fintype.card κ : ℝ)^4 * C^4 * standardGaussianFourthMoment
  change (∫ ω, (runningSum d z ω - runningSum d a ω)^4 ∂μ) ≤ (4 * L^2 + 3 * G) * _
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hG : 0 ≤ G := by
    dsimp [G]
    exact mul_nonneg (by positivity) standardGaussianFourthMoment_nonneg
  have hN : Martingale N F μ := by
    convert eulerGridState_noise_martingale grid x i hb hσ hW hW₂ hC using 1
    ext k ω
    exact eulerGridNoise_eq_driver_grid_integrals grid b σ W x i k ω
  have hRel (n : ℕ) : N (n+1) - N n = d n := by
    simp only [N, d, eulerGridNoise, runningSum_succ, add_sub_cancel_left]
  have hX := eulerGridState_stronglyAdapted grid x hb hσ (fun j => (hW j).stronglyAdapted)
  have hStep (n : ℕ) : MemLp (d n) 4 μ ∧
      (∫ ω, d n ω ^ 4 ∂μ) ≤ G * ((grid (n+1) : ℝ) - (grid n : ℝ))^2 := by
    let a (j : κ) (ω : Ω) := σ (grid n) (eulerGridState grid b σ W x n ω) i j
    let δ (j : κ) := W j (grid (n + 1)) - W j (grid n)
    let Δ := (grid (n+1) : ℝ) - (grid n : ℝ)
    have hm (j : κ) : AEStronglyMeasurable (a j) μ := by
      have h : StronglyMeasurable[𝒢 (grid n)] (a j) :=
        ((hσ _ i j).comp (hX n).measurable).stronglyMeasurable
      exact (h.mono (𝒢.le _)).aestronglyMeasurable
    have hδ₄ (j : κ) : MemLp (δ j) 4 μ := (hGaussian n j).memLp
      (by simpa using memLp_id_gaussianReal (μ := 0) (v := grid (n + 1) - grid n) (4 : ℝ≥0))
    have hMom (j : κ) : (∫ ω, δ j ω ^ 4 ∂μ) ≤ Δ^2 * standardGaussianFourthMoment :=
      ((integral_fourth_of_hasLaw_gaussianReal (hGaussian n j)).trans (by
        rw [NNReal.coe_sub (grid.monotone n.le_succ)])).le
    have h := memLp_and_integral_weighted_sum_fourth_le hm (fun _ _ => hC _ _ _ _) hδ₄ hMom
    refine ⟨h.1, ?_⟩
    change (∫ ω, (∑ j, a j ω * δ j ω)^4 ∂μ) ≤ G * Δ^2
    exact h.2.trans_eq (by dsimp only [G]; ring)
  refine integral_runningSum_sub_fourth_le grid (F := F) ?_ (fun n => (hStep n).1)
    (fun n => hRel n ▸ conditional_mean_martingale_increment hN n.le_succ)
    hL hG ?_ (fun n => (hStep n).2) haz
  · intro n
    exact hRel n ▸ (hN.stronglyMeasurable (n+1)).sub
      ((hN.stronglyMeasurable n).mono (F.mono n.le_succ))
  · intro n
    have hCovStep : μ[(fun ω => d n ω ^ 2) | F n] =ᵐ[μ]
        eulerGridCovarianceIncrement grid b σ W x i i n := by
      simpa only [d, F, gridFiltration, pow_two, Pi.mul_def] using
        condExp_eulerGridNoiseIncrement_product grid x i i n hb hσ
          (fun j => (hW j).stronglyAdapted) hW₂ hC (hCov n)
    filter_upwards [hCovStep] with ω hω
    rw [hω]
    let δ := (grid (n+1) : ℝ) - (grid n : ℝ)
    let v (j : κ) := σ (grid n) (eulerGridState grid b σ W x n ω) i j
    have hδ : 0 ≤ δ := sub_nonneg.mpr (NNReal.coe_le_coe.mpr (grid.monotone n.le_succ))
    have hSum : ∑ j, v j * v j ≤ L := by
      calc
        _ ≤ ∑ _j : κ, C^2 := Finset.sum_le_sum fun j _ => by
          have hj : |v j| ≤ C := hC _ _ _ _
          nlinarith [sq_abs (v j), mul_nonneg (sub_nonneg.mpr hj) (add_nonneg hC₀ (abs_nonneg (v j)))]
        _ = _ := by simp [L]
    change δ * (∑ j, v j * v j) ≤ L * δ
    simpa only [mul_comm δ] using mul_le_mul_of_nonneg_left hSum hδ

#print axioms RoughHeston.integral_add_fourth_le_of_conditional_variance
#print axioms RoughHeston.integral_fourth_of_hasLaw_gaussianReal
#print axioms RoughHeston.memLp_and_integral_weighted_sum_fourth_le
#print axioms RoughHeston.integral_eulerGridNoise_sub_fourth_le
#print axioms RoughHeston.integral_runningSum_sub_fourth_le

end RoughHeston
