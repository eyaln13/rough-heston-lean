import MartingalePowerMoment
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The expected finite-grid Taylor remainder vanishes on bounded
continuous martingale paths. -/

open Filter Set MeasureTheory
open scoped BigOperators ENNReal NNReal Topology

namespace RoughHeston

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The largest absolute path increment on a dyadic grid. -/
noncomputable def dyadicMaximumIncrement (T : ℝ≥0) (X : ℝ≥0 → Ω → ℝ)
    (j : ℕ) (ω : Ω) : ℝ :=
  let grid := (uniformDyadicGrids T).grid j
  (Finset.range (2 ^ j)).sup' (Finset.nonempty_range_iff.mpr (pow_ne_zero _ (by decide)))
    (fun k => |X (grid (k + 1)) ω - X (grid k) ω|)

omit [MeasurableSpace Ω] in
private theorem abs_increment_le_dyadicMaximumIncrement (T : ℝ≥0) (X : ℝ≥0 → Ω → ℝ)
    (j k : ℕ) (ω : Ω) (hk : k < 2 ^ j) :
    |X ((uniformDyadicGrids T).grid j (k + 1)) ω - X ((uniformDyadicGrids T).grid j k) ω|
      ≤ dyadicMaximumIncrement T X j ω := by
  unfold dyadicMaximumIncrement
  exact Finset.le_sup' (f := fun k => |X ((uniformDyadicGrids T).grid j (k + 1)) ω -
    X ((uniformDyadicGrids T).grid j k) ω|) (Finset.mem_range.mpr hk)

omit [MeasurableSpace Ω] in
theorem dyadicMaximumIncrement_nonneg (T : ℝ≥0) (X : ℝ≥0 → Ω → ℝ) (j : ℕ) (ω : Ω) :
    0 ≤ dyadicMaximumIncrement T X j ω :=
  (abs_nonneg _).trans (abs_increment_le_dyadicMaximumIncrement T X j 0 ω (by positivity))

theorem measurable_dyadicMaximumIncrement {T : ℝ≥0} {X : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (X t)) (j : ℕ) : Measurable (dyadicMaximumIncrement T X j) := by
  unfold dyadicMaximumIncrement
  let g := (uniformDyadicGrids T).grid j
  convert Finset.measurable_sup' (s := Finset.range (2 ^ j))
    (Finset.nonempty_range_iff.mpr (pow_ne_zero _ (by decide)))
    (f := fun k ω => |X (g (k + 1)) ω - X (g k) ω|)
    (fun k _ => continuous_abs.measurable.comp ((hm (g (k + 1))).sub (hm (g k)))) using 1
  ext ω
  simp only [Finset.sup'_apply, g]

omit [MeasurableSpace Ω] in
theorem tendsto_dyadicMaximumIncrement_of_continuousOn {T : ℝ≥0} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hX : ContinuousOn (fun t => X t ω) (Icc 0 T)) :
    Tendsto (fun j => dyadicMaximumIncrement T X j ω) atTop (𝓝 0) := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨δ, hδ, hUC⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hX) ε hε
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
    (show 0 ≤ (2 : ℝ)⁻¹ by norm_num) (show (2 : ℝ)⁻¹ < 1 by norm_num)
  have hmesh : Tendsto (fun j : ℕ => (T : ℝ) / (2 : ℝ) ^ j) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, mul_zero] using
      (tendsto_const_nhds (x := (T : ℝ))).mul hpow
  filter_upwards [hmesh.eventually_lt_const hδ] with j hj
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (dyadicMaximumIncrement_nonneg T X j ω)]
  unfold dyadicMaximumIncrement
  apply (Finset.sup'_lt_iff _).mpr
  intro k hk
  let g := (uniformDyadicGrids T).grid j
  have hg (k : ℕ) (h : k ≤ 2 ^ j) : g k ∈ Icc 0 T :=
    ⟨zero_le, (g.monotone h).trans_eq (uniform_dyadic_terminal_vertex T j)⟩
  have hk' := Finset.mem_range.mp hk
  have hstep : g (k + 1) = g k + T / (2 : ℝ≥0) ^ j := by
    change ((k + 1 : ℕ) : ℝ≥0) * T / (2 : ℝ≥0) ^ j =
      (k : ℝ≥0) * T / (2 : ℝ≥0) ^ j + T / (2 : ℝ≥0) ^ j
    push_cast
    rw [add_mul, one_mul, add_div]
  rw [← Real.dist_eq]
  apply hUC _ (hg _ (Nat.succ_le_of_lt hk')) _ (hg _ hk'.le)
  change dist (g (k + 1)) (g k) < δ
  rw [hstep, NNReal.dist_eq, NNReal.coe_add, add_sub_cancel_left,
    abs_of_nonneg (show 0 ≤ (↑(T / (2 : ℝ≥0) ^ j) : ℝ) from NNReal.coe_nonneg _)]
  exact hj

/-- The third-order remainder follows from a Lipschitz second derivative,
with a constant uniform on the bounded range of the path. -/
theorem abs_discreteTaylorRemainder_le_cube
    {f f' f'' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    {B : ℝ} {L : ℝ≥0} (hLip : LipschitzOnWith L f'' (Icc (-B) B))
    {x y : ℝ} (hx : |x| ≤ B) (hy : |y| ≤ B) :
    |MathFin.discreteTaylorRemainder f f' f'' x y| ≤ (L : ℝ) * |y - x| * (y - x) ^ 2 := by
  -- Two mean-value estimates, as in MathFin's oscillation bound in
  -- Probability/Brownian/Ito/ItoFormulaAdapted.lean.
  let η := (L : ℝ) * |y - x|
  have hη0 : 0 ≤ η := by unfold η; positivity
  have hx' : x ∈ Icc (-B) B := abs_le.mp hx
  have hy' : y ∈ Icc (-B) B := abs_le.mp hy
  have hη (t : ℝ) (ht : t ∈ uIcc x y) : |f'' t - f'' x| ≤ η := by
    have ht' : t ∈ Icc (-B) B := uIcc_subset_Icc hx' hy' ht
    have hdist := hLip.dist_le_mul t ht' x hx'
    rw [Real.dist_eq, Real.dist_eq] at hdist
    exact hdist.trans (mul_le_mul_of_nonneg_left (abs_sub_left_of_mem_uIcc ht) L.property)
  let g (t : ℝ) := f' t - f' x - f'' x * (t - x)
  have hg (t : ℝ) : HasDerivAt g (f'' t - f'' x) t := by
    have h := ((hf' t).sub_const (f' x)).sub (((hasDerivAt_id t).sub_const x).const_mul (f'' x))
    simp only [id_eq] at h
    convert h using 1
    ring
  have hfirst (t : ℝ) (ht : t ∈ uIcc x y) : |g t| ≤ η * |y - x| := by
    have h := (convex_uIcc x y).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t _ => (hg t).hasDerivWithinAt)
      (fun t ht => (Real.norm_eq_abs _).trans_le (hη t ht)) left_mem_uIcc ht
    simp only [Real.norm_eq_abs, g, sub_self, mul_zero, sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left (abs_sub_left_of_mem_uIcc ht) hη0)
  let F (t : ℝ) := f t - f x - f' x * (t - x) - (1 / 2 * f'' x) * (t - x) ^ 2
  have hF (t : ℝ) : HasDerivAt F (g t) t := by
    have h := (((hf t).sub_const (f x)).sub (((hasDerivAt_id t).sub_const x).const_mul (f' x))).sub
      ((((hasDerivAt_id t).sub_const x).pow 2).const_mul (1 / 2 * f'' x))
    simp only [id_eq] at h
    convert h using 1
    unfold g
    ring
  have h := (convex_uIcc x y).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hF t).hasDerivWithinAt)
    (fun t ht => (Real.norm_eq_abs _).trans_le (hfirst t ht)) left_mem_uIcc right_mem_uIcc
  have hF0 : F x = 0 := by simp [F]
  have hFy : F y = MathFin.discreteTaylorRemainder f f' f'' x y := by
    unfold F MathFin.discreteTaylorRemainder
    ring
  rw [hF0, sub_zero, hFy, Real.norm_eq_abs, Real.norm_eq_abs] at h
  have hr : η * |y - x| * |y - x| = (L : ℝ) * |y - x| * (y - x) ^ 2 := by
    rw [mul_assoc, ← sq, sq_abs]
  exact h.trans_eq hr

/-- Sum of the Taylor remainders along one dyadic grid. -/
noncomputable def dyadicTaylorRemainderSum (T : ℝ≥0) (X : ℝ≥0 → Ω → ℝ)
    (f f' f'' : ℝ → ℝ) (j : ℕ) (ω : Ω) : ℝ :=
  let grid := (uniformDyadicGrids T).grid j
  ∑ k ∈ Finset.range (2 ^ j),
    MathFin.discreteTaylorRemainder f f' f'' (X (grid k) ω) (X (grid (k + 1)) ω)

omit [MeasurableSpace Ω] in
/-- On each grid the absolute remainder sum is bounded by a constant
times the largest increment times the sum of squared increments. -/
theorem abs_dyadicTaylorRemainderSum_le {T : ℝ≥0} {X : ℝ≥0 → Ω → ℝ}
    {f f' f'' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    {B : ℝ} {L : ℝ≥0} (hLip : LipschitzOnWith L f'' (Icc (-B) B))
    (j : ℕ) (ω : Ω) (hbound : ∀ k ≤ 2 ^ j, |X ((uniformDyadicGrids T).grid j k) ω| ≤ B) :
    |dyadicTaylorRemainderSum T X f f' f'' j ω| ≤
      (L : ℝ) * dyadicMaximumIncrement T X j ω *
        gridQuadraticSum ((uniformDyadicGrids T).grid j) X (2 ^ j) ω := by
  let g := (uniformDyadicGrids T).grid j
  let R (k : ℕ) := MathFin.discreteTaylorRemainder f f' f'' (X (g k) ω) (X (g (k + 1)) ω)
  change |∑ k ∈ Finset.range (2 ^ j), R k| ≤ _
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  unfold gridQuadraticSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hk' := Finset.mem_range.mp hk
  refine (abs_discreteTaylorRemainder_le_cube hf hf' hLip (hbound k hk'.le)
    (hbound (k + 1) (Nat.succ_le_of_lt hk'))).trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (abs_increment_le_dyadicMaximumIncrement T X j k ω hk') L.property)
    (sq_nonneg _)

/-- The expected absolute second-order Taylor remainder vanishes on finer
dyadic grids for a bounded continuous martingale with nondecreasing
compensator. The proof uses the Cauchy–Schwarz inequality and the uniform
second moment of the squared-increment sums. -/
theorem tendsto_integral_abs_dyadicTaylorRemainderSum [IsFiniteMeasure μ]
    {𝒢 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {X C : ℝ≥0 → Ω → ℝ}
    (T : ℝ≥0) (hX : Martingale X 𝒢 μ)
    (hC : Martingale (fun t => X t * X t - C t) 𝒢 μ)
    (hCmono : ∀ s t, s ≤ t → C s ≤ᵐ[μ] C t)
    {B : ℝ} (hbound : ∀ t, ∀ᵐ ω ∂μ, ‖X t ω‖ ≤ B)
    (hcont : ∀ᵐ ω ∂μ, ContinuousOn (fun t => X t ω) (Icc 0 T))
    {f f' f'' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x) (hf'' : Continuous f'')
    {L : ℝ≥0} (hLip : LipschitzOnWith L f'' (Icc (-B) B)) :
    Tendsto (fun j => ∫ ω, |dyadicTaylorRemainderSum T X f f' f'' j ω| ∂μ) atTop (𝓝 0) := by
  let G := uniformDyadicGrids T
  let D := dyadicMaximumIncrement T X
  let Q (j : ℕ) := gridQuadraticSum (G.grid j) X (2 ^ j)
  let R := dyadicTaylorRemainderSum T X f f' f''
  let K := (2 * B ^ 4) * μ.real univ + 8 * B ^ 2 * (∫ ω, C T ω - C 0 ω ∂μ)
  have hGridBound (j : ℕ) : ∀ᵐ ω ∂μ, ∀ k : ℕ, |X (G.grid j k) ω| ≤ B := by
    rw [ae_all_iff]
    intro k
    simpa only [Real.norm_eq_abs] using hbound (G.grid j k)
  have hD0 (j : ℕ) (ω : Ω) : 0 ≤ D j ω := dyadicMaximumIncrement_nonneg T X j ω
  have hQ0 (j : ℕ) (ω : Ω) : 0 ≤ Q j ω := by
    unfold Q gridQuadraticSum
    positivity
  have hDsmall (j : ℕ) : ∀ᵐ ω ∂μ, D j ω ≤ 2 * B := by
    filter_upwards [hGridBound j] with ω hω
    unfold D dyadicMaximumIncrement
    refine Finset.sup'_le _ _ fun k _ => ?_
    calc
      |X (G.grid j (k + 1)) ω - X (G.grid j k) ω|
          ≤ |X (G.grid j (k + 1)) ω| + |X (G.grid j k) ω| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (X (G.grid j (k + 1)) ω) (-X (G.grid j k) ω)
      _ ≤ B + B := add_le_add (hω (k + 1)) (hω k)
      _ = 2 * B := by ring
  have hXm (t : ℝ≥0) : Measurable (X t) :=
    ((hX.stronglyMeasurable t).mono (𝒢.le t)).measurable
  have hDm (j : ℕ) : Measurable (D j) := measurable_dyadicMaximumIncrement hXm j
  have hD₂ (j : ℕ) : MemLp (D j) 2 μ := by
    apply MemLp.of_bound (hDm j).aestronglyMeasurable (2 * B)
    filter_upwards [hDsmall j] with ω hω
    simpa only [Real.norm_of_nonneg (hD0 j ω)] using hω
  have hQ₂ (j : ℕ) := gridQuadraticSum_sq_integral_le (G.grid j) hX hC hCmono hbound (2 ^ j)
  have hQbound (j : ℕ) : (∫ ω, Q j ω ^ 2 ∂μ) ≤ K := by
    obtain ⟨_, hj⟩ := hQ₂ j
    rw [show G.grid j (2 ^ j) = T from uniform_dyadic_terminal_vertex T j,
      show G.grid j 0 = 0 from uniform_dyadic_first_vertex T j] at hj
    exact hj
  have hDlim : ∀ᵐ ω ∂μ, Tendsto (fun j => D j ω) atTop (𝓝 0) :=
    hcont.mono fun ω hω => tendsto_dyadicMaximumIncrement_of_continuousOn hω
  have hDsq : Tendsto (fun j => ∫ ω, D j ω ^ 2 ∂μ) atTop (𝓝 0) := by
    simpa only [integral_zero] using
      (tendsto_integral_of_dominated_convergence (μ := μ)
        (F := fun j ω => D j ω ^ 2) (f := fun _ => 0) (fun _ => (2 * B) ^ 2)
        (fun j => ((hDm j).pow_const 2).aestronglyMeasurable)
        (integrable_const _) (fun j => by
          filter_upwards [hDsmall j] with ω hω
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          exact pow_le_pow_left₀ (hD0 j ω) hω 2)
        (hDlim.mono fun ω hω => by simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using hω.pow 2))
  have hRbound (j : ℕ) :
      ∀ᵐ ω ∂μ, |R j ω| ≤ (L : ℝ) * (D j ω * Q j ω) := by
    filter_upwards [hGridBound j] with ω hω
    rw [← mul_assoc]
    exact abs_dyadicTaylorRemainderSum_le hf hf' hLip j ω (fun k _ => hω k)
  have hRm (j : ℕ) : Measurable (R j) := by
    have hf0 : Continuous f := (show Differentiable ℝ f from fun x => (hf x).differentiableAt).continuous
    have hf1 : Continuous f' := (show Differentiable ℝ f' from fun x => (hf' x).differentiableAt).continuous
    unfold R dyadicTaylorRemainderSum MathFin.discreteTaylorRemainder
    apply Finset.measurable_fun_sum
    intro k _
    exact (((hf0.measurable.comp (hXm _)).sub (hf0.measurable.comp (hXm _))).sub
      ((hf1.measurable.comp (hXm _)).mul ((hXm _).sub (hXm _)))).sub
      (measurable_const.mul ((hf''.measurable.comp (hXm _)).mul (((hXm _).sub (hXm _)).pow_const 2)))
  have hRprod (j : ℕ) : Integrable (fun ω => D j ω * Q j ω) μ :=
    (hD₂ j).integrable_mul (hQ₂ j).1
  have hRint (j : ℕ) : Integrable (R j) μ := by
    refine ((hRprod j).const_mul (L : ℝ)).mono' (hRm j).aestronglyMeasurable ?_
    simpa only [Real.norm_eq_abs] using hRbound j
  have hCS (j : ℕ) : (∫ ω, D j ω * Q j ω ∂μ) ≤
      Real.sqrt (∫ ω, D j ω ^ 2 ∂μ) * Real.sqrt (∫ ω, Q j ω ^ 2 ∂μ) := by
    have h2 : (2 : ℝ).HolderConjugate 2 := by
      apply Real.holderConjugate_iff.2
      norm_num
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg h2
      (Eventually.of_forall (hD0 j)) (Eventually.of_forall (hQ0 j))
      (by simpa only [ENNReal.ofReal_ofNat] using hD₂ j)
      (by simpa only [ENNReal.ofReal_ofNat] using (hQ₂ j).1)
    simpa only [Real.rpow_two, Real.sqrt_eq_rpow] using h
  have hExpect (j : ℕ) : (∫ ω, |R j ω| ∂μ) ≤
      (L : ℝ) * (Real.sqrt (∫ ω, D j ω ^ 2 ∂μ) * Real.sqrt K) := by
    calc
      _ ≤ ∫ ω, (L : ℝ) * (D j ω * Q j ω) ∂μ := by
        apply integral_mono_ae
          (by simpa only [Real.norm_eq_abs] using (hRint j).norm)
          ((hRprod j).const_mul (L : ℝ))
        exact hRbound j
      _ = (L : ℝ) * (∫ ω, D j ω * Q j ω ∂μ) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left ((hCS j).trans
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hQbound j)) (Real.sqrt_nonneg _))) L.property
  have hLim : Tendsto (fun j => (L : ℝ) * (Real.sqrt (∫ ω, D j ω ^ 2 ∂μ) * Real.sqrt K))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero, zero_mul, mul_zero] using
      (((Real.continuous_sqrt.tendsto 0).comp hDsq).mul_const (Real.sqrt K)).const_mul (L : ℝ)
  exact squeeze_zero (fun j => integral_nonneg fun ω => abs_nonneg (R j ω)) hExpect hLim

private theorem continuous_comp_memLp_top_of_uniform_bound {X : Ω → ℝ} {g : ℝ → ℝ}
    {B : ℝ} (hX : Measurable X) (hg : Continuous g) (hbound : ∀ᵐ ω ∂μ, ‖X ω‖ ≤ B) :
    MemLp (fun ω => g (X ω)) ⊤ μ := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := -B) (b := B)).bddAbove_image
    (continuous_norm.comp hg).continuousOn
  refine memLp_top_of_bound (hg.measurable.comp hX).aestronglyMeasurable K ?_
  filter_upwards [hbound] with ω hω
  rw [Real.norm_eq_abs] at hω
  exact hK (mem_image_of_mem (fun x => ‖g x‖) (abs_le.mp hω))

/-- On a bounded continuous martingale, the expected compensator sums with
the second-derivative weight converge to the expected Itô identity. -/
theorem tendsto_expected_dyadic_ito_compensator_sum [IsFiniteMeasure μ]
    {𝒢 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {X C : ℝ≥0 → Ω → ℝ}
    (T : ℝ≥0) (hX : Martingale X 𝒢 μ)
    (hC : Martingale (fun t => X t * X t - C t) 𝒢 μ)
    (hCmono : ∀ s t, s ≤ t → C s ≤ᵐ[μ] C t)
    {B : ℝ} (hbound : ∀ t, ∀ᵐ ω ∂μ, ‖X t ω‖ ≤ B)
    (hcont : ∀ᵐ ω ∂μ, ContinuousOn (fun t => X t ω) (Icc 0 T))
    {f f' f'' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x) (hf'' : Continuous f'')
    {L : ℝ≥0} (hLip : LipschitzOnWith L f'' (Icc (-B) B)) :
    Tendsto (fun j =>
      let g := (uniformDyadicGrids T).grid j
      (1 / 2 : ℝ) * ∑ k ∈ Finset.range (2 ^ j),
        ∫ ω, f'' (X (g k) ω) * (C (g (k + 1)) ω - C (g k) ω) ∂μ)
      atTop (𝓝 (∫ ω, f (X T ω) - f (X 0 ω) ∂μ)) := by
  let G := uniformDyadicGrids T
  let R := dyadicTaylorRemainderSum T X f f' f''
  have hRL : Tendsto (fun j => ∫ ω, R j ω ∂μ) atTop (𝓝 0) := by
    apply tendsto_iff_dist_tendsto_zero.2
    refine squeeze_zero (fun _ => dist_nonneg) (fun j => ?_)
      (tendsto_integral_abs_dyadicTaylorRemainderSum T hX hC hCmono hbound hcont hf hf' hf'' hLip)
    rw [dist_zero_right]
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun ω => R j ω)
  have hXm (t : ℝ≥0) : Measurable (X t) :=
    ((hX.stronglyMeasurable t).mono (𝒢.le t)).measurable
  have hX₂ (t : ℝ≥0) : MemLp (X t) 2 μ :=
    MemLp.of_bound (hXm t).aestronglyMeasurable B (hbound t)
  have hf0 : Continuous f := (show Differentiable ℝ f from fun x => (hf x).differentiableAt).continuous
  have hf1 : Continuous f' :=
    (show Differentiable ℝ f' from fun x => (hf' x).differentiableAt).continuous
  have hTop {F : ℝ → ℝ} (hF : Continuous F) (t : ℝ≥0) :
      MemLp (fun ω => F (X t ω)) ⊤ μ :=
    continuous_comp_memLp_top_of_uniform_bound (hXm t) hF (hbound t)
  have hFrom (j : ℕ) :=
    integral_grid_ito_expansion (G.grid j) hX hX₂ hC f f' f''
      (fun k => (hTop hf0 _).integrable le_top)
      (fun k => ⟨hf1.comp_stronglyMeasurable (hX.stronglyMeasurable _), hTop hf1 _⟩)
      (fun k => ⟨hf''.comp_stronglyMeasurable (hX.stronglyMeasurable _), hTop hf'' _⟩)
      (2 ^ j)
  have hConst : Tendsto (fun j => (∫ ω, f (X T ω) - f (X 0 ω) ∂μ) - ∫ ω, R j ω ∂μ)
      atTop (𝓝 (∫ ω, f (X T ω) - f (X 0 ω) ∂μ)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hRL
  apply hConst.congr
  intro j
  have he := hFrom j
  rw [show G.grid j (2 ^ j) = T from uniform_dyadic_terminal_vertex T j,
    show G.grid j 0 = 0 from uniform_dyadic_first_vertex T j] at he
  change (∫ ω, f (X T ω) - f (X 0 ω) ∂μ) = _ + (∫ ω, R j ω ∂μ) at he
  change (∫ ω, f (X T ω) - f (X 0 ω) ∂μ) - (∫ ω, R j ω ∂μ) = _
  linarith

/-- A predictable finite-grid estimate gives an expected upper bound
whenever one terminal random variable dominates the second derivative
along the path. -/
theorem expected_ito_le_of_second_derivative_envelope [IsFiniteMeasure μ]
    {𝒢 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {X C : ℝ≥0 → Ω → ℝ}
    (T : ℝ≥0) (hX : Martingale X 𝒢 μ)
    (hC : Martingale (fun t => X t * X t - C t) 𝒢 μ)
    (hCmono : ∀ s t, s ≤ t → C s ≤ᵐ[μ] C t)
    {B : ℝ} (hbound : ∀ t, ∀ᵐ ω ∂μ, ‖X t ω‖ ≤ B)
    (hcont : ∀ᵐ ω ∂μ, ContinuousOn (fun t => X t ω) (Icc 0 T))
    {f f' f'' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x) (hf'' : Continuous f'')
    {L : ℝ≥0} (hLip : LipschitzOnWith L f'' (Icc (-B) B))
    {W : Ω → ℝ} (hW : MemLp W ⊤ μ) (hDom : ∀ᵐ ω ∂μ, ∀ t ≤ T, f'' (X t ω) ≤ W ω) :
    (∫ ω, f (X T ω) - f (X 0 ω) ∂μ) ≤ (1 / 2) * (∫ ω, W ω * (C T ω - C 0 ω) ∂μ) := by
  apply le_of_tendsto'
    (tendsto_expected_dyadic_ito_compensator_sum T hX hC hCmono hbound hcont hf hf' hf'' hLip)
  intro j
  let g := (uniformDyadicGrids T).grid j
  let A (k : ℕ) := C (g (k + 1)) - C (g k)
  have hXm (t : ℝ≥0) : Measurable (X t) :=
    ((hX.stronglyMeasurable t).mono (𝒢.le t)).measurable
  have hX₂ (t : ℝ≥0) : MemLp (X t) 2 μ := MemLp.of_bound (hXm t).aestronglyMeasurable B (hbound t)
  have hCint (t : ℝ≥0) : Integrable (C t) μ := by
    have h := (hX₂ t).integrable_sq
    simp only [pow_two] at h
    change Integrable (X t * X t) μ at h
    simpa only [sub_sub_cancel] using h.sub (hC.integrable t)
  have hAint (k : ℕ) : Integrable (A k) μ := (hCint _).sub (hCint _)
  have hAprod (k : ℕ) : Integrable (fun ω => W ω * A k ω) μ :=
    memLp_one_iff_integrable.1 (hW.mul (memLp_one_iff_integrable.2 (hAint k)))
  have hF (k : ℕ) : MemLp (fun ω => f'' (X (g k) ω)) ⊤ μ :=
    continuous_comp_memLp_top_of_uniform_bound (hXm _) hf'' (hbound _)
  have hFprod (k : ℕ) : Integrable (fun ω => f'' (X (g k) ω) * A k ω) μ :=
    memLp_one_iff_integrable.1 ((hF k).mul (memLp_one_iff_integrable.2 (hAint k)))
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (1 / 2 : ℝ))
  change (∑ k ∈ Finset.range (2 ^ j), ∫ ω, f'' (X (g k) ω) * A k ω ∂μ) ≤ _
  calc
    _ ≤ ∑ k ∈ Finset.range (2 ^ j), ∫ ω, W ω * A k ω ∂μ := by
      apply Finset.sum_le_sum
      intro k hk
      have hkg : g k ≤ T :=
        (g.monotone (Finset.mem_range.mp hk).le).trans_eq (uniform_dyadic_terminal_vertex T j)
      apply integral_mono_ae (hFprod k) (hAprod k)
      filter_upwards [hDom, hCmono _ _ (g.monotone k.le_succ)] with ω hw ha
      exact mul_le_mul_of_nonneg_right (hw _ hkg) (sub_nonneg.mpr ha)
    _ = ∫ ω, W ω * (C T ω - C 0 ω) ∂μ := by
      rw [← integral_finsetSum _ (fun k _ => hAprod k)]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro ω
      change (∑ k ∈ Finset.range (2 ^ j), W ω * A k ω) = W ω * (C T ω - C 0 ω)
      rw [← Finset.mul_sum]
      have he : (∑ k ∈ Finset.range (2 ^ j), A k ω) = C (g (2 ^ j)) ω - C (g 0) ω :=
        Finset.sum_range_sub (fun k => C (g k) ω) (2 ^ j)
      rw [he, show g (2 ^ j) = T from uniform_dyadic_terminal_vertex T j,
        show g 0 = 0 from uniform_dyadic_first_vertex T j]

/-- The second derivative of an integer power has a finite Lipschitz
constant on every bounded interval. -/
theorem exists_lipschitzOnWith_power_second (k : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ L : ℝ≥0, LipschitzOnWith L
      (fun x : ℝ => (k : ℝ) * ((k - 1 : ℕ) : ℝ) * x ^ (k - 2)) (Icc (-B) B) := by
  let n := k - 2
  let c : ℝ := (k : ℝ) * ((k - 1 : ℕ) : ℝ)
  let L : ℝ≥0 := ⟨c * (n : ℝ) * B ^ (n - 1), by unfold c; positivity⟩
  refine ⟨L, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
  have hc : 0 ≤ c := by unfold c; positivity
  have hxy : max |x| |y| ≤ B := max_le (abs_le.2 hx) (abs_le.2 hy)
  have hpow : |x ^ n - y ^ n| ≤ |x - y| * (n : ℝ) * B ^ (n - 1) :=
    (abs_pow_sub_pow_le (a := x) (b := y) (n := n)).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ ((abs_nonneg _).trans (le_max_left _ _)) hxy _)
        (by positivity))
  change dist (c * x ^ n) (c * y ^ n) ≤ (L : ℝ) * dist x y
  rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg hc]
  calc
    _ ≤ c * (|x - y| * (n : ℝ) * B ^ (n - 1)) := mul_le_mul_of_nonneg_left hpow hc
    _ = _ := by
      change _ = (c * (n : ℝ) * B ^ (n - 1)) * |x - y|
      ring

/-- The expected power estimate for a bounded, zero-start martingale.
The running envelope is any bounded random variable dominating the
absolute path on the horizon. -/
theorem expected_even_power_le_of_bounded_martingale_envelope [IsFiniteMeasure μ]
    {𝒢 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {X C : ℝ≥0 → Ω → ℝ}
    (T : ℝ≥0) (hX : Martingale X 𝒢 μ) (hX0 : X 0 =ᵐ[μ] 0)
    (hC : Martingale (fun t => X t * X t - C t) 𝒢 μ)
    (hCmono : ∀ s t, s ≤ t → C s ≤ᵐ[μ] C t)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ t, ∀ᵐ ω ∂μ, ‖X t ω‖ ≤ B)
    (hcont : ∀ᵐ ω ∂μ, ContinuousOn (fun t => X t ω) (Icc 0 T))
    (m : ℕ) (hm : 0 < m)
    {S : Ω → ℝ} (hS : MemLp S ⊤ μ) (hDom : ∀ᵐ ω ∂μ, ∀ t ≤ T, ‖X t ω‖ ≤ S ω) :
    (∫ ω, ‖X T ω‖ ^ (2 * m) ∂μ) ≤
      ((2 * m : ℕ) : ℝ) * (((2 * m - 1 : ℕ) : ℝ) / 2) *
        ∫ ω, S ω ^ (2 * m - 2) * (C T ω - C 0 ω) ∂μ := by
  let k := 2 * m
  let f (x : ℝ) := x ^ k
  let f' (x : ℝ) := (k : ℝ) * x ^ (k - 1)
  let f'' (x : ℝ) := (k : ℝ) * ((k - 1 : ℕ) : ℝ) * x ^ (k - 2)
  let W (ω : Ω) := (k : ℝ) * ((k - 1 : ℕ) : ℝ) * S ω ^ (k - 2)
  have hk : 0 < k := by dsimp [k]; omega
  have hf (x : ℝ) : HasDerivAt f (f' x) x := hasDerivAt_pow k x
  have hf' (x : ℝ) : HasDerivAt f' (f'' x) x := by
    simpa only [f', f'', Nat.sub_sub, one_add_one_eq_two, ← mul_assoc] using
      (hasDerivAt_pow (k - 1) x).const_mul (k : ℝ)
  have hf'' : Continuous f'' := continuous_const.mul (continuous_id.pow _)
  obtain ⟨L, hLip⟩ := exists_lipschitzOnWith_power_second k hB
  have hS_pow (n : ℕ) : MemLp (fun ω => S ω ^ n) ⊤ μ := by
    induction n with
    | zero =>
        simpa only [pow_zero] using (memLp_const (1 : ℝ) :
          MemLp (fun _ : Ω => (1 : ℝ)) ⊤ μ)
    | succ n ih =>
        simp only [pow_succ]
        exact ih.mul hS
  have hW : MemLp W ⊤ μ :=
    (hS_pow (k - 2)).const_mul ((k : ℝ) * ((k - 1 : ℕ) : ℝ))
  have hWdom : ∀ᵐ ω ∂μ, ∀ t ≤ T, f'' (X t ω) ≤ W ω := by
    filter_upwards [hDom] with ω hω
    intro t ht
    have habs : |X t ω| ≤ S ω := by simpa only [Real.norm_eq_abs] using hω t ht
    have hx : X t ω ^ (k - 2) ≤ S ω ^ (k - 2) := by
      calc
        _ ≤ |X t ω ^ (k - 2)| := le_abs_self _
        _ = |X t ω| ^ (k - 2) := abs_pow _ _
        _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) habs _
    exact mul_le_mul_of_nonneg_left hx (by positivity)
  have hI := expected_ito_le_of_second_derivative_envelope T hX hC hCmono hbound hcont
    hf hf' hf'' hLip hW hWdom
  have hEq : (∫ ω, f (X T ω) - f (X 0 ω) ∂μ) =
      ∫ ω, ‖X T ω‖ ^ (2 * m) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hX0] with ω hω
    change X 0 ω = 0 at hω
    rw [hω]
    change (X T ω) ^ k - (0 : ℝ) ^ k = _
    rw [zero_pow hk.ne', sub_zero]
    simp only [k, pow_mul, Real.norm_eq_abs, sq_abs]
  rw [hEq] at hI
  refine hI.trans_eq ?_
  have hW_eq (ω : Ω) : W ω * (C T ω - C 0 ω) =
      ((k : ℝ) * ((k - 1 : ℕ) : ℝ)) * (S ω ^ (k - 2) * (C T ω - C 0 ω)) := by
    dsimp only [W]
    ring
  simp_rw [hW_eq, integral_const_mul]
  dsimp only [k]
  ring

/-- The moment constant for a zero-start bounded continuous martingale. -/
noncomputable def boundedMartingaleEvenPowerConstant (m : ℕ) : ℝ≥0∞ :=
  let p : ℝ := 2 * (m : ℝ)
  let D := ENNReal.ofReal (((2 * m : ℕ) : ℝ) * (((2 * m - 1 : ℕ) : ℝ) / 2))
  let K := ENNReal.ofReal (p / (p - 1)) ^ p
  (D * K ^ (1 - (m : ℝ)⁻¹)) ^ (m : ℝ)

theorem boundedMartingaleEvenPowerConstant_ne_top (m : ℕ) (hm : 2 ≤ m) :
    boundedMartingaleEvenPowerConstant m ≠ ⊤ := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : 0 < (m : ℝ) := by linarith
  have ha : 0 < 1 - (m : ℝ)⁻¹ := sub_pos.mpr ((inv_lt_one₀ hm0).2 (by linarith))
  have hp : 0 < 2 * (m : ℝ) := by positivity
  unfold boundedMartingaleEvenPowerConstant
  intro h
  have hinner := (ENNReal.rpow_eq_top_iff_of_pos hm0).1 h
  apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top _ hinner
  intro hK
  have hK' := (ENNReal.rpow_eq_top_iff_of_pos ha).1 hK
  exact ENNReal.ofReal_ne_top ((ENNReal.rpow_eq_top_iff_of_pos hp).1 hK')

/-- Upper even-moment bound for a bounded continuous, zero-start martingale
with a nondecreasing square compensator. -/
theorem bounded_martingale_even_power_le [IsFiniteMeasure μ]
    {𝒢 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {X C : ℝ≥0 → Ω → ℝ}
    (T : ℝ≥0) (hX : Martingale X 𝒢 μ) (hX0 : X 0 =ᵐ[μ] 0)
    (hC : Martingale (fun t => X t * X t - C t) 𝒢 μ)
    (hCmono : ∀ s t, s ≤ t → C s ≤ᵐ[μ] C t)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ t, ∀ᵐ ω ∂μ, ‖X t ω‖ ≤ B)
    (hPathBound : ∀ᵐ ω ∂μ, ∀ t ≤ T, ‖X t ω‖ ≤ B)
    (hcont : ∀ᵐ ω ∂μ, ContinuousOn (fun t => X t ω) (Icc 0 T))
    (m : ℕ) (hm : 2 ≤ m) :
    (∫⁻ ω, ‖X T ω‖ₑ ^ (2 * m : ℕ) ∂μ) ≤
      boundedMartingaleEvenPowerConstant m *
        (∫⁻ ω, ENNReal.ofReal (C T ω - C 0 ω) ^ m ∂μ) := by
  let p : ℝ := 2 * (m : ℝ)
  let c : ℝ := ((2 * m : ℕ) : ℝ) * (((2 * m - 1 : ℕ) : ℝ) / 2)
  let A (ω : Ω) := C T ω - C 0 ω
  let Q (ω : Ω) := ENNReal.ofReal (A ω)
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hp : 1 < p := by dsimp [p]; linarith
  have hc : 0 ≤ c := by unfold c; positivity
  have hM (t : ℝ≥0) : Measurable (X t) :=
    ((hX.stronglyMeasurable t).mono (𝒢.le t)).measurable
  have hXm (t : ℝ≥0) : MemLp (X t) 2 μ := MemLp.of_bound (hM t).aestronglyMeasurable B (hbound t)
  have hCmeas (t : ℝ≥0) : Measurable (C t) := by
    have h := (hM t).mul (hM t)
    have h' := ((hC.stronglyMeasurable t).mono (𝒢.le t)).measurable
    change Measurable (X t * X t) at h
    change Measurable (X t * X t - C t) at h'
    simpa only [sub_sub_cancel] using h.sub h'
  have hQmeas : Measurable Q := ((hCmeas T).sub (hCmeas 0)).ennreal_ofReal
  have hCint (t : ℝ≥0) : Integrable (C t) μ := by
    have hh := (hXm t).integrable_sq
    simp only [pow_two] at hh
    change Integrable (X t * X t) μ at hh
    simpa only [sub_sub_cancel] using hh.sub (hC.integrable t)
  have hAint : Integrable A μ := (hCint T).sub (hCint 0)
  have hA0 : ∀ᵐ ω ∂μ, 0 ≤ A ω :=
    (hCmono 0 T zero_le).mono fun _ h => sub_nonneg.mpr h
  obtain ⟨E, hEm, hEd, hDoob⟩ := exists_continuous_martingale_norm_envelope hX T hcont hp
  let S (ω : Ω) := min (E ω) (ENNReal.ofReal B)
  let U (ω : Ω) := (S ω).toReal
  have hSm : Measurable S := hEm.min measurable_const
  have hUmeas : Measurable U := ENNReal.measurable_toReal.comp hSm
  have hSfinite (ω : Ω) : S ω ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_right _ _)
  have hUB (ω : Ω) : ‖U ω‖ ≤ B := by
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (show S ω ≤ ENNReal.ofReal B from min_le_right _ _)
    simpa only [ENNReal.toReal_ofReal hB] using hh
  have hUtop : MemLp U ⊤ μ :=
    memLp_top_of_bound hUmeas.aestronglyMeasurable B (Eventually.of_forall hUB)
  have hUdom : ∀ᵐ ω ∂μ, ∀ t ≤ T, ‖X t ω‖ ≤ U ω := by
    filter_upwards [hPathBound, hEd] with ω hw he
    intro t ht
    have hh : ‖X t ω‖ₑ ≤ S ω := le_min (he t ht) (by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hw t ht))
    have hd := ENNReal.toReal_mono (hSfinite ω) hh
    simpa only [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)] using hd
  have hUval (ω : Ω) : ENNReal.ofReal (U ω) = S ω := ENNReal.ofReal_toReal (hSfinite ω)
  have hUpow : MemLp (fun ω => U ω ^ (2 * m - 2)) ⊤ μ :=
    continuous_comp_memLp_top_of_uniform_bound hUmeas (continuous_id.pow _)
      (Eventually.of_forall hUB)
  have hRint : Integrable (fun ω => U ω ^ (2 * m - 2) * A ω) μ :=
    memLp_one_iff_integrable.1 (hUpow.mul (memLp_one_iff_integrable.2 hAint))
  have hTpow : Integrable (fun ω => ‖X T ω‖ ^ (2 * m)) μ :=
    (continuous_comp_memLp_top_of_uniform_bound (hM T) (continuous_norm.pow _) (hbound T)).integrable
      le_top
  have hNat : p = ((2 * m : ℕ) : ℝ) := by
    change 2 * (m : ℝ) = _
    rw [Nat.cast_mul, Nat.cast_ofNat]
  have hNSub : 2 * ((m : ℝ) - 1) = ((2 * m - 2 : ℕ) : ℝ) := by
    have h2 : 2 ≤ 2 * m := by omega
    rw [Nat.cast_sub h2]
    push_cast
    ring
  have hTerm : (∫⁻ ω, ‖X T ω‖ₑ ^ p ∂μ) =
      ENNReal.ofReal (∫ ω, ‖X T ω‖ ^ (2 * m) ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hTpow
      (Eventually.of_forall fun ω => pow_nonneg (norm_nonneg _) _)]
    apply lintegral_congr
    intro ω
    rw [hNat, ENNReal.rpow_natCast, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  have hBracket : (∫⁻ ω, S ω ^ (2 * ((m : ℝ) - 1)) * Q ω ∂μ) =
      ENNReal.ofReal (∫ ω, U ω ^ (2 * m - 2) * A ω ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hRint
      (hA0.mono fun ω h => mul_nonneg (pow_nonneg ENNReal.toReal_nonneg _) h)]
    apply lintegral_congr
    intro ω
    change S ω ^ (2 * ((m : ℝ) - 1)) * ENNReal.ofReal (A ω) =
      ENNReal.ofReal (U ω ^ (2 * m - 2) * A ω)
    have hU0 : 0 ≤ U ω := ENNReal.toReal_nonneg
    rw [hNSub, ENNReal.rpow_natCast, ← hUval ω, ← ENNReal.ofReal_pow hU0,
      ← ENNReal.ofReal_mul (pow_nonneg hU0 _)]
  have hIto : (∫⁻ ω, ‖X T ω‖ₑ ^ p ∂μ) ≤ ENNReal.ofReal c *
      (∫⁻ ω, S ω ^ (2 * ((m : ℝ) - 1)) * Q ω ∂μ) := by
    rw [hTerm, hBracket, ← ENNReal.ofReal_mul hc]
    exact ENNReal.ofReal_le_ofReal
      (expected_even_power_le_of_bounded_martingale_envelope T hX hX0 hC hCmono hB hbound hcont
        m (by omega) hUtop hUdom)
  have hDoobS : (∫⁻ ω, S ω ^ p ∂μ) ≤ ENNReal.ofReal (p / (p - 1)) ^ p *
      (∫⁻ ω, ‖X T ω‖ₑ ^ p ∂μ) :=
    (lintegral_mono fun ω => ENNReal.rpow_le_rpow (min_le_left _ _) (by positivity)).trans hDoob
  have hFinite : (∫⁻ ω, ‖X T ω‖ₑ ^ p ∂μ) ≠ ⊤ := by
    rw [hTerm]
    exact ENNReal.ofReal_ne_top
  have hEstimate := terminal_even_moment_le_of_power_identity_and_doob
    (μ := μ) (m := (m : ℝ)) (by linarith : 1 < (m : ℝ))
    hSm hQmeas hFinite hIto hDoobS
  change (∫⁻ ω, ‖X T ω‖ₑ ^ p ∂μ) ≤
    boundedMartingaleEvenPowerConstant m * (∫⁻ ω, Q ω ^ (m : ℝ) ∂μ) at hEstimate
  simpa only [hNat, ENNReal.rpow_natCast, Q] using hEstimate

#print axioms tendsto_dyadicMaximumIncrement_of_continuousOn
#print axioms abs_discreteTaylorRemainder_le_cube
#print axioms abs_dyadicTaylorRemainderSum_le
#print axioms tendsto_integral_abs_dyadicTaylorRemainderSum
#print axioms tendsto_expected_dyadic_ito_compensator_sum
#print axioms expected_ito_le_of_second_derivative_envelope
#print axioms exists_lipschitzOnWith_power_second
#print axioms expected_even_power_le_of_bounded_martingale_envelope
#print axioms boundedMartingaleEvenPowerConstant_ne_top
#print axioms bounded_martingale_even_power_le

end RoughHeston
