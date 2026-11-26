import EulerObservableCompactLimits

/-! Uniform integrability of the actual Euler martingale-problem tests. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston

variable {Ω ι κ : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  [Fintype ι] [Fintype κ] {𝒢 : Filtration ℝ≥0 m}

theorem integrable_pow_four_of_memLp {X : Ω → ℝ} (hX : MemLp X 4 μ) :
    Integrable (fun ω => X ω ^ 4) μ := by
  have h := hX.integrable_norm_pow (p := 4) (by decide)
  convert h using 1
  ext ω
  rw [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity : 0 ≤ X ω ^ 4)]

theorem integral_sq_le_one_add_integral_pow_four [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : MemLp X 4 μ) :
    MemLp X 2 μ ∧ (∫ ω, X ω^2 ∂μ) ≤ 1 + ∫ ω, X ω^4 ∂μ := by
  have hX₂ : MemLp X 2 μ := hX.mono_exponent (by norm_num)
  have hX4 := integrable_pow_four_of_memLp hX
  refine ⟨hX₂, ?_⟩
  calc
    _ ≤ ∫ ω, 1 + X ω^4 ∂μ := by
      apply integral_mono hX₂.integrable_sq ((integrable_const _).add hX4)
      intro ω
      change X ω ^ 2 ≤ 1 + X ω ^ 4
      nlinarith [sq_nonneg (X ω ^ 2 - 1), sq_nonneg (X ω)]
    _ = _ := by rw [integral_add (integrable_const (1 : ℝ)) hX4]; simp

theorem integral_pow_four_add_le [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 4 μ) (hY : MemLp Y 4 μ) :
    (∫ ω, (X ω + Y ω)^4 ∂μ) ≤ 8 * ((∫ ω, X ω^4 ∂μ) + ∫ ω, Y ω^4 ∂μ) := by
  have hi := integrable_pow_four_of_memLp hX
  have hj := integrable_pow_four_of_memLp hY
  have hDom : Integrable (fun ω => X ω^4 + Y ω^4) μ := hi.add hj
  calc
    _ ≤ ∫ ω, 8 * (X ω^4 + Y ω^4) ∂μ := by
      apply integral_mono (integrable_pow_four_of_memLp (hX.add hY)) (hDom.const_mul 8)
      intro ω
      change (X ω + Y ω)^4 ≤ 8 * (X ω^4 + Y ω^4)
      have h1 : (X ω + Y ω)^2 ≤ 2 * (X ω^2 + Y ω^2) := by
        nlinarith [sq_nonneg (X ω - Y ω)]
      have h2 : (X ω^2 + Y ω^2)^2 ≤ 2 * (X ω^4 + Y ω^4) := by
        nlinarith [sq_nonneg (X ω^2 - Y ω^2)]
      nlinarith [pow_le_pow_left₀ (sq_nonneg (X ω + Y ω)) h1 2]
    _ = _ := by rw [integral_const_mul, integral_add hi hj]

theorem integral_sq_sub_le [IsFiniteMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    (∫ ω, (X ω - Y ω)^2 ∂μ) ≤ 2 * ((∫ ω, X ω^2 ∂μ) + ∫ ω, Y ω^2 ∂μ) := by
  have hDom : Integrable (fun ω => X ω^2 + Y ω^2) μ := hX.integrable_sq.add hY.integrable_sq
  calc
    _ ≤ ∫ ω, 2 * (X ω^2 + Y ω^2) ∂μ := by
      apply integral_mono (hX.sub hY).integrable_sq (hDom.const_mul 2)
      intro ω
      change (X ω - Y ω)^2 ≤ 2 * (X ω^2 + Y ω^2)
      nlinarith [sq_nonneg (X ω + Y ω)]
    _ = _ := by rw [integral_const_mul, integral_add hX.integrable_sq hY.integrable_sq]

theorem integral_sq_mul_le_of_four {X Y : Ω → ℝ} (hX : MemLp X 4 μ) (hY : MemLp Y 4 μ) :
    MemLp (X * Y) 2 μ ∧
    (∫ ω, (X ω * Y ω)^2 ∂μ) ≤ (1/2 : ℝ) * ((∫ ω, X ω^4 ∂μ) + ∫ ω, Y ω^4 ∂μ) := by
  have hi := integrable_pow_four_of_memLp hX
  have hj := integrable_pow_four_of_memLp hY
  have hDom : Integrable (fun ω => X ω^4 + Y ω^4) μ := hi.add hj
  have hPoint (ω : Ω) : (X ω * Y ω)^2 ≤ (1/2 : ℝ) * (X ω^4 + Y ω^4) := by
    nlinarith [sq_nonneg (X ω^2 - Y ω^2)]
  have hIn : Integrable (fun ω => (X ω * Y ω)^2) μ :=
    (hDom.const_mul _).mono' ((hX.aestronglyMeasurable.mul hY.aestronglyMeasurable).pow 2)
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hPoint ω)
  refine ⟨(memLp_two_iff_integrable_sq (hX.aestronglyMeasurable.mul hY.aestronglyMeasurable)).2 hIn, ?_⟩
  calc
    _ ≤ ∫ ω, (1/2 : ℝ) * (X ω^4 + Y ω^4) ∂μ := integral_mono hIn (hDom.const_mul _) hPoint
    _ = _ := by rw [integral_const_mul, integral_add hi hj]

/-- The original Euler sample path, interpolated on the dyadic grid. -/
noncomputable def eulerDyadicInterpolant (T : ℝ≥0) (j : ℕ)
    (b : ℝ≥0 → (ι → ℝ) → ι → ℝ) (σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ)
    (W : κ → ℝ≥0 → Ω → ℝ) (x : ι → ℝ) (ω : Ω) : CanonicalPath T (ι → ℝ) :=
  gridLinearInterpolateVectorPath T ((uniformDyadicGrids T).grid j)
    (fun k => eulerGridState ((uniformDyadicGrids T).grid j) b σ W x k ω) (2^j)

theorem measurable_eulerDyadicInterpolant (T : ℝ≥0) (j : ℕ)
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    {W : κ → ℝ≥0 → Ω → ℝ} (x : ι → ℝ)
    (hb : ∀ t i, Measurable (fun y => b t y i)) (hσ : ∀ t i j, Measurable (fun y => σ t y i j))
    (hW : ∀ j, StronglyAdapted 𝒢 (W j)) :
    Measurable (eulerDyadicInterpolant T j b σ W x) := by
  have hX := eulerGridState_stronglyAdapted ((uniformDyadicGrids T).grid j) x hb hσ hW
  exact measurable_gridLinearInterpolateVectorPath T _ _
    (fun k i => ((measurable_pi_apply i).comp (hX k).measurable).mono (𝒢.le _) le_rfl) _

/-- The probability law of the actual dyadic Euler interpolation. -/
noncomputable def eulerDyadicLaw [IsProbabilityMeasure μ] (T : ℝ≥0) (j : ℕ)
    (b : ℝ≥0 → (ι → ℝ) → ι → ℝ) (σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ)
    (W : κ → ℝ≥0 → Ω → ℝ) (x : ι → ℝ) : ProbabilityMeasure (CanonicalPath T (ι → ℝ)) :=
  ProbabilityMeasure.map (⟨μ, inferInstance⟩ : ProbabilityMeasure Ω) (eulerDyadicInterpolant T j b σ W x)

theorem eulerDyadicInterpolant_at_zero {T : ℝ≥0} (hT : 0 < T) (j : ℕ)
    (b : ℝ≥0 → (ι → ℝ) → ι → ℝ) (σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ)
    (W : κ → ℝ≥0 → Ω → ℝ) (x : ι → ℝ) (ω : Ω) :
    canonicalPathEval T 0 (eulerDyadicInterpolant T j b σ W x ω) = x := by
  have h := canonicalPathEval_gridLinearInterpolateVectorPath_at_vertex T
    ((uniformDyadicGrids T).grid j)
    (fun k => eulerGridState ((uniformDyadicGrids T).grid j) b σ W x k ω)
    (fun k (_ : k < 2^j) => uniformDyadicGrid_strictMono hT j k.lt_succ_self)
    (uniform_dyadic_terminal_vertex T j).le (Nat.zero_le (2^j))
  simpa only [eulerDyadicInterpolant, uniform_dyadic_first_vertex, eulerGridState] using h

/-- The fourth-moment bound in canonical path variables, uniform over all
times and over the dyadic Euler laws. -/
theorem eulerDyadicLaw_coordinate_fourth_moment [DecidableEq κ] [IsProbabilityMeasure μ]
    {T : ℝ≥0} (hT : 0 < T) (j : ℕ)
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    {W : κ → ℝ≥0 → Ω → ℝ} (x : ι → ℝ) (i : ι)
    (hb : ∀ t i, Measurable (fun y => b t y i)) (hσ : ∀ t i j, Measurable (fun y => σ t y i j))
    (hW : ∀ j, Martingale (W j) 𝒢 μ) (hW₂ : ∀ j t, MemLp (W j t) 2 μ)
    {B C : ℝ} (hB₀ : 0 ≤ B) (hC₀ : 0 ≤ C)
    (hB : ∀ t y i, ‖b t y i‖ ≤ B) (hC : ∀ t y i j, ‖σ t y i j‖ ≤ C)
    (hGaussian : ∀ k j', HasLaw
      (W j' (((uniformDyadicGrids T).grid j) (k+1)) - W j' (((uniformDyadicGrids T).grid j) k))
      (gaussianReal 0 (((uniformDyadicGrids T).grid j) (k+1) - ((uniformDyadicGrids T).grid j) k)) μ)
    (hCov : ∀ k a a', μ[(W a (((uniformDyadicGrids T).grid j) (k+1)) -
      W a (((uniformDyadicGrids T).grid j) k)) * (W a' (((uniformDyadicGrids T).grid j) (k+1)) -
      W a' (((uniformDyadicGrids T).grid j) k)) | 𝒢 (((uniformDyadicGrids T).grid j) k)] =ᵐ[μ]
      fun _ => if a = a' then ((((uniformDyadicGrids T).grid j) (k+1) : ℝ) -
        (((uniformDyadicGrids T).grid j) k : ℝ)) else 0)
    (t : ℝ≥0) :
    let P := (eulerDyadicLaw (μ := μ) T j b σ W x : Measure (CanonicalPath T (ι → ℝ)))
    let U (p : CanonicalPath T (ι → ℝ)) := canonicalPathEval T t p i - x i
    MemLp U 4 P ∧ (∫ p, U p^4 ∂P) ≤ 81 * boundedEulerGridFourthConstant κ B C T * (T : ℝ)^2 := by
  dsimp only
  let g := (uniformDyadicGrids T).grid j
  let I := eulerDyadicInterpolant T j b σ W x
  let U (p : CanonicalPath T (ι → ℝ)) := canonicalPathEval T t p i - x i
  let P := (eulerDyadicLaw (μ := μ) T j b σ W x : Measure (CanonicalPath T (ι → ℝ)))
  have hI : Measurable I := measurable_eulerDyadicInterpolant T j x hb hσ (fun j' => (hW j').stronglyAdapted)
  have hU : Continuous U := ((continuous_apply i).comp (continuous_canonicalPathEval T t)).sub continuous_const
  have h0 : (0 : ℝ≥0) ∈ Icc (g 0) (g (2^j)) := by dsimp only [g]; simp
  have ht : min t T ∈ Icc (g 0) (g (2^j)) := by
    dsimp only [g]
    simp
  have h := integral_eulerLinearInterpolate_sub_fourth_le g (2^j)
    (fun k _ => uniformDyadicGrid_strictMono hT j k.lt_succ_self)
    x i hb hσ hW hW₂ hB₀ hC₀ hB hC hGaussian hCov (uniform_dyadic_terminal_vertex T j).le
    (show (0 : ℝ≥0) ≤ min t T from zero_le) h0 ht
  have he (ω : Ω) :
      U (I ω) = gridLinearInterpolate g (fun k => eulerGridState g b σ W x k ω i) (2^j) (min t T) -
          gridLinearInterpolate g (fun k => eulerGridState g b σ W x k ω i) (2^j) 0 := by
    have hI0 := congrFun (eulerDyadicInterpolant_at_zero hT j b σ W x ω) i
    change gridLinearInterpolate g (fun k => eulerGridState g b σ W x k ω i) (2^j) (min 0 T) = x i at hI0
    rw [min_eq_left (show (0 : ℝ≥0) ≤ T from zero_le)] at hI0
    change _ - x i = _
    rw [hI0]
    rfl
  have hPull : MemLp (U ∘ I) 4 μ :=
    MemLp.ae_eq (Eventually.of_forall fun ω => (he ω).symm) h.1
  have hMeasure : P = μ.map I := rfl
  change MemLp U 4 P ∧ (∫ p, U p^4 ∂P) ≤ _
  rw [hMeasure]
  refine ⟨(memLp_map_measure_iff hU.stronglyMeasurable.aestronglyMeasurable hI.aemeasurable).2 hPull, ?_⟩
  have hU₄ : AEStronglyMeasurable (fun p => U p^4) (μ.map I) :=
    (hU.pow 4).stronglyMeasurable.aestronglyMeasurable
  rw [integral_map hI.aemeasurable hU₄]
  change (∫ ω, U (I ω)^4 ∂μ) ≤ _
  calc
    _ ≤ 81 * boundedEulerGridFourthConstant κ B C T * ((min t T : ℝ≥0) : ℝ)^2 := by
      simp_rw [he]
      simpa only [NNReal.coe_zero, sub_zero] using h.2
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (NNReal.coe_nonneg _) (NNReal.coe_le_coe.mpr (min_le_right t T)) 2)
      exact mul_nonneg (by norm_num) (boundedEulerGridFourthConstant_nonneg κ B C T)

#print axioms RoughHeston.eulerDyadicLaw_coordinate_fourth_moment
#print axioms RoughHeston.integral_sq_mul_le_of_four

end RoughHeston
