import EulerInterpolationMoments
import CanonicalProperPathTightness

/-! Weak subsequence extraction for the continuous Euler state laws. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston

variable {Ω ι κ : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  [Fintype ι] [Fintype κ]

/-- Apply the same affine interpolation to each state coordinate. -/
noncomputable def gridLinearInterpolateVectorPath (T : ℝ≥0) (grid : ℕ →o ℝ≥0)
    (X : ℕ → ι → ℝ) (n : ℕ) : CanonicalPath T (ι → ℝ) where
  toFun s i := gridLinearInterpolate grid (fun k => X k i) n s
  continuous_toFun := continuous_pi fun i =>
    (continuous_gridLinearInterpolate grid (fun k => X k i) n).comp continuous_subtype_val

theorem measurable_gridLinearInterpolateVectorPath (T : ℝ≥0) (grid : ℕ →o ℝ≥0)
    (X : ℕ → Ω → ι → ℝ) (hX : ∀ k i, Measurable (fun ω => X k ω i)) (n : ℕ) :
    Measurable (fun ω => gridLinearInterpolateVectorPath T grid (fun k => X k ω) n) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro s
  exact Measurable.of_eval fun i =>
    measurable_gridLinearInterpolate_eval grid (fun k ω => X k ω i) (fun k => hX k i) n s

private theorem edist_vector_pow_four_le_sum (u v : ι → ℝ) :
    edist u v ^ (4 : ℕ) ≤ ∑ i, ENNReal.ofReal ((u i - v i)^4) := by
  let R := ∑ i, (u i - v i)^4
  let r := Real.sqrt (Real.sqrt R)
  have hR : 0 ≤ R := Finset.sum_nonneg fun _ _ => by positivity
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr4 : r^4 = R := by
    calc
      _ = (r^2)^2 := by ring
      _ = _ := by dsimp only [r]; rw [Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hR]
  have hd : dist u v ≤ r := (dist_pi_le_iff hr).2 fun i => by
    apply le_of_pow_le_pow_left₀ (by decide : (4 : ℕ) ≠ 0) hr
    rw [hr4, Real.dist_eq, ← abs_pow, abs_of_nonneg (by positivity : 0 ≤ (u i - v i)^4)]
    exact Finset.single_le_sum (f := fun j => (u j - v j)^4) (fun j _ => by positivity) (Finset.mem_univ i)
  have h := pow_le_pow_left₀ dist_nonneg hd 4
  rw [hr4] at h
  rw [edist_dist, ← ENNReal.ofReal_pow dist_nonneg, ← ENNReal.ofReal_sum_of_nonneg
    (fun i _ => by positivity)]
  exact ENNReal.ofReal_le_ofReal h

/-- The canonical laws of the continuous Euler interpolants have a weakly
convergent subsequence, uniformly over grids ending at one fixed horizon. -/
theorem eulerLinearInterpolationLaw_subsequence [DecidableEq κ] [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} {T : ℝ≥0} (hT : 0 < T)
    (grid : ℕ → (ℕ →o ℝ≥0)) (steps : ℕ → ℕ)
    (hgrid : ∀ n k, k < steps n → grid n k < grid n (k+1))
    (hStart : ∀ n, grid n 0 = 0) (hEnd : ∀ n, grid n (steps n) = T)
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    {W : κ → ℝ≥0 → Ω → ℝ} (x : ι → ℝ)
    (hb : ∀ t i, Measurable (fun y => b t y i))
    (hσ : ∀ t i j, Measurable (fun y => σ t y i j))
    (hW : ∀ j, Martingale (W j) 𝒢 μ) (hW₂ : ∀ j t, MemLp (W j t) 2 μ)
    {B C : ℝ} (hB₀ : 0 ≤ B) (hC₀ : 0 ≤ C)
    (hB : ∀ t y i, ‖b t y i‖ ≤ B) (hC : ∀ t y i j, ‖σ t y i j‖ ≤ C)
    (hGaussian : ∀ n k j, HasLaw (W j (grid n (k + 1)) - W j (grid n k))
      (gaussianReal 0 (grid n (k + 1) - grid n k)) μ)
    (hCov : ∀ n k j l, μ[(W j (grid n (k + 1)) - W j (grid n k)) *
        (W l (grid n (k + 1)) - W l (grid n k)) | 𝒢 (grid n k)] =ᵐ[μ]
      fun _ => if j = l then ((grid n (k + 1) : ℝ) - (grid n k : ℝ)) else 0) :
    let Pn (n : ℕ) := ProbabilityMeasure.map (⟨μ, inferInstance⟩ : ProbabilityMeasure Ω) (fun ω =>
      gridLinearInterpolateVectorPath T (grid n)
        (fun k => eulerGridState (grid n) b σ W x k ω) (steps n))
    ∃ P : ProbabilityMeasure (CanonicalPath T (ι → ℝ)), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (Pn ∘ φ) atTop (𝓝 P) := by
  classical
  dsimp only
  let X (n k : ℕ) := eulerGridState (grid n) b σ W x k
  let I (n : ℕ) (ω : Ω) :=
    gridLinearInterpolateVectorPath T (grid n) (fun k => X n k ω) (steps n)
  let Pn (n : ℕ) := ProbabilityMeasure.map (⟨μ, inferInstance⟩ : ProbabilityMeasure Ω) (I n)
  let Q := 81 * boundedEulerGridFourthConstant κ B C T
  let Qvec := (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal Q
  have hQ : 0 ≤ Q := mul_nonneg (by norm_num) (boundedEulerGridFourthConstant_nonneg κ B C T)
  have hQv : Qvec ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
  have hI (n : ℕ) : Measurable (I n) := by
    have hX := eulerGridState_stronglyAdapted (grid n) x hb hσ
      (fun j => (hW j).stronglyAdapted)
    apply measurable_gridLinearInterpolateVectorPath
    intro k i
    exact ((measurable_pi_apply i).comp (hX k).measurable).mono (𝒢.le _) le_rfl
  have hInitial (n : ℕ) :
      (Pn n : Measure (CanonicalPath T (ι → ℝ)))
        {f | ‖x‖ < ‖f (canonicalEvalTime T 0)‖} = 0 := by
    let A : Set (CanonicalPath T (ι → ℝ)) := {f | ‖x‖ < ‖f (canonicalEvalTime T 0)‖}
    have hA : MeasurableSet A :=
      measurableSet_lt measurable_const
        (continuous_norm.comp (continuous_canonicalPathEval T 0)).measurable
    change (μ.map (I n)) A = 0
    rw [Measure.map_apply (hI n) hA]
    have hI0 (ω : Ω) : I n ω (canonicalEvalTime T 0) = x := by
      funext i
      change gridLinearInterpolate (grid n) (fun k => X n k ω i) (steps n) (min 0 T) = x i
      rw [min_eq_left (zero_le : 0 ≤ T), ← hStart n,
        gridLinearInterpolate_at_vertex (grid n) _ (hgrid n) (Nat.zero_le (steps n))]
      rfl
    simp [A, hI0]
  have hMom (n : ℕ) (s t : CanonicalPathTime T) (hst : s ≤ t) :
      (∫⁻ f : CanonicalPath T (ι → ℝ), edist (f t) (f s) ^ (4 : ℝ) ∂(Pn n : Measure _)) ≤
        Qvec * edist s t ^ (2 : ℝ) := by
    let d := ((t : ℝ≥0) : ℝ) - ((s : ℝ≥0) : ℝ)
    let V (i : ι) (ω : Ω) := I n ω t i - I n ω s i
    have hst' : (s : ℝ≥0) ≤ (t : ℝ≥0) := hst
    have hs : s.val ∈ Icc (grid n 0) (grid n (steps n)) := by
      rw [hStart, hEnd]
      exact s.property
    have ht : t.val ∈ Icc (grid n 0) (grid n (steps n)) := by
      rw [hStart, hEnd]
      exact t.property
    have hV (i : ι) : MemLp (V i) 4 μ ∧ (∫ ω, V i ω ^ 4 ∂μ) ≤ Q * d^2 :=
      integral_eulerLinearInterpolate_sub_fourth_le (grid n) (steps n) (hgrid n)
        x i hb hσ hW hW₂ hB₀ hC₀ hB hC (hGaussian n) (hCov n)
        (hEnd n).le hst' hs ht
    have hV4 (i : ι) : Integrable (fun ω => V i ω ^ 4) μ := by
      have hf := (hV i).1.integrable_norm_pow (p := 4) (by decide)
      convert hf using 1
      ext ω
      rw [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity : 0 ≤ V i ω ^ 4)]
    have hd : 0 ≤ d := sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst')
    have htime : ENNReal.ofReal (d^2) = edist s t ^ (2 : ℝ) := by
      have he : dist s t = d := by
        change |((s : ℝ≥0) : ℝ) - ((t : ℝ≥0) : ℝ)| = d
        rw [abs_of_nonpos (sub_nonpos.mpr (NNReal.coe_le_coe.mpr hst'))]
        dsimp [d]
        ring
      rw [edist_dist, he, ENNReal.ofReal_pow hd]
      simp
    have hEval : Measurable (fun f : CanonicalPath T (ι → ℝ) => edist (f t) (f s) ^ (4 : ℝ)) :=
      (ENNReal.continuous_rpow_const.comp ((continuous_eval_const t).edist
        (continuous_eval_const s))).measurable
    change (∫⁻ f, edist (f t) (f s) ^ (4 : ℝ) ∂Measure.map (I n) μ) ≤ _
    rw [lintegral_map hEval (hI n)]
    have h4 : (4 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
    simp_rw [h4, ENNReal.rpow_natCast]
    calc
      _ ≤ ∫⁻ ω, ∑ i, ENNReal.ofReal ((V i ω)^4) ∂μ :=
        lintegral_mono fun ω => edist_vector_pow_four_le_sum (I n ω t) (I n ω s)
      _ = ∑ i, ∫⁻ ω, ENNReal.ofReal ((V i ω)^4) ∂μ :=
        lintegral_finsetSum' Finset.univ fun i _ => (hV4 i).aestronglyMeasurable.aemeasurable.ennreal_ofReal
      _ ≤ ∑ _i : ι, ENNReal.ofReal (Q * d^2) := by
        apply Finset.sum_le_sum
        intro i _
        rw [← ofReal_integral_eq_lintegral_ofReal (hV4 i) (Eventually.of_forall fun _ => by positivity)]
        exact ENNReal.ofReal_le_ofReal (hV i).2
      _ = Qvec * edist s t ^ (2 : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul hQ, htime]
        ring
  refine canonicalProperPath_subsequence_of_increment_moments hT 4 2 ‖x‖ (by norm_num)
    (by norm_num) Pn Qvec hQv hInitial fun n s t => ?_
  rcases le_total s t with h | h
  · have hswap (f : CanonicalPath T (ι → ℝ)) : edist (f t) (f s) = edist (f s) (f t) :=
      edist_comm _ _
    simpa only [hswap] using hMom n s t h
  · simpa only [edist_comm s t] using hMom n t s h

#print axioms RoughHeston.measurable_gridLinearInterpolateVectorPath
#print axioms RoughHeston.eulerLinearInterpolationLaw_subsequence

end RoughHeston
