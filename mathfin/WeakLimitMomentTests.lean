import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Linarith

open MeasureTheory Filter
open scoped MeasureTheory BoundedContinuousFunction Topology ENNReal

namespace RoughHeston

variable {E I : Type*} [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]

/-- Clip a continuous real function at both ends to obtain a bounded
continuous test. -/
private noncomputable def clippedContinuous {g : E → ℝ} (hg : Continuous g)
    {R : ℝ} (hR : 0 ≤ R) : E →ᵇ ℝ where
  toFun x := max (-R) (min R (g x))
  continuous_toFun := continuous_const.max (continuous_const.min hg)
  map_bounded' := ⟨2 * R, fun x y => by
    rw [Real.dist_eq]
    apply abs_le.mpr
    have hlow (a : E) : -R ≤ max (-R) (min R (g a)) := le_max_left _ _
    have hhigh (a : E) : max (-R) (min R (g a)) ≤ R :=
      max_le (by linarith) (min_le_left _ _)
    constructor <;> linarith [hlow x, hlow y, hhigh x, hhigh y]⟩

private theorem abs_sub_clip_le_sq_div {R : ℝ} (hR : 0 < R) (z : ℝ) :
    |z - max (-R) (min R z)| ≤ z ^ 2 / R := by
  by_cases hu : R ≤ z
  · rw [min_eq_left hu, max_eq_right (by linarith : -R ≤ R),
      abs_of_nonneg (sub_nonneg.mpr hu), le_div_iff₀ hR]
    nlinarith [mul_nonneg (hR.le.trans hu) (sub_nonneg.mpr hu), sq_nonneg (z - R)]
  · have hur : z ≤ R := le_of_not_ge hu
    by_cases hl : z ≤ -R
    · rw [min_eq_right hur, max_eq_left hl, abs_of_nonpos (sub_nonpos.mpr hl), le_div_iff₀ hR]
      have h1 : 0 ≤ -z := by linarith
      have h2 : 0 ≤ -(z + R) := by linarith
      nlinarith [mul_nonneg h1 h2, sq_nonneg (z + R)]
    · rw [min_eq_right hur, max_eq_right (le_of_not_ge hl), sub_self, abs_zero]
      exact div_nonneg (sq_nonneg _) hR.le

private theorem integral_clip_error_le
    (P : ProbabilityMeasure E) {g : E → ℝ} (hg : Continuous g)
    (hg₂ : MemLp g 2 (P : Measure E)) {R C : ℝ} (hR : 0 < R)
    (hC : (∫ x, g x ^ 2 ∂(P : Measure E)) ≤ C) :
    dist (∫ x, g x ∂(P : Measure E))
      (∫ x, clippedContinuous hg hR.le x ∂(P : Measure E)) ≤ C / R := by
  let gR := clippedContinuous hg hR.le
  have hi := hg₂.integrable one_le_two
  have hRi : Integrable gR (P : Measure E) := gR.integrable (μ := (P : Measure E))
  calc
    _ = ‖∫ x, g x - gR x ∂(P : Measure E)‖ := by
      rw [Real.dist_eq, integral_sub hi hRi, Real.norm_eq_abs]
    _ ≤ ∫ x, ‖g x - gR x‖ ∂(P : Measure E) := norm_integral_le_integral_norm _
    _ ≤ ∫ x, g x ^ 2 / R ∂(P : Measure E) := by
      apply integral_mono (hi.sub hRi).norm (hg₂.integrable_sq.div_const R)
      intro x
      exact abs_sub_clip_le_sq_div hR (g x)
    _ = (∫ x, g x ^ 2 ∂(P : Measure E)) / R := integral_div R _
    _ ≤ C / R := div_le_div_of_nonneg_right hC hR.le

/-- Weak convergence passes integrals of a continuous real test with
uniformly bounded second moments under the approximating and limit
probability measures. -/
theorem tendsto_integral_of_weak_of_uniform_sq_moment
    {l : Filter I} {Pn : I → ProbabilityMeasure E} {P : ProbabilityMeasure E}
    (hweak : Tendsto Pn l (𝓝 P)) {g : E → ℝ} (hg : Continuous g)
    (hgn : ∀ i, MemLp g 2 (Pn i : Measure E)) (hgP : MemLp g 2 (P : Measure E))
    {C : ℝ} (hCn : ∀ i, (∫ x, g x ^ 2 ∂(Pn i : Measure E)) ≤ C)
    (hCP : (∫ x, g x ^ 2 ∂(P : Measure E)) ≤ C) :
    Tendsto (fun i => ∫ x, g x ∂(Pn i : Measure E)) l
      (𝓝 (∫ x, g x ∂(P : Measure E))) := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨R, hR⟩ := exists_gt (max 0 (3 * C / ε))
  have hRpos : 0 < R := (le_max_left _ _).trans_lt hR
  have htail : C / R < ε / 3 := by
    have h₁ : 3 * C < R * ε :=
      (div_lt_iff₀ hε).1 ((le_max_right _ _).trans_lt hR)
    apply (div_lt_iff₀ hRpos).2
    nlinarith
  let gR := clippedContinuous hg hRpos.le
  have hclip := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hweak gR
  filter_upwards [Metric.tendsto_nhds.1 hclip (ε / 3) (by positivity)] with i hi
  have h₁ := integral_clip_error_le (Pn i) hg (hgn i) hRpos (hCn i)
  have h₃ := integral_clip_error_le P hg hgP hRpos hCP
  calc
    _ ≤ dist (∫ x, g x ∂(Pn i : Measure E)) (∫ x, gR x ∂(Pn i : Measure E)) +
        dist (∫ x, gR x ∂(Pn i : Measure E)) (∫ x, gR x ∂(P : Measure E)) +
        dist (∫ x, gR x ∂(P : Measure E)) (∫ x, g x ∂(P : Measure E)) :=
      dist_triangle4 _ _ _ _
    _ < ε := by
      rw [dist_comm (∫ x, gR x ∂(P : Measure E)) (∫ x, g x ∂(P : Measure E))]
      change dist _ (∫ x, clippedContinuous hg hRpos.le x ∂(Pn i : Measure E)) +
        dist (∫ x, gR x ∂(Pn i : Measure E)) (∫ x, gR x ∂(P : Measure E)) +
        dist _ (∫ x, clippedContinuous hg hRpos.le x ∂(P : Measure E)) < ε
      linarith

/-- The second-moment bound itself passes to the weak limit. -/
theorem weak_limit_memLp_two_and_sq_moment_bound
    {l : Filter I} [NeBot l] {Pn : I → ProbabilityMeasure E} {P : ProbabilityMeasure E}
    (hweak : Tendsto Pn l (𝓝 P)) {g : E → ℝ} (hg : Continuous g)
    (hgn : ∀ i, MemLp g 2 (Pn i : Measure E)) {C : ℝ}
    (hCn : ∀ i, (∫ x, g x ^ 2 ∂(Pn i : Measure E)) ≤ C) :
    MemLp g 2 (P : Measure E) ∧ (∫ x, g x ^ 2 ∂(P : Measure E)) ≤ C := by
  let f (n : ℕ) : E →ᵇ ℝ :=
    clippedContinuous (hg.pow 2) (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n)
  have hEq (n : ℕ) (x : E) : f n x = min (n : ℝ) (g x ^ 2) := by
    change max (-(n : ℝ)) (min (n : ℝ) (g x ^ 2)) = _
    exact max_eq_right ((neg_nonpos.mpr (Nat.cast_nonneg n)).trans
      (le_min (Nat.cast_nonneg n) (sq_nonneg _)))
  have hf0 (n : ℕ) (x : E) : 0 ≤ f n x := by
    rw [hEq]
    exact le_min (Nat.cast_nonneg n) (sq_nonneg _)
  have hbound (n : ℕ) : (∫ x, f n x ∂(P : Measure E)) ≤ C := by
    apply le_of_tendsto' (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hweak (f n))
    intro i
    refine (integral_mono ((f n).integrable (μ := (Pn i : Measure E)))
      (hgn i).integrable_sq (fun x => ?_)).trans (hCn i)
    rw [hEq]
    exact min_le_right _ _
  have hC : 0 ≤ C := (integral_nonneg (hf0 0)).trans (hbound 0)
  let F (n : ℕ) (x : E) := ENNReal.ofReal (f n x)
  have hFm (n : ℕ) : Measurable (F n) := (f n).continuous.measurable.ennreal_ofReal
  have hmono : Monotone F := by
    intro n k hnk x
    apply ENNReal.ofReal_le_ofReal
    rw [hEq, hEq]
    exact min_le_min_right _ (by exact_mod_cast hnk)
  have hF (x : E) : ENNReal.ofReal (g x ^ 2) = ⨆ n, F n x := by
    apply le_antisymm
    · obtain ⟨n, hn⟩ := exists_nat_gt (g x ^ 2)
      calc
        _ = F n x := by simp only [F, hEq, min_eq_right hn.le]
        _ ≤ _ := le_iSup (fun n => F n x) n
    · exact iSup_le fun n => ENNReal.ofReal_le_ofReal (by rw [hEq]; exact min_le_right _ _)
  have hL : (∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂(P : Measure E)) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ x, ⨆ n, F n x ∂(P : Measure E) := lintegral_congr hF
      _ = ⨆ n, ∫⁻ x, F n x ∂(P : Measure E) := lintegral_iSup hFm hmono
      _ ≤ _ := by
        apply iSup_le
        intro n
        change (∫⁻ x, ENNReal.ofReal (f n x) ∂(P : Measure E)) ≤ ENNReal.ofReal C
        rw [← ofReal_integral_eq_lintegral_ofReal ((f n).integrable (μ := (P : Measure E)))
          (Eventually.of_forall (hf0 n))]
        exact ENNReal.ofReal_le_ofReal (hbound n)
  have hsq : Integrable (fun x => g x ^ 2) (P : Measure E) :=
    ⟨(hg.pow 2).measurable.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => sq_nonneg (g x))).2
        (hL.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨(memLp_two_iff_integrable_sq hg.measurable.aestronglyMeasurable).2 hsq, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hsq (Eventually.of_forall fun x => sq_nonneg (g x)),
    ENNReal.ofReal_le_ofReal_iff hC] at hL
  exact hL

/-- A uniform second moment on the approximating laws suffices for the
convergence of continuous test integrals. -/
theorem tendsto_integral_of_weak_of_uniform_sq_moment'
    {l : Filter I} [NeBot l] {Pn : I → ProbabilityMeasure E} {P : ProbabilityMeasure E}
    (hweak : Tendsto Pn l (𝓝 P)) {g : E → ℝ} (hg : Continuous g)
    (hgn : ∀ i, MemLp g 2 (Pn i : Measure E)) {C : ℝ}
    (hCn : ∀ i, (∫ x, g x ^ 2 ∂(Pn i : Measure E)) ≤ C) :
    Tendsto (fun i => ∫ x, g x ∂(Pn i : Measure E)) l
      (𝓝 (∫ x, g x ∂(P : Measure E))) := by
  obtain ⟨hgP, hCP⟩ := weak_limit_memLp_two_and_sq_moment_bound hweak hg hgn hCn
  exact tendsto_integral_of_weak_of_uniform_sq_moment hweak hg hgn hgP hCn hCP

end RoughHeston

#print axioms RoughHeston.tendsto_integral_of_weak_of_uniform_sq_moment
#print axioms RoughHeston.weak_limit_memLp_two_and_sq_moment_bound
#print axioms RoughHeston.tendsto_integral_of_weak_of_uniform_sq_moment'
