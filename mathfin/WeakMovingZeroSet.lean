import WeakCompactTestConvergence

/-! Exactly satisfied path identities pass to weak limits when their
continuous residuals converge uniformly on compact sets. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace RoughHeston

private noncomputable def clippedNormTest {X : Type*} [TopologicalSpace X]
    {g : X → ℝ} (hg : Continuous g) : X →ᵇ ℝ where
  toFun x := min 1 ‖g x‖
  continuous_toFun := continuous_const.min hg.norm
  map_bounded' := ⟨1, fun x y => by
    rw [Real.dist_eq]
    apply abs_le.mpr
    have h0 (z : X) : 0 ≤ min 1 ‖g z‖ := le_min zero_le_one (norm_nonneg _)
    have h1 (z : X) : min 1 ‖g z‖ ≤ 1 := min_le_left _ _
    constructor <;> linarith [h0 x, h0 y, h1 x, h1 y]⟩

theorem ae_eq_zero_of_weak_of_continuous_moving_zero
    {X : Type*} [MetricSpace X] [SecondCountableTopology X] [CompleteSpace X]
    [MeasurableSpace X] [BorelSpace X] {Pn : ℕ → ProbabilityMeasure X} {P : ProbabilityMeasure X}
    (hweak : Tendsto Pn atTop (𝓝 P)) {F : X → ℝ} {Fn : ℕ → X → ℝ}
    (hF : Continuous F) (hFn : ∀ n, Continuous (Fn n))
    (hTest : ∀ n, Fn n =ᵐ[(Pn n : Measure X)] 0)
    (hClose : ∀ K : Set X, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ x ∈ K, ‖F x - Fn n x‖ < ε) :
    F =ᵐ[(P : Measure X)] 0 := by
  let f : X →ᵇ ℝ := clippedNormTest hF
  let fn (n : ℕ) : X →ᵇ ℝ := clippedNormTest (hFn n)
  have hf (x : X) : f x = min 1 ‖F x‖ := rfl
  have hfn (n : ℕ) (x : X) : fn n x = min 1 ‖Fn n x‖ := rfl
  let d (n : ℕ) (x : X) := f x - fn n x
  have hd₁ (n : ℕ) (x : X) : ‖d n x‖ ≤ 1 := by
    change ‖f x - fn n x‖ ≤ 1
    rw [hf, hfn, Real.norm_eq_abs, abs_le]
    have h0 (y : ℝ) : 0 ≤ min 1 ‖y‖ := le_min zero_le_one (norm_nonneg _)
    have h1 (y : ℝ) : min 1 ‖y‖ ≤ 1 := min_le_left _ _
    constructor <;> linarith [h0 (F x), h0 (Fn n x), h1 (F x), h1 (Fn n x)]
  have hdLp (n : ℕ) : MemLp (d n) 2 (Pn n : Measure X) :=
    (memLp_top_of_bound ((f.continuous.sub (fn n).continuous).aestronglyMeasurable)
      1 (Eventually.of_forall (hd₁ n))).mono_exponent le_top
  have hdSq (n : ℕ) : (∫ x, (d n x)^2 ∂(Pn n : Measure X)) ≤ 1 := by
    have hb := integral_mono (hdLp n).integrable_sq (integrable_const (1 : ℝ)) (fun x => by
      have he := pow_le_pow_left₀ (norm_nonneg _) (hd₁ n x) 2
      simpa only [Real.norm_eq_abs, sq_abs, one_pow] using he)
    simpa [measureReal_def] using hb
  have hdClose (K : Set X) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ n in atTop, ∀ x ∈ K, ‖d n x‖ < ε := by
    filter_upwards [hClose K hK ε hε] with n hn x hx
    refine lt_of_le_of_lt ?_ (hn x hx)
    change dist (f x) (fn n x) ≤ ‖F x-Fn n x‖
    rw [hf, hfn]
    rw [Real.dist_eq]
    have hdmin := abs_min_sub_min_le_max (1 : ℝ) ‖F x‖ 1 ‖Fn n x‖
    rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)] at hdmin
    exact hdmin.trans (abs_norm_sub_norm_le (F x) (Fn n x))
  have hL := tendsto_integral_norm_zero_of_uniform_on_compacts_of_weak hweak zero_le_one hdLp hdSq hdClose
  have hA (n : ℕ) : (fun x => ‖d n x‖) =ᵐ[(Pn n : Measure X)] f := by
    filter_upwards [hTest n] with x hx
    have hx' : Fn n x = 0 := hx
    simp only [d, hfn, hx', norm_zero, min_eq_right zero_le_one, sub_zero]
    rw [Real.norm_of_nonneg]
    rw [hf]
    exact le_min zero_le_one (norm_nonneg _)
  have hweakf := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hweak f
  have hint : (∫ x, f x ∂(P : Measure X)) = 0 :=
    tendsto_nhds_unique hweakf (hL.congr (fun n => integral_congr_ae (hA n)))
  have hf0 : ∀ x, 0 ≤ f x := fun x => (hf x).symm ▸ le_min zero_le_one (norm_nonneg _)
  have hae := (integral_eq_zero_iff_of_nonneg hf0
    (f.integrable (μ := (P : Measure X)))).mp hint
  filter_upwards [hae] with x hx
  change F x = 0
  rw [hf] at hx
  by_contra hne
  exact (lt_min zero_lt_one (norm_pos_iff.mpr hne)).ne' hx

#print axioms RoughHeston.ae_eq_zero_of_weak_of_continuous_moving_zero

end RoughHeston
