import AffineMeanFubini
import Mathlib.Topology.UniformSpace.UniformApproximation

open MeasureTheory Set Filter
open scoped Topology

namespace RoughHeston

theorem measurable_affine_variance_mean {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [SFinite μ] {V : ℝ → Ω → ℝ}
    (hVm : ∀ t, Measurable (V t)) (hVc : ∀ ω, Continuous (fun t => V t ω)) :
    Measurable (fun t => ∫ ω,V t ω ∂μ) :=
  (measurable_uncurry_of_continuous_of_measurable hVc hVm).stronglyMeasurable.integral_prod_right'.measurable

/-- Continuous nonnegative paths with a locally uniform second moment
have a continuous mean on that time set. -/
theorem continuousOn_affine_variance_mean {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {V : ℝ → Ω → ℝ} {S : Set ℝ} {B : ℝ}
    (hVm : ∀ t, Measurable (V t)) (hVc : ∀ ω, Continuous (fun t => V t ω))
    (hVn : ∀ t ω, 0≤V t ω) (hVi : ∀ t∈S,Integrable (V t) μ)
    (hV₂ : ∀ t∈S,Integrable (fun ω => (V t ω)^2) μ)
    (hB : 0≤B) (hVB : ∀ t∈S,(∫ ω, (V t ω)^2 ∂μ)≤B) :
    ContinuousOn (fun t => ∫ ω,V t ω ∂μ) S := by
  let U (R t : ℝ) := ∫ ω,min (V t ω) R ∂μ
  let F (t : ℝ) := ∫ ω,V t ω ∂μ
  have hM (R t : ℝ) : AEStronglyMeasurable (fun ω => min (V t ω) R) μ :=
    ((hVm t).min measurable_const).aestronglyMeasurable
  have hBdd (R : ℝ) (hR : 0≤R) (t : ℝ) (ω : Ω) : ‖min (V t ω) R‖≤R := by
    rw [Real.norm_of_nonneg (le_min (hVn _ _) hR)]
    exact min_le_right _ _
  have hUc (R : ℝ) (hR : 0≤R) : Continuous (U R) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact tendsto_integral_filter_of_dominated_convergence (fun _ => R)
      (Eventually.of_forall (hM R))
      (Eventually.of_forall fun t => ae_of_all _ (hBdd R hR t))
      (integrable_const R) (ae_of_all _ fun ω => ((hVc ω).min continuous_const).continuousAt)
  have hErr (R : ℝ) (hR : 0<R) (t : ℝ) (ht : t∈S) : dist (F t) (U R t)≤B/R := by
    have hUi : Integrable (fun ω => min (V t ω) R) μ :=
      (integrable_const R).mono' (hM R t) (ae_of_all _ (hBdd R hR.le t))
    have hDiff (ω : Ω) : 0≤V t ω-min (V t ω) R := sub_nonneg.mpr (min_le_left _ _)
    rw [Real.dist_eq]
    change |(∫ ω,V t ω ∂μ)-(∫ ω,min (V t ω) R ∂μ)|≤B/R
    rw [← integral_sub (hVi t ht) hUi]
    have hn : 0≤(∫ ω,V t ω-min (V t ω) R ∂μ) := integral_nonneg hDiff
    rw [abs_of_nonneg hn]
    refine (integral_mono ((hVi t ht).sub hUi) ((hV₂ t ht).div_const R) ?_).trans ?_
    · intro ω
      change V t ω-min (V t ω) R≤(V t ω)^2/R
      by_cases h : V t ω≤R
      · rw [min_eq_left h,sub_self]
        positivity
      · rw [min_eq_right (le_of_not_ge h)]
        apply (le_div_iff₀ hR).mpr
        have hh := mul_le_mul_of_nonneg_left (le_of_not_ge h) (hVn t ω)
        nlinarith [sq_nonneg R]
    · rw [integral_div]
      exact div_le_div_of_nonneg_right (hVB t ht) hR.le
  have hLim : TendstoUniformlyOn U F atTop S := Metric.tendstoUniformlyOn_iff.mpr (by
    intro ε hε
    filter_upwards [eventually_ge_atTop (B/ε+1)] with R hR t ht
    have hR₀ : 0<R := by linarith [div_nonneg hB hε.le]
    refine (hErr R hR₀ t ht).trans_lt ((div_lt_iff₀ hR₀).mpr ?_)
    have hh : B/ε<R := lt_of_lt_of_le (lt_add_one _) hR
    simpa only [mul_comm ε R] using (div_lt_iff₀ hε).mp hh)
  apply hLim.continuousOn
  have he : ∀ᶠ R : ℝ in atTop, ContinuousOn (U R) S :=
    (eventually_ge_atTop (0:ℝ)).mono fun R hR => (hUc R hR).continuousOn
  exact he.frequently

#print axioms continuousOn_affine_variance_mean

end RoughHeston
