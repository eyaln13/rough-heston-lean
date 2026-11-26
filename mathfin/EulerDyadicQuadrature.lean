import EulerCanonicalCoefficientIntegral
import EulerStoppedGridTests
import Mathlib.Topology.UniformSpace.HeineCantor

/-! Dyadic quadrature of bounded continuous coefficients on canonical paths. -/

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston

open MathFin.ItoIntegralCLM

variable {ι : Type*} [Fintype ι]

/-- Integrate the left-endpoint coefficient interpolation, with the
same deterministic cutoff as the canonical coefficient integral. -/
noncomputable def canonicalDyadicCoefficientIntegral (T : ℝ≥0) (j : ℕ)
    (c : ℝ≥0 → (ι → ℝ) → ℝ) (t : ℝ≥0) (p : CanonicalPath T (ι → ℝ)) : ℝ :=
  ∫ r, uniformDyadicStep T j (fun q => c q (canonicalPathEval T q p)) r
    ∂timeMeasureHorizon (min t T)

theorem canonicalDyadicCoefficientIntegral_at_grid_vertex (T : ℝ≥0) (j : ℕ)
    (c : ℝ≥0 → (ι → ℝ) → ℝ) {a : ℕ} (ha : a ≤ 2 ^ j)
    (p : CanonicalPath T (ι → ℝ)) :
    canonicalDyadicCoefficientIntegral T j c ((uniformDyadicGrids T).grid j a) p =
      canonicalGridCoefficientSum T ((uniformDyadicGrids T).grid j) c a p := by
  let g := (uniformDyadicGrids T).grid j
  let S (k : ℕ) := Ioc (g k) (g (k+1))
  let b (k : ℕ) := c (g k) (canonicalPathEval T (g k) p)
  have hgT : g a ≤ T := (g.monotone ha).trans_eq (uniform_dyadic_terminal_vertex T j)
  have hInt (k : ℕ) :
      Integrable ((S k).indicator (fun _ => b k)) (timeMeasureHorizon (g a)) :=
    (integrable_const (b k)).indicator measurableSet_Ioc
  rw [canonicalGridCoefficientSum, runningSum, Finset.sum_apply]
  change (∫ r, ∑ k ∈ Finset.range (2 ^ j), (S k).indicator (fun _ => b k) r
      ∂timeMeasureHorizon (min (g a) T)) =
      ∑ k ∈ Finset.range a, b k * ((g (k+1) : ℝ) - (g k : ℝ))
  rw [min_eq_left hgT, integral_finsetSum _ (fun k _ => hInt k)]
  let d (k : ℕ) := ∫ r, (S k).indicator (fun _ => b k) r ∂timeMeasureHorizon (g a)
  have hd (k : ℕ) :
      d k = if k < a then b k * ((g (k+1) : ℝ) - (g k : ℝ)) else 0 := by
    have hmeas : MeasurableSet (S k) := measurableSet_Ioc
    dsimp only [d]
    rw [integral_indicator hmeas, setIntegral_const, smul_eq_mul,
      measureReal_def, timeMeasureHorizon, Measure.restrict_apply hmeas]
    by_cases hk : k < a
    · have hsub : S k ⊆ Ioc 0 (g a) := by
        intro r hr
        exact ⟨(show (0 : ℝ≥0) ≤ g k from zero_le).trans_lt hr.1,
          hr.2.trans (g.monotone (Nat.succ_le_of_lt hk))⟩
      rw [inter_eq_left.mpr hsub]
      dsimp only [S]
      rw [MathFin.ItoIntegralL2.timeMeasure_Ioc, ENNReal.toReal_ofReal
        (sub_nonneg.mpr (NNReal.coe_le_coe.mpr (g.monotone k.le_succ))), if_pos hk, mul_comm]
    · have hdisj : Disjoint (S k) (Ioc 0 (g a)) := by
        refine disjoint_left.2 fun r hr hra => ?_
        exact (not_lt_of_ge (hra.2.trans (g.monotone (Nat.le_of_not_gt hk)))) hr.1
      rw [hdisj.inter_eq]
      simp [hk]
  change ∑ k ∈ Finset.range (2 ^ j), d k =
      ∑ k ∈ Finset.range a, b k * ((g (k+1) : ℝ) - (g k : ℝ))
  have hsub : Finset.range a ⊆ Finset.range (2 ^ j) := Finset.range_mono ha
  rw [← Finset.sum_subset hsub (fun k _ hk => by
    rw [hd, if_neg (fun h => hk (Finset.mem_range.mpr h))])]
  exact Finset.sum_congr rfl fun k hk => by rw [hd, if_pos (Finset.mem_range.mp hk)]

private theorem uniform_dyadic_mesh_tendsto_zero (T : ℝ≥0) :
    Tendsto (fun j : ℕ => ((T / (2 ^ j : ℝ≥0) : ℝ≥0) : ℝ)) atTop (𝓝 0) := by
  have h := NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (2 : ℝ≥0)⁻¹ < 1 by exact_mod_cast (by norm_num : (2 : ℝ)⁻¹ < 1))
  have hn : Tendsto (fun j : ℕ => T / (2 ^ j : ℝ≥0)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, mul_zero] using (tendsto_const_nhds (x := T)).mul h
  simpa only [Function.comp_def, NNReal.coe_zero] using (NNReal.continuous_coe.tendsto 0).comp hn

private theorem dist_dyadic_left_vertex_le_mesh (T : ℝ≥0) {j k : ℕ} {s : ℝ≥0}
    (hs : s ∈ Ioc ((uniformDyadicGrids T).grid j k) ((uniformDyadicGrids T).grid j (k+1))) :
    dist ((uniformDyadicGrids T).grid j k) s ≤ (↑(T / (2 ^ j : ℝ≥0)) : ℝ) := by
  rw [NNReal.dist_eq, abs_of_nonpos (sub_nonpos.mpr (NNReal.coe_le_coe.mpr hs.1.le))]
  have ht := NNReal.coe_le_coe.mpr hs.2
  change (s : ℝ) ≤ (↑((k+1 : ℕ) * T / (2 ^ j : ℝ≥0)) : ℝ) at ht
  change -(↑((k : ℕ) * T / (2 ^ j : ℝ≥0)) - (s : ℝ)) ≤ _
  push_cast at ht ⊢
  linarith [show ((k : ℝ) + 1) * (T : ℝ) / 2 ^ j =
    (k : ℝ) * (T : ℝ) / 2 ^ j + (T : ℝ) / 2 ^ j by ring]

private theorem measurable_uniformDyadicStep (T : ℝ≥0) (j : ℕ) (f : ℝ≥0 → ℝ) :
    Measurable (uniformDyadicStep T j f) := by
  unfold uniformDyadicStep
  exact Finset.measurable_sum _ fun k _ => measurable_const.indicator measurableSet_Ioc

private theorem timeMeasureHorizon_real_univ' (t : ℝ≥0) :
    (timeMeasureHorizon t).real univ = (t : ℝ) := by
  rw [measureReal_def, timeMeasureHorizon, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, MathFin.ItoIntegralL2.timeMeasure_Ioc]
  simpa only [NNReal.coe_zero, sub_zero] using ENNReal.toReal_ofReal t.coe_nonneg

/-- On a compact set of paths, the Euler coefficient quadratures converge
uniformly, with the same bound for every deterministic cutoff time. -/
theorem uniform_canonicalDyadicCoefficientIntegral_approx
    (T : ℝ≥0) {c : ℝ≥0 → (ι → ℝ) → ℝ}
    (hc : Continuous (Function.uncurry c)) {B : ℝ} (hB : ∀ r y, ‖c r y‖ ≤ B)
    {K : Set (CanonicalPath T (ι → ℝ))} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop, ∀ p ∈ K, ∀ t,
      ‖canonicalDyadicCoefficientIntegral T j c t p - canonicalCoefficientIntegral T c t p‖ < ε := by
  let F (z : ℝ≥0 × CanonicalPath T (ι → ℝ)) := c z.1 (canonicalPathEval T z.1 z.2)
  have hEvalTime : Continuous (canonicalEvalTime T) :=
    (continuous_id.min continuous_const).subtype_mk _
  have hEval : Continuous (fun z : ℝ≥0 × CanonicalPath T (ι → ℝ) =>
      canonicalPathEval T z.1 z.2) :=
    continuous_eval.comp (continuous_snd.prodMk (hEvalTime.comp continuous_fst))
  have hF : Continuous F := hc.comp (continuous_fst.prodMk hEval)
  have hUc : UniformContinuousOn F ((Icc 0 T) ×ˢ K) :=
    (isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hF.continuousOn
  let η := ε / ((T : ℝ) + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨δ, hδ, hδbound⟩ := Metric.uniformContinuousOn_iff.mp hUc η hη
  have hMesh := (uniform_dyadic_mesh_tendsto_zero T).eventually (Iio_mem_nhds hδ)
  filter_upwards [hMesh] with j hj p hp t
  let q := min t T
  let g (r : ℝ≥0) := c r (canonicalPathEval T r p)
  let step := uniformDyadicStep T j g
  have hgm : AEStronglyMeasurable g (timeMeasureHorizon q) :=
    (hF.comp (continuous_id.prodMk continuous_const)).stronglyMeasurable.aestronglyMeasurable
  have hStepMeas : AEStronglyMeasurable step (timeMeasureHorizon q) :=
    (measurable_uniformDyadicStep T j g).aestronglyMeasurable
  have hIn : ∀ᵐ r ∂timeMeasureHorizon q, r ∈ Ioc 0 q := ae_restrict_mem measurableSet_Ioc
  have hStepB : ∀ᵐ r ∂timeMeasureHorizon q, ‖step r‖ ≤ B := by
    filter_upwards [hIn] with r hr
    obtain ⟨k, hk, hc, he⟩ := uniformDyadicStep_eq_coeff g
      (show r ∈ Ioc 0 T from ⟨hr.1, hr.2.trans (min_le_right _ _)⟩) j
    change ‖uniformDyadicStep T j g r‖ ≤ B
    rw [he]
    exact hB _ _
  have hStepI : Integrable step (timeMeasureHorizon q) :=
    (integrable_const B).mono' hStepMeas hStepB
  have hGI : Integrable g (timeMeasureHorizon q) :=
    (integrable_const B).mono' hgm (Eventually.of_forall fun r => hB _ _)
  have hDiffB : ∀ᵐ r ∂timeMeasureHorizon q, ‖step r - g r‖ ≤ η := by
    filter_upwards [hIn] with r hr
    have hrT : r ≤ T := hr.2.trans (min_le_right _ _)
    obtain ⟨k, hk, hcell, he⟩ := uniformDyadicStep_eq_coeff g ⟨hr.1, hrT⟩ j
    have hvT := hcell.1.le.trans hrT
    have hr' : (r, p) ∈ Icc 0 T ×ˢ K := ⟨⟨zero_le, hrT⟩, hp⟩
    have hv' : ((uniformDyadicGrids T).grid j k, p) ∈ Icc 0 T ×ˢ K :=
      ⟨⟨zero_le, hvT⟩, hp⟩
    have hDist : dist ((uniformDyadicGrids T).grid j k, p) (r, p) < δ := by
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
      exact (dist_dyadic_left_vertex_le_mesh T hcell).trans_lt hj
    have hd := (hδbound _ hv' _ hr' hDist).le
    change ‖uniformDyadicStep T j g r - g r‖ ≤ η
    rw [he]
    simpa only [dist_eq_norm, F, g] using hd
  change ‖(∫ r, step r ∂timeMeasureHorizon q) - ∫ r, g r ∂timeMeasureHorizon q‖ < ε
  rw [← integral_sub hStepI hGI]
  have hi := norm_integral_le_of_norm_le_const hDiffB
  rw [timeMeasureHorizon_real_univ'] at hi
  apply hi.trans_lt
  have hq : (q : ℝ) < (T : ℝ) + 1 := by
    have := NNReal.coe_le_coe.mpr (min_le_right t T)
    linarith
  exact (mul_lt_mul_of_pos_left hq hη).trans_eq (div_mul_cancel₀ ε (by positivity))

#print axioms RoughHeston.canonicalDyadicCoefficientIntegral_at_grid_vertex
#print axioms RoughHeston.uniform_canonicalDyadicCoefficientIntegral_approx

end RoughHeston
