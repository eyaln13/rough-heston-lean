import EulerDyadicQuadrature

/-! Right grid endpoints and convergence of canonical Euler observables. -/

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston

open MathFin.ItoIntegralCLM

private theorem dyadic_vertex_above_exists (T : ℝ≥0) (j : ℕ) (t : ℝ≥0) :
    ∃ k : ℕ, min t T ≤ (uniformDyadicGrids T).grid j k :=
  ⟨2 ^ j, (min_le_right t T).trans_eq (uniform_dyadic_terminal_vertex T j).symm⟩

/-- The first grid vertex at or after the requested time, clipped at T. -/
noncomputable def eulerDyadicCeiling (T : ℝ≥0) (j : ℕ) (t : ℝ≥0) : ℕ :=
  Nat.find (dyadic_vertex_above_exists T j t)

theorem eulerDyadicCeiling_spec (T : ℝ≥0) (j : ℕ) (t : ℝ≥0) :
    min t T ≤ (uniformDyadicGrids T).grid j (eulerDyadicCeiling T j t) :=
  Nat.find_spec (dyadic_vertex_above_exists T j t)

theorem eulerDyadicCeiling_le_terminal (T : ℝ≥0) (j : ℕ) (t : ℝ≥0) :
    eulerDyadicCeiling T j t ≤ 2 ^ j :=
  Nat.find_min' _ ((min_le_right t T).trans_eq (uniform_dyadic_terminal_vertex T j).symm)

theorem eulerDyadicCeiling_monotone (T : ℝ≥0) (j : ℕ) :
    Monotone (eulerDyadicCeiling T j) := fun s t hst =>
  Nat.find_min' _ ((min_le_min_right T hst).trans (eulerDyadicCeiling_spec T j t))

theorem uniformDyadicGrid_strictMono {T : ℝ≥0} (hT : 0 < T) (j : ℕ) :
    StrictMono ((uniformDyadicGrids T).grid j) := by
  intro k l hkl
  change (k : ℝ≥0) * T / (2 ^ j : ℝ≥0) < (l : ℝ≥0) * T / (2 ^ j : ℝ≥0)
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right (by exact_mod_cast hkl) hT) (by positivity)

private theorem eulerDyadicCeiling_time_le_horizon (T : ℝ≥0) (j : ℕ) (t : ℝ≥0) :
    (uniformDyadicGrids T).grid j (eulerDyadicCeiling T j t) ≤ T :=
  ((uniformDyadicGrids T).grid j).monotone (eulerDyadicCeiling_le_terminal T j t) |>.trans_eq
    (uniform_dyadic_terminal_vertex T j)

theorem eulerDyadicCeiling_time_dist_le (T : ℝ≥0) (j : ℕ) (t : ℝ≥0) :
    dist ((uniformDyadicGrids T).grid j (eulerDyadicCeiling T j t)) (min t T) ≤
      (↑(T / (2 ^ j : ℝ≥0)) : ℝ) := by
  let g := (uniformDyadicGrids T).grid j
  let k := eulerDyadicCeiling T j t
  have hk : min t T ≤ g k := eulerDyadicCeiling_spec T j t
  change dist (g k) (min t T) ≤ _
  cases he : k with
  | zero =>
    have heq : min t T = g k := hk.antisymm (by rw [he, uniform_dyadic_first_vertex]; exact zero_le)
    have heq' : min t T = g 0 := by simpa only [he] using heq
    rw [heq', dist_self]
    exact NNReal.coe_nonneg _
  | succ d =>
    have hd : d < k := by simp [he]
    have hPrev : g d < min t T := lt_of_not_ge (Nat.find_min (dyadic_vertex_above_exists T j t) hd)
    have hMesh : (g (d+1) : ℝ) - (g d : ℝ) = (↑(T / (2 ^ j : ℝ≥0)) : ℝ) := by
      change (↑((d+1 : ℕ) * T / (2 ^ j : ℝ≥0)) : ℝ) -
        (↑((d : ℕ) * T / (2 ^ j : ℝ≥0)) : ℝ) = _
      push_cast
      ring
    have hk' : min t T ≤ g (d+1) := by simpa only [he] using hk
    rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hk')), ← hMesh]
    exact sub_le_sub_left (NNReal.coe_le_coe.mpr hPrev.le) _

theorem tendsto_eulerDyadicCeiling_time (T t : ℝ≥0) :
    Tendsto (fun j : ℕ => (uniformDyadicGrids T).grid j (eulerDyadicCeiling T j t))
      atTop (𝓝 (min t T)) := by
  have h := NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (2 : ℝ≥0)⁻¹ < 1 by exact_mod_cast (by norm_num : (2 : ℝ)⁻¹ < 1))
  have hMesh : Tendsto (fun j : ℕ => T / (2 ^ j : ℝ≥0)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, mul_zero] using (tendsto_const_nhds (x := T)).mul h
  have hMesh' : Tendsto (fun j : ℕ => (↑(T / (2 ^ j : ℝ≥0)) : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, NNReal.coe_zero] using (NNReal.continuous_coe.tendsto 0).comp hMesh
  exact tendsto_iff_dist_tendsto_zero.2 <|
    squeeze_zero (fun _ => dist_nonneg) (fun j => eulerDyadicCeiling_time_dist_le T j t) hMesh'

private theorem norm_canonicalCoefficientIntegral_sub_le {ι : Type*} [Fintype ι] (T : ℝ≥0)
    {c : ℝ≥0 → (ι → ℝ) → ℝ} (hc : Continuous (Function.uncurry c))
    {B : ℝ} (hB : ∀ r y, ‖c r y‖ ≤ B) {u v : ℝ≥0} (huv : u ≤ v)
    (p : CanonicalPath T (ι → ℝ)) :
    ‖canonicalCoefficientIntegral T c v p - canonicalCoefficientIntegral T c u p‖ ≤
      B * (↑(min v T - min u T : ℝ≥0) : ℝ) := by
  let a := min u T
  let b := min v T
  let f (r : ℝ≥0) := c r (canonicalPathEval T r p)
  let ν := MathFin.ItoIntegralL2.timeMeasure
  have hab : a ≤ b := min_le_min_right T huv
  have hf : StronglyMeasurable f := by
    have hET : Continuous (canonicalEvalTime T) :=
      (continuous_id.min continuous_const).subtype_mk _
    exact (hc.comp (continuous_id.prodMk (p.continuous.comp hET))).stronglyMeasurable
  have hsplit : timeMeasureHorizon b = timeMeasureHorizon a + ν.restrict (Ioc a b) := by
    change ν.restrict (Ioc 0 b) = ν.restrict (Ioc 0 a) + ν.restrict (Ioc a b)
    rw [← Ioc_union_Ioc_eq_Ioc (zero_le : 0 ≤ a) hab,
      Measure.restrict_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc]
  have hm : (ν.restrict (Ioc a b)) univ = ENNReal.ofReal ((b : ℝ) - (a : ℝ)) := by
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, MathFin.ItoIntegralL2.timeMeasure_Ioc]
  letI : IsFiniteMeasure (ν.restrict (Ioc a b)) := ⟨hm.trans_lt ENNReal.ofReal_lt_top⟩
  have hF (τ : Measure ℝ≥0) [IsFiniteMeasure τ] : Integrable f τ :=
    (integrable_const B).mono' hf.aestronglyMeasurable (Eventually.of_forall fun r => hB _ _)
  have hi : ‖∫ r, f r ∂ν.restrict (Ioc a b)‖ ≤ B * ((b : ℝ) - (a : ℝ)) := by
    have hx := norm_integral_le_of_norm_le_const (μ := ν.restrict (Ioc a b))
      (Eventually.of_forall fun r => hB r (canonicalPathEval T r p))
    rwa [measureReal_def, hm, ENNReal.toReal_ofReal (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hab))] at hx
  change ‖(∫ r, f r ∂timeMeasureHorizon b) -
    ∫ r, f r ∂timeMeasureHorizon a‖ ≤ B * (↑(b-a) : ℝ)
  rw [hsplit, integral_add_measure (hF _) (hF _), add_sub_cancel_left, NNReal.coe_sub hab]
  exact hi

/-- Grid drift quadrature at the first endpoint above t converges
uniformly on each compact family of paths to the exact drift integral. -/
theorem uniform_canonicalGridCoefficientSum_ceiling_approx {ι : Type*} [Fintype ι]
    (T t : ℝ≥0) {c : ℝ≥0 → (ι → ℝ) → ℝ} (hc : Continuous (Function.uncurry c))
    {B : ℝ} (hB : ∀ r y, ‖c r y‖ ≤ B)
    {K : Set (CanonicalPath T (ι → ℝ))} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop, ∀ p ∈ K,
      ‖canonicalGridCoefficientSum T ((uniformDyadicGrids T).grid j) c
        (eulerDyadicCeiling T j t) p - canonicalCoefficientIntegral T c t p‖ < ε := by
  let u (j : ℕ) := (uniformDyadicGrids T).grid j (eulerDyadicCeiling T j t)
  have hu := tendsto_eulerDyadicCeiling_time T t
  have hdiff : Tendsto (fun j : ℕ => B * ((u j : ℝ) - (↑(min t T) : ℝ))) atTop (𝓝 0) := by
    have hu' := (NNReal.continuous_coe.tendsto (min t T)).comp hu
    simpa only [Function.comp_def, sub_self, mul_zero] using
      (hu'.sub (tendsto_const_nhds (x := (↑(min t T) : ℝ)))).const_mul B
  filter_upwards [uniform_canonicalDyadicCoefficientIntegral_approx T hc hB hK
      (show 0 < ε/2 by positivity), hdiff.eventually (Iio_mem_nhds (show 0 < ε/2 by positivity))]
    with j hj htime p hp
  rw [← canonicalDyadicCoefficientIntegral_at_grid_vertex T j c
    (eulerDyadicCeiling_le_terminal T j t)]
  have hQ := hj p hp (u j)
  have hS : ‖canonicalCoefficientIntegral T c (u j) p -
      canonicalCoefficientIntegral T c t p‖ < ε/2 := by
    have he : canonicalCoefficientIntegral T c (min t T) p =
        canonicalCoefficientIntegral T c t p := by
      simp only [canonicalCoefficientIntegral, min_assoc, min_self]
    rw [← he]
    have h := norm_canonicalCoefficientIntegral_sub_le T hc hB (eulerDyadicCeiling_spec T j t) p
    dsimp only [u] at htime ⊢
    rw [min_eq_left (eulerDyadicCeiling_time_le_horizon T j t),
      min_eq_left (min_le_right t T), NNReal.coe_sub (eulerDyadicCeiling_spec T j t)] at h
    exact h.trans_lt htime
  have hTri := dist_triangle (canonicalDyadicCoefficientIntegral T j c (u j) p)
    (canonicalCoefficientIntegral T c (u j) p) (canonicalCoefficientIntegral T c t p)
  simp only [dist_eq_norm] at hTri
  exact hTri.trans_lt (by linarith [hQ, hS])

#print axioms RoughHeston.tendsto_eulerDyadicCeiling_time
#print axioms RoughHeston.uniform_canonicalGridCoefficientSum_ceiling_approx

end RoughHeston
