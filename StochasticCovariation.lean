import StochasticProcess
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
Compensated products of two continuous-time grid integral processes.
The same deterministic grid is used for the two sets of weights.
-/

open MeasureTheory Filter Set
open scoped BigOperators MeasureTheory ProbabilityTheory Topology NNReal ENNReal

namespace RoughHeston

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

section Grid

variable [LinearOrder ι]

/-- At the end of the last cell the grid sum becomes constant. -/
theorem gridIntegralProcess_eq_at_end (grid : ℕ →o ι) (a : ℕ → Ω → ℝ)
    (X : ι → Ω → ℝ) (n : ℕ) {t : ι} (ht : grid n ≤ t) :
    gridIntegralProcess grid a X n t = gridIntegralProcess grid a X n (grid n) :=
  (gridIntegralProcess_terminal grid a X n ht).trans
    (gridIntegralProcess_terminal grid a X n le_rfl).symm

private theorem stochasticStep_mul_on_previous_cells
    (grid : ℕ →o ι) (a : ℕ → Ω → ℝ) (X : ι → Ω → ℝ)
    (n : ℕ) (b : Ω → ℝ) (Y : ι → Ω → ℝ) :
    (fun t => gridIntegralProcess grid a X n t *
      stochasticStep (grid n) (grid (n + 1)) b Y t) =
    stochasticStep (grid n) (grid (n + 1))
      (gridIntegralProcess grid a X n (grid n) * b) Y := by
  funext t
  by_cases ht : t ≤ grid n
  · rw [stochasticStep_before ht (grid.monotone n.le_succ),
      stochasticStep_before ht (grid.monotone n.le_succ), mul_zero]
  · rw [gridIntegralProcess_eq_at_end grid a X n (le_of_not_ge ht)]
    simp only [stochasticStep, mul_assoc]

/-- On a single cell the product of the two weighted increments,
compensated by the weighted cross-bracket increment, is a martingale. -/
theorem stochasticStep_compensated_product [IsFiniteMeasure μ]
    {𝒢 : Filtration ι m} {X Y C : ι → Ω → ℝ} {u v : ι}
    (huv : u ≤ v) (hX : Martingale X 𝒢 μ) (hY : Martingale Y 𝒢 μ)
    (hXY : Martingale (fun t => X t * Y t - C t) 𝒢 μ)
    (hX₂ : ∀ t, MemLp (X t) 2 μ) (hY₂ : ∀ t, MemLp (Y t) 2 μ)
    {a b : Ω → ℝ} (ha : StronglyMeasurable[𝒢 u] a) (hb : StronglyMeasurable[𝒢 u] b)
    (haTop : MemLp a ⊤ μ) (hbTop : MemLp b ⊤ μ) :
    Martingale (fun t => stochasticStep u v a X t * stochasticStep u v b Y t -
      stochasticStep u v (a * b) C t) 𝒢 μ := by
  let P := fun t => X t * Y t - C t
  let c := a * b
  have hc := ha.mul hb
  have hcTop : MemLp c ⊤ μ := haTop.mul hbTop
  have hP : Martingale (stochasticStep u v c P) 𝒢 μ :=
    stochasticStep_martingale_of_integrable huv hXY hc (fun s t =>
      (hcTop.mul (memLp_one_iff_integrable.mpr ((hXY.integrable t).sub (hXY.integrable s))) :
        MemLp (c * (P t - P s)) 1 μ).integrable le_rfl)
  have hcx : MemLp (c * X u) 2 μ := hcTop.mul (hX₂ u)
  have hcy : MemLp (c * Y u) 2 μ := hcTop.mul (hY₂ u)
  have hcyX : Martingale (stochasticStep u v (c * Y u) X) 𝒢 μ :=
    stochasticStep_martingale_of_integrable huv hX (hc.mul (hY.stronglyMeasurable u))
      (fun s t => (hcy.mul ((hX₂ t).sub (hX₂ s)) :
        MemLp ((c * Y u) * (X t - X s)) 1 μ).integrable le_rfl)
  have hcxY : Martingale (stochasticStep u v (c * X u) Y) 𝒢 μ :=
    stochasticStep_martingale_of_integrable huv hY (hc.mul (hX.stronglyMeasurable u))
      (fun s t => (hcx.mul ((hY₂ t).sub (hY₂ s)) :
        MemLp ((c * X u) * (Y t - Y s)) 1 μ).integrable le_rfl)
  convert (hP.sub hcyX).sub hcxY using 1
  funext t
  by_cases ht : t ≤ u
  · simp [stochasticStep_before ht huv]
  · have hut : u ≤ t := le_of_not_ge ht
    ext ω
    simp only [stochasticStep, min_eq_right hut, P, c, Pi.sub_apply, Pi.mul_apply]
    ring

/-- The compensator as a process, with the bracket increments stopped at
the observation time on each cell. -/
def gridCompensatorProcess (grid : ℕ →o ι) (a b : ℕ → Ω → ℝ)
    (C : ι → Ω → ℝ) (n : ℕ) : ι → Ω → ℝ :=
  gridIntegralProcess grid (fun k => a k * b k) C n

/-- Compensated-product formula for continuous-time simple integrals,
valid at all times in the original filtration. -/
theorem gridIntegralProcess_compensated_product [IsFiniteMeasure μ]
    {𝒢 : Filtration ι m} (grid : ℕ →o ι) {X Y C : ι → Ω → ℝ}
    (hX : Martingale X 𝒢 μ) (hY : Martingale Y 𝒢 μ)
    (hXY : Martingale (fun t => X t * Y t - C t) 𝒢 μ)
    (hX₂ : ∀ t, MemLp (X t) 2 μ) (hY₂ : ∀ t, MemLp (Y t) 2 μ)
    {a b : ℕ → Ω → ℝ}
    (ha : ∀ k, StronglyMeasurable[𝒢 (grid k)] (a k))
    (hb : ∀ k, StronglyMeasurable[𝒢 (grid k)] (b k))
    (haTop : ∀ k, MemLp (a k) ⊤ μ) (hbTop : ∀ k, MemLp (b k) ⊤ μ) (n : ℕ) :
    Martingale (fun t => gridIntegralProcess grid a X n t * gridIntegralProcess grid b Y n t -
      gridCompensatorProcess grid a b C n t) 𝒢 μ := by
  induction n with
  | zero =>
    simp only [gridCompensatorProcess, gridIntegralProcess_zero, Pi.zero_apply, mul_zero, sub_zero]
    change Martingale (0 : ι → Ω → ℝ) 𝒢 μ
    exact martingale_zero ℝ 𝒢 μ
  | succ n ih =>
    let u := grid n
    let v := grid (n + 1)
    let I := gridIntegralProcess grid a X n
    let J := gridIntegralProcess grid b Y n
    let P := gridCompensatorProcess grid a b C n
    let S := stochasticStep u v (a n) X
    let R := stochasticStep u v (b n) Y
    let D := stochasticStep u v (a n * b n) C
    have huv : u ≤ v := grid.monotone n.le_succ
    have hIS : Martingale (fun t => I t * R t) 𝒢 μ := by
      rw [stochasticStep_mul_on_previous_cells grid a X n (b n) Y]
      have hI := gridIntegralProcess_martingale grid hX hX₂ ha haTop n
      have hI₂ := gridIntegralProcess_memLp_two grid hX₂ haTop n u
      have hc : MemLp (I u * b n) 2 μ := hI₂.mul (hbTop n)
      exact stochasticStep_martingale_of_integrable huv hY
        ((hI.stronglyMeasurable u).mul (hb n))
        (fun s t => (hc.mul ((hY₂ t).sub (hY₂ s)) :
          MemLp ((I u * b n) * (Y t - Y s)) 1 μ).integrable le_rfl)
    have hJR : Martingale (fun t => J t * S t) 𝒢 μ := by
      rw [stochasticStep_mul_on_previous_cells grid b Y n (a n) X]
      have hJ := gridIntegralProcess_martingale grid hY hY₂ hb hbTop n
      have hJ₂ := gridIntegralProcess_memLp_two grid hY₂ hbTop n u
      have hc : MemLp (J u * a n) 2 μ := hJ₂.mul (haTop n)
      exact stochasticStep_martingale_of_integrable huv hX
        ((hJ.stronglyMeasurable u).mul (ha n))
        (fun s t => (hc.mul ((hX₂ t).sub (hX₂ s)) :
          MemLp ((J u * a n) * (X t - X s)) 1 μ).integrable le_rfl)
    have hSD : Martingale (fun t => S t * R t - D t) 𝒢 μ :=
      stochasticStep_compensated_product huv hX hY hXY hX₂ hY₂
        (ha n) (hb n) (haTop n) (hbTop n)
    simp only [gridCompensatorProcess, gridIntegralProcess_succ, Pi.add_apply]
    change Martingale (fun t => (I t + S t) * (J t + R t) - (P t + D t)) 𝒢 μ
    convert ((ih.add hIS).add hJR).add hSD using 1
    ext t ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring

end Grid

/-- The compensator inherits adaptedness from the compensated product and
the two martingales. -/
theorem adapted_compensator_of_compensated_product [Preorder ι]
    {𝒢 : Filtration ι m} {X Y C : ι → Ω → ℝ}
    (hX : StronglyAdapted 𝒢 X) (hY : StronglyAdapted 𝒢 Y)
    (hXY : Martingale (fun t => X t * Y t - C t) 𝒢 μ) :
    StronglyAdapted 𝒢 C := by
  intro t
  have hf := ((hX t).mul (hY t)).sub (hXY.stronglyMeasurable t)
  rwa [sub_sub_cancel] at hf


section Density

/-- Bound the difference between an integral with a time-varying weight
and the corresponding weighted cell integrals. -/
theorem grid_density_error {x : ℕ → ℝ} (hx : Monotone x) (n : ℕ)
    {v w : ℝ → ℝ} (hv : IntervalIntegrable v volume (x 0) (x n))
    (hwv : IntervalIntegrable (fun s => w s * v s) volume (x 0) (x n))
    {a : ℕ → ℝ} {δ : ℝ}
    (hclose : ∀ k < n, ∀ s ∈ Ioc (x k) (x (k + 1)), |a k - w s| ≤ δ) :
    |(∑ k ∈ Finset.range n, a k * (∫ s in (x k)..(x (k + 1)), v s)) -
        (∫ s in (x 0)..(x n), w s * v s)| ≤ δ * (∫ s in (x 0)..(x n), |v s|) := by
  have hsub (k : ℕ) (hk : k < n) :
      uIcc (x k) (x (k + 1)) ⊆ uIcc (x 0) (x n) := by
    rw [uIcc_of_le (hx k.le_succ), uIcc_of_le (hx zero_le)]
    exact Icc_subset_Icc (hx zero_le) (hx hk)
  rw [← intervalIntegral.sum_integral_adjacent_intervals (fun k hk => hwv.mono_set (hsub k hk)),
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ k ∈ Finset.range n, δ * (∫ s in (x k)..(x (k + 1)), |v s|) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have hle := hx k.le_succ
      have hi := hv.mono_set (hsub k hk')
      have hi' := hwv.mono_set (hsub k hk')
      have hf := (hi.const_mul (a k)).sub hi'
      have hg := hi.abs.const_mul δ
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
        (hi.const_mul _) hi']
      refine (intervalIntegral.abs_integral_le_integral_abs hle).trans ?_
      rw [← intervalIntegral.integral_const_mul]
      rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle]
      apply setIntegral_mono_on
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp hf.abs)
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp hg) measurableSet_Ioc
      intro s hs
      change |a k * v s - w s * v s| ≤ δ * |v s|
      rw [← sub_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right (hclose k hk' s hs) (abs_nonneg _)
    _ = _ := by
      rw [← Finset.mul_sum, intervalIntegral.sum_integral_adjacent_intervals
        (fun k hk => hv.abs.mono_set (hsub k hk))]

/-- The (k)-th endpoint of the equal dyadic division, stopped at (t). -/
private noncomputable def clampedDyadic (T t : ℝ≥0) (n k : ℕ) : ℝ :=
  min t ((uniformDyadicGrids T).grid n k) |>.toReal

private theorem clampedDyadic_mono (T t : ℝ≥0) (n : ℕ) :
    Monotone (clampedDyadic T t n) := by
  intro k l hkl
  exact_mod_cast min_le_min_left t (((uniformDyadicGrids T).grid n).monotone hkl)

private theorem uniformDyadicGrids_add_one (T : ℝ≥0) (n k : ℕ) :
    (uniformDyadicGrids T).grid n (k + 1) =
      (uniformDyadicGrids T).grid n k + T / (2 ^ n : ℝ≥0) := by
  change ((k + 1 : ℕ) : ℝ≥0) * T / (2 ^ n : ℝ≥0) =
    (k : ℝ≥0) * T / (2 ^ n : ℝ≥0) + T / (2 ^ n : ℝ≥0)
  push_cast
  rw [add_mul, one_mul, add_div]

private theorem dyadic_cell_contains {T t : ℝ≥0} {n k : ℕ}
    {s : ℝ} (hs : s ∈ Ioc (clampedDyadic T t n k) (clampedDyadic T t n (k + 1))) :
    let v := ((uniformDyadicGrids T).grid n k : ℝ)
    v ≤ s ∧ s ≤ v + (T / (2 ^ n : ℝ≥0) : ℝ≥0) := by
  let G := uniformDyadicGrids T
  have hsleft : ¬ t ≤ G.grid n k := by
    intro h
    have ht : t ≤ G.grid n (k + 1) := h.trans ((G.grid n).monotone k.le_succ)
    exact (not_lt_of_ge hs.2) (by simpa [clampedDyadic, G, min_eq_left h, min_eq_left ht] using hs.1)
  have hlo : (G.grid n k : ℝ) < s := by
    simpa [clampedDyadic, G, min_eq_right (le_of_not_ge hsleft)] using hs.1
  have hhi : s ≤ (G.grid n (k + 1) : ℝ) :=
    hs.2.trans (by exact_mod_cast min_le_right t (G.grid n (k + 1)))
  exact ⟨hlo.le, by simpa only [G, uniformDyadicGrids_add_one, NNReal.coe_add] using hhi⟩


private theorem clampedDyadic_zero (T t : ℝ≥0) (n : ℕ) :
    clampedDyadic T t n 0 = 0 := by simp [clampedDyadic]

private theorem clampedDyadic_end (T t : ℝ≥0) (n : ℕ) :
    clampedDyadic T t n (2 ^ n) = (min t T : ℝ≥0) := by simp [clampedDyadic]

private theorem clampedDyadic_draw (T t : ℝ≥0) {n k : ℕ} (hk : k ≤ 2 ^ n) :
    clampedDyadic T t n k ≤ (min t T : ℝ≥0) := by
  simpa only [clampedDyadic_end] using clampedDyadic_mono T t n hk

private theorem clampedDyadic_nonneg (T t : ℝ≥0) (n k : ℕ) : 0 ≤ clampedDyadic T t n k :=
  NNReal.coe_nonneg _

/-- Pathwise approximation of a weighted integral of an integrable
bracket density. The weight is continuous on the compact interval. -/
theorem dyadic_density_tendsto (T t : ℝ≥0) {w : ℝ≥0 → ℝ} {v : ℝ → ℝ}
    (hw : ContinuousOn w (Icc 0 T))
    (hv : IntervalIntegrable v volume 0 (T : ℝ))
    (hwv : IntervalIntegrable (fun s => w s.toNNReal * v s) volume 0 (T : ℝ)) :
    Tendsto (fun n => ∑ k ∈ Finset.range (2 ^ n),
      w ((uniformDyadicGrids T).grid n k) *
        ∫ s in (clampedDyadic T t n k)..(clampedDyadic T t n (k + 1)), v s)
      atTop (𝓝 (∫ s in (0 : ℝ)..((min t T : ℝ≥0) : ℝ), w s.toNNReal * v s)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let C := ∫ s in (0 : ℝ)..(T : ℝ), |v s|
  have hC : 0 ≤ C := intervalIntegral.integral_nonneg_of_forall (NNReal.coe_nonneg _) (fun _ => abs_nonneg _)
  let δ := ε / (2 * (C + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδC : δ * C < ε := by
    dsimp [δ]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (C + 1))).2
    nlinarith
  obtain ⟨η, hη, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hw) δ hδ
  have hm : Tendsto (fun n : ℕ => (T : ℝ) / 2 ^ n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, mul_zero] using
      (tendsto_const_nhds (x := (T : ℝ))).mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (2 : ℝ)⁻¹) (by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hm.eventually_lt_const hη)
  refine ⟨N, fun n hn => ?_⟩
  let x := clampedDyadic T t n
  let G := uniformDyadicGrids T
  have hsub : uIcc (x 0) (x (2 ^ n)) ⊆ uIcc (0 : ℝ) T := by
    change uIcc (clampedDyadic T t n 0) (clampedDyadic T t n (2 ^ n)) ⊆ uIcc (0 : ℝ) T
    rw [clampedDyadic_zero, clampedDyadic_end, uIcc_of_le (NNReal.coe_nonneg _),
      uIcc_of_le (NNReal.coe_nonneg _)]
    exact Icc_subset_Icc le_rfl (by exact_mod_cast min_le_right t T)
  have hclose (k : ℕ) (hk : k < 2 ^ n) (s : ℝ) (hs : s ∈ Ioc (x k) (x (k + 1))) :
      |w (G.grid n k) - w s.toNNReal| ≤ δ := by
    have htT : s ≤ T := hs.2.trans ((clampedDyadic_draw T t hk).trans
      (by exact_mod_cast min_le_right t T))
    obtain ⟨hlo, hhi⟩ := dyadic_cell_contains hs
    have hs0 : 0 ≤ s := (NNReal.coe_nonneg (G.grid n k)).trans hlo
    have hxT : G.grid n k ≤ T := by simpa [G] using (G.grid n).monotone hk.le
    have hc : (s.toNNReal : ℝ) ≤ (T : ℝ) := by rwa [Real.coe_toNNReal s hs0]
    have hst : s.toNNReal ≤ T := by exact_mod_cast hc
    have hd : dist (G.grid n k) s.toNNReal < η := by
      change dist (G.grid n k : ℝ) (s.toNNReal : ℝ) < η
      rw [Real.dist_eq, Real.coe_toNNReal s hs0, abs_of_nonpos (sub_nonpos.mpr hlo)]
      have hle : -(↑(G.grid n k) - s) ≤ (T : ℝ) / 2 ^ n := by
        have hhi' : s ≤ (G.grid n k : ℝ) + (T : ℝ) / 2 ^ n := by
          simpa only [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat] using hhi
        linarith
      exact hle.trans_lt (hN n hn)
    have hw' := hmod (G.grid n k) ⟨zero_le, hxT⟩ s.toNNReal ⟨zero_le, hst⟩ hd
    exact le_of_lt (by simpa only [Real.dist_eq] using hw')
  have herr := grid_density_error (clampedDyadic_mono T t n) (2 ^ n)
    (hv.mono_set hsub) (hwv.mono_set hsub) hclose
  rw [clampedDyadic_zero, clampedDyadic_end] at herr
  have hvol : (∫ s in (0 : ℝ)..((min t T : ℝ≥0) : ℝ), |v s|) ≤ C :=
    intervalIntegral.integral_mono_interval le_rfl (NNReal.coe_nonneg _)
      (by exact_mod_cast min_le_right t T) (Eventually.of_forall fun _ => abs_nonneg _) hv.abs
  rw [Real.dist_eq]
  exact herr.trans_lt ((mul_le_mul_of_nonneg_left hvol hδ.le).trans_lt hδC)


private theorem clampedDyadic_interval_subset (T t : ℝ≥0) (n : ℕ) :
    uIcc (clampedDyadic T t n 0) (clampedDyadic T t n (2 ^ n)) ⊆ uIcc (0 : ℝ) T := by
  rw [clampedDyadic_zero, clampedDyadic_end, uIcc_of_le (NNReal.coe_nonneg _),
    uIcc_of_le (NNReal.coe_nonneg _)]
  exact Icc_subset_Icc le_rfl (by exact_mod_cast min_le_right t T)

private theorem dyadic_grid_from_density (T t : ℝ≥0) (n : ℕ)
    {c w : ℝ≥0 → ℝ} {v : ℝ → ℝ}
    (hC : ∀ k ≤ 2 ^ n, c (min t ((uniformDyadicGrids T).grid n k)) =
      ∫ s in (0 : ℝ)..(clampedDyadic T t n k), v s)
    (hv : IntervalIntegrable v volume 0 (T : ℝ)) :
    ∑ k ∈ Finset.range (2 ^ n), w ((uniformDyadicGrids T).grid n k) *
        (c (min t ((uniformDyadicGrids T).grid n (k + 1))) -
          c (min t ((uniformDyadicGrids T).grid n k))) =
      ∑ k ∈ Finset.range (2 ^ n), w ((uniformDyadicGrids T).grid n k) *
        ∫ s in (clampedDyadic T t n k)..(clampedDyadic T t n (k + 1)), v s := by
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  let G := uniformDyadicGrids T
  have ht (j : ℕ) (hj : j ≤ 2 ^ n) : min t (G.grid n j) ≤ T :=
    (min_le_right _ _).trans (by simpa [G] using (G.grid n).monotone hj)
  have ha := ht k (Finset.mem_range.mp hk).le
  have hb := ht (k + 1) (Finset.mem_range.mp hk)
  have hint (u : ℝ≥0) (hu : u ≤ T) : IntervalIntegrable v volume (0 : ℝ) u :=
    hv.mono_set (by
      rw [uIcc_of_le (NNReal.coe_nonneg u), uIcc_of_le (NNReal.coe_nonneg T)]
      exact Icc_subset_Icc le_rfl (by exact_mod_cast hu))
  rw [hC k (Finset.mem_range.mp hk).le, hC (k + 1) (Finset.mem_range.mp hk)]
  exact intervalIntegral.integral_interval_sub_left (hint _ hb) (hint _ ha)

private theorem dyadic_density_error_of_bounded (T t : ℝ≥0) (n : ℕ)
    {w : ℝ≥0 → ℝ} {v : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hw : ∀ u ≤ T, |w u| ≤ A)
    (hv : IntervalIntegrable v volume (0 : ℝ) T)
    (hwv : IntervalIntegrable (fun s => w s.toNNReal * v s) volume (0 : ℝ) T) :
    |(∑ k ∈ Finset.range (2 ^ n), w ((uniformDyadicGrids T).grid n k) *
        ∫ s in (clampedDyadic T t n k)..(clampedDyadic T t n (k + 1)), v s) -
      (∫ s in (0 : ℝ)..((min t T : ℝ≥0) : ℝ), w s.toNNReal * v s)| ≤
      2 * A * (∫ s in (0 : ℝ)..(T : ℝ), |v s|) := by
  let G := uniformDyadicGrids T
  have hsub := clampedDyadic_interval_subset T t n
  have herr := grid_density_error (w := fun s => w s.toNNReal) (clampedDyadic_mono T t n) (2 ^ n)
    (hv.mono_set hsub) (hwv.mono_set hsub) (δ := 2 * A) (a := fun k => w (G.grid n k)) ?_
  · rw [clampedDyadic_zero, clampedDyadic_end] at herr
    refine herr.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact intervalIntegral.integral_mono_interval le_rfl (NNReal.coe_nonneg _)
      (by exact_mod_cast min_le_right t T) (Eventually.of_forall fun _ => abs_nonneg _) hv.abs
  · intro k hk s hs
    have htT : s ≤ T := hs.2.trans ((clampedDyadic_draw T t hk).trans
      (by exact_mod_cast min_le_right t T))
    have hco : (s.toNNReal : ℝ) ≤ (T : ℝ) := by
      rwa [Real.coe_toNNReal s ((clampedDyadic_nonneg T t n k).trans hs.1.le)]
    have hxT : G.grid n k ≤ T := by simpa [G] using (G.grid n).monotone hk.le
    calc
      |w (G.grid n k) - w s.toNNReal| ≤ |w (G.grid n k)| + |w s.toNNReal| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le (w (G.grid n k)) 0 (w s.toNNReal)
      _ ≤ 2 * A := by
        have h₁ := hw _ hxT
        have h₂ := hw _ (by exact_mod_cast hco : s.toNNReal ≤ T)
        linarith

/-- Convergence of the grid compensators in L¹. The limit has an
adapted representative and agrees almost surely at each time with the
integral of the weighted bracket density. -/
theorem dyadic_compensator_density_L1 [IsFiniteMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} (T : ℝ≥0) {C W : ℝ≥0 → Ω → ℝ}
    {D : ℝ → Ω → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hC : ∀ t ≤ T, C t =ᵐ[μ] fun ω => ∫ s in (0 : ℝ)..(t : ℝ), D s ω)
    (hcts : ∀ᵐ ω ∂μ, ContinuousOn (fun s => W s ω) (Icc 0 T))
    (hbound : ∀ᵐ ω ∂μ, ∀ t ≤ T, |W t ω| ≤ A)
    (hD : ∀ᵐ ω ∂μ, IntervalIntegrable (fun s => D s ω) volume (0 : ℝ) T)
    (hWD : ∀ᵐ ω ∂μ, IntervalIntegrable (fun s => W s.toNNReal ω * D s ω) volume (0 : ℝ) T)
    (hDint : Integrable (fun ω => ∫ s in (0 : ℝ)..(T : ℝ), |D s ω|) μ) :
    let G := uniformDyadicGrids T
    let Cn := fun n => gridIntegralProcess (G.grid n) (fun k => W (G.grid n k)) C (2 ^ n)
    (∀ n, StronglyAdapted 𝒢 (Cn n)) →
    ∃ Cw : ℝ≥0 → Ω → ℝ, StronglyAdapted 𝒢 Cw ∧ (∀ t, Integrable (Cw t) μ) ∧
      (∀ n t, Integrable (Cn n t) μ) ∧
      (∀ t, Cw t =ᵐ[μ] fun ω => ∫ s in (0 : ℝ)..((min t T : ℝ≥0) : ℝ),
        W s.toNNReal ω * D s ω) ∧
      ∀ t, Tendsto (fun n => eLpNorm (Cn n t - Cw t) 1 μ) atTop (𝓝 0) := by
  dsimp only
  let G := uniformDyadicGrids T
  let Cn := fun n => gridIntegralProcess (G.grid n) (fun k => W (G.grid n k)) C (2 ^ n)
  intro hCn
  let raw (t : ℝ≥0) (ω : Ω) := ∫ s in (0 : ℝ)..((min t T : ℝ≥0) : ℝ), W s.toNNReal ω * D s ω
  let mass (ω : Ω) := ∫ s in (0 : ℝ)..(T : ℝ), |D s ω|
  let Cw (t : ℝ≥0) (ω : Ω) := limUnder atTop fun n => Cn n t ω
  have hCw : StronglyAdapted 𝒢 Cw := by
    intro t
    let : MeasurableSpace Ω := 𝒢 t
    exact StronglyMeasurable.limUnder (l := atTop) (fun n => hCn n t)
  have hgrid (t : ℝ≥0) :
      ∀ᵐ ω ∂μ, ∀ n, Cn n t ω =
        ∑ k ∈ Finset.range (2 ^ n), W (G.grid n k) ω *
          ∫ s in (clampedDyadic T t n k)..(clampedDyadic T t n (k + 1)), D s ω := by
    have hvertices : ∀ᵐ ω ∂μ, ∀ n k, k ≤ 2 ^ n →
        C (min t (G.grid n k)) ω = ∫ s in (0 : ℝ)..(clampedDyadic T t n k), D s ω := by
      refine ae_all_iff.mpr fun n => ae_all_iff.mpr fun k => ?_
      by_cases hk : k ≤ 2 ^ n
      · have ht : min t (G.grid n k) ≤ T := (min_le_right _ _).trans
          (by simpa [G] using (G.grid n).monotone hk)
        exact (hC _ ht).mono (fun _ h _ => h)
      · exact Eventually.of_forall fun _ h => (hk h).elim
    filter_upwards [hvertices, hD] with ω hCω hDω n
    simp only [Cn, gridIntegralProcess, Finset.sum_apply, stochasticStep, Pi.mul_apply, Pi.sub_apply]
    exact dyadic_grid_from_density T t n (c := fun u => C u ω) (w := fun u => W u ω) (hCω n) hDω
  have hpath (t : ℝ≥0) : ∀ᵐ ω ∂μ, Tendsto (fun n => Cn n t ω) atTop (𝓝 (raw t ω)) := by
    filter_upwards [hgrid t, hcts, hD, hWD] with ω hgr hw hv hwv
    have hh := dyadic_density_tendsto T t hw hv hwv
    exact hh.congr' (Eventually.of_forall (fun n => (hgr n).symm))
  have hraw (t : ℝ≥0) : Cw t =ᵐ[μ] raw t :=
    (hpath t).mono (fun _ hω => hω.limUnder_eq)
  have hrawbound (t : ℝ≥0) : ∀ᵐ ω ∂μ, |raw t ω| ≤ A * mass ω := by
    filter_upwards [hbound, hD, hWD] with ω hω hv hwv
    let sT : ℝ := (min t T : ℝ≥0).toReal
    have h0 : 0 ≤ sT := NNReal.coe_nonneg _
    have hT : sT ≤ (T : ℝ) := by exact_mod_cast min_le_right t T
    have hsub : uIcc (0 : ℝ) sT ⊆ uIcc (0 : ℝ) T := by
      rw [uIcc_of_le h0, uIcc_of_le (NNReal.coe_nonneg _)]
      exact Icc_subset_Icc le_rfl hT
    have hi := hwv.mono_set hsub
    have hj := (hv.abs.mono_set hsub).const_mul A
    refine (intervalIntegral.abs_integral_le_integral_abs h0).trans ?_
    calc
      _ ≤ ∫ s in (0 : ℝ)..sT, A * |D s ω| := by
        rw [intervalIntegral.integral_of_le h0, intervalIntegral.integral_of_le h0]
        apply setIntegral_mono_on hi.abs.1 hj.1 measurableSet_Ioc
        intro s hs
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right
          (hω _ (by
            have hr : (s.toNNReal : ℝ) ≤ (T : ℝ) := by
              rw [Real.coe_toNNReal s hs.1.le]
              exact hs.2.trans hT
            exact_mod_cast hr)) (abs_nonneg _)
      _ ≤ _ := by
        rw [intervalIntegral.integral_const_mul]
        exact mul_le_mul_of_nonneg_left
          (intervalIntegral.integral_mono_interval le_rfl h0 hT
            (Eventually.of_forall fun _ => abs_nonneg _) hv.abs) hA
  have herror (n : ℕ) (t : ℝ≥0) : ∀ᵐ ω ∂μ, |(Cn n t - Cw t) ω| ≤ (2 * A) * mass ω := by
    filter_upwards [hgrid t, hraw t, hbound, hD, hWD] with ω hg hr hb hv hwv
    rw [Pi.sub_apply, hr, hg n]
    exact dyadic_density_error_of_bounded T t n hA hb hv hwv
  have hcint (t : ℝ≥0) : Integrable (Cw t) μ := by
    refine (hDint.const_mul A).mono' ((hCw t).mono (𝒢.le t)).aestronglyMeasurable ?_
    filter_upwards [hraw t, hrawbound t] with ω he hb
    simpa only [Real.norm_eq_abs, he] using hb
  have hdiff (n : ℕ) (t : ℝ≥0) : Integrable (Cn n t - Cw t) μ := by
    refine (hDint.const_mul (2 * A)).mono'
      ((((hCn n t).sub (hCw t)).mono (𝒢.le t)).aestronglyMeasurable) ?_
    simpa only [Real.norm_eq_abs] using herror n t
  have hnint (n : ℕ) (t : ℝ≥0) : Integrable (Cn n t) μ := by
    simpa only [sub_add_cancel] using (hdiff n t).add (hcint t)
  refine ⟨Cw, hCw, hcint, hnint, hraw, fun t => ?_⟩
  have hp : ∀ᵐ ω ∂μ, Tendsto (fun n => ‖(Cn n t - Cw t) ω‖) atTop (𝓝 ((0 : Ω → ℝ) ω)) := by
    filter_upwards [hpath t, hraw t] with ω hω he
    simpa only [Pi.sub_apply, Pi.zero_apply, he, sub_self, norm_zero] using
      (hω.sub (tendsto_const_nhds (x := raw t ω))).norm
  have hconv := tendsto_integral_of_dominated_convergence (fun ω => (2 * A) * mass ω)
    (fun n => (hdiff n t).norm.aestronglyMeasurable) (hDint.const_mul (2 * A))
    (fun n => by simpa only [Real.norm_eq_abs, abs_abs] using herror n t) hp
  have heq (n : ℕ) : eLpNorm (Cn n t - Cw t) 1 μ =
      ENNReal.ofReal (∫ ω, ‖(Cn n t - Cw t) ω‖ ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm (hdiff n t).aestronglyMeasurable,
      ofReal_integral_norm_eq_lintegral_enorm (hdiff n t)]
  simpa only [Function.comp_def, ← heq, Pi.zero_apply, integral_zero, ENNReal.ofReal_zero]
    using (ENNReal.continuous_ofReal.tendsto _).comp hconv


/-- The compensated product of two continuous stochastic integrals.
The integrals are the timewise L² limits of their dyadic sums on
`[0,T]`. The resulting martingale and compensator are stopped at `T`. -/
theorem continuous_integrals_compensated_product [IsFiniteMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} (T : ℝ≥0)
    {X Y C H G I J : ℝ≥0 → Ω → ℝ} {D : ℝ → Ω → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hX : Martingale X 𝒢 μ) (hY : Martingale Y 𝒢 μ)
    (hXY : Martingale (fun t => X t * Y t - C t) 𝒢 μ)
    (hX₂ : ∀ t, MemLp (X t) 2 μ) (hY₂ : ∀ t, MemLp (Y t) 2 μ)
    (hH : StronglyAdapted 𝒢 H) (hG : StronglyAdapted 𝒢 G)
    (hHtop : ∀ t, MemLp (H t) ⊤ μ) (hGtop : ∀ t, MemLp (G t) ⊤ μ)
    (hI : StronglyAdapted 𝒢 I) (hJ : StronglyAdapted 𝒢 J)
    (hI₂ : ∀ t, MemLp (I t) 2 μ) (hJ₂ : ∀ t, MemLp (J t) 2 μ)
    (hC : ∀ t ≤ T, C t =ᵐ[μ] fun ω => ∫ s in (0 : ℝ)..(t : ℝ), D s ω)
    (hcts : ∀ᵐ ω ∂μ, ContinuousOn (fun s => H s ω * G s ω) (Icc 0 T))
    (hbound : ∀ᵐ ω ∂μ, ∀ t ≤ T, |H t ω * G t ω| ≤ A)
    (hD : ∀ᵐ ω ∂μ, IntervalIntegrable (fun s => D s ω) volume (0 : ℝ) T)
    (hHD : ∀ᵐ ω ∂μ, IntervalIntegrable
      (fun s => H s.toNNReal ω * G s.toNNReal ω * D s ω) volume (0 : ℝ) T)
    (hDint : Integrable (fun ω => ∫ s in (0 : ℝ)..(T : ℝ), |D s ω|) μ)
    (hIconv : ∀ t ≤ T, Tendsto (fun n => eLpNorm
      (gridIntegralProcess ((uniformDyadicGrids T).grid n)
        (fun k => H ((uniformDyadicGrids T).grid n k)) X (2 ^ n) t - I t) 2 μ) atTop (𝓝 0))
    (hJconv : ∀ t ≤ T, Tendsto (fun n => eLpNorm
      (gridIntegralProcess ((uniformDyadicGrids T).grid n)
        (fun k => G ((uniformDyadicGrids T).grid n k)) Y (2 ^ n) t - J t) 2 μ) atTop (𝓝 0)) :
    ∃ Cw : ℝ≥0 → Ω → ℝ,
      (∀ t, Cw t =ᵐ[μ] fun ω => ∫ s in (0 : ℝ)..((min t T : ℝ≥0) : ℝ),
        H s.toNNReal ω * G s.toNNReal ω * D s ω) ∧
      Martingale (fun t => I (min t T) * J (min t T) - Cw t) 𝒢 μ := by
  let P := uniformDyadicGrids T
  let a := fun n k => H (P.grid n k)
  let b := fun n k => G (P.grid n k)
  let In := fun n => gridIntegralProcess (P.grid n) (a n) X (2 ^ n)
  let Jn := fun n => gridIntegralProcess (P.grid n) (b n) Y (2 ^ n)
  let Cn := fun n => gridCompensatorProcess (P.grid n) (a n) (b n) C (2 ^ n)
  have hm (n : ℕ) : Martingale (fun t => In n t * Jn n t - Cn n t) 𝒢 μ :=
    gridIntegralProcess_compensated_product (P.grid n) hX hY hXY hX₂ hY₂
      (fun k => hH _) (fun k => hG _) (fun k => hHtop _) (fun k => hGtop _) (2 ^ n)
  have hIn (n : ℕ) : StronglyAdapted 𝒢 (In n) :=
    (gridIntegralProcess_martingale (P.grid n) hX hX₂ (fun k => hH _)
      (fun k => hHtop _) (2 ^ n)).stronglyAdapted
  have hJn (n : ℕ) : StronglyAdapted 𝒢 (Jn n) :=
    (gridIntegralProcess_martingale (P.grid n) hY hY₂ (fun k => hG _)
      (fun k => hGtop _) (2 ^ n)).stronglyAdapted
  obtain ⟨Cw, hCa, hCi, hCni, hCeq, hCconv⟩ := dyadic_compensator_density_L1
    (W := fun t => H t * G t) T hA hC hcts hbound hD hHD hDint
    (fun n => adapted_compensator_of_compensated_product (hIn n) (hJn n) (hm n))
  have hstop (t : ℝ≥0) (n : ℕ) (w : ℕ → Ω → ℝ) (V : ℝ≥0 → Ω → ℝ) :
      gridIntegralProcess (P.grid n) w V (2 ^ n) (min t T) =
        gridIntegralProcess (P.grid n) w V (2 ^ n) t := by
    rcases le_total t T with ht | ht
    · rw [min_eq_left ht]
    · rw [min_eq_right ht]
      have hP : P.grid n (2 ^ n) = T := uniform_dyadic_terminal_vertex T n
      exact (gridIntegralProcess_terminal (P.grid n) w V (2 ^ n) hP.le).trans
        (gridIntegralProcess_terminal (P.grid n) w V (2 ^ n) (hP.le.trans ht)).symm
  refine ⟨Cw, hCeq, ?_⟩
  refine compensated_product_martingale_of_limits
    (fun t => (hI (min t T)).mono (𝒢.mono (min_le_left t T)))
    (fun t => (hJ (min t T)).mono (𝒢.mono (min_le_left t T)))
    hCa (fun t => hI₂ (min t T)) (fun t => hJ₂ (min t T))
    (fun n t => gridIntegralProcess_memLp_two (P.grid n) hX₂ (fun k => hHtop _) (2 ^ n) t)
    (fun n t => gridIntegralProcess_memLp_two (P.grid n) hY₂ (fun k => hGtop _) (2 ^ n) t)
    hCi hCni hm ?_ ?_ hCconv
  · intro t
    refine (hIconv (min t T) (min_le_right t T)).congr' (Eventually.of_forall fun n => ?_)
    rw [hstop t n (a n) X]
  · intro t
    refine (hJconv (min t T) (min_le_right t T)).congr' (Eventually.of_forall fun n => ?_)
    rw [hstop t n (b n) Y]

end Density

end RoughHeston

#print axioms RoughHeston.stochasticStep_compensated_product
#print axioms RoughHeston.gridIntegralProcess_compensated_product
#print axioms RoughHeston.adapted_compensator_of_compensated_product
#print axioms RoughHeston.grid_density_error
#print axioms RoughHeston.dyadic_density_tendsto
#print axioms RoughHeston.dyadic_compensator_density_L1
#print axioms RoughHeston.continuous_integrals_compensated_product
