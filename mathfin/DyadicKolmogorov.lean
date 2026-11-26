import CanonicalTightness
import DyadicStepApproximation
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! A dyadic increment estimate for families of continuous pair laws. -/

open Filter Set MeasureTheory
open scoped BigOperators ENNReal NNReal Topology

namespace RoughHeston

/-- The weighted power of the endpoint distance along a dyadic edge. -/
noncomputable def weightedDyadicIncrement (T : ℝ≥0) (p : ℝ) (w : ℕ → ℝ≥0)
    (j : ℕ) (k : Fin (2 ^ j)) (f : CanonicalPath T (ℝ × ℝ)) : ℝ≥0∞ :=
  let G := uniformDyadicGrids T
  (w j : ℝ≥0∞) * (edist (canonicalPathEval T (G.grid j k) f)
    (canonicalPathEval T (G.grid j (k + 1)) f)) ^ p

theorem continuous_weightedDyadicIncrement (T : ℝ≥0) (p : ℝ) (w : ℕ → ℝ≥0)
    (j : ℕ) (k : Fin (2 ^ j)) : Continuous (weightedDyadicIncrement T p w j k) := by
  unfold weightedDyadicIncrement
  exact (ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp (ENNReal.continuous_rpow_const.comp
    ((continuous_canonicalPathEval _ _).edist (continuous_canonicalPathEval _ _)))

/-- Paths for which every normalized dyadic increment is bounded. -/
def boundedDyadicIncrements (T : ℝ≥0) (p : ℝ) (w : ℕ → ℝ≥0) (L : ℝ≥0∞) :
    Set (CanonicalPath T (ℝ × ℝ)) :=
  {f | ∀ (j : ℕ) (k : Fin (2 ^ j)), weightedDyadicIncrement T p w j k f ≤ L}

theorem isClosed_boundedDyadicIncrements (T : ℝ≥0) (p : ℝ) (w : ℕ → ℝ≥0) (L : ℝ≥0∞) :
    IsClosed (boundedDyadicIncrements T p w L) := by
  have he : boundedDyadicIncrements T p w L =
      ⋂ j, ⋂ k : Fin (2 ^ j), {f | weightedDyadicIncrement T p w j k f ≤ L} := by
    ext f
    simp [boundedDyadicIncrements]
  rw [he]
  exact isClosed_iInter fun j => isClosed_iInter fun k =>
    isClosed_le (continuous_weightedDyadicIncrement T p w j k) continuous_const

/-- Markov's inequality and the countable union bound for dyadic increments.
The factor of two in the geometric sum counts the edges at each level. -/
theorem measure_boundedDyadicIncrements_compl_le {T : ℝ≥0} {p : ℝ} {w : ℕ → ℝ≥0}
    {μ : Measure (CanonicalPath T (ℝ × ℝ))} {C q L : ℝ≥0∞} (hL0 : L ≠ 0) (hLtop : L ≠ ⊤)
    (hmoment : ∀ (j : ℕ) (k : Fin (2 ^ j)),
      (∫⁻ f, weightedDyadicIncrement T p w j k f ∂μ) ≤ C * q ^ j) :
    μ (boundedDyadicIncrements T p w L)ᶜ ≤ (C / L) * (1 - 2 * q)⁻¹ := by
  let U (j : ℕ) (k : Fin (2 ^ j)) := {f | L < weightedDyadicIncrement T p w j k f}
  have hU : (boundedDyadicIncrements T p w L)ᶜ = ⋃ j, ⋃ k, U j k := by
    ext f
    simp [boundedDyadicIncrements, U, not_le]
  have hmarkov (j : ℕ) (k : Fin (2 ^ j)) : μ (U j k) ≤ (C * q ^ j) / L := by
    have hsub : U j k ⊆ {f | L ≤ weightedDyadicIncrement T p w j k f} :=
      by
        intro f hf
        change L < weightedDyadicIncrement T p w j k f at hf
        exact hf.le
    refine (measure_mono hsub).trans ?_
    exact (meas_ge_le_lintegral_div
      (continuous_weightedDyadicIncrement T p w j k).measurable.aemeasurable hL0 hLtop).trans
        (by gcongr; exact hmoment j k)
  rw [hU]
  calc
    μ (⋃ j, ⋃ k, U j k) ≤ ∑' j, μ (⋃ k, U j k) := measure_iUnion_le _
    _ ≤ ∑' j, ∑' k : Fin (2 ^ j), μ (U j k) :=
      ENNReal.tsum_le_tsum fun j => measure_iUnion_le _
    _ ≤ ∑' j, ∑' _ : Fin (2 ^ j), (C * q ^ j) / L :=
      ENNReal.tsum_le_tsum fun j => ENNReal.tsum_le_tsum (hmarkov j)
    _ = ∑' j : ℕ, (C / L) * ((2 : ℝ≥0∞) * q) ^ j := by
      congr 1
      funext j
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, div_eq_mul_inv, mul_pow]
      ac_rfl
    _ = (C / L) * (1 - 2 * q)⁻¹ := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

section Chaining

variable {T : ℝ≥0}

private noncomputable def dyadicScaled (T : ℝ≥0) (j : ℕ) (s : CanonicalPathTime T) : ℝ :=
  (s.val : ℝ) * 2 ^ j / (T : ℝ)

private noncomputable def dyadicLeftIndex (T : ℝ≥0) (j : ℕ) (s : CanonicalPathTime T) : ℕ :=
  ⌊dyadicScaled T j s⌋₊

private theorem dyadicScaled_nonneg (j : ℕ) (s : CanonicalPathTime T) :
    0 ≤ dyadicScaled T j s := by
  unfold dyadicScaled
  positivity

private theorem dyadicLeftIndex_le (hT : 0 < T) (j : ℕ) (s : CanonicalPathTime T) :
    dyadicLeftIndex T j s ≤ 2 ^ j := by
  have hTR : 0 < (T : ℝ) := by exact_mod_cast hT
  have hsR : (s.val : ℝ) ≤ (T : ℝ) := s.property.2
  apply Nat.floor_le_of_le
  push_cast
  unfold dyadicScaled
  rw [div_le_iff₀ hTR]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right hsR (show 0 ≤ (2 : ℝ) ^ j by positivity)

private theorem dyadicLeftIndex_succ (j : ℕ) (s : CanonicalPathTime T) :
    dyadicLeftIndex T (j + 1) s = 2 * dyadicLeftIndex T j s ∨
      dyadicLeftIndex T (j + 1) s = 2 * dyadicLeftIndex T j s + 1 := by
  have hscale : dyadicScaled T (j + 1) s = 2 * dyadicScaled T j s := by
    unfold dyadicScaled
    rw [pow_succ, ← mul_div_assoc]
    congr 1
    ring
  have hlo := Nat.floor_le (dyadicScaled_nonneg j s)
  have hhi := Nat.lt_floor_add_one (dyadicScaled T j s)
  change (dyadicLeftIndex T j s : ℝ) ≤ _ at hlo
  change _ < (dyadicLeftIndex T j s : ℝ) + 1 at hhi
  have h₁ : 2 * dyadicLeftIndex T j s ≤ dyadicLeftIndex T (j + 1) s := by
    apply Nat.le_floor
    rw [hscale]
    push_cast
    linarith
  have h₂ : dyadicLeftIndex T (j + 1) s < 2 * dyadicLeftIndex T j s + 2 := by
    apply (Nat.floor_lt (dyadicScaled_nonneg (j + 1) s)).2
    rw [hscale]
    push_cast
    linarith
  omega

private noncomputable def dyadicLeftTime (T : ℝ≥0) (j : ℕ) (s : CanonicalPathTime T) :
    CanonicalPathTime T :=
  canonicalEvalTime T ((uniformDyadicGrids T).grid j (dyadicLeftIndex T j s))

private theorem dyadicLeftTime_real (hT : 0 < T) (j : ℕ) (s : CanonicalPathTime T) :
    ((dyadicLeftTime T j s).val : ℝ) =
      (dyadicLeftIndex T j s : ℝ) * (T : ℝ) / (2 : ℝ) ^ j := by
  let G := uniformDyadicGrids T
  have hgrid : G.grid j (dyadicLeftIndex T j s) ≤ T := by
    calc
      G.grid j (dyadicLeftIndex T j s) ≤ G.grid j (2 ^ j) :=
        (G.grid j).monotone (dyadicLeftIndex_le hT j s)
      _ = T := uniform_dyadic_terminal_vertex T j
  change (↑(min (G.grid j (dyadicLeftIndex T j s)) T) : ℝ) = _
  rw [min_eq_left hgrid]
  change (↑((dyadicLeftIndex T j s : ℝ≥0) * T / (2 : ℝ≥0) ^ j) : ℝ) = _
  push_cast
  rfl

private theorem dyadicLeftTime_close (hT : 0 < T) (j : ℕ) (s : CanonicalPathTime T) :
    dist (dyadicLeftTime T j s) s ≤ (T : ℝ) / (2 : ℝ) ^ j := by
  have hTR : 0 < (T : ℝ) := by exact_mod_cast hT
  have hpow : 0 < (2 : ℝ) ^ j := by positivity
  have hlo := Nat.floor_le (dyadicScaled_nonneg j s)
  have hhi := Nat.lt_floor_add_one (dyadicScaled T j s)
  change (dyadicLeftIndex T j s : ℝ) ≤ _ at hlo
  change _ < (dyadicLeftIndex T j s : ℝ) + 1 at hhi
  unfold dyadicScaled at hlo hhi
  rw [le_div_iff₀ hTR] at hlo
  rw [div_lt_iff₀ hTR, add_mul, one_mul] at hhi
  have hl : (dyadicLeftIndex T j s : ℝ) * (T : ℝ) / (2 : ℝ) ^ j ≤ (s.val : ℝ) :=
    (div_le_iff₀ hpow).2 hlo
  have hh : (s.val : ℝ) ≤ (dyadicLeftIndex T j s : ℝ) * (T : ℝ) / (2 : ℝ) ^ j +
      (T : ℝ) / (2 : ℝ) ^ j := by
    rw [← add_div, le_div_iff₀ hpow]
    exact hhi.le
  change |((dyadicLeftTime T j s).val : ℝ) - (s.val : ℝ)| ≤ _
  rw [dyadicLeftTime_real hT, abs_of_nonpos (sub_nonpos.mpr hl), neg_sub]
  linarith

private theorem tendsto_dyadicLeftTime (hT : 0 < T) (s : CanonicalPathTime T) :
    Tendsto (fun j => dyadicLeftTime T j s) atTop (𝓝 s) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (show 0 ≤ (2 : ℝ)⁻¹ by norm_num)
    (show (2 : ℝ)⁻¹ < 1 by norm_num)
  have hmesh : Tendsto (fun j : ℕ => (T : ℝ) / (2 : ℝ) ^ j) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, mul_zero] using
      (tendsto_const_nhds (x := (T : ℝ))).mul hp
  exact tendsto_iff_dist_tendsto_zero.mpr
    (squeeze_zero (fun _ => dist_nonneg) (fun j => dyadicLeftTime_close hT j s) hmesh)

private theorem dyadicLeftIndex_nearby (hT : 0 < T) (j : ℕ) (s t : CanonicalPathTime T)
    (hs : s.val ≤ t.val) (hnear : dist s t ≤ (T : ℝ) / (2 : ℝ) ^ j) :
    dyadicLeftIndex T j t = dyadicLeftIndex T j s ∨
      dyadicLeftIndex T j t = dyadicLeftIndex T j s + 1 := by
  have hTR : 0 < (T : ℝ) := by exact_mod_cast hT
  have hp : 0 < (2 : ℝ) ^ j := by positivity
  have hsR : (s.val : ℝ) ≤ (t.val : ℝ) := hs
  have hlo : dyadicLeftIndex T j s ≤ dyadicLeftIndex T j t := by
    apply Nat.floor_mono
    unfold dyadicScaled
    gcongr
  have htd : (t.val : ℝ) - (s.val : ℝ) ≤ (T : ℝ) / (2 : ℝ) ^ j := by
    change |(s.val : ℝ) - (t.val : ℝ)| ≤ _ at hnear
    simpa only [abs_of_nonpos (sub_nonpos.mpr hsR), neg_sub] using hnear
  have hdiff : dyadicScaled T j t - dyadicScaled T j s ≤ 1 := by
    unfold dyadicScaled
    rw [← sub_div, ← sub_mul, div_le_iff₀ hTR, one_mul]
    exact (le_div_iff₀ hp).1 htd
  have hhi := Nat.lt_floor_add_one (dyadicScaled T j s)
  change _ < (dyadicLeftIndex T j s : ℝ) + 1 at hhi
  have hupper : dyadicLeftIndex T j t < dyadicLeftIndex T j s + 2 := by
    apply (Nat.floor_lt (dyadicScaled_nonneg j t)).2
    push_cast
    linarith
  omega

/-- If every adjacent dyadic edge at level j has distance at most D times r ^ j,
then all times within one mesh have distance at most a fixed multiple of this
quantity. The proof sums one edge at each finer level. -/
theorem canonicalPath_dyadic_modulus {E : Type*} [PseudoMetricSpace E]
    (hT : 0 < T) (f : CanonicalPath T E) (D r : ℝ) (hD : 0 ≤ D)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hedge : ∀ (j : ℕ) (k : Fin (2 ^ j)),
      dist (canonicalPathEval T ((uniformDyadicGrids T).grid j k) f)
        (canonicalPathEval T ((uniformDyadicGrids T).grid j (k + 1)) f) ≤ D * r ^ j) :
    ∀ (j : ℕ) (s t : CanonicalPathTime T), dist s t ≤ (T : ℝ) / (2 : ℝ) ^ j →
      dist (f s) (f t) ≤ D * (1 + 2 * r / (1 - r)) * r ^ j := by
  let G := uniformDyadicGrids T
  have hrefine (j k : ℕ) : G.grid j k = G.grid (j + 1) (2 * k) := by
    simpa only [pow_one] using G.vertex_at_refinement j 1 k
  have hstep (j : ℕ) (s : CanonicalPathTime T) :
      dist (f (dyadicLeftTime T j s)) (f (dyadicLeftTime T (j + 1) s)) ≤ D * r ^ (j + 1) := by
    change dist (canonicalPathEval T (G.grid j (dyadicLeftIndex T j s)) f)
      (canonicalPathEval T (G.grid (j + 1) (dyadicLeftIndex T (j + 1) s)) f) ≤ _
    rw [hrefine j (dyadicLeftIndex T j s)]
    rcases dyadicLeftIndex_succ j s with he | he
    · rw [he, dist_self]
      positivity
    · have hk : 2 * dyadicLeftIndex T j s < 2 ^ (j + 1) := by
        have h := dyadicLeftIndex_le hT (j + 1) s
        omega
      rw [he]
      exact hedge (j + 1) ⟨2 * dyadicLeftIndex T j s, hk⟩
  have htail (j : ℕ) (s : CanonicalPathTime T) :
      dist (f (dyadicLeftTime T j s)) (f s) ≤ D * r ^ j * r / (1 - r) := by
    have hconv : Tendsto (fun n : ℕ => f (dyadicLeftTime T (j + n) s)) atTop (𝓝 (f s)) :=
      (f.continuous.tendsto s).comp ((tendsto_dyadicLeftTime hT s).comp
        (by simpa only [Nat.add_comm] using tendsto_add_atTop_nat j))
    have hsum := (summable_geometric_of_lt_one hr0 hr1).mul_left (D * r ^ (j + 1))
    have h := dist_le_tsum_of_dist_le_of_tendsto₀ (fun n => (D * r ^ (j + 1)) * r ^ n)
      (f := fun n => f (dyadicLeftTime T (j + n) s)) (fun n => by
        rw [mul_assoc, ← pow_add]
        simpa only [Nat.add_assoc, Nat.add_comm 1 n] using hstep (j + n) s)
      hsum hconv
    simpa only [Nat.add_zero, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1,
      pow_succ r j, ← mul_assoc, div_eq_mul_inv] using h
  have hcoarse_ordered (j : ℕ) (s t : CanonicalPathTime T) (hs : s.val ≤ t.val)
      (hnear : dist s t ≤ (T : ℝ) / (2 : ℝ) ^ j) :
      dist (f (dyadicLeftTime T j s)) (f (dyadicLeftTime T j t)) ≤ D * r ^ j := by
    change dist (canonicalPathEval T (G.grid j (dyadicLeftIndex T j s)) f)
      (canonicalPathEval T (G.grid j (dyadicLeftIndex T j t)) f) ≤ _
    rcases dyadicLeftIndex_nearby hT j s t hs hnear with he | he
    · rw [he, dist_self]
      positivity
    · have hk : dyadicLeftIndex T j s < 2 ^ j := by
        have h := dyadicLeftIndex_le hT j t
        omega
      rw [he]
      exact hedge j ⟨dyadicLeftIndex T j s, hk⟩
  intro j s t hnear
  have hcoarse : dist (f (dyadicLeftTime T j s)) (f (dyadicLeftTime T j t)) ≤ D * r ^ j := by
    rcases le_total s.val t.val with hst | hts
    · exact hcoarse_ordered j s t hst hnear
    · rw [dist_comm]
      exact hcoarse_ordered j t s hts (by simpa only [dist_comm t s] using hnear)
  calc
    dist (f s) (f t) ≤ dist (f s) (f (dyadicLeftTime T j s)) +
          dist (f (dyadicLeftTime T j s)) (f (dyadicLeftTime T j t)) +
          dist (f (dyadicLeftTime T j t)) (f t) := by
      have h₁ := dist_triangle (f s) (f (dyadicLeftTime T j s)) (f t)
      have h₂ := dist_triangle (f (dyadicLeftTime T j s)) (f (dyadicLeftTime T j t)) (f t)
      linarith
    _ ≤ D * r ^ j * r / (1 - r) + D * r ^ j + D * r ^ j * r / (1 - r) := by
      rw [dist_comm (f s)]
      exact add_le_add (add_le_add (htail j s) hcoarse) (htail j t)
    _ = D * (1 + 2 * r / (1 - r)) * r ^ j := by ring

/-- For a geometric target rate r, normalize the p-th power by the
corresponding power of the mesh rate. -/
noncomputable def dyadicMomentWeight (p : ℝ) (r : ℝ≥0) (j : ℕ) : ℝ≥0 :=
  ((r ^ j) ^ p)⁻¹

private theorem dyadic_edge_bound_of_mem {p : ℝ} {r L : ℝ≥0} (hp : 0 < p) (hr : 0 < r)
    {f : CanonicalPath T (ℝ × ℝ)} (hf : f ∈ boundedDyadicIncrements T p (dyadicMomentWeight p r) L)
    (j : ℕ) (k : Fin (2 ^ j)) :
    dist (canonicalPathEval T ((uniformDyadicGrids T).grid j k) f)
      (canonicalPathEval T ((uniformDyadicGrids T).grid j (k + 1)) f) ≤
        (L ^ p⁻¹ : ℝ≥0) * (r : ℝ) ^ j := by
  let a := canonicalPathEval T ((uniformDyadicGrids T).grid j k) f
  let b := canonicalPathEval T ((uniformDyadicGrids T).grid j (k + 1)) f
  let z := nndist a b
  let R : ℝ≥0 := (r ^ j) ^ p
  have hR : 0 < R := NNReal.rpow_pos (pow_pos hr _)
  have h : (↑(R⁻¹) : ℝ≥0∞) * (edist a b) ^ p ≤ (L : ℝ≥0∞) := hf j k
  rw [edist_nndist, ← ENNReal.coe_rpow_of_nonneg _ hp.le, ← ENNReal.coe_mul,
    ENNReal.coe_le_coe] at h
  have hP : z ^ p ≤ L * R := by
    have hh := mul_le_mul_of_nonneg_right h (zero_le : 0 ≤ R)
    change R⁻¹ * z ^ p * R ≤ L * R at hh
    calc
      z ^ p = R⁻¹ * z ^ p * R := by rw [mul_right_comm, inv_mul_cancel₀ hR.ne', one_mul]
      _ ≤ L * R := hh
  have hz : z ≤ L ^ p⁻¹ * r ^ j := by
    apply (NNReal.rpow_le_rpow_iff hp).1
    rw [NNReal.mul_rpow, ← one_div, NNReal.rpow_self_rpow_inv hp.ne']
    exact hP
  simpa only [z, a, b, NNReal.coe_mul, NNReal.coe_pow, coe_nndist] using
    (show (z : ℝ) ≤ ((L ^ p⁻¹ * r ^ j : ℝ≥0) : ℝ) from hz)

private theorem canonicalPathTime_dist_zero_le (t : CanonicalPathTime T) :
    dist t (canonicalEvalTime T 0) ≤ (T : ℝ) := by
  change |(t.val : ℝ) - (↑(min (0 : ℝ≥0) T) : ℝ)| ≤ _
  rw [min_eq_left (zero_le : 0 ≤ T), NNReal.coe_zero, sub_zero,
    abs_of_nonneg (show 0 ≤ (t.val : ℝ) from t.val.property)]
  exact t.property.2

/-- A bound on the initial point and geometric bounds along all dyadic edges
define a compact family of pair paths. -/
theorem isCompact_boundedDyadicIncrements_start (hT : 0 < T) (p A : ℝ) (r L : ℝ≥0)
    (hp : 0 < p) (hr0 : 0 < r) (hr1 : r < 1) :
    IsCompact ({f : CanonicalPath T (ℝ × ℝ) | ‖f (canonicalEvalTime T 0)‖ ≤ A} ∩
        boundedDyadicIncrements T p (dyadicMomentWeight p r) L) := by
  let K := {f : CanonicalPath T (ℝ × ℝ) | ‖f (canonicalEvalTime T 0)‖ ≤ A} ∩
        boundedDyadicIncrements T p (dyadicMomentWeight p r) L
  let e := ContinuousMap.isometryEquivBoundedOfCompact (CanonicalPathTime T) (ℝ × ℝ)
  let Kb := e.symm ⁻¹' K
  let D : ℝ := (L ^ p⁻¹ : ℝ≥0) * (1 + 2 * (r : ℝ) / (1 - r))
  have hrR0 : 0 ≤ (r : ℝ) := r.property
  have hrR1 : (r : ℝ) < 1 := by exact_mod_cast hr1
  have hmod f (hf : f ∈ K) j s t (h : dist s t ≤ (T : ℝ) / (2 : ℝ) ^ j) :
      dist (f s) (f t) ≤ D * (r : ℝ) ^ j :=
    canonicalPath_dyadic_modulus hT f (↑(L ^ p⁻¹ : ℝ≥0)) r (by positivity) hrR0 hrR1
      (dyadic_edge_bound_of_mem hp hr0 hf.2) j s t h
  suffices hKb : IsCompact Kb by
    convert hKb.image e.symm.continuous using 1
    ext f
    constructor
    · intro hf
      exact ⟨e f, by simpa only [Kb, mem_preimage, e.symm_apply_apply] using hf, e.symm_apply_apply f⟩
    · rintro ⟨g, hg, rfl⟩
      exact hg
  refine BoundedContinuousFunction.arzela_ascoli₂ (Metric.closedBall 0 (A + D))
    (isCompact_closedBall _ _) Kb ?_ ?_ ?_
  · apply IsClosed.preimage e.symm.continuous
    apply IsClosed.inter
    · exact isClosed_le (continuous_norm.comp (continuous_canonicalPathEval T 0)) continuous_const
    · exact isClosed_boundedDyadicIncrements T p (dyadicMomentWeight p r) L
  · intro f t hf
    have ht : dist t (canonicalEvalTime T 0) ≤ (T : ℝ) / (2 : ℝ) ^ 0 := by
      simpa only [pow_zero, div_one] using canonicalPathTime_dist_zero_le t
    have hm : dist (f t) (f (canonicalEvalTime T 0)) ≤ D := by
      have hh := hmod (e.symm f) hf 0 t (canonicalEvalTime T 0) ht
      change dist (f t) (f (canonicalEvalTime T 0)) ≤ D * (r : ℝ) ^ 0 at hh
      simpa only [pow_zero, mul_one] using hh
    have hz : dist (f (canonicalEvalTime T 0)) 0 ≤ A := by
      have hstart := (show e.symm f ∈ K from hf).1
      change ‖f (canonicalEvalTime T 0)‖ ≤ A at hstart
      simpa only [dist_zero_right] using hstart
    rw [Metric.mem_closedBall]
    exact (dist_triangle _ (f (canonicalEvalTime T 0)) _).trans
      ((add_le_add hm hz).trans_eq (add_comm _ _))
  · apply UniformEquicontinuous.equicontinuous
    rw [Metric.uniformEquicontinuous_iff]
    intro ε hε
    have hconv : Tendsto (fun j : ℕ => D * (r : ℝ) ^ j) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one hrR0 hrR1).const_mul D
    obtain ⟨j, hj⟩ := (hconv.eventually (Iio_mem_nhds hε)).exists
    have hTR : 0 < (T : ℝ) := by exact_mod_cast hT
    refine ⟨(T : ℝ) / (2 : ℝ) ^ j, by positivity, fun s t hst f => ?_⟩
    exact (hmod (e.symm f.val) f.property j s t hst.le).trans_lt hj

/-- Uniform normalized dyadic moment bounds and bounded initial values imply
weak subsequence extraction for canonical pair laws. -/
theorem canonicalPairPath_subsequence_of_dyadic_moments (hT : 0 < T) (p A : ℝ) (r : ℝ≥0)
    (hp : 0 < p) (hr0 : 0 < r) (hr1 : r < 1)
    (Pn : ℕ → ProbabilityMeasure (CanonicalPath T (ℝ × ℝ))) (C q : ℝ≥0∞)
    (hC : C ≠ ⊤) (hq : 2 * q < 1)
    (hstart : ∀ n, (Pn n : Measure (CanonicalPath T (ℝ × ℝ)))
      {f | A < ‖f (canonicalEvalTime T 0)‖} = 0)
    (hmoment : ∀ (n j : ℕ) (k : Fin (2 ^ j)),
      (∫⁻ f, weightedDyadicIncrement T p (dyadicMomentWeight p r) j k f ∂(Pn n : Measure _)) ≤
        C * q ^ j) :
    ∃ P : ProbabilityMeasure (CanonicalPath T (ℝ × ℝ)), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (Pn ∘ φ) atTop (𝓝 P) := by
  refine canonicalPairPath_subsequence_of_uniform_tightness Pn fun ε hε => ?_
  by_cases hεtop : ε = ⊤
  · exact ⟨∅, isCompact_empty, fun _ => hεtop ▸ le_top⟩
  let G : ℝ≥0∞ := (1 - 2 * q)⁻¹
  have hG : G ≠ ⊤ := ENNReal.inv_ne_top.2 (tsub_pos_of_lt hq).ne'
  let B := C * G
  have hB : B ≠ ⊤ := ENNReal.mul_ne_top hC hG
  let L : ℝ≥0 := (B / ε + 1).toNNReal
  have hL : (L : ℝ≥0∞) = B / ε + 1 :=
    ENNReal.coe_toNNReal (ENNReal.add_ne_top.2 ⟨ENNReal.div_ne_top hB hε.ne', ENNReal.one_ne_top⟩)
  have hL0 : (L : ℝ≥0∞) ≠ 0 := by rw [hL]; positivity
  have hsmall : (C / L) * G ≤ ε := by
    rw [div_eq_mul_inv, mul_right_comm C, ← div_eq_mul_inv]
    apply (ENNReal.div_le_iff_le_mul (Or.inl hL0) (Or.inl ENNReal.coe_ne_top)).2
    rw [mul_comm ε]
    apply (ENNReal.div_le_iff_le_mul (Or.inl hε.ne') (Or.inl hεtop)).1
    rw [hL]
    exact le_add_right (le_refl _)
  refine ⟨_, isCompact_boundedDyadicIncrements_start hT p A r L hp hr0 hr1, fun n => ?_⟩
  rw [compl_inter]
  refine (measure_union_le _ _).trans ?_
  have hzero : (Pn n : Measure (CanonicalPath T (ℝ × ℝ)))
      {f | ‖f (canonicalEvalTime T 0)‖ ≤ A}ᶜ = 0 := by
    simpa only [compl_ofPred, not_le] using hstart n
  rw [hzero, zero_add]
  exact (measure_boundedDyadicIncrements_compl_le hL0 ENNReal.coe_ne_top (hmoment n)).trans hsmall

/-- Geometrically decaying unweighted p-th moments of dyadic increments,
with rate strictly below one half, imply weak subsequence extraction. -/
theorem canonicalPairPath_subsequence_of_geometric_increment_moments (hT : 0 < T)
    (p A : ℝ) (hp : 0 < p)
    (Pn : ℕ → ProbabilityMeasure (CanonicalPath T (ℝ × ℝ))) (C : ℝ≥0∞) (a : ℝ≥0)
    (hC : C ≠ ⊤) (ha : 2 * a < 1)
    (hstart : ∀ n, (Pn n : Measure (CanonicalPath T (ℝ × ℝ)))
      {f | A < ‖f (canonicalEvalTime T 0)‖} = 0)
    (hmoment : ∀ (n j : ℕ) (k : Fin (2 ^ j)),
      (∫⁻ f, weightedDyadicIncrement T p (fun _ => 1) j k f ∂(Pn n : Measure _)) ≤
        C * (a : ℝ≥0∞) ^ j) :
    ∃ P : ProbabilityMeasure (CanonicalPath T (ℝ × ℝ)), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (Pn ∘ φ) atTop (𝓝 P) := by
  let b : ℝ≥0 := (2 * a + 1) / 2
  have haR : 2 * (a : ℝ) < 1 := by exact_mod_cast ha
  have hb : 2 * a < b := by exact_mod_cast (show 2 * (a : ℝ) < (2 * a + 1) / 2 by linarith)
  have hb0 : 0 < b := by positivity
  have hb1 : b < 1 := by exact_mod_cast (show (2 * (a : ℝ) + 1) / 2 < 1 by linarith)
  let r : ℝ≥0 := b ^ (1 / p)
  let q : ℝ≥0 := a * b⁻¹
  have hq : 2 * q < 1 := by
    change 2 * (a * b⁻¹) < 1
    rw [← mul_assoc, ← div_eq_mul_inv, div_lt_iff₀ hb0, one_mul]
    exact hb
  have hr0 : 0 < r := NNReal.rpow_pos hb0
  have hr1 : r < 1 := NNReal.rpow_lt_one hb1 (one_div_pos.mpr hp)
  have hrp : r ^ p = b := NNReal.rpow_self_rpow_inv hp.ne' b
  refine canonicalPairPath_subsequence_of_dyadic_moments hT p A r hp hr0 hr1 Pn C q hC
    (by exact_mod_cast hq) hstart fun n j k => ?_
  have hw : dyadicMomentWeight p r j = (b⁻¹) ^ j := by
    unfold dyadicMomentWeight
    rw [← NNReal.rpow_natCast_mul, mul_comm, NNReal.rpow_mul_natCast, hrp, inv_pow]
  let F := weightedDyadicIncrement T p (fun _ => 1) j k
  have hchange (f : CanonicalPath T (ℝ × ℝ)) :
      weightedDyadicIncrement T p (dyadicMomentWeight p r) j k f =
        ((dyadicMomentWeight p r j : ℝ≥0) : ℝ≥0∞) * F f := by
    simp [F, weightedDyadicIncrement]
  simp only [hchange]
  rw [lintegral_const_mul _ (show Measurable F from
    (continuous_weightedDyadicIncrement T p (fun _ => 1) j k).measurable)]
  calc
    _ ≤ (dyadicMomentWeight p r j : ℝ≥0∞) * (C * (a : ℝ≥0∞) ^ j) :=
      mul_right_mono (hmoment n j k)
    _ = C * (q : ℝ≥0∞) ^ j := by
      rw [hw]
      push_cast [q, mul_pow]
      ac_rfl

private theorem edist_canonicalDyadic_edge_time (j : ℕ) (k : Fin (2 ^ j)) :
    edist (canonicalEvalTime T ((uniformDyadicGrids T).grid j k))
      (canonicalEvalTime T ((uniformDyadicGrids T).grid j (k + 1))) =
        ((T / (2 : ℝ≥0) ^ j : ℝ≥0) : ℝ≥0∞) := by
  let G := uniformDyadicGrids T
  have h₁ : G.grid j k ≤ T :=
    ((G.grid j).monotone k.isLt.le).trans_eq (uniform_dyadic_terminal_vertex T j)
  have h₂ : G.grid j (k + 1) ≤ T :=
    ((G.grid j).monotone (Nat.succ_le_of_lt k.isLt)).trans_eq (uniform_dyadic_terminal_vertex T j)
  rw [edist_nndist, ENNReal.coe_inj]
  apply NNReal.eq
  rw [coe_nndist]
  change |(↑(min (G.grid j k) T) : ℝ) - (↑(min (G.grid j (k + 1)) T) : ℝ)| = _
  rw [min_eq_left h₁, min_eq_left h₂]
  change |(↑((k : ℕ) * T / (2 : ℝ≥0) ^ j) : ℝ) -
    (↑((k + 1 : ℕ) * T / (2 : ℝ≥0) ^ j) : ℝ)| = _
  push_cast
  have he : (k : ℝ) * (T : ℝ) / (2 : ℝ) ^ j -
      ((k : ℝ) + 1) * (T : ℝ) / (2 : ℝ) ^ j = -((T : ℝ) / (2 : ℝ) ^ j) := by ring
  rw [he, abs_neg, abs_of_nonneg (by positivity)]

/-- Kolmogorov's tightness implication for canonical pair-valued paths with
bounded initial values and a uniform moment exponent greater than one. -/
theorem canonicalPairPath_subsequence_of_increment_moments (hT : 0 < T)
    (p β A : ℝ) (hp : 0 < p) (hβ : 1 < β)
    (Pn : ℕ → ProbabilityMeasure (CanonicalPath T (ℝ × ℝ))) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hstart : ∀ n, (Pn n : Measure (CanonicalPath T (ℝ × ℝ)))
      {f | A < ‖f (canonicalEvalTime T 0)‖} = 0)
    (hmoment : ∀ (n : ℕ) (s t : CanonicalPathTime T),
      (∫⁻ f : CanonicalPath T (ℝ × ℝ), edist (f s) (f t) ^ p ∂(Pn n : Measure _)) ≤ C * edist s t ^ β) :
    ∃ P : ProbabilityMeasure (CanonicalPath T (ℝ × ℝ)), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (Pn ∘ φ) atTop (𝓝 P) := by
  let a : ℝ≥0 := (2 : ℝ≥0) ^ (-β)
  have ha : 2 * a < 1 := by
    have h := NNReal.rpow_lt_rpow_of_exponent_lt (show (1 : ℝ≥0) < 2 by norm_num)
      (show -β < (-1 : ℝ) by linarith)
    change a < (2 : ℝ≥0) ^ (-1 : ℝ) at h
    rw [NNReal.rpow_neg_one] at h
    rw [mul_comm]
    exact (lt_div_iff₀ (show (0 : ℝ≥0) < 2 by norm_num)).1 (by simpa only [one_div] using h)
  refine canonicalPairPath_subsequence_of_geometric_increment_moments hT p A hp Pn
    (C * (↑(T ^ β : ℝ≥0) : ℝ≥0∞)) a (ENNReal.mul_ne_top hC ENNReal.coe_ne_top) ha hstart
    fun n j k => ?_
  let G := uniformDyadicGrids T
  let s := canonicalEvalTime T (G.grid j k)
  let t := canonicalEvalTime T (G.grid j (k + 1))
  have hmesh : edist s t ^ β =
      (↑(T ^ β : ℝ≥0) : ℝ≥0∞) * (a : ℝ≥0∞) ^ j := by
    change edist (canonicalEvalTime T (G.grid j k))
      (canonicalEvalTime T (G.grid j (k + 1))) ^ β = _
    rw [edist_canonicalDyadic_edge_time j k, ← ENNReal.coe_rpow_of_nonneg _ (by linarith : 0 ≤ β),
      ← ENNReal.coe_pow, ← ENNReal.coe_mul, ENNReal.coe_inj]
    rw [div_eq_mul_inv, NNReal.mul_rpow, ← inv_pow, ← NNReal.rpow_natCast_mul,
      mul_comm (j : ℝ) β, NNReal.rpow_mul_natCast, NNReal.inv_rpow]
    simp only [a, NNReal.rpow_neg]
  have hm := hmoment n s t
  rw [hmesh, ← mul_assoc] at hm
  simpa only [weightedDyadicIncrement, ENNReal.coe_one, one_mul, s, t, G, canonicalPathEval] using hm

end Chaining

#print axioms canonicalPath_dyadic_modulus
#print axioms isCompact_boundedDyadicIncrements_start
#print axioms canonicalPairPath_subsequence_of_dyadic_moments
#print axioms canonicalPairPath_subsequence_of_geometric_increment_moments
#print axioms canonicalPairPath_subsequence_of_increment_moments
#print axioms isClosed_boundedDyadicIncrements
#print axioms measure_boundedDyadicIncrements_compl_le

end RoughHeston
