import DyadicKolmogorov

/-! Prokhorov extraction in a proper normed path space. The dyadic estimate
and compactness proof generalize the scripts in `DyadicKolmogorov` and
`CanonicalTightness`, reusing their deterministic chaining theorem. -/

open Filter Set MeasureTheory
open scoped BigOperators ENNReal NNReal Topology

namespace RoughHeston

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E] {T : ℝ≥0}

omit [ProperSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- A uniformly tight sequence of canonical laws has a weakly convergent
subsequence. The convergence is in the probability-measure weak topology. -/
theorem canonicalProperPath_subsequence_of_uniform_tightness {T : ℝ≥0}
    (Pn : ℕ → ProbabilityMeasure (CanonicalPath T E))
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set (CanonicalPath T E),
      IsCompact K ∧ ∀ n, (Pn n : Measure (CanonicalPath T E)) Kᶜ ≤ ε) :
    ∃ P : ProbabilityMeasure (CanonicalPath T E), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (Pn ∘ φ) atTop (𝓝 P) := by
  let S := Set.range Pn
  have hS : IsTightMeasureSet
      {((P : ProbabilityMeasure (CanonicalPath T E)) :
        Measure (CanonicalPath T E)) | P ∈ S} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    obtain ⟨K, hK, hKt⟩ := htight ε hε
    refine ⟨K, hK, ?_⟩
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    exact hKt n
  obtain ⟨P, _, φ, hmono, hconv⟩ :=
    (isCompact_closure_of_isTightMeasureSet hS).tendsto_subseq
      (fun n => subset_closure (Set.mem_range_self n : Pn n ∈ S))
  exact ⟨P, φ, hmono, hconv⟩

/-- The weighted power of the endpoint distance along a dyadic edge. -/
noncomputable def properWeightedDyadicIncrement (T : ℝ≥0) (p : ℝ) (w : ℕ → ℝ≥0)
    (j : ℕ) (k : Fin (2 ^ j)) (f : CanonicalPath T E) : ℝ≥0∞ :=
  let G := uniformDyadicGrids T
  (w j : ℝ≥0∞) * (edist (canonicalPathEval T (G.grid j k) f)
    (canonicalPathEval T (G.grid j (k + 1)) f)) ^ p

omit [ProperSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_properWeightedDyadicIncrement (T : ℝ≥0) (p : ℝ) (w : ℕ → ℝ≥0)
    (j : ℕ) (k : Fin (2 ^ j)) : Continuous (properWeightedDyadicIncrement (E := E) T p w j k) := by
  unfold properWeightedDyadicIncrement
  exact (ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp (ENNReal.continuous_rpow_const.comp
    ((continuous_canonicalPathEval _ _).edist (continuous_canonicalPathEval _ _)))

/-- Paths for which every normalized dyadic increment is bounded. -/
def properBoundedDyadicIncrements (T : ℝ≥0) (p : ℝ) (w : ℕ → ℝ≥0) (L : ℝ≥0∞) :
    Set (CanonicalPath T E) :=
  {f | ∀ (j : ℕ) (k : Fin (2 ^ j)), properWeightedDyadicIncrement (E := E) T p w j k f ≤ L}

omit [ProperSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
theorem isClosed_properBoundedDyadicIncrements (T : ℝ≥0) (p : ℝ) (w : ℕ → ℝ≥0) (L : ℝ≥0∞) :
    IsClosed (properBoundedDyadicIncrements (E := E) T p w L) := by
  have he : properBoundedDyadicIncrements (E := E) T p w L =
      ⋂ j, ⋂ k : Fin (2 ^ j), {f | properWeightedDyadicIncrement (E := E) T p w j k f ≤ L} := by
    ext f
    simp [properBoundedDyadicIncrements]
  rw [he]
  exact isClosed_iInter fun j => isClosed_iInter fun k =>
    isClosed_le (continuous_properWeightedDyadicIncrement (E := E) T p w j k) continuous_const

omit [ProperSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
/-- Markov's inequality and the countable union bound for dyadic increments.
The factor of two in the geometric sum counts the edges at each level. -/
theorem measure_properBoundedDyadicIncrements_compl_le {T : ℝ≥0} {p : ℝ} {w : ℕ → ℝ≥0}
    {μ : Measure (CanonicalPath T E)} {C q L : ℝ≥0∞} (hL0 : L ≠ 0) (hLtop : L ≠ ⊤)
    (hmoment : ∀ (j : ℕ) (k : Fin (2 ^ j)),
      (∫⁻ f, properWeightedDyadicIncrement (E := E) T p w j k f ∂μ) ≤ C * q ^ j) :
    μ (properBoundedDyadicIncrements (E := E) T p w L)ᶜ ≤ (C / L) * (1 - 2 * q)⁻¹ := by
  let U (j : ℕ) (k : Fin (2 ^ j)) := {f : CanonicalPath T E | L < properWeightedDyadicIncrement (E := E) T p w j k f}
  have hU : (properBoundedDyadicIncrements (E := E) T p w L)ᶜ = ⋃ j, ⋃ k, U j k := by
    ext f
    simp [properBoundedDyadicIncrements, U, not_le]
  have hmarkov (j : ℕ) (k : Fin (2 ^ j)) : μ (U j k) ≤ (C * q ^ j) / L := by
    have hsub : U j k ⊆ {f | L ≤ properWeightedDyadicIncrement (E := E) T p w j k f} :=
      by
        intro f hf
        change L < properWeightedDyadicIncrement (E := E) T p w j k f at hf
        exact hf.le
    refine (measure_mono hsub).trans ?_
    exact (meas_ge_le_lintegral_div
      (continuous_properWeightedDyadicIncrement (E := E) T p w j k).measurable.aemeasurable hL0 hLtop).trans
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

omit [ProperSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
private theorem dyadic_edge_bound_of_mem {p : ℝ} {r L : ℝ≥0} (hp : 0 < p) (hr : 0 < r)
    {f : CanonicalPath T E} (hf : f ∈ properBoundedDyadicIncrements (E := E) T p (dyadicMomentWeight p r) L)
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

omit [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
/-- A bound on the initial point and geometric bounds along all dyadic edges
define a compact family of paths. -/
theorem isCompact_properBoundedDyadicIncrements_start (hT : 0 < T) (p A : ℝ) (r L : ℝ≥0)
    (hp : 0 < p) (hr0 : 0 < r) (hr1 : r < 1) :
    IsCompact ({f : CanonicalPath T E | ‖f (canonicalEvalTime T 0)‖ ≤ A} ∩
        properBoundedDyadicIncrements (E := E) T p (dyadicMomentWeight p r) L) := by
  let K := {f : CanonicalPath T E | ‖f (canonicalEvalTime T 0)‖ ≤ A} ∩
        properBoundedDyadicIncrements (E := E) T p (dyadicMomentWeight p r) L
  let e := ContinuousMap.isometryEquivBoundedOfCompact (CanonicalPathTime T) E
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
    · exact isClosed_properBoundedDyadicIncrements (E := E) T p (dyadicMomentWeight p r) L
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

omit [MeasurableSpace E] [BorelSpace E] in
/-- Uniform normalized dyadic moment bounds and bounded initial values imply
weak subsequence extraction for canonical laws. -/
theorem canonicalProperPath_subsequence_of_dyadic_moments (hT : 0 < T) (p A : ℝ) (r : ℝ≥0)
    (hp : 0 < p) (hr0 : 0 < r) (hr1 : r < 1)
    (Pn : ℕ → ProbabilityMeasure (CanonicalPath T E)) (C q : ℝ≥0∞)
    (hC : C ≠ ⊤) (hq : 2 * q < 1)
    (hstart : ∀ n, (Pn n : Measure (CanonicalPath T E))
      {f | A < ‖f (canonicalEvalTime T 0)‖} = 0)
    (hmoment : ∀ (n j : ℕ) (k : Fin (2 ^ j)),
      (∫⁻ f, properWeightedDyadicIncrement (E := E) T p (dyadicMomentWeight p r) j k f ∂(Pn n : Measure (CanonicalPath T E))) ≤
        C * q ^ j) :
    ∃ P : ProbabilityMeasure (CanonicalPath T E), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (Pn ∘ φ) atTop (𝓝 P) := by
  refine canonicalProperPath_subsequence_of_uniform_tightness Pn fun ε hε => ?_
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
  refine ⟨_, isCompact_properBoundedDyadicIncrements_start hT p A r L hp hr0 hr1, fun n => ?_⟩
  rw [compl_inter]
  refine (measure_union_le _ _).trans ?_
  have hzero : (Pn n : Measure (CanonicalPath T E))
      {f | ‖f (canonicalEvalTime T 0)‖ ≤ A}ᶜ = 0 := by
    simpa only [compl_ofPred, not_le] using hstart n
  rw [hzero, zero_add]
  exact (measure_properBoundedDyadicIncrements_compl_le hL0 ENNReal.coe_ne_top (hmoment n)).trans hsmall

omit [MeasurableSpace E] [BorelSpace E] in
/-- Geometrically decaying unweighted p-th moments of dyadic increments,
with rate strictly below one half, imply weak subsequence extraction. -/
theorem canonicalProperPath_subsequence_of_geometric_increment_moments (hT : 0 < T)
    (p A : ℝ) (hp : 0 < p)
    (Pn : ℕ → ProbabilityMeasure (CanonicalPath T E)) (C : ℝ≥0∞) (a : ℝ≥0)
    (hC : C ≠ ⊤) (ha : 2 * a < 1)
    (hstart : ∀ n, (Pn n : Measure (CanonicalPath T E))
      {f | A < ‖f (canonicalEvalTime T 0)‖} = 0)
    (hmoment : ∀ (n j : ℕ) (k : Fin (2 ^ j)),
      (∫⁻ f, properWeightedDyadicIncrement (E := E) T p (fun _ => 1) j k f ∂(Pn n : Measure (CanonicalPath T E))) ≤
        C * (a : ℝ≥0∞) ^ j) :
    ∃ P : ProbabilityMeasure (CanonicalPath T E), ∃ φ : ℕ → ℕ,
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
  refine canonicalProperPath_subsequence_of_dyadic_moments hT p A r hp hr0 hr1 Pn C q hC
    (by exact_mod_cast hq) hstart fun n j k => ?_
  have hw : dyadicMomentWeight p r j = (b⁻¹) ^ j := by
    unfold dyadicMomentWeight
    rw [← NNReal.rpow_natCast_mul, mul_comm, NNReal.rpow_mul_natCast, hrp, inv_pow]
  let F := properWeightedDyadicIncrement (E := E) T p (fun _ => 1) j k
  have hchange (f : CanonicalPath T E) :
      properWeightedDyadicIncrement (E := E) T p (dyadicMomentWeight p r) j k f =
        ((dyadicMomentWeight p r j : ℝ≥0) : ℝ≥0∞) * F f := by
    simp [F, properWeightedDyadicIncrement]
  simp only [hchange]
  rw [lintegral_const_mul _ (show Measurable F from
    (continuous_properWeightedDyadicIncrement (E := E) T p (fun _ => 1) j k).measurable)]
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

omit [MeasurableSpace E] [BorelSpace E] in
/-- Kolmogorov's tightness implication for canonical valued in a proper normed space paths with
bounded initial values and a uniform moment exponent greater than one. -/
theorem canonicalProperPath_subsequence_of_increment_moments (hT : 0 < T)
    (p β A : ℝ) (hp : 0 < p) (hβ : 1 < β)
    (Pn : ℕ → ProbabilityMeasure (CanonicalPath T E)) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hstart : ∀ n, (Pn n : Measure (CanonicalPath T E))
      {f | A < ‖f (canonicalEvalTime T 0)‖} = 0)
    (hmoment : ∀ (n : ℕ) (s t : CanonicalPathTime T),
      (∫⁻ f : CanonicalPath T E, edist (f s) (f t) ^ p ∂(Pn n : Measure (CanonicalPath T E))) ≤ C * edist s t ^ β) :
    ∃ P : ProbabilityMeasure (CanonicalPath T E), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (Pn ∘ φ) atTop (𝓝 P) := by
  let a : ℝ≥0 := (2 : ℝ≥0) ^ (-β)
  have ha : 2 * a < 1 := by
    have h := NNReal.rpow_lt_rpow_of_exponent_lt (show (1 : ℝ≥0) < 2 by norm_num)
      (show -β < (-1 : ℝ) by linarith)
    change a < (2 : ℝ≥0) ^ (-1 : ℝ) at h
    rw [NNReal.rpow_neg_one] at h
    rw [mul_comm]
    exact (lt_div_iff₀ (show (0 : ℝ≥0) < 2 by norm_num)).1 (by simpa only [one_div] using h)
  refine canonicalProperPath_subsequence_of_geometric_increment_moments hT p A hp Pn
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
  simpa only [properWeightedDyadicIncrement, ENNReal.coe_one, one_mul, s, t, G, canonicalPathEval] using hm

#print axioms RoughHeston.canonicalProperPath_subsequence_of_increment_moments

end RoughHeston
