import CanonicalSeparation

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace RoughHeston

variable {Ω ι : Type*}

private noncomputable def clusterEventIndicator (A : Set Ω) : Ω → ℝ :=
  A.indicator (fun _ => 1)

/-- Number of cluster events that occur, viewed as a real random variable. -/
noncomputable def clusterEventCount (F : Finset ι) (E : ι → Set Ω) (ω : Ω) : ℝ :=
  ∑ i ∈ F, clusterEventIndicator (E i) ω

private theorem clusterEventIndicator_nonneg (A : Set Ω) (ω : Ω) :
    0 ≤ clusterEventIndicator A ω := by
  classical
  by_cases h : ω ∈ A <;> simp [clusterEventIndicator, h]

theorem clusterEventCount_nonneg (F : Finset ι) (E : ι → Set Ω) (ω : Ω) :
    0 ≤ clusterEventCount F E ω :=
  Finset.sum_nonneg fun i _ => clusterEventIndicator_nonneg (E i) ω

theorem clusterEventCount_pos_iff (F : Finset ι) (E : ι → Set Ω) (ω : Ω) :
    0 < clusterEventCount F E ω ↔ ∃ i ∈ F, ω ∈ E i := by
  classical
  constructor
  · intro hp
    by_contra! hn
    have hz : clusterEventCount F E ω = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [clusterEventIndicator, hn i hi]
    exact (ne_of_gt hp) hz
  · rintro ⟨i, hi, hω⟩
    have hsum : clusterEventIndicator (E i) ω ≤ clusterEventCount F E ω :=
      Finset.single_le_sum (f := fun j => clusterEventIndicator (E j) ω)
        (fun j _ => clusterEventIndicator_nonneg (E j) ω) hi
    exact (by simp [clusterEventIndicator, hω] :
      0 < clusterEventIndicator (E i) ω).trans_le hsum

section Moments

variable [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

private theorem clusterEventIndicator_memLp (A : Set Ω) (hA : MeasurableSet A) :
    MemLp (clusterEventIndicator A) 2 μ :=
  (memLp_const (1 : ℝ)).indicator hA.nullMeasurableSet

theorem measurable_clusterEventCount (F : Finset ι) (E : ι → Set Ω)
    (hmE : ∀ i ∈ F, MeasurableSet (E i)) :
    Measurable (clusterEventCount F E) :=
  Finset.measurable_fun_sum F (fun i hi => measurable_const.indicator (hmE i hi))

theorem memLp_clusterEventCount (F : Finset ι) (E : ι → Set Ω)
    (hmE : ∀ i ∈ F, MeasurableSet (E i)) :
    MemLp (clusterEventCount F E) 2 μ :=
  memLp_finsetSum F (fun i hi => clusterEventIndicator_memLp (E i) (hmE i hi))

omit [MeasurableSpace Ω] in
private theorem clusterEventIndicator_mul (A B : Set Ω) (ω : Ω) :
    clusterEventIndicator A ω * clusterEventIndicator B ω = clusterEventIndicator (A ∩ B) ω := by
  classical
  by_cases ha : ω ∈ A <;> by_cases hb : ω ∈ B <;>
    simp [clusterEventIndicator, ha, hb]

omit [IsFiniteMeasure μ] in
private theorem integral_clusterEventIndicator (A : Set Ω) (hA : MeasurableSet A) :
    (∫ ω, clusterEventIndicator A ω ∂μ) = μ.real A :=
  integral_indicator_one hA

/-- The first moment of the count is the sum of the individual probabilities. -/
theorem integral_clusterEventCount (F : Finset ι) (E : ι → Set Ω)
    (hmE : ∀ i ∈ F, MeasurableSet (E i)) :
    (∫ ω, clusterEventCount F E ω ∂μ) = ∑ i ∈ F, μ.real (E i) := by
  unfold clusterEventCount
  rw [integral_finsetSum F
    (fun i hi => (clusterEventIndicator_memLp (E i) (hmE i hi)).integrable (by norm_num))]
  exact Finset.sum_congr rfl (fun i hi => integral_clusterEventIndicator (E i) (hmE i hi))

/-- The second moment is the first moment plus the sum of pair intersection
probabilities over ordered distinct pairs. -/
theorem integral_clusterEventCount_sq [DecidableEq ι] (F : Finset ι) (E : ι → Set Ω)
    (hmE : ∀ i ∈ F, MeasurableSet (E i)) :
    (∫ ω, clusterEventCount F E ω ^ 2 ∂μ) =
      (∫ ω, clusterEventCount F E ω ∂μ) + ∑ i ∈ F, ∑ j ∈ F.erase i, μ.real (E i ∩ E j) := by
  have hexpand (ω : Ω) : clusterEventCount F E ω ^ 2 =
      ∑ i ∈ F, ∑ j ∈ F, clusterEventIndicator (E i ∩ E j) ω := by
    simp only [clusterEventCount, pow_two, Finset.sum_mul, Finset.mul_sum, clusterEventIndicator_mul]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [inter_comm]
  simp_rw [hexpand]
  rw [integral_finsetSum F (fun i hi => integrable_finsetSum F (fun j hj =>
    (clusterEventIndicator_memLp (E i ∩ E j) ((hmE i hi).inter (hmE j hj))).integrable
      (by norm_num))), integral_clusterEventCount F E hmE, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum F (fun j hj =>
    (clusterEventIndicator_memLp (E i ∩ E j) ((hmE i hi).inter (hmE j hj))).integrable
      (by norm_num))]
  have hs : (∑ j ∈ F, ∫ ω, clusterEventIndicator (E i ∩ E j) ω ∂μ) =
      ∑ j ∈ F, μ.real (E i ∩ E j) :=
    Finset.sum_congr rfl (fun j hj => integral_clusterEventIndicator _ ((hmE i hi).inter (hmE j hj)))
  rw [hs, ← Finset.sum_erase_add F (fun j => μ.real (E i ∩ E j)) hi, inter_self, add_comm]

end Moments

/-- Event probabilities of order `ε`, pair intersection probabilities at
most of order `ε²`, and a cluster count of order `1/ε` give uniform
first and second moment bounds. The first moment's upper bound follows from
the second moment identity and Cauchy–Schwarz. -/
theorem clusterEventCount_uniform_moment_bounds [MeasurableSpace Ω] [DecidableEq ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (F : Finset ι) (E : ι → Set Ω)
    (hmE : ∀ i ∈ F, MeasurableSet (E i)) {ε c C L U : ℝ}
    (hε : 0 ≤ ε) (hc : 0 < c) (hC : 0 ≤ C) (hU : 0 ≤ U)
    (hsize₁ : L ≤ (F.card : ℝ) * ε) (hsize₂ : (F.card : ℝ) * ε ≤ U)
    (hsingle : ∀ i ∈ F, c * ε ≤ μ.real (E i))
    (hpair : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → μ.real (E i ∩ E j) ≤ C * ε ^ 2) :
    c * L ≤ (∫ ω, clusterEventCount F E ω ∂μ) ∧
      (∫ ω, clusterEventCount F E ω ^ 2 ∂μ) ≤ 1 + 2 * C * U ^ 2 := by
  let first : ℝ := ∫ ω, clusterEventCount F E ω ∂μ
  let second : ℝ := ∫ ω, clusterEventCount F E ω ^ 2 ∂μ
  let D := C * U ^ 2
  have hD : 0 ≤ D := mul_nonneg hC (sq_nonneg _)
  have hfirst : c * L ≤ first := by
    calc
      c * L ≤ c * ((F.card : ℝ) * ε) := mul_le_mul_of_nonneg_left hsize₁ hc.le
      _ = ∑ i ∈ F, c * ε := by simp; ring
      _ ≤ first := by
        dsimp only [first]
        rw [integral_clusterEventCount F E hmE]
        exact Finset.sum_le_sum hsingle
  have hoff : (∑ i ∈ F, ∑ j ∈ F.erase i, μ.real (E i ∩ E j)) ≤ D := by
    calc
      _ ≤ ∑ i ∈ F, ∑ j ∈ F.erase i, C * ε ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact hpair i hi j (Finset.mem_erase.mp hj).2 (Finset.mem_erase.mp hj).1.symm
      _ ≤ ∑ i ∈ F, ∑ j ∈ F, C * ε ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun _ _ _ => mul_nonneg hC (sq_nonneg _))
      _ = C * ((F.card : ℝ) * ε)^2 := by simp; ring
      _ ≤ D := mul_le_mul_of_nonneg_left
        (sq_le_sq' ((neg_nonpos.mpr hU).trans (mul_nonneg (Nat.cast_nonneg _) hε)) hsize₂) hC
  have hsecond : second ≤ first + D := by
    dsimp only [second]
    rw [integral_clusterEventCount_sq F E hmE]
    exact add_le_add (le_refl first) hoff
  have hsq : first ^ 2 ≤ second := by
    refine (second_moment_support (measurable_clusterEventCount F E hmE)
      (clusterEventCount_nonneg F E) (memLp_clusterEventCount (μ := μ) F E hmE)).trans ?_
    exact mul_le_of_le_one_right (integral_nonneg (fun ω => sq_nonneg (clusterEventCount F E ω)))
      measureReal_le_one
  have hfirstUpper : first ≤ 1 + D := by
    by_contra! h
    have hf : 1 ≤ first := by linarith
    have hprod := mul_le_mul_of_nonneg_right hf (show 0 ≤ first - 1 by linarith)
    nlinarith only [hprod, hsq, hsecond, h]
  refine ⟨hfirst, ?_⟩
  have hfinal : second ≤ 1 + 2 * D := by linarith only [hsecond, hfirstUpper]
  simpa only [D, mul_assoc] using hfinal

/-- A uniform positive lower bound on the union of selected cluster events. -/
theorem clusterEventUnion_uniform_probability_bound [MeasurableSpace Ω] [DecidableEq ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (F : Finset ι) (E : ι → Set Ω)
    (hmE : ∀ i ∈ F, MeasurableSet (E i)) {ε c C L U : ℝ}
    (hε : 0 ≤ ε) (hc : 0 < c) (hC : 0 ≤ C) (hL : 0 < L) (hU : 0 ≤ U)
    (hsize₁ : L ≤ (F.card : ℝ) * ε) (hsize₂ : (F.card : ℝ) * ε ≤ U)
    (hsingle : ∀ i ∈ F, c * ε ≤ μ.real (E i))
    (hpair : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → μ.real (E i ∩ E j) ≤ C * ε ^ 2) :
    ENNReal.ofReal ((c * L)^2 / (1 + 2 * C * U^2)) ≤ μ {ω | ∃ i ∈ F, ω ∈ E i} := by
  obtain ⟨hfirst, hsecond⟩ := clusterEventCount_uniform_moment_bounds F E hmE
    hε hc hC hU hsize₁ hsize₂ hsingle hpair
  have hcs := second_moment_support (measurable_clusterEventCount F E hmE)
    (clusterEventCount_nonneg F E) (memLp_clusterEventCount (μ := μ) F E hmE)
  have hreal := (count_lower_bound (mul_pos hc hL) (by positivity)
    hfirst hsecond ENNReal.toReal_nonneg hcs).2
  have hsupport : {ω | 0 < clusterEventCount F E ω} = {ω | ∃ i ∈ F, ω ∈ E i} :=
    Set.ext (clusterEventCount_pos_iff F E)
  rw [← hsupport]
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr hreal

/-- A uniform single-cluster lower bound and distinct-cluster upper bound
force positive separation in the canonical weak limit. The cluster events
may live on the approximating spaces, and only the pair paths are pushed
forward to the canonical space. -/
theorem canonicalPairDifferent_of_cluster_event_bounds [DecidableEq ι] {T : ℝ≥0}
    {Ωn : ℕ → Type*} [∀ n, MeasurableSpace (Ωn n)] {μn : ∀ n, Measure (Ωn n)}
    [∀ n, IsProbabilityMeasure (μn n)]
    {Pn : ℕ → ProbabilityMeasure (CanonicalPath T (ℝ × ℝ))}
    {P : ProbabilityMeasure (CanonicalPath T (ℝ × ℝ))}
    (hweak : Tendsto Pn atTop (𝓝 P)) {path : ∀ n, Ωn n → CanonicalPath T (ℝ × ℝ)}
    (hpathMeas : ∀ n, Measurable (path n))
    (hlaw : ∀ n, (Pn n : Measure (CanonicalPath T (ℝ × ℝ))) = Measure.map (path n) (μn n))
    (F : ℕ → Finset ι) (E : ∀ n, ι → Set (Ωn n))
    (hmE : ∀ n i, i ∈ F n → MeasurableSet (E n i))
    {ε : ℕ → ℝ} {c C L U ℓ : ℝ} (hε : ∀ n, 0 ≤ ε n)
    (hc : 0 < c) (hC : 0 ≤ C) (hL : 0 < L) (hU : 0 ≤ U) (hℓ : 0 < ℓ)
    (hsize₁ : ∀ n, L ≤ ((F n).card : ℝ) * ε n)
    (hsize₂ : ∀ n, ((F n).card : ℝ) * ε n ≤ U)
    (hsingle : ∀ n i, i ∈ F n → c * ε n ≤ (μn n).real (E n i))
    (hpair : ∀ n i, i ∈ F n → ∀ j, j ∈ F n → i ≠ j →
      (μn n).real (E n i ∩ E n j) ≤ C * (ε n)^2)
    (hgap : ∀ n i, i ∈ F n → ∀ ω ∈ E n i, ℓ ≤ canonicalPairGap T (path n ω)) :
    0 < (P : Measure (CanonicalPath T (ℝ × ℝ)))
      {q | ∃ t : ℝ≥0, t ≤ T ∧ (canonicalPathEval T t q).1 ≠ (canonicalPathEval T t q).2} := by
  have hp : 0 < ENNReal.ofReal ((c * L)^2 / (1 + 2 * C * U^2)) :=
    ENNReal.ofReal_pos.mpr (by positivity)
  refine canonicalPairDifferent_of_weak_limit hweak hℓ hp ?_
  intro n
  rw [hlaw n, Measure.map_apply (hpathMeas n) (isClosed_canonicalPairSeparation T ℓ).measurableSet]
  exact (clusterEventUnion_uniform_probability_bound (F n) (E n) (hmE n) (hε n)
    hc hC hL hU (hsize₁ n) (hsize₂ n) (hsingle n) (hpair n)).trans
      (measure_mono fun ω ⟨i, hi, hω⟩ => hgap n i hi ω hω)

#print axioms integral_clusterEventCount
#print axioms integral_clusterEventCount_sq
#print axioms clusterEventCount_uniform_moment_bounds
#print axioms clusterEventUnion_uniform_probability_bound
#print axioms canonicalPairDifferent_of_cluster_event_bounds

end RoughHeston
