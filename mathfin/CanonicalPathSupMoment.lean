import DyadicKolmogorov
import WeakLimitMomentTests

/-! Uniform moments of the supremum norm from dyadic increment bounds. -/

open Filter Set MeasureTheory
open scoped BigOperators ENNReal NNReal Topology

namespace RoughHeston

variable {T : ℝ≥0}

/-- Sum the normalized p-th powers of the increments over all dyadic edges. -/
noncomputable def dyadicIncrementPowerSum (T : ℝ≥0) (p : ℝ) (r : ℝ≥0)
    (f : CanonicalPath T (ℝ × ℝ)) : ℝ≥0∞ :=
  ∑' j : ℕ, ∑' k : Fin (2 ^ j), weightedDyadicIncrement T p (dyadicMomentWeight p r) j k f

theorem measurable_dyadicIncrementPowerSum (T : ℝ≥0) (p : ℝ) (r : ℝ≥0) :
    Measurable (dyadicIncrementPowerSum T p r) := by
  exact Measurable.tsum fun j => Measurable.tsum fun k =>
    (continuous_weightedDyadicIncrement T p (dyadicMomentWeight p r) j k).measurable

theorem lintegral_dyadicIncrementPowerSum_le {p : ℝ} {r : ℝ≥0}
    {μ : Measure (CanonicalPath T (ℝ × ℝ))} {C q : ℝ≥0∞}
    (hmoment : ∀ (j : ℕ) (k : Fin (2 ^ j)),
      (∫⁻ f, weightedDyadicIncrement T p (dyadicMomentWeight p r) j k f ∂μ) ≤ C * q ^ j) :
    (∫⁻ f, dyadicIncrementPowerSum T p r f ∂μ) ≤ C * (1 - 2 * q)⁻¹ := by
  have hm (j : ℕ) (k : Fin (2 ^ j)) :
      Measurable (weightedDyadicIncrement T p (dyadicMomentWeight p r) j k) :=
    (continuous_weightedDyadicIncrement T p (dyadicMomentWeight p r) j k).measurable
  unfold dyadicIncrementPowerSum
  rw [lintegral_tsum (fun j => (Measurable.tsum (hm j)).aemeasurable)]
  calc
    _ = ∑' j, ∑' k : Fin (2 ^ j),
        ∫⁻ f, weightedDyadicIncrement T p (dyadicMomentWeight p r) j k f ∂μ := by
      congr 1
      funext j
      exact lintegral_tsum fun k => (hm j k).aemeasurable
    _ ≤ ∑' j : ℕ, ∑' _ : Fin (2 ^ j), C * q ^ j :=
      ENNReal.tsum_le_tsum fun j => ENNReal.tsum_le_tsum (hmoment j)
    _ = ∑' j : ℕ, C * ((2 : ℝ≥0∞) * q) ^ j := by
      congr 1
      funext j
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, mul_pow]
      ac_rfl
    _ = _ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

private theorem dyadic_dist_le_of_weighted_le {p : ℝ} {r L : ℝ≥0} (hp : 0 < p) (hr : 0 < r)
    {f : CanonicalPath T (ℝ × ℝ)} (j : ℕ) (k : Fin (2 ^ j))
    (h : weightedDyadicIncrement T p (dyadicMomentWeight p r) j k f ≤ L) :
    dist (canonicalPathEval T ((uniformDyadicGrids T).grid j k) f)
      (canonicalPathEval T ((uniformDyadicGrids T).grid j (k + 1)) f) ≤
        (L ^ p⁻¹ : ℝ≥0) * (r : ℝ) ^ j := by
  let a := canonicalPathEval T ((uniformDyadicGrids T).grid j k) f
  let b := canonicalPathEval T ((uniformDyadicGrids T).grid j (k + 1)) f
  let z := nndist a b
  let R : ℝ≥0 := (r ^ j) ^ p
  have hR : 0 < R := NNReal.rpow_pos (pow_pos hr _)
  change (↑(R⁻¹) : ℝ≥0∞) * (edist a b) ^ p ≤ (L : ℝ≥0∞) at h
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

theorem norm_canonicalPath_le_of_dyadicIncrementPowerSum (hT : 0 < T) {p : ℝ}
    {r : ℝ≥0} (hp : 0 < p) (hr0 : 0 < r) (hr1 : r < 1)
    (f : CanonicalPath T (ℝ × ℝ)) (hf : dyadicIncrementPowerSum T p r f ≠ ⊤) :
    ‖f‖ ≤ ‖f (canonicalEvalTime T 0)‖ +
      (1 + 2 * (r : ℝ) / (1 - r)) * ((dyadicIncrementPowerSum T p r f).toNNReal ^ p⁻¹ : ℝ≥0) := by
  let L := (dyadicIncrementPowerSum T p r f).toNNReal
  have hL : (L : ℝ≥0∞) = dyadicIncrementPowerSum T p r f := ENNReal.coe_toNNReal hf
  have hedge (j : ℕ) (k : Fin (2 ^ j)) :
      weightedDyadicIncrement T p (dyadicMomentWeight p r) j k f ≤ (L : ℝ≥0∞) := by
    rw [hL]
    exact (ENNReal.le_tsum (f := fun k => weightedDyadicIncrement T p
      (dyadicMomentWeight p r) j k f) k).trans
      (ENNReal.le_tsum (f := fun j => ∑' k, weightedDyadicIncrement T p
        (dyadicMomentWeight p r) j k f) j)
  have hrR : (r : ℝ) < 1 := by exact_mod_cast hr1
  let : Nonempty (CanonicalPathTime T) := ⟨canonicalEvalTime T 0⟩
  apply (ContinuousMap.norm_le_of_nonempty f).2
  intro t
  have ht : dist t (canonicalEvalTime T 0) ≤ (T : ℝ) / (2 : ℝ) ^ 0 := by
    rw [pow_zero, div_one]
    change |(t.val : ℝ) - (↑(min (0 : ℝ≥0) T) : ℝ)| ≤ _
    rw [min_eq_left (zero_le : 0 ≤ T), NNReal.coe_zero, sub_zero,
      abs_of_nonneg (show 0 ≤ (t.val : ℝ) from t.val.property)]
    exact t.property.2
  have hm := canonicalPath_dyadic_modulus hT f (↑(L ^ p⁻¹ : ℝ≥0)) r (by positivity)
    r.property hrR (fun j k => dyadic_dist_le_of_weighted_le hp hr0 j k (hedge j k))
    0 t (canonicalEvalTime T 0) ht
  rw [pow_zero, mul_one] at hm
  have htri := dist_triangle (f t) (f (canonicalEvalTime T 0)) 0
  rw [dist_zero_right, dist_zero_right] at htri
  exact htri.trans ((add_le_add hm le_rfl).trans_eq (by
    simp only [L]
    ring))

private theorem rpow_inv_sq_le_one_add (p : ℝ) (hp : 2 ≤ p) (x : ℝ≥0) :
    ((x ^ p⁻¹ : ℝ≥0) : ℝ) ^ (2 : ℕ) ≤ 1 + (x : ℝ) := by
  have hp0 : 0 < p := by linarith
  have hx0 : 0 ≤ (x : ℝ) := x.property
  have hq : p⁻¹ * 2 ≤ 1 := by
    rw [mul_comm, ← div_eq_mul_inv, div_le_iff₀ hp0, one_mul]
    exact hp
  rw [NNReal.coe_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
  norm_num only [Nat.cast_ofNat]
  rcases le_total (x : ℝ) 1 with h | h
  · exact (Real.rpow_le_one hx0 h (by positivity)).trans (by linarith)
  · have hle := Real.rpow_le_rpow_of_exponent_le h hq
    rw [Real.rpow_one] at hle
    exact hle.trans (by linarith)

/-- Second moments of the path supremum are uniformly bounded under common
dyadic moment estimates. The input power can be any p at least two. -/
theorem uniform_canonicalPath_sup_sq_moment_of_dyadic_moments {I : Type*}
    (hT : 0 < T) (p A : ℝ) (r : ℝ≥0) (hp : 2 ≤ p) (hr0 : 0 < r) (hr1 : r < 1)
    (Pn : I → ProbabilityMeasure (CanonicalPath T (ℝ × ℝ))) (C q : ℝ≥0∞)
    (hC : C ≠ ⊤) (hq : 2 * q < 1)
    (hstart : ∀ i, (Pn i : Measure (CanonicalPath T (ℝ × ℝ)))
      {f | A < ‖f (canonicalEvalTime T 0)‖} = 0)
    (hmoment : ∀ (i : I) (j : ℕ) (k : Fin (2 ^ j)),
      (∫⁻ f, weightedDyadicIncrement T p (dyadicMomentWeight p r) j k f ∂(Pn i : Measure _)) ≤
        C * q ^ j) :
    ∃ M ≥ (0 : ℝ), ∀ i, MemLp (fun f : CanonicalPath T (ℝ × ℝ) => ‖f‖) 2 (Pn i : Measure _) ∧
      (∫ f : CanonicalPath T (ℝ × ℝ), ‖f‖ ^ 2 ∂(Pn i : Measure _)) ≤ M := by
  have hp0 : 0 < p := by linarith
  have hrR : (r : ℝ) < 1 := by exact_mod_cast hr1
  let J := dyadicIncrementPowerSum T p r
  let G : ℝ := 1 + 2 * (r : ℝ) / (1 - (r : ℝ))
  let c₀ : ℝ := 2 * A ^ 2 + 2 * G ^ 2
  let c₁ : ℝ := 2 * G ^ 2
  have hc₀ : 0 ≤ c₀ := by unfold c₀; positivity
  have hc₁ : 0 ≤ c₁ := by unfold c₁; positivity
  let B := C * (1 - 2 * q)⁻¹
  have hB : B ≠ ⊤ := ENNReal.mul_ne_top hC (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hq).ne')
  let E := ENNReal.ofReal c₀ + ENNReal.ofReal c₁ * B
  have hE : E ≠ ⊤ := ENNReal.add_ne_top.2
    ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB⟩
  refine ⟨E.toReal, ENNReal.toReal_nonneg, fun i => ?_⟩
  let μ : Measure (CanonicalPath T (ℝ × ℝ)) := Pn i
  let : IsProbabilityMeasure μ :=
    inferInstanceAs (IsProbabilityMeasure (Pn i : Measure (CanonicalPath T (ℝ × ℝ))))
  have hJm : Measurable J := measurable_dyadicIncrementPowerSum T p r
  have hJ : (∫⁻ f, J f ∂μ) ≤ B := lintegral_dyadicIncrementPowerSum_le (hmoment i)
  have hJfinite : ∀ᵐ f ∂μ, J f < ⊤ := ae_lt_top hJm (ne_top_of_le_ne_top hB hJ)
  have hstartAE : ∀ᵐ f ∂μ, ‖f (canonicalEvalTime T 0)‖ ≤ A := by
    rw [ae_iff]
    simpa only [not_le] using hstart i
  have hdom : ∀ᵐ f ∂μ, ENNReal.ofReal (‖f‖ ^ 2) ≤ ENNReal.ofReal c₀ + ENNReal.ofReal c₁ * J f := by
    filter_upwards [hJfinite, hstartAE] with f hfin h0
    let x : ℝ≥0 := (J f).toNNReal
    let y : ℝ := (x ^ p⁻¹ : ℝ≥0)
    have hnorm : ‖f‖ ≤ A + G * y :=
      (norm_canonicalPath_le_of_dyadicIncrementPowerSum hT hp0 hr0 hr1 f hfin.ne).trans
        (add_le_add h0 le_rfl)
    have hy : y ^ 2 ≤ 1 + (x : ℝ) := rpow_inv_sq_le_one_add p hp x
    have hsquare : ‖f‖ ^ 2 ≤ c₀ + c₁ * (J f).toReal := by
      calc
        _ ≤ (A + G * y) ^ 2 := pow_le_pow_left₀ (norm_nonneg f) hnorm 2
        _ ≤ 2 * A ^ 2 + (2 * G ^ 2) * y ^ 2 := by nlinarith [sq_nonneg (A - G * y)]
        _ ≤ 2 * A ^ 2 + (2 * G ^ 2) * (1 + (x : ℝ)) := by gcongr
        _ = _ := by
          rw [show (x : ℝ) = (J f).toReal from rfl]
          simp only [c₀, c₁]
          ring
    refine (ENNReal.ofReal_le_ofReal hsquare).trans_eq ?_
    rw [ENNReal.ofReal_add hc₀ (mul_nonneg hc₁ ENNReal.toReal_nonneg),
      ENNReal.ofReal_mul hc₁, ENNReal.ofReal_toReal hfin.ne]
  have hLin : (∫⁻ f, ENNReal.ofReal (‖f‖ ^ 2) ∂μ) ≤ E := by
    refine (lintegral_mono_ae hdom).trans ?_
    rw [lintegral_add_left measurable_const, lintegral_const_mul _ hJm, lintegral_const,
      measure_univ, mul_one]
    exact add_le_add le_rfl (mul_right_mono hJ)
  have hCont : Continuous (fun f : CanonicalPath T (ℝ × ℝ) => ‖f‖) := continuous_norm
  have hSq : Integrable (fun f : CanonicalPath T (ℝ × ℝ) => ‖f‖ ^ 2) μ :=
    ⟨(hCont.pow 2).measurable.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun f => sq_nonneg ‖f‖)).2
        (hLin.trans_lt (lt_top_iff_ne_top.2 hE))⟩
  refine ⟨(memLp_two_iff_integrable_sq hCont.measurable.aestronglyMeasurable).2 hSq, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hSq (Eventually.of_forall fun f => sq_nonneg ‖f‖),
    ← ENNReal.ofReal_toReal hE, ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg] at hLin
  exact hLin

private theorem edist_dyadicMoment_edge_time (j : ℕ) (k : Fin (2 ^ j)) :
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


/-- The geometric factors in the dyadic chaining bound depend only on
the exponent and the moment order. In particular, the prefactor in the
increment estimate is retained when it tends to zero with the mesh. -/
theorem canonical_dyadic_geometric_factors (p β : ℝ) (hp0 : 0<p) (hβ : 1<β) :
    ∃ r q : ℝ≥0, 0<r ∧ r<1 ∧ 2*q<1 ∧ ∀ (T : ℝ≥0) (μ : Measure (CanonicalPath T (ℝ × ℝ)))
      (C : ℝ≥0∞),
      (∀ s t : CanonicalPathTime T,
        (∫⁻ f : CanonicalPath T (ℝ × ℝ), edist (f s) (f t)^p ∂μ) ≤ C*edist s t^β) →
      ∀ j (k : Fin (2^j)),
        (∫⁻ f, weightedDyadicIncrement T p (dyadicMomentWeight p r) j k f ∂μ) ≤
          (C*(↑(T^β : ℝ≥0):ℝ≥0∞))*(q:ℝ≥0∞)^j := by
  let a : ℝ≥0 := (2 : ℝ≥0) ^ (-β)
  have ha : 2 * a < 1 := by
    have h := NNReal.rpow_lt_rpow_of_exponent_lt (show (1 : ℝ≥0) < 2 by norm_num)
      (show -β < (-1 : ℝ) by linarith)
    change a < (2 : ℝ≥0) ^ (-1 : ℝ) at h
    rw [NNReal.rpow_neg_one] at h
    rw [mul_comm]
    exact (lt_div_iff₀ (show (0 : ℝ≥0) < 2 by norm_num)).1 (by simpa only [one_div] using h)
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
  have hr1 : r < 1 := NNReal.rpow_lt_one hb1 (one_div_pos.mpr hp0)
  have hrp : r ^ p = b := NNReal.rpow_self_rpow_inv hp0.ne' b
  refine ⟨r,q,hr0,hr1,hq,?_⟩
  intro T μ C hmoment j k
  let C' : ℝ≥0∞ := C*(↑(T^β : ℝ≥0):ℝ≥0∞)
  have hw : dyadicMomentWeight p r j = (b⁻¹) ^ j := by
    unfold dyadicMomentWeight
    rw [← NNReal.rpow_natCast_mul, mul_comm, NNReal.rpow_mul_natCast, hrp, inv_pow]
  let G := uniformDyadicGrids T
  let s := canonicalEvalTime T (G.grid j k)
  let t := canonicalEvalTime T (G.grid j (k + 1))
  have hmesh : edist s t ^ β = (↑(T ^ β : ℝ≥0) : ℝ≥0∞) * (a : ℝ≥0∞) ^ j := by
    change edist (canonicalEvalTime T (G.grid j k))
      (canonicalEvalTime T (G.grid j (k + 1))) ^ β = _
    rw [edist_dyadicMoment_edge_time j k, ← ENNReal.coe_rpow_of_nonneg _ (by linarith : 0 ≤ β),
      ← ENNReal.coe_pow, ← ENNReal.coe_mul, ENNReal.coe_inj]
    rw [div_eq_mul_inv, NNReal.mul_rpow, ← inv_pow, ← NNReal.rpow_natCast_mul,
      mul_comm (j : ℝ) β, NNReal.rpow_mul_natCast, NNReal.inv_rpow]
    simp only [a, NNReal.rpow_neg]
  let F (f : CanonicalPath T (ℝ × ℝ)) : ℝ≥0∞ := edist (f s) (f t) ^ p
  have hF : Measurable F := (ENNReal.continuous_rpow_const.comp
    ((continuous_eval_const s).edist (continuous_eval_const t))).measurable
  change (∫⁻ f, (dyadicMomentWeight p r j : ℝ≥0∞) * F f ∂μ) ≤ _
  rw [lintegral_const_mul _ hF]
  have hm := hmoment s t
  rw [hmesh, ← mul_assoc] at hm
  calc
    _ ≤ (dyadicMomentWeight p r j : ℝ≥0∞) * (C' * (a : ℝ≥0∞) ^ j) :=
      mul_right_mono hm
    _ = C' * (q : ℝ≥0∞) ^ j := by
      rw [hw]
      push_cast [q, mul_pow]
      ac_rfl

/-- A uniform p-th increment moment bound with time exponent larger than one
gives a uniform second moment of the supremum norm. -/
theorem uniform_canonicalPath_sup_sq_moment {I : Type*} (hT : 0 < T)
    (p β A : ℝ) (hp : 2 ≤ p) (hβ : 1 < β)
    (Pn : I → ProbabilityMeasure (CanonicalPath T (ℝ × ℝ))) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hstart : ∀ i, (Pn i : Measure (CanonicalPath T (ℝ × ℝ)))
      {f | A < ‖f (canonicalEvalTime T 0)‖} = 0)
    (hmoment : ∀ (i : I) (s t : CanonicalPathTime T),
      (∫⁻ f : CanonicalPath T (ℝ × ℝ), edist (f s) (f t) ^ p ∂(Pn i : Measure _)) ≤
        C * edist s t ^ β) :
    ∃ M ≥ (0 : ℝ), ∀ i, MemLp (fun f : CanonicalPath T (ℝ × ℝ) => ‖f‖) 2 (Pn i : Measure _) ∧
      (∫ f : CanonicalPath T (ℝ × ℝ), ‖f‖ ^ 2 ∂(Pn i : Measure _)) ≤ M := by
  have hp0 : 0 < p := by linarith
  obtain ⟨r,q,hr0,hr1,hq,hdy⟩ := canonical_dyadic_geometric_factors p β hp0 hβ
  exact uniform_canonicalPath_sup_sq_moment_of_dyadic_moments hT p A r hp hr0 hr1 Pn
    (C*(↑(T^β : ℝ≥0):ℝ≥0∞)) q (ENNReal.mul_ne_top hC ENNReal.coe_ne_top)
    (by exact_mod_cast hq) hstart (fun i => hdy T (Pn i : Measure _) C (hmoment i))

/-- The same supremum-norm second-moment bound holds in a weak limit. -/
theorem weak_limit_canonicalPath_sup_sq_moment {I : Type*} {l : Filter I} [NeBot l]
    {Pn : I → ProbabilityMeasure (CanonicalPath T (ℝ × ℝ))}
    {P : ProbabilityMeasure (CanonicalPath T (ℝ × ℝ))}
    (hweak : Tendsto Pn l (𝓝 P)) {M : ℝ}
    (hbound : ∀ i, MemLp (fun f : CanonicalPath T (ℝ × ℝ) => ‖f‖) 2 (Pn i : Measure _) ∧
      (∫ f : CanonicalPath T (ℝ × ℝ), ‖f‖ ^ 2 ∂(Pn i : Measure _)) ≤ M) :
    MemLp (fun f : CanonicalPath T (ℝ × ℝ) => ‖f‖) 2 (P : Measure _) ∧
      (∫ f : CanonicalPath T (ℝ × ℝ), ‖f‖ ^ 2 ∂(P : Measure _)) ≤ M :=
  weak_limit_memLp_two_and_sq_moment_bound hweak continuous_norm
    (fun i => (hbound i).1) (fun i => (hbound i).2)

#print axioms uniform_canonicalPath_sup_sq_moment_of_dyadic_moments
#print axioms uniform_canonicalPath_sup_sq_moment
#print axioms weak_limit_canonicalPath_sup_sq_moment

end RoughHeston

#print axioms RoughHeston.canonical_dyadic_geometric_factors
