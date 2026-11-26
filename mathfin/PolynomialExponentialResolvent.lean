import PositiveExponentialResolvent
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Roots

open Set Filter Polynomial
open scoped Topology BigOperators Polynomial

namespace RoughHeston

/-- Common numerator and denominator of the rational Laplace transform. -/
noncomputable def exponentialLaplaceDenominator {ι : Type*} (F : Finset ι) (x : ι → ℝ) : ℝ[X] :=
  ∏ i ∈ F, (X + C (x i))

noncomputable def exponentialLaplaceNumerator {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (c x : ι → ℝ) : ℝ[X] :=
  ∑ i ∈ F, C (c i) * exponentialLaplaceDenominator (F.erase i) x

theorem exponentialLaplaceNumerator_eval {ι : Type*} [DecidableEq ι] (F : Finset ι)
    (c x : ι → ℝ) (z : ℝ) (hz : ∀ i ∈ F, z + x i ≠ 0) :
    (exponentialLaplaceNumerator F c x).eval z =
      (exponentialLaplaceDenominator F x).eval z * exponentialMixtureLaplace F c x z := by
  simp only [exponentialLaplaceNumerator, exponentialLaplaceDenominator, exponentialMixtureLaplace,
    eval_finsetSum, eval_prod, eval_add, eval_X, eval_C, eval_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← F.mul_prod_erase (fun j => z + x j) hi]
  field_simp [hz i hi]

/-- The real roots in the consecutive pole intervals are distinct. -/
theorem exponentialMixtureLaplace_ordered_roots {n : ℕ} {c x : Fin (n + 1) → ℝ}
    (hc : ∀ i, 0 < c i) (hx : StrictMono x) :
    ∃ r : Fin n → ℝ, StrictAnti r ∧ ∀ i,
      r i ∈ Ioo (-x i.succ) (-x i.castSucc) ∧ exponentialMixtureLaplace Finset.univ c x (r i) = 0 := by
  have hanti (i : Fin n) : -x i.succ < -x i.castSucc := by
    exact neg_lt_neg (hx (show i.castSucc < i.succ from Nat.lt_succ_self i.val))
  have hnone (i : Fin n) (k : Fin (n + 1)) : -x k ∉ Ioo (-x i.succ) (-x i.castSucc) := by
    intro h
    have h₁ : i.castSucc < k := hx.lt_iff_lt.mp (neg_lt_neg_iff.mp h.2)
    have h₂ : k < i.succ := hx.lt_iff_lt.mp (neg_lt_neg_iff.mp h.1)
    change i.val < k.val at h₁
    change k.val < i.val + 1 at h₂
    omega
  have hex (i : Fin n) : ∃ r,
      r ∈ Ioo (-x i.succ) (-x i.castSucc) ∧ exponentialMixtureLaplace Finset.univ c x r = 0 :=
    (exponentialMixtureLaplace_interlaces (Finset.mem_univ i.succ) (Finset.mem_univ i.castSucc)
      (fun k _ => hc k) hx.injective.injOn (hanti i) (fun k _ => hnone i k)).exists
  choose r hr using hex
  refine ⟨r, ?_, hr⟩
  intro i j hij
  have hle : i.succ ≤ j.castSucc := Nat.succ_le_of_lt hij
  exact (hr j).1.2.trans (((neg_le_neg (hx.monotone hle))).trans_lt (hr i).1.1)

private theorem exponentialLaplaceNumerator_natDegree_le {n : ℕ} (c x : Fin (n + 1) → ℝ) :
    (exponentialLaplaceNumerator Finset.univ c x).natDegree ≤ n := by
  unfold exponentialLaplaceNumerator
  apply natDegree_sum_le_of_forall_le
  intro i hi
  apply (natDegree_C_mul_le _ _).trans
  unfold exponentialLaplaceDenominator
  exact (natDegree_prod_le _ _).trans (by simp [Finset.card_erase_of_mem hi])

/-- The numerator splits into the consecutive simple real roots. -/
theorem exponentialLaplaceNumerator_factorization {n : ℕ} {c x : Fin (n + 1) → ℝ}
    (hc : ∀ i, 0 < c i) (hx₀ : ∀ i, 0 < x i) (hx : StrictMono x) :
    ∃ r : Fin n → ℝ, StrictAnti r ∧
      (∀ i, r i ∈ Ioo (-x i.succ) (-x i.castSucc) ∧
        exponentialMixtureLaplace Finset.univ c x (r i) = 0) ∧
      exponentialLaplaceNumerator Finset.univ c x =
        C (exponentialLaplaceNumerator Finset.univ c x).leadingCoeff * ∏ i, (X - C (r i)) := by
  classical
  obtain ⟨r, hr, hrz⟩ := exponentialMixtureLaplace_ordered_roots hc hx
  let N := exponentialLaplaceNumerator Finset.univ c x
  let S := Finset.univ.image r
  have hN : N ≠ 0 := by
    have hpos : 0 < N.eval 0 := by
      rw [exponentialLaplaceNumerator_eval Finset.univ c x 0 (fun i _ => by simpa only [zero_add] using (hx₀ i).ne')]
      apply mul_pos
      · simp only [exponentialLaplaceDenominator, eval_prod, eval_add, eval_X, eval_C, zero_add]
        exact Finset.prod_pos fun i _ => hx₀ i
      · simp only [exponentialMixtureLaplace, zero_add]
        exact Finset.sum_pos (fun i _ => div_pos (hc i) (hx₀ i)) Finset.univ_nonempty
    intro hz
    simp only [hz, eval_zero, lt_self_iff_false] at hpos
  have hfree (i : Fin n) (j : Fin (n + 1)) : r i + x j ≠ 0 := by
    intro h
    have hrj : r i = -x j := by linarith
    have hi := (hrz i).1
    rw [hrj] at hi
    have h₁ : i.castSucc < j := hx.lt_iff_lt.mp (neg_lt_neg_iff.mp hi.2)
    have h₂ : j < i.succ := hx.lt_iff_lt.mp (neg_lt_neg_iff.mp hi.1)
    change i.val < j.val at h₁
    change j.val < i.val + 1 at h₂
    omega
  have hS : S.1 ≤ N.roots := by
    apply Finset.val_le_iff_val_subset.2
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_def.mpr ha)
    apply (Polynomial.mem_roots hN).2
    change N.eval (r i) = 0
    rw [exponentialLaplaceNumerator_eval Finset.univ c x _ (fun j _ => hfree i j), (hrz i).2, mul_zero]
  have hScard : S.card = n := by
    rw [Finset.card_image_of_injective Finset.univ hr.injective, Finset.card_univ, Fintype.card_fin]
  have hcard : N.roots.card = N.natDegree := by
    have hlo := Multiset.card_le_card hS
    change S.card ≤ N.roots.card at hlo
    rw [hScard] at hlo
    have hhi := exponentialLaplaceNumerator_natDegree_le c x
    exact le_antisymm N.card_roots' (hhi.trans hlo)
  have hroot_eq : N.roots = S.1 := by
    symm
    apply Multiset.eq_of_le_of_card_le hS
    change N.roots.card ≤ S.card
    rw [hScard, hcard]
    exact exponentialLaplaceNumerator_natDegree_le c x
  refine ⟨r, hr, hrz, ?_⟩
  calc
    N = C N.leadingCoeff * (N.roots.map (fun a => X - C a)).prod :=
      (C_leadingCoeff_mul_prod_multiset_X_sub_C hcard).symm
    _ = C N.leadingCoeff * ∏ i, (X - C (r i)) := by
      rw [hroot_eq]
      congr 1
      change (∏ a ∈ S, (X - C a)) = ∏ i, (X - C (r i))
      exact Finset.prod_image hr.injective.injOn

/-- The reciprocal of the smooth transform has a constant term and one
simple fraction at each interlacing root and at zero. -/
theorem exponentialMixtureLaplace_partialFractions {n : ℕ} {c x : Fin (n + 1) → ℝ}
    (hc : ∀ i, 0 < c i) (hx₀ : ∀ i, 0 < x i) (hx : StrictMono x) :
    ∃ (r : Option (Fin n) → ℝ) (a : ℝ) (w : Option (Fin n) → ℝ),
      r none = 0 ∧ Function.Injective r ∧
      (∀ i, r (some i) ∈ Ioo (-x i.succ) (-x i.castSucc) ∧
        exponentialMixtureLaplace Finset.univ c x (r (some i)) = 0) ∧
      (∀ z : ℝ, (∀ i, z + x i ≠ 0) → (∀ i, z ≠ r i) →
        1 / (z * exponentialMixtureLaplace Finset.univ c x z) =
          a + ∑ i, w i / (z - r i)) := by
  classical
  obtain ⟨r₀, hr₀, hbetween, hN⟩ := exponentialLaplaceNumerator_factorization hc hx₀ hx
  let r : Option (Fin n) → ℝ := fun i => i.elim 0 r₀
  have hrneg (i : Fin n) : r₀ i < 0 := (hbetween i).1.2.trans (neg_neg_of_pos (hx₀ _))
  have hr : Function.Injective r := by
    intro i j he
    cases i <;> cases j
    · rfl
    · exfalso
      exact (hrneg _).ne he.symm
    · exfalso
      exact (hrneg _).ne he
    · exact congrArg some (hr₀.injective he)
  let D := exponentialLaplaceDenominator Finset.univ x
  let N := exponentialLaplaceNumerator Finset.univ c x
  let g (i : Option (Fin n)) : ℝ[X] := X - C (r i)
  let Q := ∏ i, g i
  have hQ : X * N = C N.leadingCoeff * Q := by
    change X * N = C N.leadingCoeff * (∏ i, g i)
    rw [Fintype.prod_option]
    change X * N = C N.leadingCoeff * ((X - C (0 : ℝ)) * ∏ i : Fin n, (X - C (r₀ i)))
    rw [map_zero, sub_zero]
    have hN' : N = C N.leadingCoeff * ∏ i, (X - C (r₀ i)) := hN
    conv_lhs => rw [hN']
    ac_rfl
  have hg (i : Option (Fin n)) : (g i).Monic := monic_X_sub_C _
  have hcop : Set.Pairwise (↑(Finset.univ : Finset (Option (Fin n)))) (fun i j => IsCoprime (g i) (g j)) := by
    intro i _ j _ hij
    exact isCoprime_X_sub_C_of_isUnit_sub ((sub_ne_zero.mpr (hr.ne hij)).isUnit)
  obtain ⟨q, u, hu, hD⟩ := eq_quo_mul_prod_add_sum_rem_mul_prod D (fun i _ => hg i) hcop
  let U := ∑ i : Option (Fin n), u i * ∏ j ∈ (Finset.univ : Finset (Option (Fin n))).erase i, g j
  have hdegU (i : Option (Fin n)) : (u i).natDegree = 0 := by
    by_cases hi : u i = 0
    · simp [hi]
    have h₁ := hu i (Finset.mem_univ i)
    change (u i).degree < (X - C (r i)).degree at h₁
    rw [degree_X_sub_C, degree_eq_natDegree hi] at h₁
    exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (WithBot.coe_lt_coe.mp h₁))
  have hdegQ : Q.natDegree = n + 1 := by
    change (∏ i, g i).natDegree = n + 1
    rw [natDegree_prod_of_monic _ _ (fun i _ => hg i)]
    simp [g]
  have hQ₀ : Q ≠ 0 := by
    change (∏ i, g i) ≠ 0
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => (hg i).ne_zero)
  have hdegD : D.natDegree ≤ n + 1 := by
    unfold D exponentialLaplaceDenominator
    exact (natDegree_prod_le _ _).trans (by simp)
  have hdegU' : U.natDegree ≤ n := by
    unfold U
    apply natDegree_sum_le_of_forall_le
    intro i hi
    apply natDegree_mul_le.trans
    rw [hdegU i, zero_add]
    refine (natDegree_prod_le _ _).trans ?_
    simp [g, Finset.card_erase_of_mem hi]
  have hqU : q * Q = D - U := by
    have hD' : D = q * Q + U := hD
    rw [hD', add_sub_cancel_right]
  have hq : q = C (q.coeff 0) := by
    apply eq_C_of_natDegree_le_zero
    by_cases hq₀ : q = 0
    · simp [hq₀]
    have hdeg := natDegree_sub_le_of_le hdegD (hdegU'.trans (Nat.le_succ n))
    rw [← hqU, natDegree_mul hq₀ hQ₀, hdegQ] at hdeg
    omega
  have huC (i : Option (Fin n)) : u i = C ((u i).coeff 0) :=
    eq_C_of_natDegree_le_zero (hdegU i).le
  refine ⟨r, q.coeff 0 / N.leadingCoeff, fun i => (u i).coeff 0 / N.leadingCoeff,
    rfl, hr, hbetween, ?_⟩
  intro z hz hzr
  have hQz : Q.eval z ≠ 0 := by
    change (∏ i, g i).eval z ≠ 0
    rw [eval_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => by simpa [g] using sub_ne_zero.mpr (hzr i))
  have hDz : D.eval z ≠ 0 := by
    simp only [D, exponentialLaplaceDenominator, eval_prod, eval_add, eval_X, eval_C]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hz i)
  have hLC : N.leadingCoeff ≠ 0 := by
    intro hL
    have hn : N = 0 := leadingCoeff_eq_zero.mp hL
    have hp : 0 < N.eval 0 := by
      rw [exponentialLaplaceNumerator_eval _ _ _ _ (fun i _ => by simp [(hx₀ i).ne'])]
      apply mul_pos
      · simp only [exponentialLaplaceDenominator, eval_prod, eval_add, eval_X, eval_C, zero_add]
        exact Finset.prod_pos (fun i _ => hx₀ i)
      · simp only [exponentialMixtureLaplace, zero_add]
        exact Finset.sum_pos (fun i _ => div_pos (hc i) (hx₀ i)) Finset.univ_nonempty
    simp only [hn, eval_zero, lt_self_iff_false] at hp
  have hevalN : N.eval z = D.eval z * exponentialMixtureLaplace Finset.univ c x z :=
    exponentialLaplaceNumerator_eval _ _ _ z (fun i _ => hz i)
  have hevalQ : z * N.eval z = N.leadingCoeff * Q.eval z := by
    simpa only [eval_mul, eval_X, eval_C] using congrArg (Polynomial.eval z) hQ
  have hformula : 1 / (z * exponentialMixtureLaplace Finset.univ c x z) =
      D.eval z / (N.leadingCoeff * Q.eval z) := by
    rw [← hevalQ, hevalN, mul_left_comm z (D.eval z)]
    simpa only [mul_one] using (mul_div_mul_left (1 : ℝ)
      (z * exponentialMixtureLaplace Finset.univ c x z) hDz).symm
  rw [hformula]
  have hevalD : D.eval z = q.coeff 0 * Q.eval z +
      ∑ i : Option (Fin n), (u i).coeff 0 * (∏ j ∈ (Finset.univ : Finset (Option (Fin n))).erase i, g j).eval z := by
    have hl (i : Option (Fin n)) : (u i).eval z = (u i).coeff 0 := by
      conv_lhs => rw [huC i]
      exact eval_C
    have hqz : q.eval z = q.coeff 0 := by
      conv_lhs => rw [hq]
      exact eval_C
    simpa only [eval_add, eval_mul, eval_finsetSum, hqz, hl] using congrArg (Polynomial.eval z) hD
  rw [hevalD, add_div, Finset.sum_div]
  congr 1
  · field_simp [hLC, hQz]
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hpc : Q.eval z = (z - r i) * (∏ j ∈ (Finset.univ : Finset (Option (Fin n))).erase i, g j).eval z := by
      change (∏ j, g j).eval z = _
      rw [← Finset.mul_prod_erase _ _ hi, eval_mul]
      simp [g]
    rw [hpc] at hQz ⊢
    have htail := (mul_ne_zero_iff.mp hQz).2
    field_simp [hLC, sub_ne_zero.mpr (hzr i), htail]

private theorem simpleFraction_tendsto_coefficient {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r w : ι → ℝ) (a : ℝ) (hr : Function.Injective r) (i : ι) :
    Tendsto (fun z => (z - r i) * (a + ∑ j, w j / (z - r j))) (𝓝[≠] r i) (𝓝 (w i)) := by
  let S (z : ℝ) := a + ∑ j ∈ (Finset.univ : Finset ι).erase i, w j / (z - r j)
  have hS : ContinuousAt S (r i) := by
    have hh (j : ι) (hj : j ∈ (Finset.univ : Finset ι).erase i) :
        ContinuousAt (fun z : ℝ => w j / (z - r j)) (r i) :=
      continuousAt_const.div (continuous_id.sub continuous_const).continuousAt
        (sub_ne_zero.mpr (hr.ne (Finset.mem_erase.mp hj).1.symm))
    exact (tendsto_finsetSum _ (fun j hj => (hh j hj).tendsto)).const_add a
  have hd : Tendsto (fun z => z - r i) (𝓝[≠] r i) (𝓝 (0 : ℝ)) := by
    have ht : ContinuousAt (fun z : ℝ => z - r i) (r i) := (continuous_id.sub continuous_const).continuousAt
    simpa only [sub_self] using ht.tendsto.mono_left nhdsWithin_le_nhds
  have h := (hd.mul (hS.tendsto.mono_left nhdsWithin_le_nhds)).const_add (w i)
  have hlim : Tendsto (fun z => w i + (z - r i) * S z) (𝓝[≠] r i) (𝓝 (w i)) := by
    simpa only [zero_mul, add_zero] using h
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  change z ≠ r i at hz
  change w i + (z - r i) * (a + ∑ j ∈ (Finset.univ : Finset ι).erase i, w j / (z - r j)) =
    (z - r i) * (a + ∑ j, w j / (z - r j))
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hcancel : (z - r i) * (w i / (z - r i)) = w i := by field_simp [sub_ne_zero.mpr hz]
  rw [mul_add, mul_add, mul_add, hcancel]
  ac_rfl

/-- The smooth first-kind resolvent transform has a positive instantaneous
coefficient and positive simple-fraction weights. -/
theorem exponentialMixtureLaplace_positive_partialFractions {n : ℕ} {c x : Fin (n + 1) → ℝ}
    (hc : ∀ i, 0 < c i) (hx₀ : ∀ i, 0 < x i) (hx : StrictMono x) :
    ∃ (r : Option (Fin n) → ℝ) (a : ℝ) (w : Option (Fin n) → ℝ),
      r none = 0 ∧ Function.Injective r ∧ (∀ i, r (some i) < 0) ∧ 0 < a ∧ (∀ i, 0 < w i) ∧
      (∀ z > 0, 1 / (z * exponentialMixtureLaplace Finset.univ c x z) =
        a + ∑ i, w i / (z - r i)) := by
  classical
  obtain ⟨r, a, w, hzero, hr, hroot, hpf⟩ := exponentialMixtureLaplace_partialFractions hc hx₀ hx
  let R := exponentialMixtureLaplace Finset.univ c x
  let P (z : ℝ) := a + ∑ i, w i / (z - r i)
  have hrneg (i : Fin n) : r (some i) < 0 := (hroot i).1.2.trans (neg_neg_of_pos (hx₀ _))
  have hpos (z : ℝ) (hz : 0 < z) : 1 / (z * R z) = P z := by
    apply hpf z (fun i => (add_pos hz (hx₀ i)).ne')
    intro i
    cases i with
    | none => rw [hzero]; exact hz.ne'
    | some i => exact (hrneg i |>.trans hz).ne'
  have hF : (Finset.univ : Finset (Fin (n + 1))).Nonempty := Finset.univ_nonempty
  have hconst := exponentialMixtureLaplace_resolvent_atTop (x := x) hF (fun i _ => hc i)
  have hPatTop : Tendsto P atTop (𝓝 a) := by
    have hi (i : Option (Fin n)) : Tendsto (fun z => w i / (z - r i)) atTop (𝓝 (0 : ℝ)) := by
      have h := (tendsto_atTop_add_const_right (atTop : Filter ℝ) (-r i) tendsto_id).inv_tendsto_atTop
      simpa only [Pi.inv_apply, div_eq_mul_inv, sub_eq_add_neg, mul_zero, id_eq] using h.const_mul (w i)
    simpa only [P, Finset.sum_const_zero, add_zero] using
      (tendsto_finsetSum Finset.univ (fun i _ => hi i)).const_add a
  have hA : 0 < a := by
    have h' := hconst.2.congr' ((eventually_gt_atTop (0 : ℝ)).mono fun z hz => hpos z hz)
    rw [← tendsto_nhds_unique h' hPatTop]
    exact hconst.1
  refine ⟨r, a, w, hzero, hr, hrneg, hA, ?_, hpos⟩
  intro i
  have hfree (j : Fin (n + 1)) : r i + x j ≠ 0 := by
    cases i with
    | none => rw [hzero, zero_add]; exact (hx₀ j).ne'
    | some k =>
      intro he
      have hp : r (some k) = -x j := by linarith
      have hk := (hroot k).1
      rw [hp] at hk
      have h₁ : k.castSucc < j := hx.lt_iff_lt.mp (neg_lt_neg_iff.mp hk.2)
      have h₂ : j < k.succ := hx.lt_iff_lt.mp (neg_lt_neg_iff.mp hk.1)
      change k.val < j.val at h₁
      change j.val < k.val + 1 at h₂
      omega
  have heq : (fun z => (z - r i) * P z) =ᶠ[𝓝[≠] r i] fun z => (z - r i) / (z * R z) := by
    have hA : ∀ᶠ z in 𝓝[≠] r i, ∀ j, z ≠ -x j := by
      rw [eventually_all]
      intro j
      have h : r i ≠ -x j := fun he => hfree j (by rw [he, neg_add_cancel])
      exact mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds h)
    have hB : ∀ᶠ z in 𝓝[≠] r i, ∀ j, z ≠ r j := by
      rw [eventually_all]
      intro j
      by_cases h : i = j
      · subst j
        exact self_mem_nhdsWithin
      · exact mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds (hr.ne h))
    filter_upwards [hA, hB] with z hz hz'
    have h := hpf z (fun j h => hz j (by linarith)) hz'
    change (z - r i) * P z = (z - r i) / (z * R z)
    rw [← show 1 / (z * R z) = P z from h, div_eq_mul_inv, one_mul, div_eq_mul_inv]
  have hl := (simpleFraction_tendsto_coefficient r w a hr i).congr' heq
  cases i with
  | none =>
      have ha := exponentialMixtureLaplace_origin_residue (x := x) hF (fun i _ => hc i) (fun i _ => hx₀ i)
      rw [hzero] at hl
      have he := tendsto_nhds_unique hl (by simpa only [sub_zero] using ha.2)
      rw [he]
      exact ha.1
  | some i =>
      have ha := exponentialMixtureLaplace_residue_limit hF (fun i _ => hc i) (fun j _ => hfree j)
        (hrneg i) (hroot i).2
      have he := tendsto_nhds_unique hl ha
      rw [he]
      exact exponentialMixtureLaplace_residue_pos hF (fun i _ => hc i) (fun j _ => hfree j) (hrneg i)

end RoughHeston

#print axioms RoughHeston.exponentialLaplaceNumerator_eval
#print axioms RoughHeston.exponentialMixtureLaplace_ordered_roots
#print axioms RoughHeston.exponentialLaplaceNumerator_factorization

#print axioms RoughHeston.exponentialMixtureLaplace_partialFractions

#print axioms RoughHeston.exponentialMixtureLaplace_positive_partialFractions
