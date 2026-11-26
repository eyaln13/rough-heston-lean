import FractionalKernelL1
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RoughHeston

private theorem volterra_intervalIntegrable_reversed_product {k h : ℝ → ℝ}
    {T t : ℝ} (hT : 0 ≤ T) (ht : t ∈ Icc 0 T)
    (hk : IntervalIntegrable k volume 0 T) (hkm : Measurable k) (hhm : Measurable h)
    (hkpos : ∀ r ∈ Icc 0 T, 0 ≤ k r) (hhpos : ∀ s ∈ Icc 0 T, 0 ≤ h s)
    (hhb : BddAbove (h '' Icc 0 T)) :
    IntervalIntegrable (fun r => k r * h (t - r)) volume 0 t := by
  obtain ⟨B, hB⟩ := hhb
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1]
  have hki : IntervalIntegrable k volume 0 t := by
    apply hk.mono_set
    rw [uIcc_of_le ht.1, uIcc_of_le hT]
    exact Icc_subset_Icc le_rfl ht.2
  refine (hki.mul_const B).1.mono'
    ((hkm.mul (hhm.comp (measurable_const.sub measurable_id))).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  have hrT : r ∈ Icc 0 T := ⟨hr.1.le, hr.2.trans ht.2⟩
  have htr : t - r ∈ Icc 0 T :=
    ⟨sub_nonneg.mpr hr.2, (sub_le_self t hr.1.le).trans ht.2⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hkpos r hrT) (hhpos _ htr))]
  exact mul_le_mul_of_nonneg_left (hB ⟨_, htr, rfl⟩) (hkpos r hrT)

/-- A uniform Volterra bound obtained by induction over intervals of length `δ`. -/
theorem uniform_volterra_bound_of_small_step {ι : Type*} {k : ℝ → ℝ} {h : ι → ℝ → ℝ}
    {T C δ : ℝ} (hδ : 0 < δ) (hδT : δ ≤ T) (hC : 0 ≤ C)
    (hk : IntervalIntegrable k volume 0 T) (hkm : Measurable k)
    (hkpos : ∀ r ∈ Icc 0 T, 0 ≤ k r)
    (hsmall : C * (∫ r in 0..δ, k r) ≤ 1 / 2)
    (hhm : ∀ i, Measurable (h i)) (hhpos : ∀ i s, s ∈ Icc 0 T → 0 ≤ h i s)
    (hhb : ∀ i, BddAbove (h i '' Icc 0 T))
    (hineq : ∀ i t, t ∈ Icc 0 T → h i t ≤ C * (1 + volterraConvolution k (h i) t)) :
    ∃ B : ℝ, ∀ i t, t ∈ Icc 0 T → h i t ≤ B := by
  have hT := hδ.le.trans hδT
  let M : ℝ := ∫ r in 0..T, k r
  have hM : 0 ≤ M := intervalIntegral.integral_nonneg hT hkpos
  have hsegment (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
      IntervalIntegrable k volume a b := by
    apply hk.mono_set
    rw [uIcc_of_le hT, uIcc_of_le hab]
    exact Icc_subset_Icc ha hb
  have hstep (n : ℕ) (A : ℝ) (hA : 0 ≤ A)
      (hprev : ∀ i t, t ∈ Icc 0 (min T ((n : ℝ) * δ)) → h i t ≤ A) :
      ∀ i t, t ∈ Icc 0 (min T (((n + 1 : ℕ) : ℝ) * δ)) →
        h i t ≤ 2 * (C * (1 + A * M)) := by
    intro i
    let L : ℝ := min T (((n + 1 : ℕ) : ℝ) * δ)
    let S : Set ℝ := h i '' Icc 0 L
    let B := sSup S
    have hL : 0 ≤ L := le_min hT (mul_nonneg (Nat.cast_nonneg _) hδ.le)
    have hne : S.Nonempty := ⟨h i 0, 0, ⟨le_rfl, hL⟩, rfl⟩
    have hBdd : BddAbove S := (hhb i).mono (image_mono (Icc_subset_Icc le_rfl (min_le_left _ _)))
    have hB (s : ℝ) (hs : s ∈ Icc 0 L) : h i s ≤ B := le_csSup hBdd ⟨_, hs, rfl⟩
    have hBnonneg : 0 ≤ B := (hhpos i 0 ⟨le_rfl, hT⟩).trans (hB 0 ⟨le_rfl, hL⟩)
    have hper (t : ℝ) (ht : t ∈ Icc 0 L) :
        h i t ≤ C * (1 + A * M) + B / 2 := by
      have htT : t ∈ Icc 0 T := ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
      let a := min δ t
      have ha : 0 ≤ a := le_min hδ.le ht.1
      have hat : a ≤ t := min_le_right _ _
      have haδ : a ≤ δ := min_le_left _ _
      have htint := volterra_intervalIntegrable_reversed_product hT htT hk hkm (hhm i)
        hkpos (hhpos i) (hhb i)
      have hnearI : IntervalIntegrable (fun r => k r * h i (t - r)) volume 0 a := by
        apply htint.mono_set
        rw [uIcc_of_le ht.1, uIcc_of_le ha]
        exact Icc_subset_Icc le_rfl hat
      have hfarI : IntervalIntegrable (fun r => k r * h i (t - r)) volume a t := by
        apply htint.mono_set
        rw [uIcc_of_le ht.1, uIcc_of_le hat]
        exact Icc_subset_Icc ha le_rfl
      have hnear : (∫ r in 0..a, k r * h i (t - r)) ≤ (∫ r in 0..a, k r) * B := by
        rw [← intervalIntegral.integral_mul_const]
        refine intervalIntegral.integral_mono_on ha hnearI ((hsegment 0 a le_rfl ha (hat.trans htT.2)).mul_const B) ?_
        intro r hr
        have htrL : t - r ∈ Icc 0 L :=
          ⟨sub_nonneg.mpr (hr.2.trans hat), (sub_le_self t hr.1).trans ht.2⟩
        exact mul_le_mul_of_nonneg_left (hB _ htrL)
          (hkpos r ⟨hr.1, hr.2.trans (hat.trans htT.2)⟩)
      have hfar : (∫ r in a..t, k r * h i (t - r)) ≤ (∫ r in a..t, k r) * A := by
        rw [← intervalIntegral.integral_mul_const]
        refine intervalIntegral.integral_mono_on_of_le_Ioo hat hfarI
          ((hsegment a t ha hat htT.2).mul_const A) ?_
        intro r hr
        have hδr : δ ≤ r := by
          by_contra! hn
          exact (not_lt_of_ge hr.1.le) (lt_min hn hr.2)
        have htδ : t ≤ ((n : ℝ) + 1) * δ := by
          exact_mod_cast ht.2.trans (min_le_right T _)
        have htr : t - r ∈ Icc 0 (min T ((n : ℝ) * δ)) := by
          refine ⟨sub_nonneg.mpr hr.2.le, le_min ((sub_le_self t (ha.trans hr.1.le)).trans htT.2) ?_⟩
          linarith only [htδ, hδr]
        exact mul_le_mul_of_nonneg_left (hprev i _ htr)
          (hkpos r ⟨ha.trans hr.1.le, hr.2.le.trans htT.2⟩)
      have hnear_mass : (∫ r in 0..a, k r) ≤ ∫ r in 0..δ, k r :=
        intervalIntegral.integral_mono_interval le_rfl ha haδ (by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
          exact hkpos r ⟨hr.1.le, hr.2.trans hδT⟩) (hsegment 0 δ le_rfl hδ.le hδT)
      have hfar_mass : (∫ r in a..t, k r) ≤ M :=
        intervalIntegral.integral_mono_interval ha hat htT.2 (by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
          exact hkpos r (Ioc_subset_Icc_self hr)) hk
      have hnear' : C * (∫ r in 0..a, k r * h i (t - r)) ≤ B / 2 := by
        calc
          _ ≤ C * ((∫ r in 0..a, k r) * B) := mul_le_mul_of_nonneg_left hnear hC
          _ = (C * (∫ r in 0..a, k r)) * B := (mul_assoc _ _ _).symm
          _ ≤ (1 / 2) * B := mul_le_mul_of_nonneg_right
            ((mul_le_mul_of_nonneg_left hnear_mass hC).trans hsmall) hBnonneg
          _ = B / 2 := by ring
      have hfar' : C * (∫ r in a..t, k r * h i (t - r)) ≤ C * (A * M) := by
        rw [mul_comm A M]
        exact mul_le_mul_of_nonneg_left
          (hfar.trans (mul_le_mul_of_nonneg_right hfar_mass hA)) hC
      have hrefl : volterraConvolution k (h i) t = ∫ r in 0..t, k r * h i (t - r) := by
        rw [volterraConvolution, ← intervalIntegral.integral_of_le ht.1]
        have he := intervalIntegral.integral_comp_sub_left (a := 0) (b := t)
          (fun r => k r * h i (t - r)) t
        simpa only [sub_self, sub_zero, sub_sub_cancel] using he
      have hi := hineq i t htT
      rw [hrefl, ← intervalIntegral.integral_add_adjacent_intervals hnearI hfarI] at hi
      linarith only [hi, hnear', hfar']
    have hsB : B ≤ C * (1 + A * M) + B / 2 := by
      apply csSup_le hne
      rintro _ ⟨s, hs, rfl⟩
      exact hper s hs
    intro t ht
    linarith only [hB t ht, hsB]
  have hgrid (n : ℕ) : ∃ A : ℝ, 0 ≤ A ∧
      ∀ i t, t ∈ Icc 0 (min T ((n : ℝ) * δ)) → h i t ≤ A := by
    induction n with
    | zero =>
        refine ⟨C, hC, fun i t ht => ?_⟩
        have ht0 : t = 0 := le_antisymm (by simpa [hT] using ht.2) ht.1
        subst t
        simpa [volterraConvolution] using hineq i 0 ⟨le_rfl, hT⟩
    | succ n ih =>
        obtain ⟨A, hA, hbound⟩ := ih
        exact ⟨2 * (C * (1 + A * M)), by positivity, hstep n A hA hbound⟩
  obtain ⟨n, hn⟩ := exists_nat_ge (T / δ)
  have hTn := (div_le_iff₀ hδ).mp hn
  obtain ⟨A, -, hA⟩ := hgrid n
  exact ⟨A, fun i t ht => hA i t (by simpa [min_eq_left hTn] using ht)⟩

/-- Uniform control on a finite horizon for a family satisfying the same scalar
Volterra inequality with a nonnegative integrable kernel. Each trajectory needs
its own finite local bound, with no uniformity assumed in that bound. -/
theorem uniform_volterra_moment_bound {ι : Type*} {k : ℝ → ℝ} {h : ι → ℝ → ℝ}
    {T C : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hk : IntervalIntegrable k volume 0 T) (hkm : Measurable k)
    (hkpos : ∀ r ∈ Icc 0 T, 0 ≤ k r)
    (hhm : ∀ i, Measurable (h i)) (hhpos : ∀ i s, s ∈ Icc 0 T → 0 ≤ h i s)
    (hhb : ∀ i, BddAbove (h i '' Icc 0 T))
    (hineq : ∀ i t, t ∈ Icc 0 T → h i t ≤ C * (1 + volterraConvolution k (h i) t)) :
    ∃ B : ℝ, ∀ i t, t ∈ Icc 0 T → h i t ≤ B := by
  rcases eq_or_lt_of_le hT with hzero | hTpos
  · refine ⟨C, fun i t ht => ?_⟩
    have ht0 : t = 0 := le_antisymm (ht.2.trans_eq hzero.symm) ht.1
    subst t
    simpa [volterraConvolution] using hineq i 0 ⟨le_rfl, hT⟩
  have hcont : ContinuousWithinAt (fun x => C * (∫ r in 0..x, k r)) (Icc 0 T) 0 := by
    refine continuousWithinAt_const.mul (intervalIntegral.continuousWithinAt_primitive
      (measure_singleton _) ?_)
    simpa [hT] using hk
  obtain ⟨ε, hε, hdist⟩ := Metric.continuousWithinAt_iff.mp hcont (1 / 2) (by norm_num)
  let δ := min T (ε / 2)
  have hδ : 0 < δ := lt_min hTpos (by linarith)
  have hδT : δ ≤ T := min_le_left _ _
  have hδε : δ < ε := (min_le_right _ _).trans_lt (by linarith)
  have hsmall := hdist (show δ ∈ Icc 0 T from ⟨hδ.le, hδT⟩)
    (by simpa [Real.dist_eq, abs_of_pos hδ] using hδε)
  simp only [Real.dist_eq, intervalIntegral.integral_same, mul_zero, sub_zero] at hsmall
  exact uniform_volterra_bound_of_small_step hδ hδT hC hk hkm hkpos
    ((le_abs_self _).trans hsmall.le) hhm hhpos hhb hineq

/-- The fractional moment kernel is integrable when its singularity is square integrable. -/
theorem intervalIntegrable_fractionalK_add_sq {α T : ℝ} (hα : 1 / 2 < α) (hT : 0 ≤ T) :
    IntervalIntegrable (fun r => fractionalK α r + (fractionalK α r)^2) volume 0 T := by
  have hαpos : 0 < α := by linarith
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
  refine (fractionalK_integrableOn_Ioc hαpos T).add ?_
  have hp : -1 < (α - 1) + (α - 1) := by linarith
  have hrpow : IntervalIntegrable (fun r : ℝ => r ^ ((α - 1) + (α - 1))) volume 0 T :=
    intervalIntegral.intervalIntegrable_rpow' hp
  refine ((hrpow.mul_const ((Real.Gamma α)⁻¹ ^ 2)).1).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  have he : r ^ ((α - 1) + (α - 1)) = (r ^ (α - 1)) ^ 2 := by
    rw [Real.rpow_add hr.1, pow_two]
  simp [fractionalK, not_le_of_gt hr.1, he, div_eq_mul_inv, mul_pow]

/-- Uniform finite-horizon control for the fractional kernel and its square. -/
theorem uniform_fractional_volterra_moment_bound {ι : Type*} {h : ι → ℝ → ℝ}
    {α T C : ℝ} (hα : 1 / 2 < α) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hhm : ∀ i, Measurable (h i)) (hhpos : ∀ i s, s ∈ Icc 0 T → 0 ≤ h i s)
    (hhb : ∀ i, BddAbove (h i '' Icc 0 T))
    (hineq : ∀ i t, t ∈ Icc 0 T → h i t ≤ C *
      (1 + volterraConvolution (fun r => fractionalK α r + (fractionalK α r)^2) (h i) t)) :
    ∃ B : ℝ, ∀ i t, t ∈ Icc 0 T → h i t ≤ B := by
  have hαpos : 0 < α := by linarith
  refine uniform_volterra_moment_bound hT hC (intervalIntegrable_fractionalK_add_sq hα hT)
    ((fractionalK_measurable α).add ((fractionalK_measurable α).pow_const 2)) ?_
    hhm hhpos hhb hineq
  intro r _
  have hKr : 0 ≤ fractionalK α r := by
    unfold fractionalK
    split
    · exact le_rfl
    · rename_i hr
      exact div_nonneg (Real.rpow_nonneg (le_of_lt (not_le.mp hr)) _)
        (Real.Gamma_pos_of_pos hαpos).le
  exact add_nonneg hKr (sq_nonneg _)

#print axioms uniform_volterra_bound_of_small_step
#print axioms uniform_volterra_moment_bound
#print axioms uniform_fractional_volterra_moment_bound

end RoughHeston
