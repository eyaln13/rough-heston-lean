import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace RoughHeston

/-- Rational continuation to the real line of the Laplace transform of a
finite exponential mixture. The derivative statements are away from its poles. -/
noncomputable def exponentialMixtureLaplace {ι : Type*} (F : Finset ι) (c x : ι → ℝ) (z : ℝ) : ℝ :=
  ∑ i ∈ F, c i / (z + x i)

theorem exponentialMixtureLaplace_hasDerivAt {ι : Type*} {F : Finset ι} {c x : ι → ℝ} {z : ℝ}
    (hz : ∀ i ∈ F, z + x i ≠ 0) :
    HasDerivAt (exponentialMixtureLaplace F c x) (∑ i ∈ F, -(c i / (z + x i) ^ 2)) z := by
  unfold exponentialMixtureLaplace
  refine HasDerivAt.fun_sum fun i hi => ?_
  simpa only [zero_mul, mul_one, zero_sub, neg_div, id_eq] using
    (hasDerivAt_const z (c i)).fun_div ((hasDerivAt_id z).add_const (x i)) (hz i hi)

/-- Every real derivative of the transform away from the poles is negative. -/
theorem exponentialMixtureLaplace_deriv_neg {ι : Type*} {F : Finset ι} {c x : ι → ℝ} {z : ℝ}
    (hF : F.Nonempty) (hc : ∀ i ∈ F, 0 < c i) (hz : ∀ i ∈ F, z + x i ≠ 0) :
    deriv (exponentialMixtureLaplace F c x) z < 0 := by
  rw [(exponentialMixtureLaplace_hasDerivAt hz).deriv, Finset.sum_neg_distrib]
  exact neg_neg_of_pos (Finset.sum_pos (fun i hi => div_pos (hc i hi) (sq_pos_of_ne_zero (hz i hi))) hF)

/-- The real transform is strictly decreasing between poles. -/
theorem exponentialMixtureLaplace_strictAntiOn {ι : Type*} {F : Finset ι} {c x : ι → ℝ} {a b : ℝ}
    (hF : F.Nonempty) (hc : ∀ i ∈ F, 0 < c i)
    (hfree : ∀ z ∈ Ioo a b, ∀ i ∈ F, z + x i ≠ 0) :
    StrictAntiOn (exponentialMixtureLaplace F c x) (Ioo a b) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo a b)
  · intro z hz
    exact (exponentialMixtureLaplace_hasDerivAt (c := c) (hfree z hz)).continuousAt.continuousWithinAt
  · intro z hz
    exact exponentialMixtureLaplace_deriv_neg hF hc (hfree z (interior_subset hz))

/-- The transform has a positive blow-up on the right of each simple pole. -/
theorem exponentialMixtureLaplace_tendsto_right_pole {ι : Type*} {F : Finset ι} {c x : ι → ℝ}
    {i : ι} (hi : i ∈ F) (hc : 0 < c i) (hx : Set.InjOn x ↑F) :
    Tendsto (exponentialMixtureLaplace F c x) (𝓝[>] (-x i)) atTop := by
  classical
  let R (z : ℝ) := exponentialMixtureLaplace (F.erase i) c x z
  have hr (j : ι) (hj : j ∈ F.erase i) : -x i + x j ≠ 0 := by
    intro h
    exact (Finset.mem_erase.mp hj).1 (hx (Finset.mem_erase.mp hj).2 hi (by linarith))
  have hR : Tendsto R (𝓝[>] (-x i)) (𝓝 (R (-x i))) :=
    (exponentialMixtureLaplace_hasDerivAt (c := c) hr).continuousAt.continuousWithinAt
  have hzero : Tendsto (fun z : ℝ => z + x i) (𝓝[>] (-x i)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hcont : Continuous (fun z : ℝ => z + x i) := continuous_id.add continuous_const
      simpa only [neg_add_cancel] using
        ((hcont.continuousAt (x := -x i)).tendsto.mono_left
          (show 𝓝[>] (-x i) ≤ 𝓝 (-x i) from nhdsWithin_le_nhds))
    · filter_upwards [self_mem_nhdsWithin] with z hz
      change -x i < z at hz
      change 0 < z + x i
      linarith
  have hp := (tendsto_inv_nhdsGT_zero.comp hzero).const_mul_atTop hc
  have h := hp.atTop_add hR
  convert h using 1
  funext z
  change (∑ j ∈ F, c j / (z + x j)) = c i * (z + x i)⁻¹ + ∑ j ∈ F.erase i, c j / (z + x j)
  rw [← Finset.add_sum_erase _ _ hi, div_eq_mul_inv]

/-- The transform has a negative blow-up on the left of each simple pole. -/
theorem exponentialMixtureLaplace_tendsto_left_pole {ι : Type*} {F : Finset ι} {c x : ι → ℝ}
    {i : ι} (hi : i ∈ F) (hc : 0 < c i) (hx : Set.InjOn x ↑F) :
    Tendsto (exponentialMixtureLaplace F c x) (𝓝[<] (-x i)) atBot := by
  classical
  let R (z : ℝ) := exponentialMixtureLaplace (F.erase i) c x z
  have hr (j : ι) (hj : j ∈ F.erase i) : -x i + x j ≠ 0 := by
    intro h
    exact (Finset.mem_erase.mp hj).1 (hx (Finset.mem_erase.mp hj).2 hi (by linarith))
  have hR : Tendsto R (𝓝[<] (-x i)) (𝓝 (R (-x i))) :=
    (exponentialMixtureLaplace_hasDerivAt (c := c) hr).continuousAt.continuousWithinAt
  have hzero : Tendsto (fun z : ℝ => z + x i) (𝓝[<] (-x i)) (𝓝[<] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hcont : Continuous (fun z : ℝ => z + x i) := continuous_id.add continuous_const
      simpa only [neg_add_cancel] using
        ((hcont.continuousAt (x := -x i)).tendsto.mono_left
          (show 𝓝[<] (-x i) ≤ 𝓝 (-x i) from nhdsWithin_le_nhds))
    · filter_upwards [self_mem_nhdsWithin] with z hz
      change z < -x i at hz
      change z + x i < 0
      linarith
  have hp := (tendsto_inv_nhdsLT_zero.comp hzero).const_mul_atBot hc
  have h := hp.atBot_add hR
  convert h using 1
  funext z
  change (∑ j ∈ F, c j / (z + x j)) = c i * (z + x i)⁻¹ + ∑ j ∈ F.erase i, c j / (z + x j)
  rw [← Finset.add_sum_erase _ _ hi, div_eq_mul_inv]

/-- There is exactly one simple real zero between consecutive real poles. -/
theorem exponentialMixtureLaplace_interlaces {ι : Type*} {F : Finset ι} {c x : ι → ℝ}
    {i j : ι} (hi : i ∈ F) (hj : j ∈ F) (hc : ∀ k ∈ F, 0 < c k) (hx : Set.InjOn x ↑F)
    (hij : -x i < -x j) (hbetween : ∀ k ∈ F, -x k ∉ Ioo (-x i) (-x j)) :
    ∃! z, z ∈ Ioo (-x i) (-x j) ∧ exponentialMixtureLaplace F c x z = 0 := by
  have hfree (z : ℝ) (hz : z ∈ Ioo (-x i) (-x j)) (k : ι) (hk : k ∈ F) : z + x k ≠ 0 := by
    intro he
    have hzk : z = -x k := by linarith
    exact hbetween k hk (hzk ▸ hz)
  let f := exponentialMixtureLaplace F c x
  have hpos := (tendsto_atTop.mp (exponentialMixtureLaplace_tendsto_right_pole hi (hc i hi) hx)) (1 : ℝ)
  have hneg := (tendsto_atBot.mp (exponentialMixtureLaplace_tendsto_left_pole hj (hc j hj) hx)) (-1 : ℝ)
  have hl : ∃ a ∈ Ioo (-x i) (-x j), 0 < f a := by
    have H : ∀ᶠ a in 𝓝[>] (-x i), a ∈ Ioo (-x i) (-x j) ∧ 0 < f a := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hij), hpos] with a ha hb hp
      exact ⟨⟨ha, hb⟩, by linarith⟩
    exact H.exists
  have hr : ∃ b ∈ Ioo (-x i) (-x j), f b < 0 := by
    have H : ∀ᶠ b in 𝓝[<] (-x j), b ∈ Ioo (-x i) (-x j) ∧ f b < 0 := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hij), self_mem_nhdsWithin, hneg] with b ha hb hp
      exact ⟨⟨ha, hb⟩, by linarith⟩
    exact H.exists
  obtain ⟨a, ha, hfa⟩ := hl
  obtain ⟨b, hb, hfb⟩ := hr
  have hm := exponentialMixtureLaplace_strictAntiOn (⟨i, hi⟩ : F.Nonempty) hc hfree
  have hab : a ≤ b := by
    by_contra! h
    exact (not_lt_of_ge (le_trans hfb.le hfa.le)) (hm hb ha h)
  have hsub : Icc a b ⊆ Ioo (-x i) (-x j) := fun z hz =>
    ⟨ha.1.trans_le hz.1, hz.2.trans_lt hb.2⟩
  have hfcont : ContinuousOn f (Icc a b) := fun z hz =>
    (exponentialMixtureLaplace_hasDerivAt (c := c) (hfree z (hsub hz))).continuousAt.continuousWithinAt
  obtain ⟨z, hz, hzero⟩ := intermediate_value_Icc' hab hfcont (show 0 ∈ Icc (f b) (f a) from ⟨hfb.le, hfa.le⟩)
  exact ⟨z, ⟨hsub hz, hzero⟩, fun w hw => hm.injOn hw.1 (hsub hz) (hw.2.trans hzero.symm)⟩

/-- The resolvent residue at a negative real zero of the transform is positive. -/
theorem exponentialMixtureLaplace_residue_pos {ι : Type*} {F : Finset ι} {c x : ι → ℝ} {z : ℝ}
    (hF : F.Nonempty) (hc : ∀ i ∈ F, 0 < c i) (hz : ∀ i ∈ F, z + x i ≠ 0)
    (hz₀ : z < 0) : 0 < 1 / (z * deriv (exponentialMixtureLaplace F c x) z) :=
  one_div_pos.mpr (mul_pos_of_neg_of_neg hz₀ (exponentialMixtureLaplace_deriv_neg hF hc hz))

/-- The real punctured limit identifies the coefficient of the simple
resolvent pole at a negative zero. -/
theorem exponentialMixtureLaplace_residue_limit {ι : Type*} {F : Finset ι} {c x : ι → ℝ} {z : ℝ}
    (hF : F.Nonempty) (hc : ∀ i ∈ F, 0 < c i) (hz : ∀ i ∈ F, z + x i ≠ 0)
    (hz₀ : z < 0) (hzf : exponentialMixtureLaplace F c x z = 0) :
    Tendsto (fun y => (y - z) / (y * exponentialMixtureLaplace F c x y)) (𝓝[≠] z)
      (𝓝 (1 / (z * deriv (exponentialMixtureLaplace F c x) z))) := by
  let f := exponentialMixtureLaplace F c x
  have hD := (exponentialMixtureLaplace_hasDerivAt (c := c) hz).differentiableAt.hasDerivAt
  have hS : Tendsto (fun y => f y / (y - z)) (𝓝[≠] z) (𝓝 (deriv f z)) := by
    simpa only [f, slope_fun_def_field, hzf, sub_zero] using hD.tendsto_slope
  have hY : Tendsto (fun y : ℝ => y) (𝓝[≠] z) (𝓝 z) := nhdsWithin_le_nhds
  have hP : z * deriv f z ≠ 0 := (mul_pos_of_neg_of_neg hz₀
    (exponentialMixtureLaplace_deriv_neg hF hc hz)).ne'
  apply (tendsto_const_nhds.div (hY.mul hS) hP).congr'
  exact Eventually.of_forall fun y => by
    change 1 / (y * (f y / (y - z))) = (y - z) / (y * f y)
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, one_mul, mul_assoc]

/-- Away from the real continuation, the rational sum equals the actual
Laplace transform on positive real arguments. -/
theorem exponentialMixtureLaplace_eq_integral {ι : Type*} {F : Finset ι} {c x : ι → ℝ} {z : ℝ}
    (hz : 0 < z) (hx : ∀ i ∈ F, 0 ≤ x i) :
    exponentialMixtureLaplace F c x z = ∫ t in Ioi (0 : ℝ),
      Real.exp (-(z * t)) * ∑ i ∈ F, c i * Real.exp (-(x i * t)) := by
  let ν := volume.restrict (Ioi (0 : ℝ))
  let f (i : ι) (t : ℝ) := Real.exp (-((z + x i) * t))
  have hf (i : ι) (hi : i ∈ F) : (∫ t, f i t ∂ν) = 1 / (z + x i) := by
    simpa only [f, ν, sub_self, Real.rpow_zero, one_mul, Real.rpow_one, Real.Gamma_one, mul_one] using
      (Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) one_pos (add_pos_of_pos_of_nonneg hz (hx i hi)))
  have hfi (i : ι) (hi : i ∈ F) : Integrable (f i) ν := by
    by_contra hn
    have he := hf i hi
    rw [integral_undef hn] at he
    exact ((one_div_pos.mpr (add_pos_of_pos_of_nonneg hz (hx i hi))).ne') he.symm
  have heq (t : ℝ) : Real.exp (-(z * t)) * (∑ i ∈ F, c i * Real.exp (-(x i * t))) =
      ∑ i ∈ F, c i * f i t := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [show f i t = Real.exp (-((z + x i) * t)) from rfl, add_mul, neg_add, Real.exp_add]
    ring
  rw [show (fun t : ℝ => Real.exp (-(z * t)) * (∑ i ∈ F, c i * Real.exp (-(x i * t)))) =
      fun t => ∑ i ∈ F, c i * f i t from funext heq]
  rw [integral_finsetSum _ fun i hi => (hfi i hi).const_mul _]
  unfold exponentialMixtureLaplace
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul, hf i hi, mul_one_div]

/-- At zero, the simple-pole coefficient in the reciprocal transform is positive. -/
theorem exponentialMixtureLaplace_origin_residue {ι : Type*} {F : Finset ι} {c x : ι → ℝ}
    (hF : F.Nonempty) (hc : ∀ i ∈ F, 0 < c i) (hx : ∀ i ∈ F, 0 < x i) :
    0 < 1 / exponentialMixtureLaplace F c x 0 ∧
      Tendsto (fun y => y / (y * exponentialMixtureLaplace F c x y)) (𝓝[≠] (0 : ℝ))
        (𝓝 (1 / exponentialMixtureLaplace F c x 0)) := by
  let f := exponentialMixtureLaplace F c x
  have hp : 0 < f 0 := by
    unfold f exponentialMixtureLaplace
    simp only [zero_add]
    exact Finset.sum_pos (fun i hi => div_pos (hc i hi) (hx i hi)) hF
  have hf : Tendsto f (𝓝[≠] (0 : ℝ)) (𝓝 (f 0)) :=
    ((exponentialMixtureLaplace_hasDerivAt (c := c)
      (z := 0) (fun i hi => by simpa only [zero_add] using (hx i hi).ne')).continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds
  refine ⟨one_div_pos.mpr hp, (tendsto_const_nhds.div hf hp.ne').congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with y hy
  change y ≠ 0 at hy
  change 1 / f y = y / (y * f y)
  simpa only [mul_one] using (mul_div_mul_left (1 : ℝ) (f y) hy).symm

/-- The coefficient of the instantaneous atom is the reciprocal of the
kernel's total weight. -/
theorem exponentialMixtureLaplace_resolvent_atTop {ι : Type*} {F : Finset ι} {c x : ι → ℝ}
    (hF : F.Nonempty) (hc : ∀ i ∈ F, 0 < c i) :
    0 < 1 / (∑ i ∈ F, c i) ∧
      Tendsto (fun z => 1 / (z * exponentialMixtureLaplace F c x z)) atTop (𝓝 (1 / (∑ i ∈ F, c i))) := by
  have hsum : 0 < ∑ i ∈ F, c i := Finset.sum_pos hc hF
  have hi (i : ι) : Tendsto (fun z => z * (c i / (z + x i))) atTop (𝓝 (c i)) := by
    have hz : Tendsto (fun z : ℝ => z + x i) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub ((hz.inv_tendsto_atTop).const_mul (x i))
    have hh : Tendsto (fun z => c i * (1 - x i * (z + x i)⁻¹)) atTop (𝓝 (c i)) := by
      simpa only [Pi.inv_apply, mul_zero, sub_zero, mul_one] using h.const_mul (c i)
    refine hh.congr' ?_
    filter_upwards [hz.eventually_ne_atTop 0] with z hz₀
    field_simp [hz₀]
    ring
  have hlim : Tendsto (fun z => z * exponentialMixtureLaplace F c x z) atTop (𝓝 (∑ i ∈ F, c i)) := by
    simp only [exponentialMixtureLaplace, Finset.mul_sum]
    exact tendsto_finsetSum _ fun i _ => hi i
  exact ⟨one_div_pos.mpr hsum, tendsto_const_nhds.div hlim hsum.ne'⟩

end RoughHeston

#print axioms RoughHeston.exponentialMixtureLaplace_hasDerivAt
#print axioms RoughHeston.exponentialMixtureLaplace_deriv_neg
#print axioms RoughHeston.exponentialMixtureLaplace_strictAntiOn
#print axioms RoughHeston.exponentialMixtureLaplace_tendsto_right_pole
#print axioms RoughHeston.exponentialMixtureLaplace_tendsto_left_pole
#print axioms RoughHeston.exponentialMixtureLaplace_interlaces
#print axioms RoughHeston.exponentialMixtureLaplace_residue_pos

#print axioms RoughHeston.exponentialMixtureLaplace_residue_limit

#print axioms RoughHeston.exponentialMixtureLaplace_eq_integral
#print axioms RoughHeston.exponentialMixtureLaplace_origin_residue
#print axioms RoughHeston.exponentialMixtureLaplace_resolvent_atTop
