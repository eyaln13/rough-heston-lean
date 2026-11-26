import PolynomialExponentialResolvent
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Set Filter MeasureTheory
open scoped Topology BigOperators Interval

namespace RoughHeston

private theorem exponential_pair_convolution {r x t : ℝ} (h : r + x ≠ 0) :
    (∫ s in (0 : ℝ)..t, Real.exp (r * (t - s)) * Real.exp (-(x * s))) =
      (Real.exp (r * t) - Real.exp (-(x * t))) / (r + x) := by
  have he (s : ℝ) : Real.exp (r * (t - s)) * Real.exp (-(x * s)) =
      Real.exp (r * t) * Real.exp (-(r + x) * s) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr h),
    integral_exp, mul_zero, Real.exp_zero, smul_eq_mul, inv_neg]
  have he' : Real.exp (r * t) * Real.exp (-(r + x) * t) = Real.exp (-(x * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (r * t) - Real.exp (r * t) * Real.exp (-(r + x) * t)) / (r + x) := by
      simp only [div_eq_mul_inv]
      ring
    _ = _ := by rw [he']

/-- Termwise integration of finite exponential kernels. -/
theorem exponential_mixture_convolution_expansion {ι jι : Type*} [Fintype ι] [Fintype jι]
    (c x : ι → ℝ) (w r : jι → ℝ) (hfree : ∀ j i, r j + x i ≠ 0) (t : ℝ) :
    (∫ s in (0 : ℝ)..t,
      (∑ j, w j * Real.exp (r j * (t - s))) * (∑ i, c i * Real.exp (-(x i * s)))) =
      (∑ j, (w j * (∑ i, c i / (r j + x i))) * Real.exp (r j * t)) -
        (∑ i, (c i * (∑ j, w j / (r j + x i))) * Real.exp (-(x i * t))) := by
  let f (j : jι) (i : ι) (s : ℝ) := (w j * c i) *
    (Real.exp (r j * (t - s)) * Real.exp (-(x i * s)))
  have hfi (j : jι) (i : ι) : IntervalIntegrable (f j i) volume 0 t := by
    apply Continuous.intervalIntegrable
    unfold f
    fun_prop
  have hsum (s : ℝ) : (∑ j, w j * Real.exp (r j * (t - s))) * (∑ i, c i * Real.exp (-(x i * s))) =
      ∑ j, ∑ i, f j i s := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only [f]
    ring
  have hf (j : jι) (i : ι) : (∫ s in (0 : ℝ)..t, f j i s) =
      w j * (c i / (r j + x i)) * Real.exp (r j * t) -
        c i * (w j / (r j + x i)) * Real.exp (-(x i * t)) := by
    change (∫ s in (0 : ℝ)..t, (w j * c i) *
      (Real.exp (r j * (t - s)) * Real.exp (-(x i * s)))) = _
    rw [intervalIntegral.integral_const_mul, exponential_pair_convolution (hfree j i)]
    simp only [div_eq_mul_inv]
    ring
  simp_rw [hsum]
  have hfi' (j : jι) : IntervalIntegrable (fun s => ∑ i, f j i s) volume 0 t := by
    have heq : (fun s => ∑ i, f j i s) = ∑ i, f j i := by
      funext s
      simp only [Finset.sum_apply]
    rw [heq]
    exact IntervalIntegrable.sum Finset.univ (fun i _ => hfi j i)
  rw [intervalIntegral.integral_finsetSum (fun j _ => hfi' j)]
  simp_rw [intervalIntegral.integral_finsetSum (fun i _ => hfi _ i), hf, Finset.sum_sub_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum]

private theorem eventually_avoids_finite_rates {ι : Type*} [Finite ι] {l : Filter ℝ} {z₀ : ℝ}
    (r : ι → ℝ) (hl : l ≤ 𝓝 z₀) (hne : ∀ᶠ z in l, z ≠ z₀) :
    ∀ᶠ z in l, ∀ i, z ≠ r i := by
  rw [eventually_all]
  intro i
  by_cases h : z₀ = r i
  · simpa only [← h] using hne
  · exact hl (isOpen_ne.mem_nhds h)

private theorem continuousAt_partial_fraction {ι : Type*} (F : Finset ι) {r w : ι → ℝ} {a z₀ : ℝ}
    (h : ∀ i ∈ F, z₀ ≠ r i) : ContinuousAt (fun z => a + ∑ i ∈ F, w i / (z - r i)) z₀ := by
  have ht (i : ι) (hi : i ∈ F) : ContinuousAt (fun z => w i / (z - r i)) z₀ :=
    continuousAt_const.div (continuous_id.sub continuous_const).continuousAt (sub_ne_zero.mpr (h i hi))
  exact (tendsto_finsetSum F (fun i hi => (ht i hi).tendsto)).const_add a

private theorem partial_fraction_coefficient {ι : Type*} [Fintype ι] [DecidableEq ι]
    {r w : ι → ℝ} {a : ℝ} (hr : Function.Injective r) (i : ι) :
    Tendsto (fun z => (z - r i) * (a + ∑ j, w j / (z - r j))) (𝓝[≠] r i) (𝓝 (w i)) := by
  let E (z : ℝ) := a + ∑ j ∈ (Finset.univ : Finset ι).erase i, w j / (z - r j)
  have hE : ContinuousAt E (r i) := continuousAt_partial_fraction _ (fun j hj =>
    hr.ne ((Finset.mem_erase.mp hj).1.symm))
  have hd : Tendsto (fun z => z - r i) (𝓝[≠] r i) (𝓝 (0 : ℝ)) := by
    have ht : ContinuousAt (fun z : ℝ => z - r i) (r i) := (continuous_id.sub continuous_const).continuousAt
    simpa only [sub_self] using ht.tendsto.mono_left nhdsWithin_le_nhds
  have h := (hd.mul (hE.tendsto.mono_left nhdsWithin_le_nhds)).const_add (w i)
  have hlim : Tendsto (fun z => w i + (z - r i) * E z) (𝓝[≠] r i) (𝓝 (w i)) := by
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

/-- Explicit positive atom and exponential density of the first-kind resolvent.
The equality includes time zero under the smooth-kernel convention. -/
theorem positive_exponential_resolvent_time_domain {n : ℕ} {c x : Fin (n + 1) → ℝ}
    (hc : ∀ i, 0 < c i) (hx₀ : ∀ i, 0 < x i) (hx : StrictMono x) :
    ∃ (r : Option (Fin n) → ℝ) (a : ℝ) (w : Option (Fin n) → ℝ),
      r none = 0 ∧ (∀ i, r (some i) < 0) ∧ 0 < a ∧ (∀ i, 0 < w i) ∧
      ∀ t : ℝ, a * (∑ i, c i * Real.exp (-(x i * t))) +
        (∫ s in (0 : ℝ)..t, (∑ j, w j * Real.exp (r j * (t - s))) *
          (∑ i, c i * Real.exp (-(x i * s)))) = 1 := by
  classical
  obtain ⟨r, a, w, hzero, hr, hroot, hpf⟩ := exponentialMixtureLaplace_partialFractions hc hx₀ hx
  let R := exponentialMixtureLaplace Finset.univ c x
  let P (z : ℝ) := a + ∑ i, w i / (z - r i)
  have hrneg (i : Fin n) : r (some i) < 0 := (hroot i).1.2.trans (neg_neg_of_pos (hx₀ _))
  have hfree (j : Option (Fin n)) (i : Fin (n + 1)) : r j + x i ≠ 0 := by
    cases j with
    | none => rw [hzero, zero_add]; exact (hx₀ i).ne'
    | some k =>
      intro he
      have hp : r (some k) = -x i := by linarith
      have hk := (hroot k).1
      rw [hp] at hk
      have h₁ : k.castSucc < i := hx.lt_iff_lt.mp (neg_lt_neg_iff.mp hk.2)
      have h₂ : i < k.succ := hx.lt_iff_lt.mp (neg_lt_neg_iff.mp hk.1)
      change k.val < i.val at h₁
      change i.val < k.val + 1 at h₂
      omega
  have hF : (Finset.univ : Finset (Fin (n + 1))).Nonempty := Finset.univ_nonempty
  have hmatch {l : Filter ℝ} {z₀ : ℝ} (hl : l ≤ 𝓝 z₀) (hne : ∀ᶠ z in l, z ≠ z₀) :
      (fun z => 1 / (z * R z)) =ᶠ[l] P := by
    filter_upwards [eventually_avoids_finite_rates (fun i => -x i) hl hne,
      eventually_avoids_finite_rates r hl hne] with z hz hz'
    exact hpf z (fun i h => hz i (by linarith)) hz'
  have hPpoles (i : Fin (n + 1)) : P (-x i) = 0 := by
    have hm : ∀ᶠ z in 𝓝[>] (-x i), z ∈ Ioi (-x i) := self_mem_nhdsWithin
    have he : ∀ᶠ z in 𝓝[>] (-x i), z ≠ -x i := hm.mono fun _ hz => ne_of_gt hz
    have hC : ContinuousAt P (-x i) := continuousAt_partial_fraction Finset.univ fun j _ h =>
      hfree j i (by linarith)
    have hR := (exponentialMixtureLaplace_tendsto_right_pole (Finset.mem_univ i) (hc i)
      hx.injective.injOn).inv_tendsto_atTop
    have hZ : Tendsto (fun z : ℝ => z⁻¹) (𝓝[>] (-x i)) (𝓝 (-x i)⁻¹) :=
      (continuousAt_inv₀ (neg_ne_zero.mpr (hx₀ i).ne')).tendsto.mono_left nhdsWithin_le_nhds
    have hU : Tendsto (fun z => 1 / (z * R z)) (𝓝[>] (-x i)) (𝓝 0) := by
      simpa only [R, one_div, mul_inv_rev, zero_mul, Pi.inv_apply] using hR.mul hZ
    exact tendsto_nhds_unique (hC.tendsto.mono_left nhdsWithin_le_nhds)
      (hU.congr' (hmatch nhdsWithin_le_nhds he))
  have haCoeff (i : Fin (n + 1)) : a = ∑ j, w j / (r j + x i) := by
    have h := hPpoles i
    change a + ∑ j, w j / (-x i - r j) = 0 at h
    simp_rw [show ∀ j, -x i - r j = -(r j + x i) by intro j; ring,
      div_neg, Finset.sum_neg_distrib] at h
    exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using h)
  have hconst := exponentialMixtureLaplace_resolvent_atTop (x := x) hF (fun i _ => hc i)
  have hPatTop : Tendsto P atTop (𝓝 a) := by
    have hi (i : Option (Fin n)) : Tendsto (fun z => w i / (z - r i)) atTop (𝓝 (0 : ℝ)) := by
      have h := (tendsto_atTop_add_const_right (atTop : Filter ℝ) (-r i) tendsto_id).inv_tendsto_atTop
      simpa only [Pi.inv_apply, div_eq_mul_inv, sub_eq_add_neg, mul_zero, id_eq] using h.const_mul (w i)
    simpa only [P, Finset.sum_const_zero, add_zero] using
      (tendsto_finsetSum Finset.univ (fun i _ => hi i)).const_add a
  have ha : 0 < a := by
    have he : (fun z => 1 / (z * R z)) =ᶠ[atTop] P := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
      apply hpf z (fun i => (add_pos hz (hx₀ i)).ne')
      intro j
      cases j with
      | none => rw [hzero]; exact hz.ne'
      | some j => exact ((hrneg j).trans hz).ne'
    rw [← tendsto_nhds_unique (hconst.2.congr' he) hPatTop]
    exact hconst.1
  have hweights (j : Option (Fin n)) :
      0 < w j ∧ w j * R (r j) = if j = none then 1 else 0 := by
    have he : (fun z => (z - r j) * P z) =ᶠ[𝓝[≠] r j] fun z => (z - r j) / (z * R z) := by
      filter_upwards [hmatch (z₀ := r j) nhdsWithin_le_nhds self_mem_nhdsWithin] with z hz
      rw [← hz, div_eq_mul_inv, one_mul, div_eq_mul_inv]
    have hl := (partial_fraction_coefficient (a := a) (w := w) hr j).congr' he
    cases j with
    | none =>
      have H := exponentialMixtureLaplace_origin_residue (x := x) hF (fun i _ => hc i) (fun i _ => hx₀ i)
      rw [hzero] at hl
      have hh := tendsto_nhds_unique hl (by simpa only [R, sub_zero] using H.2)
      refine ⟨hh.symm ▸ H.1, ?_⟩
      rw [hh, hzero, ite_eq_left rfl, one_div, inv_mul_cancel₀]
      exact (one_div_pos.mp H.1).ne'
    | some j =>
      have H := exponentialMixtureLaplace_residue_limit hF (fun i _ => hc i) (fun i _ => hfree _ i)
        (hrneg j) (hroot j).2
      have hh := tendsto_nhds_unique hl H
      refine ⟨?_, ?_⟩
      · rw [hh]
        exact exponentialMixtureLaplace_residue_pos hF (fun i _ => hc i) (fun i _ => hfree _ i) (hrneg j)
      · change w (some j) * exponentialMixtureLaplace Finset.univ c x (r (some j)) = 0
        rw [(hroot j).2, mul_zero]
  refine ⟨r, a, w, hzero, hrneg, ha, fun j => (hweights j).1, ?_⟩
  intro t
  rw [exponential_mixture_convolution_expansion c x w r hfree t]
  have hint : (∑ j, (w j * (∑ i, c i / (r j + x i))) * Real.exp (r j * t)) = 1 := by
    simp_rw [← show ∀ j, w j * R (r j) = w j * (∑ i, c i / (r j + x i)) from fun j => rfl]
    simp_rw [show ∀ j, w j * R (r j) = if j = none then 1 else 0 from fun j => (hweights j).2]
    rw [Fintype.sum_option]
    simp [hzero]
  have hcomp : (∑ i, (c i * (∑ j, w j / (r j + x i))) * Real.exp (-(x i * t))) =
      a * (∑ i, c i * Real.exp (-(x i * t))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← haCoeff i]
    ring
  rw [hint, hcomp]
  ring

/-- A finite positive mixture with nonpositive exponents has nonnegative
values and a nonpositive derivative at every real argument. -/
theorem positive_exponential_density_deriv_nonpos {ι : Type*} [Fintype ι]
    {w r : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hr : ∀ i, r i ≤ 0) (t : ℝ) :
    let ℓ (s : ℝ) := ∑ i, w i * Real.exp (r i * s)
    0 ≤ ℓ t ∧ deriv ℓ t ≤ 0 := by
  dsimp only
  refine ⟨Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (Real.exp_pos _).le), ?_⟩
  have hd : HasDerivAt (fun s : ℝ => ∑ i, w i * Real.exp (r i * s))
      (∑ i, w i * (Real.exp (r i * t) * r i)) t := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    have h := (Real.hasDerivAt_exp (r i * t)).comp t ((hasDerivAt_id t).const_mul (r i))
    simpa only [Function.comp_apply, id_eq, mul_one] using h.const_mul (w i)
  rw [hd.deriv]
  exact Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hw i)
    (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (hr i))

/-- The atom coefficient in the time-domain identity is the reciprocal
of the smooth kernel's value at zero. -/
theorem exponential_resolvent_atom_of_time_domain {ι jι : Type*} [Fintype ι] [Fintype jι]
    (c x : ι → ℝ) (w r : jι → ℝ) (a : ℝ)
    (h : ∀ t : ℝ, a * (∑ i, c i * Real.exp (-(x i * t))) +
      (∫ s in (0 : ℝ)..t, (∑ j, w j * Real.exp (r j * (t - s))) *
        (∑ i, c i * Real.exp (-(x i * s)))) = 1) :
    a = 1 / (∑ i, c i) := by
  have he := h 0
  simp only [mul_zero, neg_zero, Real.exp_zero, mul_one, intervalIntegral.integral_same, add_zero] at he
  have hne : ∑ i, c i ≠ 0 := by
    intro hz
    simp only [hz, mul_zero, zero_ne_one] at he
  exact (eq_div_iff hne).mpr he

end RoughHeston

#print axioms RoughHeston.exponential_mixture_convolution_expansion

#print axioms RoughHeston.positive_exponential_resolvent_time_domain

#print axioms RoughHeston.positive_exponential_density_deriv_nonpos
#print axioms RoughHeston.exponential_resolvent_atom_of_time_domain
