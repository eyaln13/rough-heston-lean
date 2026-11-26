import RiccatiGlobal
import RiccatiScalingBound

open MeasureTheory Set Filter
open scoped Topology NNReal

namespace RoughHeston

/-- The actual global undamped family converges to the singular solution
as positive integer charges increase. -/
theorem exists_global_undamped_riccati_family_limit
    {α a : ℝ} (hα : 1/2 < α) (hα' : α < 1) (ha : 0 < a) :
    ∃ w : ℝ≥0 → ℝ → ℝ,
      (∀ (q : ℝ≥0) (T : ℝ), PointChargeRiccatiOn α (q : ℝ) 0 (-a) T (w q)) ∧
      ∀ s > 0, Tendsto (fun n : ℕ => w (n : ℝ≥0) s) atTop
        (𝓝 (singularRiccatiProfile α (singularRiccatiCoefficient α a) s)) := by
  have hα₀ : 0 < α := by linarith
  have hex (q : ℝ≥0) : ∃ w : ℝ → ℝ, (∀ T, PointChargeRiccatiOn α (q : ℝ) 0 (-a) T w) ∧
      (q = 0 → w = fun _ => 0) := by
    rcases eq_or_lt_of_le (show 0 ≤ q from bot_le) with h0 | hq
    · subst q
      exact ⟨fun _ => 0, fun T => zero_pointChargeRiccatiOn α 0 (-a) T, fun _ => rfl⟩
    · obtain ⟨w, hw, _⟩ := exists_global_fractional_riccati_point_charge hα hα'
        (show 0 < (q : ℝ) from hq) le_rfl (neg_nonpos.mpr ha.le)
      exact ⟨w, hw, fun he => False.elim (hq.ne' he)⟩
  choose w hw hzero using hex
  refine ⟨w, hw, tendsto_undamped_riccati_charge hα hα' ha
    (fun n => (hw n 1).measurable) ?_ ?_ ?_ ?_ ?_⟩
  · intro q s hs
    have hW := hw q s
    have hs' : s ∈ Ioc (0 : ℝ) s := ⟨hs, le_rfl⟩
    constructor
    · rcases eq_or_lt_of_le (show 0 ≤ q from bot_le) with hq | hq
      · rw [hzero q hq.symm]
      · exact (point_charge_riccati_pos hα hα' hs hq hW s hs').le
    · have hv : ∀ t ∈ Ioc 0 s, w q t = (q : ℝ)*fractionalK α t +
          volterraConvolution (fractionalK α) (fun u => -(0 : ℝ)*w q u + -a*(w q u)^2) t := by
        simpa only [neg_zero] using hW.volterra
      exact (point_charge_riccati_lt_singular_profile hα hα' le_rfl ha hs
        hW.measurable hW.contDiffAt_pos hv hW.asymptotic s hs').le
  · exact point_charge_riccati_mono_charge_family hα hα'
      (show (1 : ℝ) ∈ Ioc 0 1 from ⟨zero_lt_one, le_rfl⟩) (fun q => hw q 1)
  · exact ⟨1, point_charge_riccati_pos hα hα' zero_lt_one (by norm_num)
      (hw 1 1) 1 ⟨zero_lt_one, le_rfl⟩⟩
  · intro q s hs
    rcases eq_or_lt_of_le (show 0 ≤ q from bot_le) with hq | hq
    · subst q
      rw [zero_mul, hzero 0 rfl, mul_zero]
    · let r := q * (s^(2*α-1)).toNNReal
      have hsPow := Real.rpow_pos_of_pos hs (2*α-1)
      have hr : (r : ℝ) = (q : ℝ)*s^(2*α-1) := by
        simp only [r, NNReal.coe_mul, Real.coe_toNNReal _ hsPow.le]
      have hr_pos : 0 < (r : ℝ) := by
        rw [hr]
        exact mul_pos hq hsPow
      have hres := (hw q (s*1)).rescale (T := 1) hs
      have hres' : PointChargeRiccatiOn α (r : ℝ) 0 (-a) 1 (fun t => s^α*w q (s*t)) := by
        rw [hr]
        simpa only [mul_zero] using hres
      have he := point_charge_riccati_eqOn_of_nonpositive_drift hα hα' zero_lt_one
        hr_pos le_rfl (neg_nonpos.mpr ha.le) (hw r 1) hres'
        (show (1 : ℝ) ∈ Ioc 0 1 from ⟨zero_lt_one, le_rfl⟩)
      change w r 1 = s^α*w q (s*1) at he
      rw [mul_one] at he
      change w q s = s^(-α)*w r 1
      rw [he, ← mul_assoc, ← Real.rpow_add hs, neg_add_cancel, Real.rpow_zero, one_mul]
  · intro n
    let u := w (n : ℝ≥0)
    let f (s : ℝ) := (u s)^2
    have hW := hw (n : ℝ≥0) 2
    have hWvol := hW.volterra
    have hf : IntegrableOn f (Ioc 0 2) :=
      (integrableOn_riccati_powers_of_weighted_asymptotic hα (by norm_num)
        hW.measurable hW.continuousOn_pos hW.asymptotic).2
    have hfi : IntegrableOn (fun s => (0:ℝ)*u s + -a*(u s)^2) (Ioc 0 2) := by
      simpa only [IntegrableOn, zero_mul, zero_add, f] using hf.const_mul (-a)
    have h1 := (fractional_riccati_rl_primitive hα₀ hα' (show (1:ℝ) ∈ Ioc 0 2 by norm_num)
      hW.measurable hfi hWvol).2
    have h2 := (fractional_riccati_rl_primitive hα₀ hα' (show (2:ℝ) ∈ Ioc 0 2 by norm_num)
      hW.measurable hfi hWvol).2
    simp only [zero_mul, zero_add, integral_const_mul] at h1 h2
    have hsplit : (∫ s in Ioc (0 : ℝ) 2, f s) =
        (∫ s in Ioc (0 : ℝ) 1, f s) + (∫ s in Ioc (1 : ℝ) 2, f s) := by
      rw [← Ioc_union_Ioc_eq_Ioc (show (0:ℝ) ≤ 1 by norm_num) (show (1:ℝ) ≤ 2 by norm_num)]
      exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
        (hf.mono_set (Ioc_subset_Ioc_right (by norm_num)))
        (hf.mono_set (Ioc_subset_Ioc_left (by norm_num)))
    change volterraConvolution (fractionalL α) u 2 -
      volterraConvolution (fractionalL α) u 1 = -a * ∫ s in Ioc (1 : ℝ) 2, f s
    rw [h2, h1]
    change ((n : ℝ) + -a * (∫ s in Ioc (0 : ℝ) 2, f s)) -
      ((n : ℝ) + -a * (∫ s in Ioc (0 : ℝ) 1, f s)) = _
    rw [hsplit]
    ring

/-- A uniform small-time lower bound for the actual damped point-charge
family, with the undamped singular limit and existence discharged. -/
theorem exists_global_riccati_uniform_boundary_lower
    {α a p κ H : ℝ}
    (hα : 1/2 < α) (hα' : α < 1) (ha : 0 < a) (hκ : 0 ≤ κ) (hH : 0 < H)
    (hp : caputoCoefficient α p < boundaryCoefficient α) :
    ∃ cLower : ℝ, caputoCoefficient α p < cLower ∧
      ∃ h₀ ∈ Ioc (0 : ℝ) H, ∃ N : ℕ, 0 < N ∧
        ∀ {δ u q : ℝ} {w : ℝ → ℝ}, 0 < δ → δ ≤ u → u ≤ h₀ →
          (N : ℝ) ≤ q*δ^(2*α-1) →
          PointChargeRiccatiOn α q (-κ) (-a) u w →
          cLower*u^(-α) ≤ 2*a*w u := by
  obtain ⟨w, hw, hlim⟩ := exists_global_undamped_riccati_family_limit hα hα' ha
  apply exists_scaled_riccati_uniform_boundary_lower hα hα' ha hκ hH hp (fun n => hw n 1)
  · simpa only [singularRiccatiProfile, ite_eq_left zero_lt_one, Real.one_rpow, mul_one]
      using hlim 1 zero_lt_one
  · intro q κ' hq hκ'
    obtain ⟨v, hv, _⟩ := exists_global_fractional_riccati_point_charge hα hα' hq
      (neg_nonpos.mpr hκ') (neg_nonpos.mpr ha.le)
    exact ⟨v, hv 1⟩

#print axioms exists_global_undamped_riccati_family_limit
#print axioms exists_global_riccati_uniform_boundary_lower

end RoughHeston
