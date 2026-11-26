import RiccatiDampingBound

open MeasureTheory Set Filter
open scoped Topology

namespace RoughHeston

/-- Rescale the regular point-charge solution, including its weighted
initial value and its full Volterra equation. -/
theorem PointChargeRiccatiOn.rescale
    {α q b c r T : ℝ} {w : ℝ → ℝ} (hr : 0 < r)
    (hw : PointChargeRiccatiOn α q b c (r*T) w) :
    PointChargeRiccatiOn α (q*r^(2*α-1)) (r^α*b) c T (fun s => r^α*w (r*s)) := by
  refine ⟨(hw.measurable.comp (measurable_const.mul measurable_id)).const_mul _, ?_,
    fractional_riccati_rescale hr hw.volterra, ?_⟩
  · intro t ht
    have hlin : ContDiffAt ℝ 1 (fun s : ℝ => r*s) t :=
      contDiffAt_const.mul contDiffAt_id
    exact contDiffAt_const.mul ((hw.contDiffAt_pos (r*t) (mul_pos hr ht)).comp t hlin)
  · have hDil : Tendsto (fun s : ℝ => r*s) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have h0 : ContinuousAt (fun s : ℝ => r*s) (0 : ℝ) :=
          continuousAt_const.mul continuousAt_id
        simpa only [mul_zero] using h0.tendsto.mono_left
          (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
      · filter_upwards [self_mem_nhdsWithin] with s hs
        exact mul_pos hr (show 0 < s from hs)
    have hlim := (hw.asymptotic.comp hDil).const_mul (r^(2*α-1))
    rw [show r^(2*α-1)*(q/Real.Gamma α)=q*r^(2*α-1)/Real.Gamma α by ring] at hlim
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs₀ : 0 < s := hs
    change r^(2*α-1)*((r*s)^(1-α)*w (r*s)) = s^(1-α)*(r^α*w (r*s))
    have hpow : r^α = r^(2*α-1)*r^(1-α) := by
      rw [← Real.rpow_add hr, show 2*α-1+(1-α)=α by ring]
    rw [Real.mul_rpow hr.le hs₀.le, hpow]
    ring

/-- One coefficient strictly above the Caputo comparison level works at
all sufficiently small observation times. The same finite threshold
applies to the rescaled charge based on the lower time cutoff. -/
theorem exists_scaled_riccati_uniform_boundary_lower
    {α a p κ H : ℝ} {v : ℕ → ℝ → ℝ}
    (hα : 1/2 < α) (hα' : α < 1) (ha : 0 < a) (hκ : 0 ≤ κ) (hH : 0 < H)
    (hp : caputoCoefficient α p < boundaryCoefficient α)
    (hv : ∀ n : ℕ, PointChargeRiccatiOn α (n : ℝ) 0 (-a) 1 (v n))
    (hlim : Tendsto (fun n => v n 1) atTop (𝓝 (singularRiccatiCoefficient α a)))
    (hDamped : ∀ (q κraw : ℝ), 0 < q → 0 ≤ κraw →
      ∃ w : ℝ → ℝ, PointChargeRiccatiOn α q (-κraw) (-a) 1 w) :
    ∃ cLower : ℝ, caputoCoefficient α p < cLower ∧
      ∃ h₀ ∈ Ioc (0 : ℝ) H, ∃ N : ℕ, 0 < N ∧
        ∀ {δ u q : ℝ} {w : ℝ → ℝ}, 0 < δ → δ ≤ u → u ≤ h₀ →
          (N : ℝ) ≤ q*δ^(2*α-1) →
          PointChargeRiccatiOn α q (-κ) (-a) u w →
          cLower*u^(-α) ≤ 2*a*w u := by
  have hα₀ : 0 < α := by linarith
  have hβ : 0 < 2*α-1 := by linarith
  let c := (caputoCoefficient α p + boundaryCoefficient α)/2
  have hcp : caputoCoefficient α p < c := by dsimp [c]; linarith only [hp]
  have hcb : c < boundaryCoefficient α := by dsimp [c]; linarith only [hp]
  let η := (boundaryCoefficient α-c)/(2*a)
  have hη : 0 < η := div_pos (sub_pos.mpr hcb) (mul_pos (by norm_num) ha)
  have hlim' (t : ℝ) (ht : t ∈ Icc (1 : ℝ) 1) :
      Tendsto (fun n => v n t) atTop
        (𝓝 (singularRiccatiProfile α (singularRiccatiCoefficient α a) t)) := by
    have he : t = 1 := le_antisymm ht.2 ht.1
    subst t
    simpa only [singularRiccatiProfile, ite_eq_left zero_lt_one, Real.one_rpow, mul_one] using hlim
  obtain ⟨N, hN, κ₀, hκ₀, hLower⟩ := exists_finite_charge_damped_lower_bound hα hα' ha.le
    (show (0 : ℝ) < 1 from zero_lt_one) le_rfl hη hv hlim'
  obtain ⟨h₀, hh₀, hSmall⟩ := exists_small_fractional_riccati_scale
    (κ := κ) hα₀ hH hκ₀
  have hCoeff : 2*a*(singularRiccatiCoefficient α a-η) = c := by
    rw [mul_sub, two_mul_singularRiccatiCoefficient hα' ha]
    dsimp [η]
    field_simp [ha.ne']
    ring
  refine ⟨c, hcp, h₀, hh₀, N, hN, ?_⟩
  intro δ u q w hδ hδu huh₀ hCharge hw
  have hu := hδ.trans_le hδu
  have hN₀ : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hq : 0 < q := by
    by_contra! hq
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hq (Real.rpow_nonneg hδ.le _)))
      (hN₀.trans_le hCharge)
  let q' := q*u^(2*α-1)
  have hqN : (N : ℝ) ≤ q' := hCharge.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hδ.le hδu hβ.le) hq.le)
  let κ' := κ*u^α
  have hκ' : 0 ≤ κ' := mul_nonneg hκ (Real.rpow_nonneg hu.le _)
  have hκ'max : κ' ≤ κ₀ := by
    calc
      _ ≤ κ*h₀^α := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hu.le huh₀ hα₀.le) hκ
      _ = ‖κ‖*h₀^α := by rw [Real.norm_of_nonneg hκ]
      _ ≤ _ := hSmall.le
  let W (t : ℝ) := u^α*w (u*t)
  have hwU : PointChargeRiccatiOn α q (-κ) (-a) (u*1) w := by simpa only [mul_one] using hw
  have hW' := hwU.rescale hu
  have hW : PointChargeRiccatiOn α q' (-κ') (-a) 1 W := by
    change PointChargeRiccatiOn α (q*u^(2*α-1)) (-(κ*u^α)) (-a) 1 (fun t => u^α*w (u*t))
    simpa only [mul_neg, mul_comm (u^α) κ] using hW'
  obtain ⟨z, hz⟩ := hDamped (N : ℝ) κ' hN₀ hκ'
  have hzW := point_charge_riccati_le_of_drift_coefficients hα hα' (T := 1)
    zero_lt_one hN₀ hqN le_rfl le_rfl (neg_nonpos.mpr hκ') (neg_nonpos.mpr ha.le) hW hz
    1 ⟨zero_lt_one, le_rfl⟩
  have hzLower := hLower κ' ⟨hκ', hκ'max⟩ hz 1 ⟨le_rfl, le_rfl⟩
  rw [Real.one_rpow, mul_one] at hzLower
  have hW1 : c ≤ 2*a*(u^α*w u) := by
    rw [← hCoeff]
    have h := mul_le_mul_of_nonneg_left (hzLower.trans hzW)
      (show 0 ≤ (2 : ℝ)*a from mul_nonneg (by norm_num) ha.le)
    simpa only [W, mul_one] using h
  apply (mul_le_mul_iff_of_pos_left (Real.rpow_pos_of_pos hu α)).mp
  calc
    _ = c := by
      rw [mul_left_comm, ← Real.rpow_add hu, add_neg_cancel, Real.rpow_zero, mul_one]
    _ ≤ 2*a*(u^α*w u) := hW1
    _ = _ := by ring

#print axioms PointChargeRiccatiOn.rescale
#print axioms exists_scaled_riccati_uniform_boundary_lower

end RoughHeston
