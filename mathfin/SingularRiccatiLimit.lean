import FractionalPowerRiccati

open MeasureTheory Filter Set
open scoped MeasureTheory Topology NNReal

namespace RoughHeston

private theorem fractionalL_nonneg_for_limit {α t : ℝ} (hα : α < 1) :
    0 ≤ fractionalL α t := by
  unfold fractionalL
  split
  · exact le_rfl
  · exact div_nonneg (Real.rpow_nonneg (le_of_lt (lt_of_not_ge ‹¬t ≤ 0›)) _)
      (Real.Gamma_pos_of_pos (sub_pos.mpr hα)).le

/-- The singular profile dominates the inverse convolution of a point
charge family and justifies the limiting inverse primitive. -/
theorem tendsto_fractionalL_point_charge_primitive {α c A t : ℝ} {w : ℕ → ℝ → ℝ}
    (hα : α < 1) (hc : 0 < c) (ht : 0 < t) (hm : ∀ n, Measurable (w n))
    (hb : ∀ n s, 0 < s → 0 ≤ w n s ∧ w n s ≤ singularRiccatiProfile α c s)
    (hlim : ∀ s > 0, Tendsto (fun n => w n s) atTop (𝓝 (singularRiccatiProfile α A s))) :
    Tendsto (fun n => volterraConvolution (fractionalL α) (w n) t) atTop
      (𝓝 (volterraConvolution (fractionalL α) (singularRiccatiProfile α A) t)) := by
  let ν := volume.restrict (Ioc (0 : ℝ) t)
  let L (s : ℝ) := fractionalL α (t - s)
  let V (s : ℝ) := singularRiccatiProfile α c s
  have hL : Measurable L := (fractionalL_measurable α).comp (measurable_const.sub measurable_id)
  have hD : Integrable (fun s => L s * V s) ν := by
    by_contra hbad
    have he := singularRiccatiProfile_primitive (c := c) hα ht
    change (∫ s, L s * V s ∂ν) = _ at he
    rw [integral_undef hbad] at he
    exact (mul_pos (mul_pos hc (div_pos (Real.Gamma_pos_of_pos (sub_pos.mpr hα))
      (Real.Gamma_pos_of_pos (by linarith : 0 < 2 - 2 * α)))) (Real.rpow_pos_of_pos ht _)).ne' he.symm
  refine tendsto_integral_of_dominated_convergence (fun s => L s * V s)
    (fun n => (hL.mul (hm n)).aestronglyMeasurable) hD (fun n => ?_) ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hB := hb n s hs.1
    have hL₀ : 0 ≤ L s := fractionalL_nonneg_for_limit hα
    rw [Real.norm_of_nonneg (mul_nonneg hL₀ hB.1)]
    exact mul_le_mul_of_nonneg_left hB.2 hL₀
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact (hlim s hs.1).const_mul (L s)

/-- If an undamped family has a positive homogeneous large-charge
limit, the integrated Riccati equation fixes its coefficient. The
proof takes differences of inverse primitives at two positive times,
so the charge term cancels before the limit. -/
theorem singularRiccatiCoefficient_of_primitive_limits
    {α a A : ℝ} {w : ℕ → ℝ → ℝ}
    (hα : 1 / 2 < α) (hα' : α < 1) (ha : 0 < a) (hA : 0 < A)
    (hm : ∀ n, Measurable (w n))
    (hb : ∀ n s, 0 < s → 0 ≤ w n s ∧
      w n s ≤ singularRiccatiProfile α (singularRiccatiCoefficient α a) s)
    (hlim : ∀ s > 0, Tendsto (fun n => w n s) atTop (𝓝 (singularRiccatiProfile α A s)))
    (hId : ∀ n, volterraConvolution (fractionalL α) (w n) 2 -
      volterraConvolution (fractionalL α) (w n) 1 =
        -a * ∫ s in Ioc (1 : ℝ) 2, (w n s) ^ 2) :
    A = singularRiccatiCoefficient α a := by
  let c := singularRiccatiCoefficient α a
  have hc : 0 < c := singularRiccatiCoefficient_pos hα hα' ha
  have hdiff := (tendsto_fractionalL_point_charge_primitive hα' hc (by norm_num : 0 < (2 : ℝ))
      hm hb hlim).sub (tendsto_fractionalL_point_charge_primitive hα' hc zero_lt_one hm hb hlim)
  have hR : Tendsto (fun n => ∫ s in Ioc (1 : ℝ) 2, (w n s) ^ 2) atTop
      (𝓝 (∫ s in Ioc (1 : ℝ) 2, (singularRiccatiProfile α A s) ^ 2)) := by
    let ν := volume.restrict (Ioc (1 : ℝ) 2)
    let D (s : ℝ) := (singularRiccatiProfile α c s) ^ 2
    have hD : ContinuousOn D (Icc (1 : ℝ) 2) := by
      have hbase : ContinuousOn (fun s : ℝ => c * s ^ (-α)) (Icc 1 2) := by
        apply continuousOn_const.mul
        intro s hs
        exact (continuousAt_id.rpow_const (Or.inl (zero_lt_one.trans_le hs.1).ne')).continuousWithinAt
      exact (hbase.pow 2).congr fun s hs => by
        simp only [D, singularRiccatiProfile, Pi.pow_apply, ite_eq_left (zero_lt_one.trans_le hs.1)]
    have hDi : Integrable D ν :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1 : ℝ) ≤ 2)).1
        (hD.intervalIntegrable_of_Icc (μ := volume) (by norm_num))
    refine tendsto_integral_of_dominated_convergence D
      (fun n => ((hm n).pow_const (2 : ℕ)).aestronglyMeasurable) hDi (fun n => ?_) ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      obtain ⟨h₀, h⟩ := hb n s (zero_lt_one.trans hs.1)
      change ‖(w n s)^2‖ ≤ (singularRiccatiProfile α c s)^2
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ h₀ h 2
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact (hlim s (zero_lt_one.trans hs.1)).pow 2
  have hz := tendsto_nhds_unique (hdiff.congr hId) (hR.const_mul (-a))
  rw [singularRiccatiProfile_primitive hα' (by norm_num : 0 < (2 : ℝ)),
    singularRiccatiProfile_primitive hα' zero_lt_one, Real.one_rpow, mul_one] at hz
  let k := 1 - 2 * α
  have hk : k < 0 := by dsimp [k]; linarith
  have hJ : (∫ s in Ioc (1 : ℝ) 2, (singularRiccatiProfile α A s) ^ 2) =
      A ^ 2 * ((2 : ℝ) ^ k - 1) / k := by
    have he : (∫ s in Ioc (1 : ℝ) 2, (singularRiccatiProfile α A s) ^ 2) =
        ∫ s in Ioc (1 : ℝ) 2, A ^ 2 * s ^ (-2 * α) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      have hs' := zero_lt_one.trans hs.1
      change (singularRiccatiProfile α A s) ^ 2 = A ^ 2 * s ^ (-2 * α)
      rw [singularRiccatiProfile, ite_eq_left hs', mul_pow, pow_two (s ^ (-α)),
        ← Real.rpow_add hs', show -α + -α = -2 * α by ring]
    rw [he, integral_const_mul, ← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2)]
    rw [integral_rpow (Or.inr ⟨by dsimp [k] at hk; linarith, by norm_num [uIcc_of_le]⟩),
      show -2 * α + 1 = k by dsimp [k]; ring, Real.one_rpow, mul_div_assoc]
  rw [hJ] at hz
  have hpow : (2 : ℝ) ^ k < 1 := by
    have he := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hk
    simpa only [Real.rpow_zero] using he
  have hf : (2 : ℝ) ^ k - 1 ≠ 0 := (sub_neg.mpr hpow).ne
  have hΓ : Real.Gamma (2 - 2 * α) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hz' : A * (Real.Gamma (1 - α) / Real.Gamma (2 - 2 * α)) * ((2 : ℝ) ^ k - 1) =
      (-a * A ^ 2 / k) * ((2 : ℝ) ^ k - 1) := by
    calc
      _ = A * (Real.Gamma (1 - α) / Real.Gamma (2 - 2 * α)) * (2 : ℝ) ^ k -
          A * (Real.Gamma (1 - α) / Real.Gamma (2 - 2 * α)) := by ring
      _ = _ := hz.trans (by ring)
  have heq := (mul_left_inj' hf).1 hz'
  unfold singularRiccatiCoefficient
  apply (eq_div_iff (mul_ne_zero ha.ne' hΓ)).2
  have hscaled := congrArg (fun x : ℝ => x * k * Real.Gamma (2 - 2 * α)) heq
  field_simp [hk.ne, hΓ] at hscaled
  dsimp [k] at hscaled
  rw [show (1 - α) * 2 = 2 - 2 * α by ring] at hscaled
  nlinarith

/-- Homogeneity and monotonicity of the positive undamped point charges
give the singular limit. The inverse-primitive identity identifies
its coefficient. -/
theorem tendsto_undamped_riccati_charge
    {α a : ℝ} {w : ℝ≥0 → ℝ → ℝ}
    (hα : 1 / 2 < α) (hα' : α < 1) (ha : 0 < a)
    (hm : ∀ n : ℕ, Measurable (w (n : ℝ≥0)))
    (hb : ∀ q s, 0 < s → 0 ≤ w q s ∧
      w q s ≤ singularRiccatiProfile α (singularRiccatiCoefficient α a) s)
    (hmono : Monotone (fun q => w q 1))
    (hpositive : ∃ q, 0 < w q 1)
    (hscale : ∀ q s, 0 < s → w q s =
      s ^ (-α) * w (q * (s ^ (2 * α - 1)).toNNReal) 1)
    (hId : ∀ n : ℕ, volterraConvolution (fractionalL α) (w (n : ℝ≥0)) 2 -
      volterraConvolution (fractionalL α) (w (n : ℝ≥0)) 1 =
        -a * ∫ s in Ioc (1 : ℝ) 2, (w (n : ℝ≥0) s) ^ 2) :
    ∀ s > 0, Tendsto (fun n : ℕ => w (n : ℝ≥0) s) atTop
      (𝓝 (singularRiccatiProfile α (singularRiccatiCoefficient α a) s)) := by
  let A : ℝ := ⨆ q : ℝ≥0, w q 1
  have hB : BddAbove (range fun q => w q 1) := by
    refine ⟨singularRiccatiCoefficient α a, ?_⟩
    rintro x ⟨q, rfl⟩
    simpa only [singularRiccatiProfile, ite_eq_left zero_lt_one, Real.one_rpow, mul_one] using
      (hb q 1 zero_lt_one).2
  have hA : 0 < A := by
    obtain ⟨q, hq⟩ := hpositive
    exact hq.trans_le (le_ciSup hB q)
  have htop : Tendsto (fun q : ℝ≥0 => w q 1) atTop (𝓝 A) :=
    tendsto_atTop_ciSup hmono hB
  have hlim (s : ℝ) (hs : 0 < s) : Tendsto (fun n : ℕ => w (n : ℝ≥0) s) atTop
      (𝓝 (singularRiccatiProfile α A s)) := by
    let scale := (s ^ (2 * α - 1)).toNNReal
    have hscalePos : 0 < scale := Real.toNNReal_pos.mpr (Real.rpow_pos_of_pos hs _)
    have hscaleTop : Tendsto (fun n : ℕ => (n : ℝ≥0) * scale) atTop atTop := by
      apply tendsto_atTop.2
      intro b
      filter_upwards [(tendsto_atTop.mp
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ≥0)) atTop atTop)) (b / scale)]
        with n hn
      exact (div_le_iff₀ hscalePos).1 hn
    have h := (htop.comp hscaleTop).const_mul (s ^ (-α))
    rw [singularRiccatiProfile, ite_eq_left hs, mul_comm A]
    exact h.congr (fun n => (hscale n s hs).symm)
  have hchar := singularRiccatiCoefficient_of_primitive_limits hα hα' ha hA hm
    (fun n s hs => hb n s hs) hlim hId
  simpa only [hchar] using hlim

end RoughHeston

#print axioms RoughHeston.tendsto_fractionalL_point_charge_primitive
#print axioms RoughHeston.singularRiccatiCoefficient_of_primitive_limits

#print axioms RoughHeston.tendsto_undamped_riccati_charge
