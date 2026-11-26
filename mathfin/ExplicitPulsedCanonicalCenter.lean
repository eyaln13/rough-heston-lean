import ExplicitPulsedConvolutionLimit
import FractionalAggregatePair

/-! Uniform deterministic centering and inverse drift errors for the
physical pulse mesh in the variance-pair weak limit. -/

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

set_option maxHeartbeats 1500000

noncomputable def constantImmigrationConvolution (α b t : ℝ) : ℝ :=
  b*((max t 0)^α/(Real.Gamma α*α))

theorem continuous_constantImmigrationConvolution {α b : ℝ} (hα : 0 ≤ α) :
    Continuous (constantImmigrationConvolution α b) :=
  (((Real.continuous_rpow_const hα).comp (continuous_id.max continuous_const)).div_const _).const_mul _

theorem constantImmigrationConvolution_eq {α b t : ℝ} (hα : 0 < α) (ht : 0 ≤ t) :
    constantImmigrationConvolution α b t = b*(∫ s in (0:ℝ)..t, hestonKernel α s) := by
  rw [constantImmigrationConvolution, max_eq_left ht, hestonKernel_integral hα ht]

noncomputable def explicitPulsedCanonicalCenter (T : ℝ≥0) {α b ε d : ℝ}
    (hα : 0 < α) (hε : 0 < ε) (hb : 0 < b) (hd : 0 < d) : CanonicalPath T (ℝ × ℝ) where
  toFun t := (volterraConvolution (hestonKernel α) (explicitPulsedRate T b ε d) t.val,
    constantImmigrationConvolution α b t.val)
  continuous_toFun := ((continuous_explicitPulsed_convolution hα hε hb hd).prodMk
    (continuous_constantImmigrationConvolution hα.le)).comp
      (NNReal.continuous_coe.comp continuous_subtype_val)

noncomputable def constantImmigrationCanonicalCenter (T : ℝ≥0) {α b : ℝ}
    (hα : 0 ≤ α) : CanonicalPath T (ℝ × ℝ) where
  toFun t := (constantImmigrationConvolution α b t.val, constantImmigrationConvolution α b t.val)
  continuous_toFun := ((continuous_constantImmigrationConvolution hα).prodMk
    (continuous_constantImmigrationConvolution hα)).comp
      (NNReal.continuous_coe.comp continuous_subtype_val)

/-- For `d^α=ε`, the actual deterministic pulse convolver converges in
uniform norm on the whole observation interval. -/
theorem tendsto_explicitPulsedCanonicalCenter (T : ℝ≥0) {α b : ℝ}
    (hα : 1/2 < α) (hα' : α < 1) (hb : 0 < b)
    {ε d : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hd : ∀ n, 0 < d n) (hdΔ : ∀ n, d n ≤ ε n/b)
    (hScale : ∀ n, d n^α = ε n) (hε0 : Tendsto ε atTop (𝓝 0)) (hd0 : Tendsto d atTop (𝓝 0)) :
    Tendsto (fun n => explicitPulsedCanonicalCenter T (show 0 < α by linarith) (hε n) hb (hd n)) atTop
      (𝓝 (constantImmigrationCanonicalCenter T (b := b) (show 0 ≤ α by linarith))) := by
  have hα₀ : 0 < α := by linarith
  let C (n : ℕ) := b*((2*(ε n/b))^α/(Real.Gamma α*α))
  let E (n : ℕ) := 2*((d n)^(2*α-1)/(Real.Gamma α*α))
  have hC : Tendsto C atTop (𝓝 0) := by
    have hδ : Tendsto (fun n => 2*(ε n/b)) atTop (𝓝 0) := by
      simpa only [zero_div, mul_zero] using (hε0.div_const b).const_mul 2
    have h := (hδ.rpow_const_nhds_zero hα₀).div_const (Real.Gamma α*α)
    have h' := h.const_mul b
    simpa only [C, zero_div, mul_zero] using h'
  have hE : Tendsto E atTop (𝓝 0) := by
    simpa only [E, zero_div, mul_zero] using
      ((hd0.rpow_const_nhds_zero (show 0 < 2*α-1 by linarith)).div_const (Real.Gamma α*α)).const_mul 2
  have hBound (n : ℕ) :
      dist (explicitPulsedCanonicalCenter T hα₀ (hε n) hb (hd n))
        (constantImmigrationCanonicalCenter T (b := b) hα₀.le) ≤ C n+E n := by
    let : Nonempty (CanonicalPathTime T) := ⟨canonicalEvalTime T 0⟩
    apply (ContinuousMap.dist_le_iff_of_nonempty).2
    intro t
    have ht : (t.val:ℝ) ∈ Icc (0:ℝ) T := ⟨t.val.coe_nonneg, NNReal.coe_le_coe.mpr t.property.2⟩
    have h := explicitPulsed_convolution_difference_bounds hα₀ hα'.le (hε n) hb (hd n) (hdΔ n) ht
    dsimp only at h
    have hRate : (ε n/d n)*(d n^α/(Real.Gamma α*α)) = d n^(2*α-1)/(Real.Gamma α*α) := by
      rw [← hScale n, heston_scaled_pulse_bound (hd n)]
    rw [hRate] at h
    have hh := constantImmigrationConvolution_eq (b := b) hα₀ ht.1
    change dist (volterraConvolution (hestonKernel α) (explicitPulsedRate T b (ε n) (d n)) (t.val:ℝ),
        constantImmigrationConvolution α b t.val)
      (constantImmigrationConvolution α b t.val,constantImmigrationConvolution α b t.val) ≤ C n+E n
    rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, Real.dist_eq, hh]
    apply abs_le.mpr
    have hΓ : 0 ≤ Real.Gamma α*α := mul_nonneg (Real.Gamma_pos_of_pos hα₀).le hα₀.le
    have hCn : 0 ≤ C n := mul_nonneg hb.le
      (div_nonneg (Real.rpow_nonneg (mul_nonneg (by norm_num) (div_nonneg (hε n).le hb.le)) _) hΓ)
    have hEn : 0 ≤ E n := mul_nonneg (by norm_num) (div_nonneg (Real.rpow_nonneg (hd n).le _) hΓ)
    exact ⟨by dsimp [C,E] at *; linarith [h.1], by dsimp [C,E] at *; linarith [h.2]⟩
  have hh : Tendsto (fun n => C n+E n) atTop (𝓝 0) := by simpa only [add_zero] using hC.add hE
  exact tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero (fun _ => dist_nonneg) hBound hh)

/-- The deterministic reconstruction shift tends to zero at every
frozen time and has the uniform bound by one pulse mass. -/
theorem norm_explicitPulsed_canonicalImmigrationShift_le (T : ℝ≥0)
    {ε b d : ℝ} (hε : 0 < ε) (hb : 0 < b) (hd : 0 < d) (hdΔ : d ≤ ε/b) (t : ℝ≥0) :
    ‖canonicalImmigrationShift T b (fun s => explicitPulsedRate T b ε d s) t‖ ≤ ε := by
  let u := min t T
  have hu : (u:ℝ) ∈ Icc (0:ℝ) T := ⟨u.coe_nonneg, NNReal.coe_le_coe.mpr (min_le_right _ _)⟩
  have h := explicitPulsedRate_clock_error_le hε hb hd hdΔ hu
  unfold canonicalImmigrationShift
  have he : (∫ s in (0:ℝ)..(u:ℝ), explicitPulsedRate T b ε d (s.toNNReal:ℝ)) =
      ∫ s in (0:ℝ)..(u:ℝ), explicitPulsedRate T b ε d s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hu.1] at hs
    change explicitPulsedRate T b ε d (s.toNNReal:ℝ) = _
    rw [Real.coe_toNNReal s hs.1]
  change ‖b*(u:ℝ) - ∫ s in (0:ℝ)..(u:ℝ), explicitPulsedRate T b ε d (s.toNNReal:ℝ)‖ ≤ ε
  rw [he, Real.norm_eq_abs, abs_sub_comm]
  exact h

#print axioms RoughHeston.tendsto_explicitPulsedCanonicalCenter
#print axioms RoughHeston.norm_explicitPulsed_canonicalImmigrationShift_le

end RoughHeston
