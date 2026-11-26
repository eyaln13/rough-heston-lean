import FractionalSmoothRawWeighted
import RawMartingaleIncrementEvenPower
import KernelMomentTransfer

/-! Uniform weighted even moments for each actual smooth martingale row. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

set_option maxHeartbeats 1300000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {T : ℝ≥0} {α κ σ : ℝ} {n : ℕ} {v : Option ι → ℝ} {β : Option ι → ℝ≥0 → ℝ}

namespace FractionalCoupledSmoothLaw

/-- The square energy of the deterministic weight is the only
kernel-dependent factor in the smooth weighted even moment bound. -/
theorem rawWeightedRow_increment_even_moment_le
    (L : FractionalCoupledSmoothLaw T α n κ σ v β)
    (hK : fractionalExponentialApproximation α n 0 ≠ 0)
    (i : Option ι) {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B)
    {H : ℝ≥0} (hH : H ≤ T) {g d : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g) (hd : Continuous d) (hgd : ∀ s, HasDerivAt g (d s) s)
    {s t : ℝ≥0} (hst : s ≤ t) (ht : t ≤ H) (m : ℕ) (hm : 2 ≤ m)
    {C : ℝ≥0∞}
    (hMoment : ∀ u ≤ T, (∫⁻ p, ENNReal.ofReal (max (L.variance i u p) 0)^m
        ∂(L.law : Measure _)) ≤ C) :
    let M := L.residual i
    let Y (r : ℝ≥0) (p : CanonicalPath T (FractionalCoupledSmoothState ι n)) :=
      g (min r H : ℝ≥0) * M (min r H) p - g 0 * M 0 p -
        ∫ z in (0 : ℝ)..((min r H : ℝ≥0):ℝ), d z * M z.toNNReal p
    (∫⁻ p, ‖Y t p-Y s p‖ₑ ^ (2*m : ℕ) ∂(L.law : Measure _)) ≤
      boundedMartingaleEvenPowerConstant m *
        ENNReal.ofReal (∫ r in (s:ℝ)..(t:ℝ), (g r)^2 * σ^2)^m*C := by
  dsimp only
  let Ω := CanonicalPath T (FractionalCoupledSmoothState ι n)
  let μ : Measure Ω := L.law
  let ν := volume.restrict (Ioc (s:ℝ) (t:ℝ))
  let Y (r : ℝ≥0) (p : Ω) :=
    g (min r H : ℝ≥0) * L.residual i (min r H) p - g 0 * L.residual i 0 p -
      ∫ z in (0 : ℝ)..((min r H : ℝ≥0):ℝ), d z * L.residual i z.toNNReal p
  let A (r : ℝ≥0) (p : Ω) :=
    ∫ z in (0 : ℝ)..((min r H : ℝ≥0):ℝ), (g z)^2 * (σ^2 * max (L.variance i z.toNNReal p) 0)
  let w (r : ℝ) := (g r)^2 * σ^2
  let V (r : ℝ) (p : Ω) := max (L.variance i r.toNNReal p) 0
  obtain ⟨hY, hY₂, hYc, hAc, hAmon, _, _, hAY⟩ := L.rawDeterministicWeightedRow
    hK i hB hβ hβB hH hg hd hgd
  have hδ := continuous_raw_martingale_increment_even_power_le hY hY₂ hYc hAY hAc
    (Eventually.of_forall hAmon) hst m hm
  have hw : Continuous w := (hg.continuous.pow 2).mul continuous_const
  have hw₀ (r : ℝ) : 0 ≤ w r := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hv (p : Ω) : Continuous (fun r => V r p) :=
    ((L.variance_continuous_time i hB hβ hβB p).comp continuous_real_toNNReal).max continuous_const
  have hV (r : ℝ) : Measurable (V r) := by
    have hM : StronglyMeasurable[canonicalPathNaturalFiltration T r.toNNReal] (L.variance i r.toNNReal) :=
      L.variance_stronglyAdapted i r.toNNReal
    have hM' := hM.mono ((canonicalPathNaturalFiltration (E := FractionalCoupledSmoothState ι n) T).le _)
    exact ((continuous_id.max continuous_const).comp_stronglyMeasurable hM').measurable
  have hVm : Measurable (Function.uncurry fun r p => ENNReal.ofReal (V r p)) :=
    (measurable_uncurry_of_continuous_of_measurable hv hV).ennreal_ofReal
  have hν : ∀ᵐ r ∂ν, (∫⁻ p, ENNReal.ofReal (V r p) ^ (m:ℝ) ∂μ) ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr₀ : 0 ≤ r := (NNReal.coe_nonneg s).trans hr.1.le
    have hrt : r.toNNReal ≤ t := NNReal.coe_le_coe.mp ((Real.coe_toNNReal r hr₀).trans_le hr.2)
    simpa only [ENNReal.rpow_natCast] using hMoment r.toNNReal (hrt.trans (ht.trans hH))
  have hWint : Integrable w ν := (hw.intervalIntegrable (μ := volume) s t).1
  have hAeq (p : Ω) :
      ENNReal.ofReal (A t p - A s p) =
        ∫⁻ r, ENNReal.ofReal (w r) * ENNReal.ofReal (V r p) ∂ν := by
    have hI : IntervalIntegrable (fun r => w r*V r p) volume 0 (t : ℝ) :=
      (hw.mul (hv p)).intervalIntegrable _ _
    have hIs : IntervalIntegrable (fun r => w r*V r p) volume 0 (s : ℝ) :=
      (hw.mul (hv p)).intervalIntegrable _ _
    have hIst : IntervalIntegrable (fun r => w r*V r p) volume s (t : ℝ) :=
      (hw.mul (hv p)).intervalIntegrable _ _
    have hAdd := intervalIntegral.integral_add_adjacent_intervals hIs hIst
    have hSub : A t p-A s p = ∫ r in (s : ℝ)..(t : ℝ), w r*V r p := by
      dsimp [A]
      simp only [min_eq_left ht, min_eq_left (hst.trans ht), w, V, mul_assoc] at hAdd ⊢
      linarith
    rw [hSub, intervalIntegral.integral_of_le (NNReal.coe_le_coe.mpr hst)]
    rw [ofReal_integral_eq_lintegral_ofReal hIst.1]
    · apply lintegral_congr
      intro r
      exact ENNReal.ofReal_mul (hw₀ r)
    · exact Eventually.of_forall fun r => mul_nonneg (hw₀ r) (le_max_right _ _)
  have hp : 2*(m:ℝ) = ((2*m : ℕ) : ℝ) := by push_cast; rfl
  have hBDG :
      (∫⁻ p, ‖Y t p-Y s p‖ₑ ^ (2*(m:ℝ)) ∂μ) ≤ boundedMartingaleEvenPowerConstant m *
        ∫⁻ p, (∫⁻ r, ENNReal.ofReal (w r) * ENNReal.ofReal (V r p) ∂ν)^(m:ℝ) ∂μ := by
    rw [hp]
    simpa only [ENNReal.rpow_natCast, ← hAeq] using hδ
  have hh := kernel_noise_moment_le_of_bdg (μ := μ) (ν := ν) (m := (m:ℝ))
    (by exact_mod_cast (show 1 < m by omega)) hw.measurable.ennreal_ofReal hVm hν hBDG
  have hW : (∫⁻ r, ENNReal.ofReal (w r) ∂ν) =
      ENNReal.ofReal (∫ r in (s:ℝ)..(t:ℝ), w r) := by
    rw [intervalIntegral.integral_of_le (NNReal.coe_le_coe.mpr hst)]
    exact (ofReal_integral_eq_lintegral_ofReal hWint (Eventually.of_forall hw₀)).symm
  rw [hW, hp] at hh
  simpa only [ENNReal.rpow_natCast] using hh

end FractionalCoupledSmoothLaw

#print axioms RoughHeston.FractionalCoupledSmoothLaw.rawWeightedRow_increment_even_moment_le

end RoughHeston
