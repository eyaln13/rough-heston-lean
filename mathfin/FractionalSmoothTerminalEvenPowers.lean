import FractionalSmoothVarianceDominance
import FractionalSmoothWeightedMoment
import WeightedSquareExpectation

/-! Terminal noise moments across the complete even-power range. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

set_option maxHeartbeats 1200000

/-- At power two the exact expected bracket has constant one. -/
noncomputable def rawMartingaleMomentConstant (m : ℕ) : ℝ≥0∞ :=
  if m = 1 then 1 else boundedMartingaleEvenPowerConstant m

theorem rawMartingaleMomentConstant_ne_top (m : ℕ) (hm : 1 ≤ m) :
    rawMartingaleMomentConstant m ≠ ⊤ := by
  unfold rawMartingaleMomentConstant
  split_ifs with h
  · exact ENNReal.one_ne_top
  · exact boundedMartingaleEvenPowerConstant_ne_top m (by omega)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {T : ℝ≥0} {α κ σ : ℝ} {n : ℕ} {v : Option ι → ℝ} {β : Option ι → ℝ≥0 → ℝ}

namespace FractionalCoupledSmoothLaw

/-- The direct-kernel terminal noise has a uniform moment bound in
terms of the identical-order unweighted variance input and kernel energy. -/
theorem terminalNoise_even_moment_le
    (L : FractionalCoupledSmoothLaw T α n κ σ v β)
    (hK : fractionalExponentialApproximation α n 0 ≠ 0)
    (i : Option ι) {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B)
    {H : ℝ≥0} (hH : H ≤ T) (m : ℕ) (hm : 1 ≤ m)
    {C : ℝ≥0∞}
    (hMoment : ∀ u ≤ T, (∫⁻ p, ENNReal.ofReal (max (L.variance i u p) 0)^m
        ∂(L.law : Measure _)) ≤ C) :
    (∫⁻ p, ‖L.terminalNoise i H p‖ₑ ^ (2*m : ℕ) ∂(L.law : Measure _)) ≤
      rawMartingaleMomentConstant m * ENNReal.ofReal
        (∫ r in (0:ℝ)..(H:ℝ), (fractionalExponentialApproximation α n ((H:ℝ)-r))^2*σ^2)^m*C := by
  let Ω := CanonicalPath T (FractionalCoupledSmoothState ι n)
  let μ : Measure Ω := L.law
  let ν := volume.restrict (Ioc (0:ℝ) (H:ℝ))
  let c := fractionalApproximationFinWeight α n
  let x := fractionalApproximationFinRate n
  let K := smoothExponentialKernel c x
  let k := smoothExponentialKernelDerivative c x
  let g (r : ℝ) := K ((H : ℝ)-r)
  let d (r : ℝ) := -k ((H : ℝ)-r)
  let w (r : ℝ) := (g r)^2*σ^2
  let V (r : ℝ) (p : Ω) := max (L.variance i r.toNNReal p) 0
  let Y (r : ℝ≥0) (p : Ω) :=
    g (min r H : ℝ≥0) * L.residual i (min r H) p - g 0 * L.residual i 0 p -
      ∫ z in (0 : ℝ)..((min r H : ℝ≥0):ℝ), d z * L.residual i z.toNNReal p
  let A (r : ℝ≥0) (p : Ω) :=
    ∫ z in (0 : ℝ)..((min r H : ℝ≥0):ℝ), (g z)^2 * (σ^2 * max (L.variance i z.toNNReal p) 0)
  have hg : ContDiff ℝ 1 g := by
    unfold g K smoothExponentialKernel
    exact ContDiff.sum fun j _ => by fun_prop
  have hd : Continuous d := ((continuous_smoothExponentialKernelDerivative c x).comp
    (continuous_const.sub continuous_id)).neg
  have hgd (r : ℝ) : HasDerivAt g (d r) r := by
    have h := (smoothExponentialKernel_hasDerivAt c x ((H:ℝ)-r)).comp r
      ((hasDerivAt_id r).const_sub (H:ℝ))
    change HasDerivAt g (k ((H:ℝ)-r)*(-1)) r at h
    simpa only [mul_neg, mul_one, d] using h
  have hterm : Y H =ᵐ[μ] L.terminalNoise i H := by
    filter_upwards [L.residual_starts_zero i hB hβ hβB] with p hp
    have h0 : L.residual i 0 p = 0 := hp
    simp only [terminalNoise, smoothKernelMartingaleConvolution, Y, min_self, g, d, K, k, c, x,
      sub_self, h0, mul_zero, sub_zero, neg_mul, intervalIntegral.integral_neg,
      sub_neg_eq_add, Real.toNNReal_coe]
  have hTermPow : (fun p => ‖Y H p‖ₑ ^ (2*m : ℕ)) =ᵐ[μ]
      (fun p => ‖L.terminalNoise i H p‖ₑ ^ (2*m : ℕ)) :=
    hterm.mono fun p hp => by simp [hp]
  rw [← lintegral_congr_ae hTermPow]
  have hKg : ∀ r : ℝ, g r = fractionalExponentialApproximation α n ((H:ℝ)-r) :=
    fun r => smoothExponentialKernel_eq_fractionalExponentialApproximation α n ((H:ℝ)-r)
  simp_rw [← hKg]
  by_cases h1 : m = 1
  · subst m
    obtain ⟨hYm, hY₂, hYc, hAc, hAmon, hY₀, hA₀, hAY⟩ :=
      L.rawDeterministicWeightedRow hK i hB hβ hβB hH hg hd hgd
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
    have hν : ∀ᵐ r ∂ν, (∫⁻ p, ENNReal.ofReal (V r p) ∂μ) ≤ C := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      have hrt : r.toNNReal ≤ H :=
        NNReal.coe_le_coe.mp ((Real.coe_toNNReal r hr.1.le).trans_le hr.2)
      simpa only [pow_one] using hMoment r.toNNReal (hrt.trans hH)
    have hWint : Integrable w ν := (hw.intervalIntegrable (μ := volume) 0 H).1
    have hAeq (p : Ω) :
        A H p = ∫ r in (0:ℝ)..(H:ℝ), w r*V r p := by
      simp only [A, w, V, min_self, mul_assoc]
    have hClk : ∀ᵐ p ∂μ, 0 ≤ A H p ∧ ENNReal.ofReal (A H p) =
        ∫⁻ r, ENNReal.ofReal (w r)*ENNReal.ofReal (V r p) ∂ν := by
      apply Eventually.of_forall
      intro p
      rw [hAeq p, intervalIntegral.integral_of_le H.coe_nonneg]
      refine ⟨integral_nonneg fun r => mul_nonneg (hw₀ r) (le_max_right _ _), ?_⟩
      have hi : Integrable (fun r => w r*V r p) ν :=
        ((hw.mul (hv p)).intervalIntegrable (μ := volume) 0 H).1
      rw [ofReal_integral_eq_lintegral_ofReal hi
        (Eventually.of_forall fun r => mul_nonneg (hw₀ r) (le_max_right _ _))]
      exact lintegral_congr fun r => ENNReal.ofReal_mul (hw₀ r)
    have h := lintegral_martingale_sq_le_weighted_clock hY₂ hAY
      (Eventually.of_forall hY₀) (Eventually.of_forall hA₀) H hw.measurable.ennreal_ofReal hVm hClk hν
    rw [← ofReal_integral_eq_lintegral_ofReal hWint (Eventually.of_forall hw₀),
      ← intervalIntegral.integral_of_le H.coe_nonneg] at h
    simpa only [rawMartingaleMomentConstant, ite_true, one_mul, pow_one, Nat.mul_one, w] using h
  · have hm₂ : 2 ≤ m := by omega
    have h := L.rawWeightedRow_increment_even_moment_le hK i hB hβ hβB hH hg hd hgd
      (s := 0) (t := H) zero_le le_rfl m hm₂ hMoment
    have hY₀ (p : Ω) : Y 0 p = 0 := by simp [Y]
    simpa only [rawMartingaleMomentConstant, h1, ite_false, NNReal.coe_zero, Y, hY₀, sub_zero] using h

end FractionalCoupledSmoothLaw

#print axioms RoughHeston.FractionalCoupledSmoothLaw.terminalNoise_even_moment_le

end RoughHeston
