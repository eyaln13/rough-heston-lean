import FractionalSmoothWeightedMoment
import FractionalSmoothVarianceDominance
import FractionalSmoothIncrementKernels

/-! The old and recent stochastic increments, with approximation-uniform
fractional moment bounds. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

set_option maxHeartbeats 1300000

theorem enorm_add_pow_le {a b : ℝ} (p : ℕ) :
    ‖a+b‖ₑ^p ≤ (2:ℝ≥0∞)^p * (‖a‖ₑ^p+‖b‖ₑ^p) := by
  let c := max ‖a‖ₑ ‖b‖ₑ
  have hsum : ‖a+b‖ₑ ≤ 2*c := by
    calc
      _ ≤ ‖a‖ₑ+‖b‖ₑ := enorm_add_le _ _
      _ ≤ c+c := add_le_add (le_max_left _ _) (le_max_right _ _)
      _ = _ := (two_mul c).symm
  apply (pow_le_pow_left' hsum p).trans
  rw [mul_pow]
  gcongr
  rcases le_total ‖a‖ₑ ‖b‖ₑ with h | h
  · exact (congrArg (fun x : ℝ≥0∞ => x^p) (max_eq_right h)).le.trans le_add_self
  · exact (congrArg (fun x : ℝ≥0∞ => x^p) (max_eq_left h)).le.trans le_self_add

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {T : ℝ≥0} {α κ σ : ℝ} {n : ℕ} {v : Option ι → ℝ} {β : Option ι → ℝ≥0 → ℝ}

namespace FractionalCoupledSmoothLaw

/-- Backward deterministic weight from the smooth direct kernel. -/
noncomputable def smoothBackwardWeight (α : ℝ) (n : ℕ) (t : ℝ≥0) (r : ℝ) : ℝ :=
  smoothExponentialKernel (fractionalApproximationFinWeight α n)
    (fractionalApproximationFinRate n) ((t:ℝ)-r)

noncomputable def smoothBackwardWeightDeriv (α : ℝ) (n : ℕ) (t : ℝ≥0) (r : ℝ) : ℝ :=
  -smoothExponentialKernelDerivative (fractionalApproximationFinWeight α n)
    (fractionalApproximationFinRate n) ((t:ℝ)-r)

theorem smoothBackwardWeight_contDiff (α : ℝ) (n : ℕ) (t : ℝ≥0) :
    ContDiff ℝ 1 (smoothBackwardWeight α n t) := by
  unfold smoothBackwardWeight smoothExponentialKernel
  exact ContDiff.sum fun _ _ => by fun_prop

theorem smoothBackwardWeightDeriv_continuous (α : ℝ) (n : ℕ) (t : ℝ≥0) :
    Continuous (smoothBackwardWeightDeriv α n t) :=
  ((continuous_smoothExponentialKernelDerivative (fractionalApproximationFinWeight α n)
    (fractionalApproximationFinRate n)).comp (continuous_const.sub continuous_id)).neg

theorem hasDerivAt_smoothBackwardWeight (α : ℝ) (n : ℕ) (t : ℝ≥0) (r : ℝ) :
    HasDerivAt (smoothBackwardWeight α n t) (smoothBackwardWeightDeriv α n t r) r := by
  have h := (smoothExponentialKernel_hasDerivAt (fractionalApproximationFinWeight α n)
    (fractionalApproximationFinRate n) ((t:ℝ)-r)).comp r ((hasDerivAt_id r).const_sub (t:ℝ))
  change HasDerivAt (smoothBackwardWeight α n t)
    (smoothExponentialKernelDerivative (fractionalApproximationFinWeight α n)
      (fractionalApproximationFinRate n) ((t:ℝ)-r)*(-1)) r at h
  simpa only [smoothBackwardWeightDeriv, mul_neg, mul_one] using h

/-- Integration-by-parts form of one old or recent deterministic
weighted integral. -/
noncomputable def smoothWeightedIntegralForm (L : FractionalCoupledSmoothLaw T α n κ σ v β)
    (i : Option ι) (H : ℝ≥0) (g d : ℝ → ℝ) (r : ℝ≥0)
    (p : CanonicalPath T (FractionalCoupledSmoothState ι n)) : ℝ :=
  g (min r H : ℝ≥0) * L.residual i (min r H) p - g 0 * L.residual i 0 p -
    ∫ z in (0 : ℝ)..((min r H : ℝ≥0):ℝ), d z * L.residual i z.toNNReal p

/-- Splitting a stochastic convolution increment into a recent
increment and a change in the old weight is exact pathwise. -/
theorem ae_terminalNoise_increment_split
    (L : FractionalCoupledSmoothLaw T α n κ σ v β) (i : Option ι)
    {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B)
    {s t : ℝ≥0} (hst : s ≤ t) :
    let Y := L.smoothWeightedIntegralForm i t (smoothBackwardWeight α n t) (smoothBackwardWeightDeriv α n t)
    let Z := L.smoothWeightedIntegralForm i s
      (fun r => smoothBackwardWeight α n t r-smoothBackwardWeight α n s r)
      (fun r => smoothBackwardWeightDeriv α n t r-smoothBackwardWeightDeriv α n s r)
    ∀ᵐ p ∂(L.law : Measure _),
      L.terminalNoise i t p-L.terminalNoise i s p = (Y t p-Y s p)+Z s p := by
  dsimp only
  filter_upwards [L.residual_starts_zero i hB hβ hβB] with p hp
  have h0 : L.residual i 0 p = 0 := hp
  have hM : Continuous (fun r : ℝ => L.residual i r.toNNReal p) :=
    (L.residual_continuous_time i hB hβ hβB p).comp continuous_real_toNNReal
  have htI : IntervalIntegrable (fun r => smoothBackwardWeightDeriv α n t r * L.residual i r.toNNReal p)
      volume 0 (s:ℝ) := ((smoothBackwardWeightDeriv_continuous α n t).mul hM).intervalIntegrable _ _
  have hsI : IntervalIntegrable (fun r => smoothBackwardWeightDeriv α n s r * L.residual i r.toNNReal p)
      volume 0 (s:ℝ) := ((smoothBackwardWeightDeriv_continuous α n s).mul hM).intervalIntegrable _ _
  simp only [smoothWeightedIntegralForm, min_self, min_eq_left hst, h0, mul_zero, sub_zero, sub_mul]
  rw [intervalIntegral.integral_sub htI hsI]
  simp only [terminalNoise, smoothKernelMartingaleConvolution, smoothBackwardWeight, smoothBackwardWeightDeriv,
    sub_self, Real.toNNReal_coe, neg_mul, intervalIntegral.integral_neg]
  ring

/-- Uniform bound for the stochastic part of a smooth variance
increment. The coefficient contains only the fractional kernel
energy and the timewise variance moment at half the output order. -/
theorem terminalNoise_increment_even_moment_le
    (L : FractionalCoupledSmoothLaw T α n κ σ v β)
    (hα : 1/2 < α) (hα' : α < 1) (i : Option ι)
    {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B)
    {s t : ℝ≥0} (hst : s ≤ t) (ht : t ≤ T) (m : ℕ) (hm : 2 ≤ m)
    {C : ℝ≥0∞}
    (hMoment : ∀ u ≤ T, (∫⁻ p, ENNReal.ofReal (max (L.variance i u p) 0)^m
        ∂(L.law : Measure _)) ≤ C) :
    let e := σ^2*(2/(Real.Gamma α^2*(2*α-1)))*((t:ℝ)-(s:ℝ))^(2*α-1)
    (∫⁻ p, ‖L.terminalNoise i t p-L.terminalNoise i s p‖ₑ^(2*m : ℕ) ∂(L.law : Measure _)) ≤
      (2:ℝ≥0∞)^(2*m : ℕ) *
        (boundedMartingaleEvenPowerConstant m * ENNReal.ofReal e^m*C +
          boundedMartingaleEvenPowerConstant m * ENNReal.ofReal e^m*C) := by
  dsimp only
  let Ω := CanonicalPath T (FractionalCoupledSmoothState ι n)
  let e := σ^2*(2/(Real.Gamma α^2*(2*α-1)))*((t:ℝ)-(s:ℝ))^(2*α-1)
  let g := smoothBackwardWeight α n t
  let d := smoothBackwardWeightDeriv α n t
  let f (r : ℝ) := g r-smoothBackwardWeight α n s r
  let df (r : ℝ) := d r-smoothBackwardWeightDeriv α n s r
  let Y := L.smoothWeightedIntegralForm i t g d
  let Z := L.smoothWeightedIntegralForm i s f df
  have hg := smoothBackwardWeight_contDiff α n t
  have hd := smoothBackwardWeightDeriv_continuous α n t
  have hgd := hasDerivAt_smoothBackwardWeight α n t
  have hf : ContDiff ℝ 1 f := hg.sub (smoothBackwardWeight_contDiff α n s)
  have hdf : Continuous df := hd.sub (smoothBackwardWeightDeriv_continuous α n s)
  have hfdf (r : ℝ) : HasDerivAt f (df r) r := (hgd r).sub (hasDerivAt_smoothBackwardWeight α n s r)
  have hK : fractionalExponentialApproximation α n 0 ≠ 0 :=
    (fractionalExponentialApproximation_pos_at_zero (by linarith : 0 < α) hα' n).ne'
  have hZ₀ (p : Ω) : Z 0 p = 0 := by simp [Z, smoothWeightedIntegralForm]
  have hOld := L.rawWeightedRow_increment_even_moment_le hK i hB hβ hβB (hst.trans ht)
    hf hdf hfdf (s := 0) (t := s) zero_le le_rfl m hm hMoment
  change (∫⁻ p, ‖Z s p-Z 0 p‖ₑ^(2*m : ℕ) ∂(L.law : Measure _)) ≤ _ at hOld
  simp only [hZ₀, sub_zero, NNReal.coe_zero] at hOld
  have hRecent := L.rawWeightedRow_increment_even_moment_le hK i hB hβ hβB ht
    hg hd hgd hst le_rfl m hm hMoment
  change (∫⁻ p, ‖Y t p-Y s p‖ₑ^(2*m : ℕ) ∂(L.law : Measure _)) ≤ _ at hRecent
  have hBounds := fractionalSmooth_increment_energy_le hα hα' s.coe_nonneg
    (NNReal.coe_le_coe.mpr hst) n
  have hsum :
      (∫ r in (0:ℝ)..(s:ℝ), (f r)^2*σ^2) + (∫ r in (s:ℝ)..(t:ℝ), (g r)^2*σ^2) ≤ e := by
    simp only [f, g, smoothBackwardWeight, smoothExponentialKernel_eq_fractionalExponentialApproximation,
      intervalIntegral.integral_mul_const, ← add_mul, e, mul_assoc]
    rw [mul_comm (σ^2)]
    exact mul_le_mul_of_nonneg_right hBounds (sq_nonneg _)
  have hf₀ : 0 ≤ ∫ r in (0:ℝ)..(s:ℝ), (f r)^2*σ^2 :=
    intervalIntegral.integral_nonneg_of_forall s.coe_nonneg fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hg₀ : 0 ≤ ∫ r in (s:ℝ)..(t:ℝ), (g r)^2*σ^2 :=
    intervalIntegral.integral_nonneg_of_forall (NNReal.coe_le_coe.mpr hst)
      fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hBe (u : ℝ) (hu : u ≤ e) :
      boundedMartingaleEvenPowerConstant m*ENNReal.ofReal u^m*C ≤
        boundedMartingaleEvenPowerConstant m*ENNReal.ofReal e^m*C := by
    gcongr
  have hRecent' := hRecent.trans (hBe _ ((le_add_of_nonneg_left hf₀).trans hsum))
  have hOld' := hOld.trans (hBe _ ((le_add_of_nonneg_right hg₀).trans hsum))
  have hmY := (L.rawDeterministicWeightedRow hK i hB hβ hβB ht hg hd hgd).1
  have hmZ := (L.rawDeterministicWeightedRow hK i hB hβ hβB (hst.trans ht) hf hdf hfdf).1
  have hMy (r : ℝ≥0) : Measurable (Y r) := by
    exact (hmY.stronglyMeasurable r).measurable.mono
      ((canonicalPathNaturalFiltration (E := FractionalCoupledSmoothState ι n) T).le _) le_rfl
  have hMeasY : Measurable (fun p : Ω => ‖Y t p-Y s p‖ₑ^(2*m : ℕ)) :=
    ((hMy t).sub (hMy s)).enorm.pow_const _
  have hE : (∫⁻ p, ‖L.terminalNoise i t p-L.terminalNoise i s p‖ₑ^(2*m : ℕ) ∂(L.law : Measure _)) ≤
      ∫⁻ p, (2:ℝ≥0∞)^(2*m : ℕ)*(‖Y t p-Y s p‖ₑ^(2*m : ℕ)+‖Z s p‖ₑ^(2*m : ℕ))
        ∂(L.law : Measure _) := by
    apply lintegral_mono_ae
    filter_upwards [L.ae_terminalNoise_increment_split i hB hβ hβB hst] with p hp
    change _ = (Y t p-Y s p)+Z s p at hp
    rw [hp]
    exact enorm_add_pow_le _
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofNat_ne_top),
    lintegral_add_left hMeasY] at hE
  refine hE.trans ?_
  gcongr

end FractionalCoupledSmoothLaw

#print axioms RoughHeston.FractionalCoupledSmoothLaw.ae_terminalNoise_increment_split
#print axioms RoughHeston.FractionalCoupledSmoothLaw.terminalNoise_increment_even_moment_le

end RoughHeston
