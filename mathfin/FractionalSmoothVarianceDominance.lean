import FractionalSmoothRawWeighted
import FractionalCoupledIntegratedLimits
import FractionalKernelIncrements

/-! Mean and pointwise dominance for the actual smooth approximations.
The sign of mean reversion removes the drift term from the upper bound. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

set_option maxHeartbeats 1000000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {T : ℝ≥0} {α κ σ : ℝ} {n : ℕ} {v : Option ι → ℝ} {β : Option ι → ℝ≥0 → ℝ}

theorem fractionalExponentialApproximation_integral_reflected_le {s : ℝ}
    (hα : 0 < α) (hα' : α < 1) (n : ℕ) (hs : 0 ≤ s) (hsT : s ≤ (T : ℝ)) :
    (∫ r in (0 : ℝ)..s, fractionalExponentialApproximation α n (s-r)) ≤
      ∫ r in (0 : ℝ)..(T : ℝ), hestonKernel α r := by
  let k := fractionalExponentialApproximation α n
  have hreflect := intervalIntegral.integral_comp_sub_left (f := k) (a := 0) (b := s) s
  rw [sub_self, sub_zero] at hreflect
  change (∫ r in (0 : ℝ)..s, k (s-r)) ≤ _
  rw [hreflect, intervalIntegral.integral_of_le hs, intervalIntegral.integral_of_le T.coe_nonneg]
  have hk : IntegrableOn k (Ioc 0 s) :=
    ((fractionalExponentialApproximation_properties hα hα' n).1.integrableOn_Icc (μ := volume)).mono_set
      Ioc_subset_Icc_self
  have hKi : IntegrableOn (hestonKernel α) (Ioc 0 (T : ℝ)) := by
    have h : hestonKernel α = fractionalK α := by
      funext x
      by_cases hx : 0 < x
      · simp [hestonKernel, fractionalK, hx, not_le.mpr hx]
      · simp [hestonKernel, fractionalK, hx, le_of_not_gt hx]
    rw [h]
    exact fractionalK_integrableOn_Ioc hα ↑T
  calc
    _ ≤ ∫ r in Ioc (0 : ℝ) s, hestonKernel α r :=
      setIntegral_mono_on hk (hKi.mono_set (Ioc_subset_Ioc_right hsT)) measurableSet_Ioc
        (fun r hr => fractionalExponentialApproximation_le_hestonKernel hα hα' hr.1 n)
    _ ≤ _ := setIntegral_mono_set hKi
      (Eventually.of_forall fun r => by unfold hestonKernel; split_ifs <;> positivity) (Ioc_subset_Ioc_right hsT).eventuallyLE

namespace FractionalCoupledSmoothLaw

noncomputable def terminalNoise (L : FractionalCoupledSmoothLaw T α n κ σ v β)
    (i : Option ι) (t : ℝ≥0) (p : CanonicalPath T (FractionalCoupledSmoothState ι n)) : ℝ :=
  smoothKernelMartingaleConvolution (fractionalApproximationFinWeight α n)
    (fractionalApproximationFinRate n) (fun r : ℝ => L.residual i r.toNNReal p) t

/-- The weighted noise in the exact forward equation has zero mean and
an ordinary finite second moment. -/
theorem terminalNoise_integrable_mean_zero (L : FractionalCoupledSmoothLaw T α n κ σ v β)
    (hK : fractionalExponentialApproximation α n 0 ≠ 0) (i : Option ι)
    {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B)
    {t : ℝ≥0} (ht : t ≤ T) :
    Integrable (L.terminalNoise i t) (L.law : Measure _) ∧
      (∫ p, L.terminalNoise i t p ∂(L.law : Measure _)) = 0 := by
  let c := fractionalApproximationFinWeight α n
  let x := fractionalApproximationFinRate n
  let K := smoothExponentialKernel c x
  let k := smoothExponentialKernelDerivative c x
  let g (r : ℝ) := K ((t : ℝ)-r)
  let d (r : ℝ) := -k ((t : ℝ)-r)
  have hg : ContDiff ℝ 1 g := by
    unfold g K smoothExponentialKernel
    exact ContDiff.sum fun j _ => by fun_prop
  have hd : Continuous d := ((continuous_smoothExponentialKernelDerivative c x).comp
    (continuous_const.sub continuous_id)).neg
  have hgd (r : ℝ) : HasDerivAt g (d r) r := by
    have h := (smoothExponentialKernel_hasDerivAt c x ((t:ℝ)-r)).comp r
      ((hasDerivAt_id r).const_sub (t:ℝ))
    change HasDerivAt g (k ((t:ℝ)-r)*(-1)) r at h
    simpa only [mul_neg, mul_one, d] using h
  obtain ⟨hJ, hJ₂, _, _, _, hJ₀, _, _⟩ := L.rawDeterministicWeightedRow hK i hB hβ hβB ht hg hd hgd
  let J (s : ℝ≥0) (p : CanonicalPath T (FractionalCoupledSmoothState ι n)) :=
    g (min s t : ℝ≥0) * L.residual i (min s t) p - g 0 * L.residual i 0 p -
      ∫ r in (0 : ℝ)..((min s t : ℝ≥0):ℝ), d r * L.residual i r.toNNReal p
  have hEq : J t =ᵐ[(L.law : Measure _)] L.terminalNoise i t := by
    filter_upwards [L.residual_starts_zero i hB hβ hβB] with p hp
    have h0 : L.residual i 0 p = 0 := hp
    simp only [terminalNoise, smoothKernelMartingaleConvolution, J, min_self, g, d, K, k, c, x,
      sub_self, h0, mul_zero, sub_zero, neg_mul, intervalIntegral.integral_neg,
      sub_neg_eq_add, Real.toNNReal_coe]
  have hi : Integrable (J t) (L.law : Measure _) := hJ.integrable t
  refine ⟨hi.congr hEq, ?_⟩
  rw [← integral_congr_ae hEq]
  have hMean := hJ.setIntegral_eq (show (0 : ℝ≥0) ≤ t from zero_le)
    (show MeasurableSet[canonicalPathNaturalFiltration T 0] (univ : Set
      (CanonicalPath T (FractionalCoupledSmoothState ι n))) from MeasurableSet.univ)
  rw [setIntegral_univ, setIntegral_univ] at hMean
  rw [← hMean]
  exact (integral_congr_ae (Eventually.of_forall hJ₀)).trans (integral_zero _ _)

theorem variance_ae_le_input_plus_noise (L : FractionalCoupledSmoothLaw T α n κ σ v β)
    (hα : 0 < α) (hα' : α < 1) (hκ : 0 ≤ κ) (i : Option ι)
    {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B)
    {t : ℝ≥0} (ht : t ≤ T) :
    ∀ᵐ p ∂(L.law : Measure _), L.variance i t p ≤
      v i + B*(∫ r in (0 : ℝ)..(T : ℝ), hestonKernel α r) + L.terminalNoise i t p := by
  filter_upwards [L.nonneg, L.forward] with p hp hforward
  let K := fractionalExponentialApproximation α n
  let w (r : ℝ) := K ((t : ℝ)-r)
  let u (r : ℝ) := β i r.toNNReal - κ*L.variance i r.toNNReal p
  have hw : Continuous w := (fractionalExponentialApproximation_properties hα hα' n).1.comp
    (continuous_const.sub continuous_id)
  have hNonneg (r : ℝ) : 0 ≤ w r := (fractionalExponentialApproximation_properties hα hα' n).2.1 _
  have hV := (L.variance_continuous_time i hB hβ hβB p).comp continuous_real_toNNReal
  have hβi : IntervalIntegrable (fun r : ℝ => β i r.toNNReal) volume 0 (t : ℝ) := by
    rw [intervalIntegrable_iff]
    have hC : IntervalIntegrable (fun _ : ℝ => B) volume 0 (t : ℝ) := intervalIntegrable_const
    rw [intervalIntegrable_iff] at hC
    exact hC.mono' ((hβ i).comp continuous_real_toNNReal.measurable).stronglyMeasurable.aestronglyMeasurable
      (Eventually.of_forall fun r => hβB i r.toNNReal)
  have hui : IntervalIntegrable u volume 0 (t : ℝ) :=
    hβi.sub (hV.intervalIntegrable _ _ |>.const_mul κ)
  have hwi : IntervalIntegrable (fun r => w r * u r) volume 0 (t : ℝ) :=
    hui.continuousOn_mul hw.continuousOn
  have hbound :
      (∫ r in (0 : ℝ)..(t : ℝ), w r*u r) ≤ B*(∫ r in (0 : ℝ)..(T : ℝ), hestonKernel α r) := by
    calc
      _ ≤ ∫ r in (0 : ℝ)..(t : ℝ), B*w r := by
        apply intervalIntegral.integral_mono_on t.coe_nonneg hwi
          (hw.intervalIntegrable _ _ |>.const_mul B)
        intro r hr
        have hrt : r.toNNReal ≤ t :=
          NNReal.coe_le_coe.mp ((Real.coe_toNNReal _ hr.1).trans_le hr.2)
        have hV₀ : 0 ≤ L.variance i r.toNNReal p := hp i _ ⟨zero_le, hrt.trans ht⟩
        have hβle : β i r.toNNReal ≤ B := (le_abs_self _).trans (hβB i _)
        have hU : u r ≤ B := (sub_le_self _ (mul_nonneg hκ hV₀)).trans hβle
        rw [mul_comm (w r)]
        exact mul_le_mul_of_nonneg_right hU (hNonneg r)
      _ = B*(∫ r in (0 : ℝ)..(t : ℝ), w r) := intervalIntegral.integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (fractionalExponentialApproximation_integral_reflected_le hα hα' n t.coe_nonneg
          (NNReal.coe_le_coe.mpr ht)) hB
  have hf := hforward i t ⟨zero_le, ht⟩
  change L.variance i t p = v i + (∫ r in (0 : ℝ)..(t : ℝ), w r*u r) + L.terminalNoise i t p at hf
  linarith

/-- Kernel-independent first moment bound on each actual smooth row. -/
theorem variance_mean_le_initial_input (L : FractionalCoupledSmoothLaw T α n κ σ v β)
    (hα : 0 < α) (hα' : α < 1) (hκ : 0 ≤ κ) (i : Option ι)
    {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B)
    {t : ℝ≥0} (ht : t ≤ T) :
    (∫ p, L.variance i t p ∂(L.law : Measure _)) ≤
      v i + B*(∫ r in (0 : ℝ)..(T : ℝ), hestonKernel α r) := by
  let bound := v i + B*(∫ r in (0 : ℝ)..(T : ℝ), hestonKernel α r)
  have hV := (L.variance_memLp_two i hB hβB t).integrable one_le_two
  obtain ⟨hJ, hzero⟩ := L.terminalNoise_integrable_mean_zero
    (fractionalExponentialApproximation_pos_at_zero hα hα' n).ne' i hB hβ hβB ht
  calc
    _ ≤ ∫ p, bound+L.terminalNoise i t p ∂(L.law : Measure _) :=
      integral_mono_ae hV ((integrable_const bound).add hJ)
        (L.variance_ae_le_input_plus_noise hα hα' hκ i hB hβ hβB ht)
    _ = _ := by
      rw [integral_add (integrable_const bound) hJ, hzero]
      simp [measureReal_def, bound]

end FractionalCoupledSmoothLaw

#print axioms RoughHeston.FractionalCoupledSmoothLaw.variance_mean_le_initial_input

end RoughHeston
