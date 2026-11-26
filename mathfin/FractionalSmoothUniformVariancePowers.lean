import FractionalSmoothTerminalEvenPowers

/-! Sign-sensitive first-moment base and uniform doubling of all smooth
variance powers. Constants depend on the fractional kernel and the
fixed input bound, not the exponential approximation index. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

set_option maxHeartbeats 1100000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {T : ℝ≥0} {α κ σ : ℝ} {v : Option ι → ℝ} {β : Option ι → ℝ≥0 → ℝ}

/-- Uniform weighted kernel energy at every observation time. -/
theorem fractionalSmoothKernel_energy_le
    (hα : 1/2 < α) (hα' : α < 1) (n : ℕ) {H : ℝ≥0} (hH : H ≤ T) :
    (∫ r in (0:ℝ)..(H:ℝ), (fractionalExponentialApproximation α n ((H:ℝ)-r))^2*σ^2) ≤
      σ^2*(∫ r in (0:ℝ)..(T:ℝ), (hestonKernel α r)^2) := by
  let K := fractionalExponentialApproximation α n
  have hα₀ : 0 < α := by linarith
  have hR := intervalIntegral.integral_comp_sub_left (f := fun r => (K r)^2*σ^2)
    (a := 0) (b := (H:ℝ)) (H:ℝ)
  rw [sub_self, sub_zero] at hR
  rw [hR, intervalIntegral.integral_mul_const, intervalIntegral.integral_of_le H.coe_nonneg,
    intervalIntegral.integral_of_le T.coe_nonneg, mul_comm (σ^2)]
  have hKi : IntegrableOn (fun r => (hestonKernel α r)^2) (Ioc 0 (T:ℝ)) :=
    (hestonKernel_memLp_two hα T).integrable_sq
  have hK : IntegrableOn (fun r => (K r)^2) (Ioc 0 (H:ℝ)) :=
    (((fractionalExponentialApproximation_properties hα₀ hα' n).1.pow 2).integrableOn_Icc (μ := volume)).mono_set
      Ioc_subset_Icc_self
  have hh : (Ioc (0:ℝ) (H:ℝ)) ⊆ Ioc 0 (T:ℝ) := Ioc_subset_Ioc_right (NNReal.coe_le_coe.mpr hH)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  calc
    _ ≤ ∫ r in Ioc (0:ℝ) (H:ℝ), (hestonKernel α r)^2 :=
      setIntegral_mono_on hK (hKi.mono_set hh) measurableSet_Ioc (fun r hr =>
        pow_le_pow_left₀ ((fractionalExponentialApproximation_properties hα₀ hα' n).2.1 r)
          (fractionalExponentialApproximation_le_hestonKernel hα₀ hα' hr.1 n) 2)
    _ ≤ _ := setIntegral_mono_set hKi (Eventually.of_forall fun r => sq_nonneg _) hh.eventuallyLE

private theorem pow_add_nonnegative_le {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (q : ℕ) :
    (x+y)^q ≤ (2:ℝ)^q * (x^q+y^q) := by
  have hM : x+y ≤ 2*max x y := by linarith [le_max_left x y, le_max_right x y]
  calc
    _ ≤ (2*max x y)^q := pow_le_pow_left₀ (add_nonneg hx hy) hM q
    _ = (2:ℝ)^q * (max x y)^q := mul_pow _ _ _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rcases le_total x y with h | h
      · rw [max_eq_right h]
        exact le_add_of_nonneg_left (pow_nonneg hx _)
      · rw [max_eq_left h]
        exact le_add_of_nonneg_right (pow_nonneg hy _)

private theorem lintegral_variance_power_dominance
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {V Z : Ω → ℝ} (hZ : AEMeasurable Z μ) {D : ℝ} (hD : 0 ≤ D) (q : ℕ)
    (hAE : ∀ᵐ ω ∂μ, 0 ≤ V ω ∧ V ω ≤ D+Z ω) :
    (∫⁻ ω, ENNReal.ofReal (max (V ω) 0)^q ∂μ) ≤
      (2:ℝ≥0∞)^q * (ENNReal.ofReal D^q + ∫⁻ ω, ‖Z ω‖ₑ^q ∂μ) := by
  have hle : ∀ᵐ ω ∂μ, ENNReal.ofReal (max (V ω) 0)^q ≤
      (2:ℝ≥0∞)^q*(ENNReal.ofReal D^q+‖Z ω‖ₑ^q) := by
    filter_upwards [hAE] with ω hω
    have hBound : max (V ω) 0 ≤ D+‖Z ω‖ := by
      rw [max_eq_left hω.1]
      exact hω.2.trans (add_le_add_right (le_abs_self _) D)
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (le_max_right _ _), ← ENNReal.ofReal_pow hD,
      ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_add (pow_nonneg hD _) (pow_nonneg (norm_nonneg _) _)]
    have htwo : (2:ℝ≥0∞)^q = ENNReal.ofReal ((2:ℝ)^q) := by
      rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2)]
      simp
    rw [htwo, ← ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) q)]
    exact ENNReal.ofReal_le_ofReal
      ((pow_le_pow_left₀ (le_max_right _ _) hBound q).trans
        (pow_add_nonnegative_le hD (norm_nonneg _) q))
  refine (lintegral_mono_ae hle).trans_eq ?_
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofNat_ne_top), lintegral_add_left measurable_const]
  simp

/-- Uniform power bounds with exponents (2^j) for all variance rows
of the actual smooth approximations, obtained by a sign-sensitive
moment doubling argument. -/
theorem uniform_fractionalSmooth_variance_dyadic_powers
    (hα : 1/2 < α) (hα' : α < 1) (hκ : 0 ≤ κ) (hv : ∀ i, 0 ≤ v i)
    (L : ∀ n, FractionalCoupledSmoothLaw T α n κ σ v β)
    {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B)
    (j : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ n (i : Option ι), ∀ t ≤ T,
      (∫⁻ p, ENNReal.ofReal (max ((L n).variance i t p) 0)^(2^j : ℕ)
        ∂((L n).law : Measure _)) ≤ C := by
  let D := ‖v‖ + B*(∫ r in (0:ℝ)..(T:ℝ), hestonKernel α r)
  let G := ENNReal.ofReal (σ^2*(∫ r in (0:ℝ)..(T:ℝ), (hestonKernel α r)^2))
  have hG : G ≠ ⊤ := ENNReal.ofReal_ne_top
  have hK₁ : 0 ≤ ∫ r in (0:ℝ)..(T:ℝ), hestonKernel α r :=
    intervalIntegral.integral_nonneg_of_forall T.coe_nonneg fun r => by
      unfold hestonKernel
      split_ifs <;> positivity
  have hD : 0 ≤ D := add_nonneg (norm_nonneg _) (mul_nonneg hB hK₁)
  have hα₀ : 0 < α := by linarith
  have hK (n : ℕ) : fractionalExponentialApproximation α n 0 ≠ 0 :=
    (fractionalExponentialApproximation_pos_at_zero hα₀ hα' n).ne'
  have hDv (i : Option ι) :
      v i + B*(∫ r in (0:ℝ)..(T:ℝ), hestonKernel α r) ≤ D :=
    add_le_add_left ((le_abs_self _).trans (norm_le_pi_norm v i)) _
  induction j with
  | zero =>
    refine ⟨ENNReal.ofReal D, ENNReal.ofReal_ne_top, ?_⟩
    intro n i t ht
    have hV₀ : ∀ᵐ p ∂((L n).law : Measure _), 0 ≤ (L n).variance i t p :=
      (L n).nonneg.mono fun _ h => h i t ⟨zero_le, ht⟩
    have hi : Integrable ((L n).variance i t) ((L n).law : Measure _) :=
      ((L n).variance_memLp_two i hB hβB t).integrable one_le_two
    have hn : (fun p => ENNReal.ofReal (max ((L n).variance i t p) 0)) =ᵐ[((L n).law : Measure _)]
        fun p => ENNReal.ofReal ((L n).variance i t p) := by
      filter_upwards [hV₀] with p hp
      rw [max_eq_left hp]
    simp only [pow_zero, pow_one]
    rw [lintegral_congr_ae hn, ← ofReal_integral_eq_lintegral_ofReal hi hV₀]
    exact ENNReal.ofReal_le_ofReal
      (((L n).variance_mean_le_initial_input hα₀ hα' hκ i hB hβ hβB ht).trans (hDv i))
  | succ j ih =>
    obtain ⟨C, hC, hMoment⟩ := ih
    let m : ℕ := 2^j
    have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (by decide))
    let C' := (2:ℝ≥0∞)^(2*m) *
      (ENNReal.ofReal D^(2*m) + rawMartingaleMomentConstant m*G^m*C)
    have hC' : C' ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
      (ENNReal.add_ne_top.2 ⟨ENNReal.pow_ne_top ENNReal.ofReal_ne_top,
        ENNReal.mul_ne_top (ENNReal.mul_ne_top (rawMartingaleMomentConstant_ne_top m hm)
          (ENNReal.pow_ne_top hG)) hC⟩)
    refine ⟨C', hC', ?_⟩
    intro n i t ht
    have hMomentNoise := (L n).terminalNoise_even_moment_le (hK n) i hB hβ hβB ht m hm
      (hMoment n i)
    have hM : (∫⁻ p, ‖(L n).terminalNoise i t p‖ₑ^(2*m : ℕ) ∂((L n).law : Measure _)) ≤
        rawMartingaleMomentConstant m*G^m*C := by
      refine hMomentNoise.trans ?_
      gcongr
      exact ENNReal.ofReal_le_ofReal (fractionalSmoothKernel_energy_le hα hα' n ht)
    have hDom : ∀ᵐ p ∂((L n).law : Measure _), 0 ≤ (L n).variance i t p ∧
        (L n).variance i t p ≤ D+(L n).terminalNoise i t p := by
      filter_upwards [(L n).nonneg, (L n).variance_ae_le_input_plus_noise hα₀ hα' hκ i hB hβ hβB ht]
        with p hN hV
      exact ⟨hN i t ⟨zero_le, ht⟩, hV.trans (add_le_add_left (hDv i) _)⟩
    have hZ : AEMeasurable ((L n).terminalNoise i t) ((L n).law : Measure _) :=
      ((L n).terminalNoise_integrable_mean_zero (hK n) i hB hβ hβB ht).1.aemeasurable
    rw [pow_succ, mul_comm (2^j)]
    refine (lintegral_variance_power_dominance hZ hD (2*m) hDom).trans ?_
    dsimp [C']
    gcongr

#print axioms RoughHeston.uniform_fractionalSmooth_variance_dyadic_powers

end RoughHeston
