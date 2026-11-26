import FractionalSmoothDriftIncrements

/-! Uniform fractional increment moments for every physical variance
and residual row in the smooth approximation. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

set_option maxHeartbeats 1100000

theorem lintegral_enorm_add_pow_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X Y : Ω → ℝ} (hX : Measurable X) (p : ℕ) :
    (∫⁻ ω, ‖X ω+Y ω‖ₑ^p ∂μ) ≤
      (2:ℝ≥0∞)^p*((∫⁻ ω, ‖X ω‖ₑ^p ∂μ)+(∫⁻ ω, ‖Y ω‖ₑ^p ∂μ)) := by
  have h := lintegral_mono (μ := μ) (fun ω => enorm_add_pow_le (a := X ω) (b := Y ω) p)
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofNat_ne_top),
    lintegral_add_left (hX.enorm.pow_const p)] at h
  exact h

theorem ofReal_scaled_rpow_nat {a x q : ℝ}
    (ha : 0 ≤ a) (hx : 0 ≤ x) (hq : 0 ≤ q) (p : ℕ) :
    ENNReal.ofReal (a*x^q)^p = ENNReal.ofReal a^p * ENNReal.ofReal (x^(q*(p:ℝ))) := by
  rw [ENNReal.ofReal_mul ha, mul_pow, ← ENNReal.ofReal_pow (Real.rpow_nonneg hx q),
    ← Real.rpow_natCast, ← Real.rpow_mul hx]

theorem ofReal_rpow_le_horizon_mul_ofReal_rpow {x T a b : ℝ}
    (hx : 0 ≤ x) (hxT : x ≤ T) (hb : 0 < b) (hba : b ≤ a) :
    ENNReal.ofReal (x^a) ≤ ENNReal.ofReal (T^(a-b))*ENNReal.ofReal (x^b) := by
  by_cases h0 : x = 0
  · rw [h0, Real.zero_rpow (ne_of_gt (hb.trans_le hba)), Real.zero_rpow hb.ne', ENNReal.ofReal_zero,
      mul_zero]
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm h0)
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (hx.trans hxT) _)]
    apply ENNReal.ofReal_le_ofReal
    have ha : x^a = x^(a-b)*x^b := by
      rw [← Real.rpow_add hxp]
      congr 1
      ring
    rw [ha]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx hxT (sub_nonneg.mpr hba))
      (Real.rpow_nonneg hx _)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {T : ℝ≥0} {α κ σ : ℝ} {n : ℕ} {v : Option ι → ℝ} {β : Option ι → ℝ≥0 → ℝ}

namespace FractionalCoupledSmoothLaw

theorem driftInput_power_le_of_variance_power
    (L : FractionalCoupledSmoothLaw T α n κ σ v β) (i : Option ι)
    {B : ℝ} (hB : 0 ≤ B) (hβB : ∀ i t, ‖β i t‖ ≤ B) (p : ℕ) {C : ℝ≥0∞}
    (hV : ∀ s ≤ T, (∫⁻ q, ENNReal.ofReal (max (L.variance i s q) 0)^p
        ∂(L.law : Measure _)) ≤ C) :
    ∀ r ∈ Icc (0:ℝ) (T:ℝ), (∫⁻ q, ‖L.driftInput i r q‖ₑ^p ∂(L.law : Measure _)) ≤
      (2:ℝ≥0∞)^p*(ENNReal.ofReal B^p+‖κ‖ₑ^p*C) := by
  intro r hr
  have hrT : r.toNNReal ≤ T := NNReal.coe_le_coe.mp ((Real.coe_toNNReal r hr.1).trans_le hr.2)
  have hAE := L.nonneg.mono fun _ h => h i r.toNNReal ⟨zero_le, hrT⟩
  have h :=
    lintegral_enorm_add_pow_le (μ := (L.law : Measure
      (CanonicalPath T (FractionalCoupledSmoothState ι n))))
      (X := fun _ => β i r.toNNReal) (Y := fun q => -κ*L.variance i r.toNNReal q) measurable_const p
  have hv (q : CanonicalPath T (FractionalCoupledSmoothState ι n)) :
      β i r.toNNReal + (-κ)*L.variance i r.toNNReal q = L.driftInput i r q := by
    simp [driftInput, sub_eq_add_neg]
  simp_rw [hv] at h
  refine h.trans ?_
  have hκ : (∫⁻ q, ‖-κ * L.variance i r.toNNReal q‖ₑ^p ∂(L.law : Measure _)) ≤ ‖κ‖ₑ^p*C := by
    have he : (fun q => ‖-κ * L.variance i r.toNNReal q‖ₑ^p)
        =ᵐ[(L.law : Measure _)] fun q =>
          ‖κ‖ₑ^p*ENNReal.ofReal (max (L.variance i r.toNNReal q) 0)^p := by
      filter_upwards [hAE] with q hq
      have hq' : 0 ≤ L.variance i r.toNNReal q := hq
      rw [← ofReal_norm, norm_mul, norm_neg, Real.norm_of_nonneg hq', max_eq_left hq',
        ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, mul_pow]
    rw [lintegral_congr_ae he,
      lintegral_const_mul' _ _ (ENNReal.pow_ne_top enorm_ne_top)]
    gcongr
    exact hV _ hrT
  have hb : (∫⁻ q : CanonicalPath T (FractionalCoupledSmoothState ι n),
      ‖β i r.toNNReal‖ₑ^p ∂(L.law : Measure _)) ≤ ENNReal.ofReal B^p := by
    rw [lintegral_const, measure_univ, mul_one, ← ofReal_norm]
    gcongr
    exact hβB i r.toNNReal
  gcongr

/-- A single rate of order ((2α-1)m) for the actual variance
increments. The constants depend only on the fixed horizon, the
fractional model parameters, and the two uniform input moments. -/
theorem variance_increment_even_moment_le
    (L : FractionalCoupledSmoothLaw T α n κ σ v β)
    (hα : 1/2 < α) (hα' : α < 1) (i : Option ι)
    {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B)
    {s t : ℝ≥0} (hst : s ≤ t) (ht : t ≤ T) (m : ℕ) (hm : 2 ≤ m)
    {Cₘ C₂ₘ : ℝ≥0∞}
    (hVm : ∀ u ≤ T, (∫⁻ p, ENNReal.ofReal (max (L.variance i u p) 0)^m
        ∂(L.law : Measure _)) ≤ Cₘ)
    (hV₂ₘ : ∀ u ≤ T, (∫⁻ p, ENNReal.ofReal (max (L.variance i u p) 0)^(2*m : ℕ)
        ∂(L.law : Measure _)) ≤ C₂ₘ) :
    let p := (2*m : ℕ)
    let dn := (2/(Real.Gamma α*α))
    let fn := σ^2*(2/(Real.Gamma α^2*(2*α-1)))
    let D := (2:ℝ≥0∞)^p*(ENNReal.ofReal B^p+‖κ‖ₑ^p*C₂ₘ)
    let E := (2:ℝ≥0∞)^p*((2:ℝ≥0∞)^p*
      (ENNReal.ofReal dn^p*ENNReal.ofReal ((T:ℝ)^(m:ℝ))*D*2) +
      (2:ℝ≥0∞)^p*(boundedMartingaleEvenPowerConstant m * ENNReal.ofReal fn^m*Cₘ*2))
    (∫⁻ q, ‖L.variance i t q-L.variance i s q‖ₑ^p ∂(L.law : Measure _)) ≤
      E * ENNReal.ofReal ((((t:ℝ)-(s:ℝ)))^((2*α-1)*(m:ℝ))) := by
  dsimp only
  let Ω := CanonicalPath T (FractionalCoupledSmoothState ι n)
  let μ : Measure Ω := L.law
  let p := (2*m : ℕ)
  let Δ := (t:ℝ)-(s:ℝ)
  let e := (2*α-1)*(m:ℝ)
  let dn := (2/(Real.Gamma α*α))
  let fn := σ^2*(2/(Real.Gamma α^2*(2*α-1)))
  let D := (2:ℝ≥0∞)^p*(ENNReal.ofReal B^p+‖κ‖ₑ^p*C₂ₘ)
  have hα₀ : 0 < α := by linarith
  have hm₀ : 0 < (m:ℝ) := by positivity
  have h₂α : 0 < 2*α-1 := by linarith
  have hΔ : 0 ≤ Δ := sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst)
  have hΔT : Δ ≤ (T:ℝ) := (sub_le_self _ s.coe_nonneg).trans (NNReal.coe_le_coe.mpr ht)
  have he : 0 < e := mul_pos h₂α hm₀
  have hGamma : 0 < Real.Gamma α := Real.Gamma_pos_of_pos hα₀
  have hdn : 0 ≤ dn := by dsimp [dn]; positivity
  have hfn : 0 ≤ fn := by dsimp [fn]; positivity
  have hInput := L.driftInput_power_le_of_variance_power i hB hβB p hV₂ₘ
  have hDrift := L.driftConvolution_increment_moment_le hα₀ hα' i hB hβ hβB
    hst ht p (by dsimp [p]; omega) hInput
  have hNoise := L.terminalNoise_increment_even_moment_le hα hα' i hB hβ hβB hst ht m hm hVm
  have hRateD := ofReal_scaled_rpow_nat hdn hΔ hα₀.le p
  have hRateN := ofReal_scaled_rpow_nat hfn hΔ h₂α.le m
  have hpow : α*(p:ℝ)-e = m := by dsimp [p,e]; push_cast; ring
  have hle : e ≤ α*(p:ℝ) := by linarith [hm₀.le, hpow]
  have hRateD' := ofReal_rpow_le_horizon_mul_ofReal_rpow hΔ hΔT he hle
  rw [hpow] at hRateD'
  have hMeasD (u : ℝ≥0) : Measurable (L.driftConvolution i u) := by
    have hK : Measurable (fun r : ℝ => fractionalExponentialApproximation α n ((u:ℝ)-r)) :=
      (fractionalExponentialApproximation_properties hα₀ hα' n).1.measurable.comp
        (measurable_const.sub measurable_id)
    have h := ((hK.comp measurable_fst).mul (L.measurable_driftInput i hB hβ hβB)).stronglyMeasurable
    have hi := h.integral_prod_left' (μ := volume.restrict (Ioc (0:ℝ) (u:ℝ)))
    unfold driftConvolution
    simp_rw [intervalIntegral.integral_of_le u.coe_nonneg]
    exact hi.measurable
  have hA :
      (fun q : Ω => L.variance i t q-L.variance i s q) =ᵐ[μ]
        fun q => (L.driftConvolution i t q-L.driftConvolution i s q)+
          (L.terminalNoise i t q-L.terminalNoise i s q) := by
    filter_upwards [L.forward] with q hq
    have ht' := hq i t ⟨zero_le, ht⟩
    have hs' := hq i s ⟨zero_le, hst.trans ht⟩
    change L.variance i t q = v i + L.driftConvolution i t q + L.terminalNoise i t q at ht'
    change L.variance i s q = v i + L.driftConvolution i s q + L.terminalNoise i s q at hs'
    linarith
  have hApow : (fun q : Ω => ‖L.variance i t q-L.variance i s q‖ₑ^p) =ᵐ[μ]
    fun q => ‖(L.driftConvolution i t q-L.driftConvolution i s q)+
      (L.terminalNoise i t q-L.terminalNoise i s q)‖ₑ^p :=
    hA.mono fun q h => congrArg (fun x : ℝ => ‖x‖ₑ^p) h
  rw [lintegral_congr_ae hApow]
  refine (lintegral_enorm_add_pow_le ((hMeasD t).sub (hMeasD s)) p).trans ?_
  have hD' :
      (∫⁻ q, ‖L.driftConvolution i t q-L.driftConvolution i s q‖ₑ^p ∂μ) ≤
        (2:ℝ≥0∞)^p*(ENNReal.ofReal dn^p*ENNReal.ofReal ((T:ℝ)^(m:ℝ))*D*2) *
          ENNReal.ofReal (Δ^e) := by
    refine hDrift.trans ?_
    change (2:ℝ≥0∞)^p*(ENNReal.ofReal (dn*Δ^α)^p*D+ENNReal.ofReal (dn*Δ^α)^p*D) ≤ _
    rw [hRateD]
    have hInner : ENNReal.ofReal dn^p*ENNReal.ofReal (Δ^(α*(p:ℝ)))*D ≤
        ENNReal.ofReal dn^p*(ENNReal.ofReal ((T:ℝ)^(m:ℝ))*ENNReal.ofReal (Δ^e))*D := by
      gcongr
    exact (mul_right_mono (add_le_add hInner hInner)).trans_eq (by ring)
  have hN' :
      (∫⁻ q, ‖L.terminalNoise i t q-L.terminalNoise i s q‖ₑ^p ∂μ) ≤
        (2:ℝ≥0∞)^p*(boundedMartingaleEvenPowerConstant m * ENNReal.ofReal fn^m*Cₘ*2) *
          ENNReal.ofReal (Δ^e) := by
    refine hNoise.trans ?_
    change (2:ℝ≥0∞)^p*(boundedMartingaleEvenPowerConstant m * ENNReal.ofReal (fn*Δ^(2*α-1))^m*Cₘ +
      boundedMartingaleEvenPowerConstant m * ENNReal.ofReal (fn*Δ^(2*α-1))^m*Cₘ) ≤ _
    rw [hRateN]
    apply le_of_eq
    ring
  refine (mul_right_mono (add_le_add hD' hN')).trans_eq ?_
  dsimp [p, dn, fn, D, Δ, e]
  ring

end FractionalCoupledSmoothLaw

#print axioms RoughHeston.FractionalCoupledSmoothLaw.variance_increment_even_moment_le

end RoughHeston
