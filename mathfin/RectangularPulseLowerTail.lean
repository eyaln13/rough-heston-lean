import RectangularPulseMeasure

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace RoughHeston

/-- Accumulated cluster variance, denoted by J in the size-bias argument. -/
noncomputable def clusterAccumulatedVariance {Ω : Type*} (U : ℝ → Ω → ℝ)
    (s : ℝ) (ω : Ω) : ℝ := ∫ v in Ioc (0 : ℝ) s, U v ω

theorem clusterAccumulatedVariance_eq_closed_interval {Ω : Type*} (U : ℝ → Ω → ℝ)
    (s : ℝ) (ω : Ω) :
    clusterAccumulatedVariance U s ω = ∫ v in Icc (0 : ℝ) s, U v ω := by
  unfold clusterAccumulatedVariance
  rw [restrict_Ioc_eq_restrict_Icc]

/-- The continuous density-charge equation is the affine Riccati
equation with test density q + l (L + κ). -/
theorem density_riccati_affine_convolution
    {α κ a q l T t : ℝ} {w : ℝ → ℝ}
    (hα : 0 < α) (hα' : α < 1) (ht : t ∈ Ioc 0 T) (hw : Continuous w)
    (hV : ∀ s ∈ Icc 0 T, w s = l+
      volterraConvolution (fractionalK α) (fun u => q+κ*l-κ*w u-a*(w u)^2) s) :
    w t = volterraConvolution (fractionalK α)
      (fun u => q+l*(fractionalL α u+κ)-κ*w u-a*(w u)^2) t := by
  let G (u : ℝ) := q+κ*l-κ*w u-a*(w u)^2
  have hGc : Continuous G := (continuous_const.sub (continuous_const.mul hw)).sub
    (continuous_const.mul (hw.pow 2))
  let F (u : ℝ) := fractionalK α (t-u)*fractionalL α u
  let H (u : ℝ) := fractionalK α (t-u)*G u
  have hL : fractionalL α = fractionalK (1-α) := by
    funext u
    unfold fractionalL fractionalK
    rw [show 1-α-1 = -α by ring]
  have hFI : IntegrableOn F (Ioc 0 t) := by
    have hβ := (real_beta_weight_scaled (a := 1-α) (b := α) (sub_pos.mpr hα') hα ht.1).1
    refine (hβ.div_const (Real.Gamma (1-α)*Real.Gamma α)).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    change u^(1-α-1)*(t-u)^(α-1)/(Real.Gamma (1-α)*Real.Gamma α) = F u
    rcases lt_or_eq_of_le hu.2 with hut | hut
    · rw [show F u = fractionalK α (t-u)*fractionalL α u from rfl, hL,
        fractionalK, fractionalK, ite_eq_right (not_le.mpr (sub_pos.mpr hut)),
        ite_eq_right (not_le.mpr hu.1), div_mul_div_comm]
      ac_rfl
    · subst u
      rw [sub_self, Real.zero_rpow (by linarith : α-1 ≠ 0), mul_zero, zero_div]
      simp [F, fractionalK]
  have hHI : IntegrableOn H (Ioc 0 t) := density_conv_integrable hα (Ioc_subset_Icc_self ht) hGc
  have hF : (∫ u in Ioc (0:ℝ) t,F u) = 1 := by
    change volterraConvolution (fractionalK α) (fractionalL α) t = 1
    rw [hL,fractionalK_convolution_add hα (sub_pos.mpr hα') ht.1,
      show α+(1-α)=1 by ring, fractionalK, ite_eq_right (not_le.mpr ht.1)]
    simp [Real.Gamma_one]
  rw [hV t (Ioc_subset_Icc_self ht)]
  unfold volterraConvolution
  change l+(∫ u in Ioc (0:ℝ) t,H u) = _
  have he (u : ℝ) : fractionalK α (t-u)*
      (q+l*(fractionalL α u+κ)-κ*w u-a*(w u)^2) = l*F u+H u := by
    dsimp [F,H,G]
    ring
  simp_rw [he]
  have hs : (∫ u in Ioc (0:ℝ) t,l*F u+H u) =
      (∫ u in Ioc (0:ℝ) t,l*F u)+(∫ u in Ioc (0:ℝ) t,H u) :=
    integral_add (hFI.const_mul l) hHI
  rw [hs,integral_const_mul,hF,mul_one]

private theorem cluster_affine_density_payoff
    {Ω : Type*} {U : ℝ → Ω → ℝ} {α κ q l s : ℝ} {ω : Ω}
    (hU : IntegrableOn (fun v => U v ω) (Ioc 0 s))
    (hLU : IntegrableOn (fun v => fractionalL α (s-v)*U v ω) (Ioc 0 s)) :
    volterraConvolution (fun u => q+l*(fractionalL α u+κ)) (fun v => U v ω) s =
      q*clusterAccumulatedVariance U s ω +
        l*(volterraConvolution (fractionalL α) (fun v => U v ω) s +
          κ*clusterAccumulatedVariance U s ω) := by
  unfold volterraConvolution clusterAccumulatedVariance
  have he (v : ℝ) :
      (q+l*(fractionalL α (s-v)+κ))*U v ω =
        q*U v ω+l*(fractionalL α (s-v)*U v ω+κ*U v ω) := by ring
  simp_rw [he]
  have hs : (∫ v in Ioc (0:ℝ) s,
      q*U v ω+l*(fractionalL α (s-v)*U v ω+κ*U v ω)) =
      (∫ v in Ioc (0:ℝ) s,q*U v ω)+
        (∫ v in Ioc (0:ℝ) s,l*(fractionalL α (s-v)*U v ω+κ*U v ω)) :=
    integral_add (hU.const_mul q) ((hLU.add (hU.const_mul κ)).const_mul l)
  have hs₂ : (∫ v in Ioc (0:ℝ) s,fractionalL α (s-v)*U v ω+κ*U v ω) =
      (∫ v in Ioc (0:ℝ) s,fractionalL α (s-v)*U v ω)+(∫ v in Ioc (0:ℝ) s,κ*U v ω) :=
    integral_add hLU (hU.const_mul κ)
  rw [hs,integral_const_mul,integral_const_mul,hs₂,integral_const_mul]

/-- Post-pulse lower tail with the manuscript's rectangular input and
integrated variance. The affine transform is stated in its convolution
form, and the post-pulse mass identity supplies the size-bias payoff. -/
theorem rectangularPulse_postpulse_lower_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {U : ℝ → Ω → ℝ} {Z : Ω → ℝ} {α κ a H s ε d : ℝ}
    (hα : 1/2 < α) (hα' : α < 1) (hκ : 0 ≤ κ) (ha : 0 < a)
    (hd : 0 < d) (hds : 2*d ≤ s) (hsH : s ≤ H) (hε : 0 < ε)
    (hJ : Measurable (clusterAccumulatedVariance U s)) (hZ : Measurable Z)
    (hJ₀ : ∀ᵐ ω ∂μ, 0 ≤ clusterAccumulatedVariance U s ω)
    (hZ₀ : ∀ᵐ ω ∂μ, 0 ≤ Z ω) (hZi : Integrable Z μ)
    (hZmean : (∫ ω,Z ω ∂μ) = ε)
    (hU : ∀ᵐ ω ∂μ, IntegrableOn (fun v => U v ω) (Ioc 0 s))
    (hLU : ∀ᵐ ω ∂μ, IntegrableOn (fun v => fractionalL α (s-v)*U v ω) (Ioc 0 s))
    (hZmass : ∀ᵐ ω ∂μ, Z ω = ε-(∫ v in Ioc (0 : ℝ) s, rectangularPulseRate ε d v)+
      volterraConvolution (fractionalL α) (fun v => U v ω) s+κ*clusterAccumulatedVariance U s ω)
    (hAffine : ∀ q > 0, ∀ l ∈ Icc (0 : ℝ) 1, ∀ w : ℝ → ℝ, Continuous w →
      (∀ t ∈ Ioc 0 s, w t =
        volterraConvolution (fractionalK α)
          (fun u => q+l*(fractionalL α u+κ)-κ*w u-a*(w u)^2) t) →
      (∫ ω, Real.exp (-(volterraConvolution (fun u => q+l*(fractionalL α u+κ))
        (fun v => U v ω) s)) ∂μ) = Real.exp (-(volterraConvolution w (rectangularPulseRate ε d) s))) :
    ∃ A C : ℝ, 0 < A ∧ 0 < C ∧
      (∀ q ≥ A/s^(2*α), (∫ ω, Real.exp (-q*clusterAccumulatedVariance U s ω)
        ∂sizeBiasedLaw μ Z ε) ≤ C/(Real.sqrt q*s^α)) ∧
      ∀ x, 0 < x → x ≤ 1 →
        (sizeBiasedLaw μ Z ε).real {ω | clusterAccumulatedVariance U s ω ≤ x*s^(2*α)} ≤
          (Real.exp A*C/Real.sqrt A)*Real.sqrt x := by
  let ν := rectangularPulseMeasure ε d s
  let hν : IsFiniteMeasure ν := rectangularPulseMeasure_isFiniteMeasure ε d s
  have hs : 0 < s := by linarith
  obtain ⟨hνmass,hνage⟩ := rectangularPulseMeasure_postpulse hε.le hd hds
  have hInput : (∫ v in Ioc (0 : ℝ) s, rectangularPulseRate ε d v)=ε :=
    (rectangularPulse_accumulatedMass_eq_real_univ hε.le hd).trans hνmass
  exact cluster_postpulse_sizeBiased_lower_tail_of_affine_transform hα hα' hκ ha hs hsH hε
    hJ hZ hJ₀ hZ₀ hZi hZmean (measurable_const.sub measurable_id) hνage hνmass
    (fun q hq l hl w hw hV => by
      change (∫ ω,Real.exp (-q*clusterAccumulatedVariance U s ω-l*Z ω) ∂μ) =
        Real.exp (-(∫ v,w (s-v) ∂rectangularPulseMeasure ε d s))
      rw [rectangularPulseMeasure_integral_eq_convolution hε.le hd]
      refine (integral_congr_ae ?_).trans (hAffine q hq l hl w hw ?_)
      · filter_upwards [hU,hLU,hZmass] with ω hω hLω hZω
        have hZ' := hZω
        rw [hInput,sub_self,zero_add] at hZ'
        rw [cluster_affine_density_payoff hω hLω, hZ']
        congr 1
        ring
      · exact fun t ht => density_riccati_affine_convolution (by linarith) hα' ht hw hV)

/-- At d/4, with d = ε^(1/α), the full rectangular input supplies
the exact deterministic mass fraction needed for the early-pulse tail. -/
theorem rectangularPulse_earlypulse_lower_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {U : ℝ → Ω → ℝ} {Z : Ω → ℝ} {α κ a H ε C₀ : ℝ}
    (hα : 1/2 < α) (hα' : α < 1) (hκ : 0 ≤ κ) (ha : 0 < a)
    (hε : 0 < ε) (hC₀ : 0 < C₀) :
    let d := ε^(1/α)
    let s := d/4
    s ≤ H →
    Measurable (clusterAccumulatedVariance U s) → Measurable Z →
    (∀ᵐ ω ∂μ, 0 ≤ clusterAccumulatedVariance U s ω) →
    (∀ᵐ ω ∂μ, 0 ≤ Z ω) → Integrable Z μ → (∫ ω,Z ω ∂μ) = ε →
    MemLp Z 2 μ → (∫ ω,(Z ω)^2 ∂μ) ≤ C₀*ε^2 →
    (∀ q > 0, ∀ w : ℝ → ℝ, Continuous w →
      (∀ t ∈ Icc 0 s, w t =
        volterraConvolution (fractionalK α) (fun v => q+(-κ)*w v+(-a)*(w v)^2) t) →
      (∫ ω, Real.exp (-(volterraConvolution (fun _ => q) (fun v => U v ω) s)) ∂μ) =
        Real.exp (-(volterraConvolution w (rectangularPulseRate ε d) s))) →
    ∃ A ρ : ℝ, 0 < A ∧ 0 < ρ ∧
      (∀ q ≥ A/s^(2*α), (∫ ω, Real.exp (-q*clusterAccumulatedVariance U s ω)
        ∂sizeBiasedLaw μ Z ε) ≤ Real.sqrt C₀*Real.exp (-(ρ*Real.sqrt q*s^α))) ∧
      ∀ x, 0 < x → x ≤ 1 →
        (sizeBiasedLaw μ Z ε).real {ω | clusterAccumulatedVariance U s ω ≤ x*s^(2*α)} ≤
          (Real.exp A*(Real.sqrt C₀/ρ)/Real.sqrt A)*Real.sqrt x := by
  intro d s hsH hJ hZ hJ₀ hZ₀ hZi hZmean hZL2 hZ2 hAffine
  have hα₀ : 0 < α := by linarith
  have hd : 0 < d := Real.rpow_pos_of_pos hε _
  have hs : 0 < s := div_pos hd (by norm_num)
  let ν := rectangularPulseMeasure ε d s
  let hν : IsFiniteMeasure ν := rectangularPulseMeasure_isFiniteMeasure ε d s
  have hνage := rectangularPulseMeasure_ae_age (ε := ε) (d := d) hs.le
  have hMass : (1/8:ℝ)*s^α ≤ ν.real {v | s/2 ≤ s-v} := by
    have h := rectangularPulseMeasure_earlypulse_scaled hε hα₀
    change s^α/8 ≤ ν.real {v | s/2 ≤ s-v} at h
    linarith
  exact cluster_earlypulse_sizeBiased_lower_tail_of_affine_transform hα hα' hκ ha hs hsH hε hC₀
    (by norm_num : (0:ℝ)<1/8) hJ hZ hJ₀ hZ₀ hZi hZmean hZL2 hZ2
    (measurable_const.sub measurable_id) hνage hMass
    (fun q hq w hw hV => by
      change (∫ ω,Real.exp (-q*clusterAccumulatedVariance U s ω) ∂μ) =
        Real.exp (-(∫ v,w (s-v) ∂rectangularPulseMeasure ε d s))
      rw [rectangularPulseMeasure_integral_eq_convolution hε.le hd]
      refine (integral_congr_ae ?_).trans (hAffine q hq w hw hV)
      refine ae_of_all _ fun ω => ?_
      change Real.exp (-q*(∫ v in Ioc (0:ℝ) s,U v ω)) =
        Real.exp (-(∫ v in Ioc (0:ℝ) s,q*U v ω))
      rw [integral_const_mul,neg_mul])

/-- A quarter-duration estimate has the same square-root lower-tail
bound at the full duration scale, with a fixed change of constant. -/
theorem cluster_quarterPulse_tail_at_duration_scale
    {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {J : Ω → ℝ} {α d B : ℝ} (hα : 0 < α) (hd : 0 < d)
    (hTail : ∀ x, 0 < x → x ≤ 1 →
      Q.real {ω | J ω ≤ x*(d/4)^(2*α)} ≤ B*Real.sqrt x) :
    ∀ x, 0 < x → x ≤ 1 →
      Q.real {ω | J ω ≤ x*d^(2*α)} ≤ (max 1 B)*(4:ℝ)^α*Real.sqrt x := by
  let R := (4:ℝ)^(2*α)
  have hR : 0 < R := Real.rpow_pos_of_pos (by norm_num) _
  have hs : 0 < d/4 := div_pos hd (by norm_num)
  have hscale : d^(2*α) = R*(d/4)^(2*α) := by
    have hEq : d = 4*(d/4) := by ring
    conv_lhs => rw [hEq]
    exact Real.mul_rpow (by norm_num) hs.le
  have hSqrt : Real.sqrt R = (4:ℝ)^α := by
    dsimp [R]
    rw [mul_comm, Real.rpow_mul (by norm_num : (0:ℝ)≤4), Real.rpow_two,
      Real.sqrt_sq (by positivity)]
  intro x hx _hx₁
  have hxR : 0 < x*R := mul_pos hx hR
  have hsqrt : Real.sqrt (x*R) = (4:ℝ)^α*Real.sqrt x := by
    rw [Real.sqrt_mul hx.le, hSqrt, mul_comm]
  by_cases hxle : x*R ≤ 1
  · have hf := hTail (x*R) hxR hxle
    rw [hsqrt] at hf
    rw [hscale, ← mul_assoc]
    have hp := mul_le_mul_of_nonneg_right (le_max_right 1 B)
      (show 0 ≤ (4:ℝ)^α*Real.sqrt x by positivity)
    exact hf.trans (hp.trans_eq (by ring))
  · have hp : 1 ≤ Real.sqrt (x*R) := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (le_of_not_ge hxle)
    rw [hsqrt] at hp
    exact (measureReal_le_one (μ := Q)).trans <| hp.trans <| by
      rw [mul_assoc]
      exact le_mul_of_one_le_left (by positivity) (le_max_left _ _)

/-- Continuous variance paths supply the two finite-horizon integrals
in the post-pulse payoff expansion. -/
theorem cluster_affine_payoff_integrability_of_continuous
    {α s : ℝ} {f : ℝ → ℝ} (hα' : α < 1) (hs : 0 ≤ s) (hf : Continuous f) :
    IntegrableOn f (Ioc 0 s) ∧
      IntegrableOn (fun v => fractionalL α (s-v)*f v) (Ioc 0 s) := by
  have hL := fractionalL_reflected_integrableOn_Ioc hα' hs
  obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image (K := Icc (0:ℝ) s) hf.norm.continuousOn
  refine ⟨(hf.intervalIntegrable 0 s).1, ?_⟩
  have hm : Measurable (fun v => fractionalL α (s-v)*f v) :=
    ((fractionalL_measurable α).comp (measurable_const.sub measurable_id)).mul hf.measurable
  refine (hL.norm.mul_const B).mono' hm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hB ⟨v,Ioc_subset_Icc_self hv,rfl⟩) (norm_nonneg _)

#print axioms density_riccati_affine_convolution
#print axioms rectangularPulse_postpulse_lower_tail
#print axioms rectangularPulse_earlypulse_lower_tail
#print axioms cluster_quarterPulse_tail_at_duration_scale
#print axioms cluster_affine_payoff_integrability_of_continuous

end RoughHeston
