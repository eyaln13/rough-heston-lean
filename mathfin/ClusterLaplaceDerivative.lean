import ClusterDensitySensitivity
import SizeBiasedBurst
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open MeasureTheory Set Filter
open scoped Topology

namespace RoughHeston

private theorem right_interval_sdiff (x : ℝ) : Ici x \ {x} = Ioi x := by
  ext y
  simp

private theorem eventually_mem_unit_positive :
    ∀ᶠ l in 𝓝[>] (0 : ℝ), l ∈ Ioc 0 1 := by
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)] with l hl h1
  exact ⟨hl,(show l<1 from h1).le⟩

private theorem integral_has_right_deriv_of_dominated_slopes
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {F : ℝ → Ω → ℝ} {D B : Ω → ℝ}
    (hFi : ∀ l ∈ Icc (0 : ℝ) 1, Integrable (F l) μ) (hB : Integrable B μ)
    (hbound : ∀ᶠ l in 𝓝[>] (0 : ℝ), ∀ᵐ ω ∂μ, ‖(F l ω-F 0 ω)/l‖ ≤ B ω)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun l => (F l ω-F 0 ω)/l) (𝓝[>] 0) (𝓝 (D ω))) :
    HasDerivWithinAt (fun l => ∫ ω, F l ω ∂μ) (∫ ω, D ω ∂μ) (Ici 0) 0 := by
  have h0 := hFi 0 ⟨le_rfl,zero_le_one⟩
  have hSlope : ∀ᶠ l in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable (fun ω => (F l ω-F 0 ω)/l) μ := by
    filter_upwards [eventually_mem_unit_positive] with l hl
    exact (((hFi l (Ioc_subset_Icc_self hl)).sub h0).div_const l).aestronglyMeasurable
  have hIntegral := tendsto_integral_filter_of_dominated_convergence B hSlope hbound hB hlim
  rw [hasDerivWithinAt_iff_tendsto_slope,right_interval_sdiff]
  refine hIntegral.congr' ?_
  filter_upwards [eventually_mem_unit_positive] with l hl
  rw [integral_div, integral_sub (hFi l (Ioc_subset_Icc_self hl)) h0,
    slope_def_field, sub_zero]

private theorem exp_affine_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {J Z : Ω → ℝ} {q l : ℝ} (hJ : Measurable J) (hZ : Measurable Z)
    (hJ₀ : ∀ᵐ ω ∂μ, 0 ≤ J ω) (hZ₀ : ∀ᵐ ω ∂μ, 0 ≤ Z ω)
    (hq : 0 ≤ q) (hl : 0 ≤ l) :
    Integrable (fun ω => Real.exp (-q*J ω-l*Z ω)) μ := by
  refine (integrable_const (1:ℝ)).mono' (((hJ.const_mul (-q)).sub (hZ.const_mul l)).exp).aestronglyMeasurable ?_
  filter_upwards [hJ₀,hZ₀] with ω hj hz
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_one_iff.mpr (sub_nonpos.mpr
    ((mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq) hj).trans (mul_nonneg hl hz)))

/-- Right differentiation of the joint Laplace test in its nonnegative
tilt charges the expectation by the integrable tilt variable. -/
theorem hasDerivWithinAt_laplace_nonnegative_tilt
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {J Z : Ω → ℝ} {q : ℝ} (hq : 0 ≤ q) (hJ : Measurable J) (hZ : Measurable Z)
    (hJ₀ : ∀ᵐ ω ∂μ, 0 ≤ J ω) (hZ₀ : ∀ᵐ ω ∂μ, 0 ≤ Z ω) (hZi : Integrable Z μ) :
    HasDerivWithinAt (fun l => ∫ ω, Real.exp (-q*J ω-l*Z ω) ∂μ)
      (-(∫ ω, Z ω*Real.exp (-q*J ω) ∂μ)) (Ici 0) 0 := by
  let F (l : ℝ) (ω : Ω) := Real.exp (-q*J ω-l*Z ω)
  let D (ω : Ω) := -(Z ω*Real.exp (-q*J ω))
  have hF : ∀ l ∈ Icc (0 : ℝ) 1, Integrable (F l) μ :=
    fun l hl => exp_affine_integrable hJ hZ hJ₀ hZ₀ hq hl.1
  have hbound : ∀ᶠ l in 𝓝[>] (0 : ℝ), ∀ᵐ ω ∂μ, ‖(F l ω-F 0 ω)/l‖ ≤ Z ω := by
    filter_upwards [self_mem_nhdsWithin] with l hl
    have hl' : 0 < l := hl
    filter_upwards [hJ₀,hZ₀] with ω hj hz
    have hex₁ : Real.exp (-q*J ω) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq) hj)
    have hex₂ : Real.exp (-(l*Z ω)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hl'.le hz))
    have hlin : 1-Real.exp (-(l*Z ω)) ≤ l*Z ω := by
      linarith [Real.add_one_le_exp (-(l*Z ω))]
    have heq : F l ω-F 0 ω = Real.exp (-q*J ω)*(Real.exp (-(l*Z ω))-1) := by
      rw [show F l ω=Real.exp (-q*J ω+ -(l*Z ω)) by rfl,
        Real.exp_add, show F 0 ω=Real.exp (-q*J ω) by simp [F]]
      ring
    rw [heq,norm_div,norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg hl'.le, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hex₂)]
    apply (div_le_iff₀ hl').mpr
    rw [neg_sub, mul_comm (Z ω)]
    exact (mul_le_of_le_one_left (sub_nonneg.mpr hex₂) hex₁).trans hlin
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun l => (F l ω-F 0 ω)/l) (𝓝[>] 0) (𝓝 (D ω)) := by
    refine ae_of_all _ fun ω => ?_
    have hLin : HasDerivAt (fun l : ℝ => -q*J ω-l*Z ω) (-(Z ω)) 0 := by
      have hM := (hasDerivAt_id (0 : ℝ)).mul_const (Z ω)
      simpa only [id,one_mul] using hM.const_sub (-q*J ω)
    have hDeriv : HasDerivWithinAt (fun l => F l ω) (D ω) (Ioi 0) 0 := by
      have h := hLin.exp.hasDerivWithinAt (s := Ioi (0 : ℝ))
      convert h using 1
      simp [D]
      ring
    have hd := (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hDeriv
    refine hd.congr' (Eventually.of_forall fun l => ?_)
    rw [slope_def_field,sub_zero]
  have hD := integral_has_right_deriv_of_dominated_slopes hF hZi hbound hlim
  simpa only [F,D,integral_neg] using hD

/-- A uniform right difference-quotient bound allows differentiation
under a finite deterministic age measure. -/
theorem hasDerivWithinAt_integrated_density_riccati
    {Ξ : Type*} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsFiniteMeasure ν] {T C : ℝ}
    {age : Ξ → ℝ} {w : ℝ → ℝ → ℝ} {k : ℝ → ℝ}
    (ha : Measurable age) (haT : ∀ᵐ v ∂ν, age v ∈ Icc 0 T)
    (hw : ∀ l ∈ Icc (0 : ℝ) 1, Continuous (w l)) (hk : Continuous k)
    (hC : 0 ≤ C)
    (hD : ∀ l ∈ Ioc (0 : ℝ) 1, ∀ t ∈ Icc 0 T, ‖(w l t-w 0 t)/l-k t‖ ≤ C*l) :
    HasDerivWithinAt (fun l => ∫ v, w l (age v) ∂ν) (∫ v, k (age v) ∂ν) (Ici 0) 0 := by
  let F (l : ℝ) (v : Ξ) := w l (age v)
  have hfi {p : ℝ → ℝ} (hp : Continuous p) : Integrable (fun v => p (age v)) ν := by
    obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image (K := Icc (0 : ℝ) T) hp.norm.continuousOn
    refine (integrable_const B).mono' (hp.measurable.comp ha).aestronglyMeasurable ?_
    filter_upwards [haT] with v hv
    exact hB ⟨age v,hv,rfl⟩
  have hB : Integrable (fun v => ‖k (age v)‖+C) ν := (hfi hk).norm.add (integrable_const C)
  have hnorm : ∀ᶠ l in 𝓝[>] (0 : ℝ), ∀ᵐ v ∂ν,
      ‖(F l v-F 0 v)/l‖ ≤ ‖k (age v)‖+C := by
    filter_upwards [eventually_mem_unit_positive] with l hl
    filter_upwards [haT] with v hv
    have hD' := hD l hl (age v) hv
    have h := norm_add_le (k (age v)) (((F l v-F 0 v)/l)-k (age v))
    rw [show k (age v)+(((F l v-F 0 v)/l)-k (age v)) = (F l v-F 0 v)/l by ring] at h
    refine h.trans (add_le_add le_rfl (hD'.trans ?_))
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hl.2 hC
  have hLim : ∀ᵐ v ∂ν, Tendsto (fun l => (F l v-F 0 v)/l) (𝓝[>] 0) (𝓝 (k (age v))) := by
    filter_upwards [haT] with v hv
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsmall : Tendsto (fun l : ℝ => C*l) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have hc : Continuous (fun l : ℝ => C*l) := continuous_const.mul continuous_id
      have hl : Tendsto (fun l : ℝ => C*l) (𝓝 0) (𝓝 (C*0)) := hc.continuousAt
      simpa only [mul_zero] using hl.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hsmall
    filter_upwards [eventually_mem_unit_positive] with l hl
    exact hD l hl (age v) hv
  exact integral_has_right_deriv_of_dominated_slopes (fun l hl => hfi (hw l hl)) hB hnorm hLim

/-- Differentiating an affine transform and normalizing by the initial
mass yields the size-biased Laplace transform. -/
theorem sizeBiased_laplace_eq_density_sensitivity
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ν : Measure Ξ} [IsFiniteMeasure ν]
    {J Z : Ω → ℝ} {age : Ξ → ℝ} {w : ℝ → ℝ → ℝ} {k : ℝ → ℝ}
    {q ε T C : ℝ} (hq : 0 ≤ q) (hε : 0 < ε)
    (hJ : Measurable J) (hZ : Measurable Z) (hJ₀ : ∀ᵐ ω ∂μ, 0 ≤ J ω)
    (hZ₀ : ∀ᵐ ω ∂μ, 0 ≤ Z ω) (hZi : Integrable Z μ)
    (ha : Measurable age) (haT : ∀ᵐ v ∂ν, age v ∈ Icc 0 T)
    (hw : ∀ l ∈ Icc (0 : ℝ) 1, Continuous (w l)) (hk : Continuous k) (hC : 0 ≤ C)
    (hD : ∀ l ∈ Ioc (0 : ℝ) 1, ∀ t ∈ Icc 0 T, ‖(w l t-w 0 t)/l-k t‖ ≤ C*l)
    (htransform : ∀ l ∈ Icc (0 : ℝ) 1,
      (∫ ω, Real.exp (-q*J ω-l*Z ω) ∂μ) = Real.exp (-(∫ v, w l (age v) ∂ν))) :
    (∫ ω, Real.exp (-q*J ω) ∂sizeBiasedLaw μ Z ε) =
      Real.exp (-(∫ v, w 0 (age v) ∂ν)) * (∫ v, k (age v) ∂ν) / ε := by
  have hp := hasDerivWithinAt_laplace_nonnegative_tilt hq hJ hZ hJ₀ hZ₀ hZi
  have hν := hasDerivWithinAt_integrated_density_riccati ha haT hw hk hC hD
  have keh := hν.neg.exp
  rw [hasDerivWithinAt_iff_tendsto_slope,right_interval_sdiff] at hp keh
  have hEq : ∀ᶠ l in 𝓝[>] (0 : ℝ),
      slope (fun x => Real.exp (-(∫ v, w x (age v) ∂ν))) 0 l =
        slope (fun x => ∫ ω, Real.exp (-q*J ω-x*Z ω) ∂μ) 0 l := by
    filter_upwards [eventually_mem_unit_positive] with l hl
    rw [slope_def_field,slope_def_field,
      htransform l (Ioc_subset_Icc_self hl), htransform 0 ⟨le_rfl,zero_le_one⟩]
  have hval := tendsto_nhds_unique hp (keh.congr' hEq)
  rw [integral_sizeBiasedLaw_eq hε hZ hZ₀]
  congr 1
  change -(∫ ω, Z ω*Real.exp (-q*J ω) ∂μ) =
    Real.exp (-(∫ v, w 0 (age v) ∂ν))* -(∫ v, k (age v) ∂ν) at hval
  rw [mul_neg] at hval
  exact neg_injective hval

#print axioms hasDerivWithinAt_laplace_nonnegative_tilt
#print axioms hasDerivWithinAt_integrated_density_riccati
#print axioms sizeBiased_laplace_eq_density_sensitivity

end RoughHeston
