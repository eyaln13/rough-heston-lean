import AffinePointPreterminal
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal Interval ENNReal

namespace RoughHeston

/-- A deterministic integrable weight can be paired with the timewise
first moment of a continuous adapted process by ordinary Fubini. -/
theorem affine_weighted_mean_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {V : ℝ → Ω → ℝ}
    {s B : ℝ} {g : ℝ → ℝ}
    (hVm : ∀ r, Measurable (V r)) (hVc : ∀ ω, Continuous fun r => V r ω)
    (hVi : ∀ r ∈ Ioc 0 s, Integrable (V r) μ)
    (hVB : ∀ r ∈ Ioc 0 s, (∫ ω, ‖V r ω‖ ∂μ) ≤ B)
    (hgm : Measurable g) (hg : IntegrableOn g (Ioc 0 s)) :
    Integrable (fun p : ℝ × Ω => g p.1*V p.1 p.2) ((volume.restrict (Ioc 0 s)).prod μ) ∧
      (∫ ω, (∫ r in Ioc (0:ℝ) s, g r*V r ω) ∂μ) =
        ∫ r in Ioc (0:ℝ) s, g r*(∫ ω, V r ω ∂μ) := by
  let ν := volume.restrict (Ioc (0:ℝ) s)
  let G (p : ℝ × Ω) := g p.1*V p.1 p.2
  have hGm : Measurable G := (hgm.comp measurable_fst).mul
    (measurable_uncurry_of_continuous_of_measurable hVc hVm)
  have hGi : Integrable G (ν.prod μ) := by
    refine (integrable_prod_iff hGm.aestronglyMeasurable).mpr ⟨?_,?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact (hVi r hr).const_mul (g r)
    · refine (hg.norm.mul_const B).mono_nonneg
          (hGm.norm.stronglyMeasurable.integral_prod_right' (ν := μ)).aestronglyMeasurable
          (ae_of_all _ fun _ => integral_nonneg fun _ => norm_nonneg _) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      change (∫ ω, ‖g r*V r ω‖ ∂μ) ≤ ‖g r‖*B
      simp_rw [norm_mul]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hVB r hr) (norm_nonneg _)
  refine ⟨hGi,?_⟩
  change (∫ ω, (∫ r, G (r,ω) ∂ν) ∂μ) = ∫ r, g r*(∫ ω,V r ω ∂μ) ∂ν
  rw [← integral_prod_symm G hGi,integral_prod G hGi]
  apply integral_congr_ae
  filter_upwards with r
  change (∫ ω,g r*V r ω ∂μ) = _
  exact integral_const_mul _ _

noncomputable def affineTiltMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (D : Ω → ℝ) : Measure Ω :=
  μ.withDensity (fun ω => ENNReal.ofReal (D ω))

theorem affineTiltMeasure_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Ω → ℝ} (hD : Measurable D) (hD₀ : ∀ ω,0≤D ω) (Y : Ω → ℝ) :
    (∫ ω,Y ω ∂affineTiltMeasure μ D) = ∫ ω,D ω*Y ω ∂μ := by
  rw [affineTiltMeasure,integral_withDensity_eq_integral_toReal_smul hD.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards with ω
  change (ENNReal.ofReal (D ω)).toReal • Y ω = D ω*Y ω
  rw [ENNReal.toReal_ofReal (hD₀ ω),smul_eq_mul]

theorem affineTiltMeasure_integrable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D Y : Ω → ℝ} {C : ℝ}
    (hD : Measurable D) (hD₀ : ∀ ω,0≤D ω) (hDb : ∀ᵐ ω ∂μ, ‖D ω‖≤C)
    (hYi : Integrable Y μ) :
    Integrable Y (affineTiltMeasure μ D) := by
  refine (integrable_withDensity_iff hD.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).mpr ?_
  refine (hYi.bdd_mul hD.aestronglyMeasurable hDb).congr ?_
  exact ae_of_all _ fun ω => by
    change D ω*Y ω = Y ω*(ENNReal.ofReal (D ω)).toReal
    rw [ENNReal.toReal_ofReal (hD₀ ω),mul_comm]

theorem affineTiltMeasure_isProbability {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Ω → ℝ} (hD : Integrable D μ) (hD₀ : ∀ ω,0≤D ω)
    (hDmean : (∫ ω,D ω ∂μ)=1) :
    IsProbabilityMeasure (affineTiltMeasure μ D) := by
  constructor
  rw [affineTiltMeasure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hD (ae_of_all _ hD₀),hDmean,ENNReal.ofReal_one]

theorem affineTiltMeasure_integral_norm_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D Y : Ω → ℝ} {C : ℝ}
    (hD : Measurable D) (hD₀ : ∀ ω,0≤D ω) (hDb : ∀ᵐ ω ∂μ, ‖D ω‖≤C)
    (hYi : Integrable Y μ) :
    (∫ ω, ‖Y ω‖ ∂affineTiltMeasure μ D) ≤ C*(∫ ω, ‖Y ω‖ ∂μ) := by
  rw [affineTiltMeasure_integral hD hD₀,← integral_const_mul]
  refine integral_mono_ae (hYi.norm.bdd_mul hD.aestronglyMeasurable hDb) (hYi.norm.const_mul C) ?_
  filter_upwards [hDb] with ω hω
  exact mul_le_mul_of_nonneg_right ((le_abs_self (D ω)).trans hω) (norm_nonneg _)

theorem affineTiltMeasure_condExp_test {Ω : Type*} {m₀ m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {D D' X : Ω → ℝ} {B : ℝ}
    (hm : m₀≤m) (hD : Measurable D) (hD₀ : ∀ ω,0≤D ω)
    (hDb : ∀ᵐ ω ∂μ, ‖D ω‖≤B)
    (hc : μ[D | m₀] =ᵐ[μ] D')
    (hX : StronglyMeasurable[m₀] X) (hXi : Integrable X μ) :
    (∫ ω,X ω ∂affineTiltMeasure μ D) = ∫ ω,D' ω*X ω ∂μ := by
  let _ : MeasurableSpace Ω := m
  have hDi : Integrable D μ := (integrable_const B).mono' hD.aestronglyMeasurable hDb
  have hMul : Integrable (D*X) μ := hXi.bdd_mul hD.aestronglyMeasurable hDb
  rw [affineTiltMeasure_integral hD hD₀]
  change (∫ ω,(D*X) ω ∂μ)=_
  rw [← integral_condExp hm]
  exact integral_congr_ae ((condExp_mul_of_aestronglyMeasurable_right hX.aestronglyMeasurable
    hMul hDi).trans (hc.mul EventuallyEq.rfl))

#print axioms affine_weighted_mean_integral
#print axioms affineTiltMeasure_condExp_test

end RoughHeston
