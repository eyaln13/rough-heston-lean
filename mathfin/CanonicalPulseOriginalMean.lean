import CanonicalPulsePointMoments
import PulseMeanConvolution
import PhysicalResolventGlobalBound

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval InnerProductSpace

namespace RoughHeston
namespace FractionalFixedMeshLaw

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
  {α κ σ : ℝ} {v : Option ι→ℝ} {β : Option ι→ℝ≥0→ℝ}
  (L : FractionalFixedMeshLaw T α κ σ v β)
local notation "Path" => CanonicalPath T (CoupledPhysicalState ι)

private theorem real_lp2_expectation (f g : Lp ℝ 2 (L.law:Measure Path)) :
    ⟪f,g⟫_ℝ=∫ p,f p*g p ∂(L.law:Measure Path) := by
  rw [L2.inner_def]
  congr 1
  funext p
  change g p*f p=f p*g p
  ring

/-- The original, unconditioned pulse mean is its deterministic
rectangular resolvent profile. The result differentiates the integrated
identity in L¹ using the continuous L² trajectory of the variance. -/
theorem pulse_original_mean {i : ι} {τ : ℝ≥0} {ε d : ℝ}
    (hi : v (some i)=0) (hβ : β (some i)=translatedPulseRate τ ε d)
    (hα : 1/2<α) (hα' : α<1) (hd : 0<d)
    {R : ℝ→ℝ} (hR : Measurable R) (hR0 : ∀ r≤0,R r=0)
    {D : ℝ} (hD : 0≤D)
    (hRb : ∀ r∈Ioc (0:ℝ) (T:ℝ),|R r|≤D*fractionalK α r)
    (hRes : ∀ r∈Ioc (0:ℝ) (T:ℝ),R r=fractionalK α r-κ*volterraConvolution (fractionalK α) R r)
    {s : ℝ≥0} (hs : 0<s) (hsT : s<T) :
    (∫ p,canonicalPhysicalVariance T (some i) s p ∂(L.law:Measure Path)) =
      volterraConvolution R (fun u => translatedPulseRate τ ε d u.toNNReal) (s:ℝ) := by
  let μ := (L.law:Measure Path)
  let X (r : ℝ) := canonicalPhysicalVariance T (some i) r.toNNReal
  let m (r : ℝ) := ∫ p,X r p ∂μ
  let j (r : ℝ) := translatedPulseRate τ ε d r.toNNReal
  have hj : Measurable j :=
    (translatedPulseRate_measurable τ ε d).comp continuous_real_toNNReal.measurable
  have hjB (r : ℝ) : ‖j r‖≤‖ε/d‖ := norm_translatedPulseRate_le τ ε d r.toNNReal
  have hα₀ : 0<α := by linarith
  obtain ⟨u,hu,huX⟩ := L.variance_real_lp2_trajectory (some i)
  let hOne : MemLp (fun _ : Path => (1:ℝ)) 2 μ := memLp_const _
  let one : Lp ℝ 2 μ := hOne.toLp (fun _ => 1)
  have hone : ⇑one=ᵐ[μ] fun _ => (1:ℝ) := hOne.coeFn_toLp
  have hm : Continuous m := by
    apply (hu.inner (continuous_const (y := one))).congr
    intro r
    change ⟪u r,one⟫_ℝ=m r
    rw [real_lp2_expectation L]
    exact (integral_congr_ae ((huX r).mul hone)).trans (by simp [m,μ,X])
  have hx (r : ℝ) : MemLp (X r) 2 μ := (Lp.memLp (u r)).ae_eq (huX r)
  have hXm : Measurable (Function.uncurry X) := by
    have htime : Continuous (fun r : ℝ => canonicalEvalTime T r.toNNReal) :=
      (continuous_real_toNNReal.min continuous_const).subtype_mk _
    have he : Continuous (fun z : ℝ×Path => canonicalPathEval T z.1.toNNReal z.2) :=
      continuous_eval.comp (continuous_snd.prodMk (htime.comp continuous_fst))
    exact ((continuous_apply (some i)).comp he.fst).measurable
  obtain ⟨C,hC⟩ := L.variance_uniform_memLp 1
  norm_num at hC
  have hC₀ : 0≤C := (integral_nonneg (fun _ => sq_nonneg _)).trans (hC (some i) 0 zero_le).2
  have hMeanI (t : ℝ) (ht : t∈Icc (0:ℝ) (T:ℝ)) :
      (∫ r in (0:ℝ)..t,m r)=(∫ p,canonicalVariancePrimitive T (some i) t p ∂μ) := by
    have hXC : ∀ᵐ r ∂volume.restrict (Ioc (0:ℝ) t),(∫ p,(X r p)^2 ∂μ)≤C := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact (hC (some i) r.toNNReal (Real.toNNReal_le_iff_le_coe.mpr (hr.2.trans ht.2))).2
    have he := deterministic_weighted_path_pairing (ν := volume.restrict (Ioc (0:ℝ) t))
      hXm (measurable_const (a := (1:ℝ))) (memLp_const (1:ℝ)) measurable_const (integrable_const 1) hx hC₀ hXC
    simp only [mul_one,one_mul] at he
    simpa only [intervalIntegral.integral_of_le ht.1,canonicalVariancePrimitive,m,X] using he.symm
  have hRi : IntegrableOn R (Ioc (0:ℝ) (T:ℝ)) := by
    refine ((fractionalK_integrableOn_Ioc hα₀ (T:ℝ)).const_mul D).mono'
      hR.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    simpa only [Real.norm_eq_abs] using hRb r hr
  obtain ⟨g,hg,heqg⟩ := translatedPulse_resolvent_continuous_extension hd hR0 hRi
  have hIntegral (t : ℝ) (ht : t∈Ioo (0:ℝ) (T:ℝ)) :
      (∫ r in (0:ℝ)..t,m r)=∫ r in (0:ℝ)..t,g r := by
    rw [hMeanI t (Ioo_subset_Icc_self ht)]
    have hBm : Measurable (β (some i)) := by rw [hβ]; exact translatedPulseRate_measurable _ _ _
    have hBB (a : ℝ≥0) : ‖β (some i) a‖≤‖ε/d‖ := by rw [hβ]; exact norm_translatedPulseRate_le _ _ _ _
    rw [L.integrated_pulse_mean hi hα hα' hR hRb hRes hBm hBB (Ioo_subset_Icc_self ht),hβ]
    change volterraConvolution R (fun a => ∫ r in (0:ℝ)..a,j r) t = _
    rw [primitive_commutes_causal_resolvent hα₀ ht.1 hD hR hR0
      (fun r hr => hRb r ⟨hr.1,hr.2.trans ht.2.le⟩) hj (fun r _ => hjB r)]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le ht.1.le] at hr
    exact heqg ⟨hr.1,hr.2.trans ht.2.le⟩
  have hs' : (s:ℝ)∈Ioo (0:ℝ) (T:ℝ) := ⟨NNReal.coe_pos.mpr hs,NNReal.coe_lt_coe.mpr hsT⟩
  have hdm := intervalIntegral.integral_hasDerivAt_right (hm.intervalIntegrable 0 (s:ℝ))
    hm.stronglyMeasurable.stronglyMeasurableAtFilter hm.continuousAt
  have hdg := intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 (s:ℝ))
    hg.stronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  have he : (fun t => ∫ r in (0:ℝ)..t,m r) =ᶠ[𝓝 (s:ℝ)] fun t => ∫ r in (0:ℝ)..t,g r :=
    Filter.Eventually.mono (Ioo_mem_nhds hs'.1 hs'.2) (fun t ht => hIntegral t ht)
  have hd := (hdm.unique (hdg.congr_of_eventuallyEq he)).trans (heqg (Ioo_subset_Icc_self hs')).symm
  simpa only [m,X,Real.toNNReal_coe] using hd

#print axioms pulse_original_mean

end FractionalFixedMeshLaw
end RoughHeston
