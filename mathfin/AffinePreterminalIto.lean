import AffinePreterminalBound
import HestonWeightedFubini
import Mathlib.Analysis.Calculus.FDeriv.Measurable

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology Interval NNReal ENNReal

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℝ≥0 m} {B V : ℝ≥0 → Ω → ℝ}

/-- The preterminal integration-by-parts formula for the actual joint
Itô map. The order-one stochastic convolution is the stopped variance
martingale integrand. The formula is an equality in terminal L². -/
theorem affine_preterminal_jointIto_by_parts [IsFiniteMeasure μ]
    {w : ℝ → ℝ} {d : ℝ} (hd : 0 < d)
    (hw : ∀ x > 0, ContDiffAt ℝ 1 w x)
    (t : ℝ≥0) (hB₂ : ∀ r, MemLp (B r) 2 μ)
    (hVp : IsStronglyPredictable 𝒢 V) (hVnonneg : ∀ r ω, 0 ≤ V r ω)
    (hVint : ∀ r, Integrable (V r) μ) {C : ℝ} (hmean : ∀ r, (∫ ω,V r ω ∂μ) ≤ C) :
    let I := jointItoIntegralCLM (𝒢 := 𝒢) t hB₂
    let ψ (u : ℝ≥0) := hestonKernelFamilyLp
      (show (1:ℝ)/2 < 1 by norm_num) hVp hVnonneg hVint hmean
        (hestonNNRealHorizonPoint t u)
    ∃ G : Lp ℝ 2 (jointPredictableMeasure 𝒢 μ t),
      (⇑G =ᵐ[jointPredictableMeasure 𝒢 μ t]
        fun z => w (d+((t:ℝ)-(z.1:ℝ)))*Real.sqrt (V z.1 z.2)) ∧
      I G = w d • I (ψ t) +
        ∫ u : ℝ≥0, deriv w (d+((t:ℝ)-(u:ℝ))) • I (ψ u) ∂hestonTimeMeasure t := by
  dsimp only
  let I := jointItoIntegralCLM (𝒢 := 𝒢) t hB₂
  let hOne : (1:ℝ)/2 < 1 := by norm_num
  let ψ (u : ℝ≥0) := hestonKernelFamilyLp hOne hVp hVnonneg hVint hmean
    (hestonNNRealHorizonPoint t u)
  let q (s : ℝ) := deriv w (d+s)
  have hq : Measurable q := (measurable_deriv w).comp (measurable_const.add measurable_id)
  have hqC : ContinuousOn q (Icc 0 (t:ℝ)) := by
    have hC : ContDiffOn ℝ 1 w (Ioi 0) := fun s hs => (hw s hs).contDiffWithinAt
    exact (hC.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).comp
      (continuous_const.add continuous_id).continuousOn
      (fun s hs => add_pos_of_pos_of_nonneg hd (show 0≤s from hs.1))
  have hqI : IntegrableOn q (Ioc 0 (t:ℝ)) :=
    (hqC.intervalIntegrable_of_Icc (NNReal.coe_nonneg t)).1
  obtain ⟨g,hg,hIto⟩ := heston_weighted_stochastic_fubini hOne (le_refl 1)
    t hB₂ hVp hVnonneg hVint hmean hq hqI
  let G := w d • ψ t + g
  refine ⟨G, ?_, ?_⟩
  · have hψt := hestonKernelFamilyLp_ae hOne hVp hVnonneg hVint hmean
      (hestonNNRealHorizonPoint t t)
    have htclamp : ((hestonNNRealHorizonPoint t t : Icc (0:ℝ≥0) t) : ℝ≥0) = t := min_self _
    filter_upwards [Lp.coeFn_add (w d • ψ t) g, Lp.coeFn_smul (w d) (ψ t),
      hψt,hg,ae_fst_mem_Ioo_jointPredictableMeasure (𝒢 := 𝒢) (μ := μ) t] with z hG hs hψ hg' hz
    have hz' : 0 < (t:ℝ)-(z.1:ℝ) := sub_pos.mpr (by exact_mod_cast hz.2)
    change (G : ℝ≥0 × Ω → ℝ) z = _
    rw [hG,Pi.add_apply,hs,Pi.smul_apply,smul_eq_mul,hψ,hg']
    change w d*(hestonKernel 1 (((hestonNNRealHorizonPoint t t : Icc (0:ℝ≥0) t) : ℝ≥0) - (z.1:ℝ))*
      Real.sqrt (V z.1 z.2)) +
      (volterraConvolution q (fractionalK 1) ((t:ℝ)-(z.1:ℝ)))*Real.sqrt (V z.1 z.2) = _
    rw [htclamp, affine_recent_derivative_one_convolution hd hz'.le hw]
    simp only [hestonKernel,ite_eq_left hz',sub_self,Real.rpow_zero,Real.Gamma_one,div_one,one_mul]
    ring
  · change I G = w d • I (ψ t) + ∫ u : ℝ≥0, q ((t:ℝ)-(u:ℝ)) • I (ψ u) ∂hestonTimeMeasure t
    rw [show I G = I (w d • ψ t+g) from rfl, map_add, map_smul]
    exact congrArg (fun x => w d • I (ψ t)+x) hIto.symm

#print axioms affine_preterminal_jointIto_by_parts

end RoughHeston
