import FocalPulseDynamics
import RawFocalFirstTilt

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston.GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} {J U C W : ℝ≥0 → Ω → ℝ} {H r : ℝ≥0} {α κ σ ε d : ℝ}

/-- Bring the focal pulse to the shorter cap horizon without changing
its variance or the martingale before the observation. Its stopped
compensator is the actual continuous integrated variance. -/
theorem FocalPulseDynamics.frozen_at_cap_age
    (h : FocalPulseDynamics μ F H α κ σ ε d J U C W) (hr : r≤H) :
    let J' (t : ℝ≥0) := J (min t r)
    let C' (t : ℝ≥0) (ω : Ω) := ∫ u, σ^2*U u ω ∂hestonTimeMeasure (min t r)
    FractionalPulseProcess μ F r α κ (σ^2/2) ε d J' U C' ∧
      (∀ ω, Continuous (fun t => C' t ω)) ∧
      (∀ ω, Monotone (fun t => C' t ω)) ∧
      Integrable (Function.uncurry U) ((hestonTimeMeasure r).prod μ) := by
  let J' (t : ℝ≥0) := J (min t r)
  let C' (t : ℝ≥0) (ω : Ω) := ∫ u, σ^2*U u ω ∂hestonTimeMeasure (min t r)
  have hu : IsStronglyPredictable F U :=
    SHE.ContinuousPredictable.stronglyMeasurable _ _ h.pulse.variance_adapted h.pulse.variance_continuous
  let g (t : ℝ≥0) (ω : Ω) := σ^2 * U t ω
  have hg : IsStronglyPredictable F g := by
    let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    exact (measurable_const.mul hu.measurable).stronglyMeasurable
  have he (t : ℝ≥0) (ω : Ω) :
      C' t ω=∫ u in (0:ℝ)..((min t r:ℝ≥0):ℝ), σ^2*U u.toNNReal ω := by
    have hgm : Measurable (fun u => g u ω) :=
      ((hg.mono F.predictable_le_prod).measurable.comp (measurable_id.prodMk measurable_const))
    change (∫ u, g u ω ∂hestonTimeMeasure (min t r)) = _
    rw [hestonTimeMeasure,integral_map continuous_real_toNNReal.measurable.aemeasurable
      hgm.aestronglyMeasurable,restrict_Ioo_eq_restrict_Ioc,
      ←intervalIntegral.integral_of_le (min t r).coe_nonneg]
  have hCf (t : ℝ≥0) : C (min t r) =ᵐ[μ] C' t := by
    filter_upwards [h.clock] with ω hω
    rw [he]
    exact hω _ ((min_le_right _ _).trans hr)
  have hC' (ω : Ω) : Continuous (fun t => C' t ω) := by
    simp_rw [he]
    have hc : Continuous (fun u : ℝ => σ^2*U u.toNNReal ω) :=
      continuous_const.mul ((h.pulse.variance_continuous ω).comp continuous_real_toNNReal)
    exact (intervalIntegral.continuous_primitive (fun a d => hc.intervalIntegrable a d) 0).comp
      (NNReal.continuous_coe.comp (continuous_id.min continuous_const))
  have hmon (ω : Ω) : Monotone (fun t => C' t ω) := by
    intro s t hst
    have hc : Continuous (fun u : ℝ => σ^2*U u.toNNReal ω) :=
      continuous_const.mul ((h.pulse.variance_continuous ω).comp continuous_real_toNNReal)
    change C' s ω≤C' t ω
    rw [he s ω,he t ω]
    exact intervalIntegral.integral_mono_interval le_rfl (min s r).coe_nonneg
      (NNReal.coe_le_coe.mpr (min_le_min_right r hst))
      (ae_of_all _ fun u => mul_nonneg (sq_nonneg σ) (h.pulse.variance_nonnegative _ _))
      (hc.intervalIntegrable _ _)
  have hJ' : Martingale J' F μ := martingale_freeze_at h.pulse.martingale r
  have hC'a : StronglyAdapted F C' := by
    intro t
    exact (stronglyAdapted_timePrimitive hg (min t r)).mono (F.mono (min_le_left _ _))
  have hCs : Martingale (fun t => J' t*J' t-C' t) F μ := by
    apply (martingale_freeze_at h.pulse.compensated_square r).congr
      (fun t => ((hJ'.stronglyAdapted t).mul (hJ'.stronglyAdapted t)).sub (hC'a t))
    intro t
    filter_upwards [hCf t] with ω hω
    change J' t ω*J' t ω-C (min t r) ω = J' t ω*J' t ω-C' t ω
    rw [hω]
  have hJ₀ : ∀ᵐ ω ∂μ, J' 0 ω=0 := by
    simpa only [J',min_eq_left (zero_le : (0:ℝ≥0)≤r)] using h.pulse.martingale_zero
  have hClock (t : ℝ≥0) (ht : t≤r) : C' t =ᵐ[μ] fun ω =>
      ∫ u in (0:ℝ)..(t:ℝ), (2*(σ^2/2))*U u.toNNReal ω := by
    have htwo : 2*(σ^2/2)=σ^2 := by ring
    exact ae_of_all _ fun ω => by rw [he,min_eq_left ht,htwo]
  have hInv : ∀ᵐ ω ∂μ, ∀ t∈Ioc (0:ℝ) (r:ℝ), J' t.toNNReal ω =
      volterraConvolution (fractionalL α) (fun u => U u.toNNReal ω) t +
        ∫ u in Ioc (0:ℝ) t, κ*U u.toNNReal ω-rectangularPulseRate ε d u := by
    filter_upwards [h.pulse.inverse] with ω hw t ht
    have htr : t.toNNReal≤r := Real.toNNReal_le_iff_le_coe.mpr ht.2
    simpa only [J',min_eq_left htr] using hw t ⟨ht.1,ht.2.trans (NNReal.coe_le_coe.mpr hr)⟩
  refine ⟨⟨hJ',fun t => h.pulse.martingale_memLp (min t r),?_,hJ₀,
    h.pulse.variance_adapted,h.pulse.variance_continuous,h.pulse.variance_nonnegative,
    h.pulse.variance_zero,hCs,fun t => (h.pulse.compensator_integrable (min t r)).congr (hCf t),
    fun a b hab => ae_of_all _ fun ω => hmon ω hab,hClock,hInv⟩,hC',hmon,?_⟩
  · exact fun ω => (h.pulse.martingale_continuous ω).comp (continuous_id.min continuous_const)
  let : IsFiniteMeasure (hestonTimeMeasure r) := by
    rw [hestonTimeMeasure_eq_horizon]
    infer_instance
  obtain ⟨K,hK⟩ := h.regularity.mean_bounded
  have hh := memLp_kernel_mul_sqrt_of_uniform_mean
    (k:=fun (_ : ℝ≥0) => (1:ℝ)) (memLp_const (μ:=hestonTimeMeasure r) (1:ℝ))
    (hu.mono F.predictable_le_prod).measurable h.pulse.variance_nonnegative h.regularity.integrable hK
  change Integrable (fun p : ℝ≥0 × Ω => U p.1 p.2) ((hestonTimeMeasure r).prod μ)
  simpa only [one_mul,Real.sq_sqrt (h.pulse.variance_nonnegative _ _)] using hh.integrable_sq

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.FocalPulseDynamics.frozen_at_cap_age
