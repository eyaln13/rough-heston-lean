import FractionalCoupledInverseLaw
import HestonBoundaryPointTests
import ActualFractionalPulse

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
local notation "Ω" => CanonicalPath T (CoupledPhysicalState ι)
local notation "𝒢" => canonicalPathNaturalFiltration T (E := CoupledPhysicalState ι)

theorem canonicalPhysicalVariance_adapted (i : Option ι) :
    StronglyAdapted 𝒢 (canonicalPhysicalVariance T i) := by
  have h : StronglyAdapted 𝒢 (canonicalPathEval T) :=
    Filtration.stronglyAdapted_natural (fun t =>
      (ContinuousMap.measurable_eval (canonicalEvalTime T t)).stronglyMeasurable)
  exact fun t => ((continuous_apply i).comp continuous_fst).comp_stronglyMeasurable (h t)

theorem canonicalPhysicalVariance_time_continuous (i : Option ι) (p : Ω) :
    Continuous (fun t => canonicalPhysicalVariance T i t p) :=
  ((continuous_apply i).comp continuous_fst).comp
    (p.continuous.comp ((continuous_id.min continuous_const).subtype_mk _))

theorem canonicalPhysicalResidual_time_continuous (i : Option ι) (p : Ω) :
    Continuous (fun t => canonicalPhysicalResidual T i t p) :=
  ((continuous_apply i).comp continuous_snd).comp
    (p.continuous.comp ((continuous_id.min continuous_const).subtype_mk _))

/-- The deterministic initial value is enforced on a time-zero event.
The clamp makes all sample paths nonnegative without changing the law. -/
noncomputable def canonicalRegularVariance (T : ℝ≥0) (i : Option ι) (v : ℝ)
    (t : ℝ≥0) (p : CanonicalPath T (CoupledPhysicalState ι)) : ℝ :=
  if canonicalPhysicalVariance T i 0 p=v then max (canonicalPhysicalVariance T i t p) 0 else v

theorem canonicalRegularVariance_adapted (i : Option ι) (v : ℝ) :
    StronglyAdapted 𝒢 (canonicalRegularVariance T i v) := by
  intro t
  have h0 := ((canonicalPhysicalVariance_adapted (T := T) i 0).mono ((𝒢).mono (show 0≤t from zero_le))).measurable
  have ht := (canonicalPhysicalVariance_adapted (T := T) i t).measurable
  exact ((ht.max measurable_const).ite (measurableSet_eq_fun h0 measurable_const) measurable_const).stronglyMeasurable

theorem canonicalRegularVariance_continuous_nonnegative_initial (i : Option ι) {v : ℝ} (hv : 0≤v) :
    (∀ p : Ω,Continuous (fun t => canonicalRegularVariance T i v t p)) ∧
      (∀ t (p : Ω),0≤canonicalRegularVariance T i v t p) ∧ (∀ p : Ω,canonicalRegularVariance T i v 0 p=v) := by
  refine ⟨?_,?_,?_⟩
  · intro p
    by_cases h : canonicalPhysicalVariance T i 0 p=v
    · simpa only [canonicalRegularVariance,ite_eq_left h] using
        (canonicalPhysicalVariance_time_continuous i p).max continuous_const
    · simpa only [canonicalRegularVariance,ite_eq_right h] using
        (continuous_const : Continuous (fun _ : ℝ≥0 => v))
  · intro t p
    unfold canonicalRegularVariance
    split <;> first | exact le_max_right _ _ | exact hv
  · intro p
    by_cases h : canonicalPhysicalVariance T i 0 p=v
    · simp [canonicalRegularVariance,h,max_eq_left hv]
    · simp [canonicalRegularVariance,h]

theorem canonicalRegularVariance_ae_paths {μ : Measure Ω} {v : Option ι → ℝ}
    (hI : ∀ᵐ p ∂μ,p∈canonicalPhysicalInitialSet T v)
    (hN : ∀ᵐ p ∂μ,p∈canonicalPhysicalNonnegative (ι := ι) T) (i : Option ι) :
    ∀ᵐ p ∂μ,∀ t,canonicalRegularVariance T i (v i) t p=canonicalPhysicalVariance T i t p := by
  filter_upwards [hI,hN] with p hi hn t
  have h0 : canonicalPhysicalVariance T i 0 p=v i :=
    congrFun (congrArg Prod.fst hi) i
  have hv : 0≤canonicalPhysicalVariance T i t p := hn i (canonicalEvalTime T t)
  simp [canonicalRegularVariance,ite_eq_left h0,max_eq_left hv]

theorem canonicalPhysicalResidual_zero_ae {μ : Measure Ω} {v : Option ι → ℝ}
    (hI : ∀ᵐ p ∂μ,p∈canonicalPhysicalInitialSet T v) (i : Option ι) :
    ∀ᵐ p ∂μ,canonicalPhysicalResidual T i 0 p=0 :=
  hI.mono fun _ hi => congrFun (congrArg Prod.snd hi) i

theorem canonicalPhysical_diagonal_clock (σ : ℝ) (i : Option ι) (t : ℝ≥0) (p : Ω) :
    canonicalPhysicalCompensator T σ i i t p =
      ∫ r in (0:ℝ)..((min t T:ℝ≥0):ℝ),σ^2*max (canonicalPhysicalVariance T i r.toNNReal p) 0 := by
  unfold canonicalPhysicalCompensator canonicalCoefficientIntegral
  simp_rw [physicalCouplingDensity_diagonal]
  change (∫ r,σ^2*max (canonicalPhysicalVariance T i r p) 0
    ∂MathFin.ItoIntegralCLM.timeMeasureHorizon (min t T)) = _
  rw [← hestonTimeMeasure_eq_horizon,hestonTimeMeasure]
  have hm : Measurable (fun r => σ^2*max (canonicalPhysicalVariance T i r p) 0) :=
    ((canonicalPhysicalVariance_time_continuous i p).max continuous_const).measurable.const_mul _
  rw [integral_map continuous_real_toNNReal.measurable.aemeasurable hm.aestronglyMeasurable,
    restrict_Ioo_eq_restrict_Ioc,← intervalIntegral.integral_of_le (NNReal.coe_nonneg _)]

theorem canonicalPhysical_diagonal_monotone (σ : ℝ) (i : Option ι) (p : Ω) :
    Monotone (fun t => canonicalPhysicalCompensator T σ i i t p) := by
  intro s t hst
  change canonicalPhysicalCompensator T σ i i s p ≤ canonicalPhysicalCompensator T σ i i t p
  rw [canonicalPhysical_diagonal_clock,canonicalPhysical_diagonal_clock]
  let g (r : ℝ) := σ^2*max (canonicalPhysicalVariance T i r.toNNReal p) 0
  have hgc : Continuous g :=
    continuous_const.mul (((canonicalPhysicalVariance_time_continuous i p).comp
      continuous_real_toNNReal).max continuous_const)
  have hle : ((min s T:ℝ≥0):ℝ)≤(min t T:ℝ≥0) :=
    NNReal.coe_le_coe.mpr (min_le_min_right _ hst)
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hgc.intervalIntegrable (0:ℝ) ((min s T:ℝ≥0):ℝ)) (hgc.intervalIntegrable _ ((min t T:ℝ≥0):ℝ))
  have hz := intervalIntegral.integral_nonneg (μ := volume) hle (f := g) (fun r _ => by dsimp [g]; positivity)
  exact (le_add_of_nonneg_right hz).trans_eq hi

theorem canonicalPhysical_diagonal_clock_regular_ae {μ : Measure Ω} {v : Option ι → ℝ}
    (hI : ∀ᵐ p ∂μ,p∈canonicalPhysicalInitialSet T v)
    (hN : ∀ᵐ p ∂μ,p∈canonicalPhysicalNonnegative (ι := ι) T)
    (σ : ℝ) (i : Option ι) :
    ∀ᵐ p ∂μ,∀ t≤T,canonicalPhysicalCompensator T σ i i t p =
      ∫ r in (0:ℝ)..(t:ℝ),σ^2*canonicalRegularVariance T i (v i) r.toNNReal p := by
  filter_upwards [hN,canonicalRegularVariance_ae_paths hI hN i] with p hp hV t ht
  rw [canonicalPhysical_diagonal_clock,min_eq_left ht]
  apply intervalIntegral.integral_congr
  intro r _
  change σ^2*max (canonicalPhysicalVariance T i r.toNNReal p) 0 =
    σ^2*canonicalRegularVariance T i (v i) r.toNNReal p
  have hnn : 0 ≤ canonicalPhysicalVariance T i r.toNNReal p := hp i (canonicalEvalTime T r.toNNReal)
  rw [hV,max_eq_left hnn]

theorem canonicalPhysical_diagonal_clock_integrable {μ : Measure Ω} [IsFiniteMeasure μ]
    (σ : ℝ) (i : Option ι)
    (hM₂ : ∀ t, MemLp (canonicalPhysicalResidual T i t) 2 μ)
    (hC : Martingale (canonicalPhysicalCompensatedProduct T σ i i) 𝒢 μ) (t : ℝ≥0) :
    Integrable (canonicalPhysicalCompensator T σ i i t) μ := by
  have h := ((hM₂ t).integrable_mul (hM₂ t)).sub (hC.integrable t)
  convert h using 1
  funext p
  change _=(canonicalPhysicalResidual T i t p)*(canonicalPhysicalResidual T i t p)-
    ((canonicalPhysicalResidual T i t p)*(canonicalPhysicalResidual T i t p)-canonicalPhysicalCompensator T σ i i t p)
  ring

#print axioms canonicalRegularVariance_ae_paths
#print axioms canonicalPhysical_diagonal_clock_regular_ae

end RoughHeston
