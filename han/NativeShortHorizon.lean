import BridgeScalarNative
import JointHorizonExtension
import SHEStochastic.NativeTimeCut

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston.GirsanovPort

open SHEStochastic

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} {B : ℝ≥0 → Ω → ℝ} {T t : ℝ≥0}

/-- A native Brownian family may be used at any shorter deterministic
horizon without changing its sample paths or filtration. -/
def truncateScalarNativeFamily (P : FiniteScalarIto.Family F μ T Unit)
    (ht : t ≤ T) : FiniteScalarIto.Family F μ t Unit where
  W := P.W
  adapted := P.adapted
  law n a := by
    refine ⟨?_,?_⟩
    · exact fun u hu => (P.law n a).1 u (fun i => (hu i).trans ht)
    · exact fun s u hsu hu => (P.law n a).2 s u hsu (hu.trans ht)
  continuous := P.continuous

/-- Exact equality of joint stochastic integrals on overlapping time
horizons for a row supported on the shorter clock. -/
theorem jointIto_short_horizon_eq_of_supported_row
    (ht : t ≤ T) (hB₂ : ∀ s, MemLp (B s) 2 μ) (hB : Martingale B F μ)
    (hClock : Martingale (fun s ω => B s ω ^ 2 - ((min s T : ℝ≥0) : ℝ)) F μ)
    {f : ℝ≥0 × Ω → ℝ} {v : Lp ℝ 2 (jointPredictableMeasure F μ t)}
    {u : Lp ℝ 2 (jointPredictableMeasure F μ T)}
    (hZero : ∀ p, t < p.1 → f p = 0)
    (hv : ⇑v =ᵐ[jointPredictableMeasure F μ t] f)
    (hu : ⇑u =ᵐ[jointPredictableMeasure F μ T] f) :
    jointItoIntegralCLM (M := fun s => B (min s t)) t (fun s => hB₂ (min s t)) v =
      jointItoIntegralCLM T hB₂ u := by
  have hf : MemLp f 2 (jointPredictableMeasure F μ t) :=
    (memLp_congr_ae hv).mp (Lp.memLp v)
  have hv' : v = hf.toLp f := Lp.ext (hv.trans hf.coeFn_toLp.symm)
  have he : jointBandExtend F μ ht v = u := by
    rw [hv']
    exact Lp.ext ((jointBandExtend_toLp_ae_eq F μ ht hZero hf).trans hu.symm)
  rw [jointItoIntegralCLM_cross_horizon F μ ht hB₂ hB hClock, he]

/-- A shortened observation uses the elapsed part of the full
predictable row in the larger space. -/
theorem jointIto_short_horizon_eq_prior
    (ht : t ≤ T) (hB₂ : ∀ s, MemLp (B s) 2 μ) (hB : Martingale B F μ)
    (hClock : Martingale (fun s ω => B s ω ^ 2 - ((min s T : ℝ≥0) : ℝ)) F μ)
    {f : ℝ≥0 × Ω → ℝ} {v : Lp ℝ 2 (jointPredictableMeasure F μ t)}
    {u : Lp ℝ 2 (jointPredictableMeasure F μ T)}
    (hv : ⇑v =ᵐ[jointPredictableMeasure F μ t] f)
    (hu : ⇑u =ᵐ[jointPredictableMeasure F μ T] f) :
    jointItoIntegralCLM (M := fun s => B (min s t)) t (fun s => hB₂ (min s t)) v =
      jointItoIntegralCLM T hB₂ (NativeTimeCut.prior t u) := by
  let g (p : ℝ≥0 × Ω) := if t < p.1 then 0 else f p
  have hv' : ⇑v =ᵐ[jointPredictableMeasure F μ t] g := by
    filter_upwards [hv, ae_mem_joint_timeBand F μ t] with p hp ht
    simpa only [g, ite_eq_right (not_lt_of_ge ht.1.2)] using hp
  have hu' : ⇑(NativeTimeCut.prior t u) =ᵐ[jointPredictableMeasure F μ T] g := by
    filter_upwards [hu, NativeTimeCut.prior_ae t u] with p hp hCut
    rw [hCut]
    change (if t < p.1 then 0 else u p) = g p
    rw [hp]
  exact jointIto_short_horizon_eq_of_supported_row ht hB₂ hB hClock
    (fun p hp => by simp [g,hp]) hv' hu'

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.truncateScalarNativeFamily
#print axioms RoughHeston.GirsanovPort.jointIto_short_horizon_eq_of_supported_row
#print axioms RoughHeston.GirsanovPort.jointIto_short_horizon_eq_prior
