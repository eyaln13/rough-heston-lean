import SmoothCoupledMartingaleProblem
import RawClosedHittingTime

/-! The memory coordinates are the deterministic exponential histories of
the clipped variance coordinates, and therefore are nonnegative. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

open MathFin.ItoIntegralCLM

set_option maxHeartbeats 700000

theorem continuous_frozen_timeMeasureHorizon_integral (T : ℝ≥0) {f : ℝ≥0 → ℝ}
    (hf : Continuous f) :
    Continuous (fun t => ∫ r, f r ∂timeMeasureHorizon (min t T)) := by
  have hF : Continuous (fun r : ℝ => f r.toNNReal) := hf.comp continuous_real_toNNReal
  have hI := (intervalIntegral.differentiable_integral_of_continuous (a := 0) hF).continuous
  simp_rw [integral_timeMeasureHorizon_eq_intervalIntegral hf.measurable]
  exact hI.comp (NNReal.continuous_coe.comp (continuous_id.min continuous_const))

/-- A continuous process with zero initial value and whose square is a
martingale vanishes almost surely simultaneously on the compact horizon. -/
theorem ae_eq_zero_of_square_martingale {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {F : Filtration ℝ≥0 m}
    {T : ℝ≥0} {M : ℝ≥0 → Ω → ℝ}
    (hc : ∀ ω, Continuous (fun t => M t ω))
    (h0 : M 0 =ᵐ[μ] 0) (hM : Martingale (fun t ω => M t ω ^ 2) F μ) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, M t ω = 0 := by
  apply MathFin.LocalisationInMeasure.ae_forall_eq_of_continuousOn
    (Y' := fun _ _ => 0)
    (Eventually.of_forall fun ω => (hc ω).continuousOn)
    (Eventually.of_forall fun _ => continuousOn_const)
  intro t _
  have he : (∫ ω, M t ω ^ 2 ∂μ) = 0 := by
    have heq := hM.setIntegral_eq (show (0 : ℝ≥0) ≤ t from zero_le)
      (show MeasurableSet[F 0] (univ : Set Ω) from MeasurableSet.univ)
    rw [setIntegral_univ, setIntegral_univ] at heq
    rw [← heq]
    have hzero : (fun ω => M 0 ω ^ 2) =ᵐ[μ] (fun _ => 0) :=
      h0.mono fun ω hω => by simp [show M 0 ω = 0 from hω]
    rw [integral_congr_ae hzero]
    simp
  have hz := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (M t ω)) (hM.integrable t)).mp he
  filter_upwards [hz] with ω hω
  by_contra hne
  exact (sq_pos_of_ne_zero hne).ne' hω

/-- A continuous NNReal-time memory integral is the explicit exponential
time convolution. The differentiable auxiliary primitive extends the
equation across the two endpoints of the horizon. -/
theorem exponentialVarianceMemory_eq_of_nnreal_integral {T : ℝ≥0} {f m : ℝ≥0 → ℝ}
    {rate : ℝ} (hf : Continuous f) (hm : Continuous m)
    (heq : ∀ t ∈ Icc 0 T, m t = ∫ r, (max (f r) 0 - rate*m r) ∂timeMeasureHorizon t) :
    ∀ t ∈ Icc 0 T, m t = exponentialVarianceMemory rate (fun r : ℝ => f r.toNNReal) t := by
  let d (r : ℝ≥0) := max (f r) 0 - rate*m r
  let d' (r : ℝ) := d r.toNNReal
  let f' (r : ℝ) := f r.toNNReal
  let m' (r : ℝ) := ∫ s in (0 : ℝ)..r, d' s
  have hd : Continuous d := (hf.max continuous_const).sub (continuous_const.mul hm)
  have hd' : Continuous d' := hd.comp continuous_real_toNNReal
  have hf' : Continuous f' := hf.comp continuous_real_toNNReal
  have hcoincide (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) : m' r = m r.toNNReal := by
    have hr' : r.toNNReal ∈ Icc (0 : ℝ≥0) T :=
      ⟨zero_le, by exact_mod_cast (Real.coe_toNNReal r hr.1).trans_le hr.2⟩
    rw [heq _ hr', integral_timeMeasureHorizon_eq_intervalIntegral hd.measurable,
      Real.coe_toNNReal r hr.1]
  have hode (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) :
      HasDerivAt m' (max (f' r) 0 - rate*m' r) r := by
    rw [hcoincide r hr]
    exact intervalIntegral.integral_hasDerivAt_right (hd'.intervalIntegrable _ _)
      hd'.aestronglyMeasurable.stronglyMeasurableAtFilter hd'.continuousAt
  have hsolve := exponentialVarianceMemory_eq_of_ode hf' (show m' 0 = 0 by simp [m']) hode
  intro t ht
  have ht' : (t : ℝ) ∈ Icc 0 (T : ℝ) := ⟨t.coe_nonneg, by exact_mod_cast ht.2⟩
  have h := hcoincide t ht'
  rw [Real.toNNReal_coe] at h
  exact h.symm.trans (hsolve t ht')

variable {ι η : Type*} [Fintype ι] [Fintype η] [DecidableEq ι]

local notation "S" => SmoothCoupledState ι η
local notation "J" => Option ι × Option η

theorem continuous_smoothCoupledMartingale_time (T : ℝ≥0) (K₀ κ ℓ₀ : ℝ) (v : Option ι → ℝ)
    (q rate : η → ℝ) (β : Option ι → ℝ≥0 → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B)
    (k : J) (p : CanonicalPath T S) :
    Continuous (fun t => smoothCoupledMartingale T K₀ κ ℓ₀ v q rate β k t p) := by
  have hZ : Continuous (fun t => canonicalPathEval T t p) :=
    p.continuous.comp ((continuous_id.min continuous_const).subtype_mk _)
  have hd := (continuous_smoothCoupledShiftedDrift T K₀ κ ℓ₀ v q rate β hB hβ hβB k).comp
    (continuous_id.prodMk hZ)
  exact (((continuous_apply k).comp hZ).sub continuous_const).sub
    (continuous_frozen_timeMeasureHorizon_integral T hd)

/-- In a realized canonical martingale problem the memory coordinates
are exactly deterministic exponential convolutions, with no residual noise. -/
theorem ae_smoothCoupled_memory_eq_exponential
    (T : ℝ≥0) (K₀ κ ℓ₀ σ : ℝ) (v : Option ι → ℝ) (q rate : η → ℝ)
    (β : Option ι → ℝ≥0 → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B)
    {μ : Measure (CanonicalPath T S)} [IsFiniteMeasure μ]
    (h0 : ∀ᵐ p ∂μ, smoothCoupledPath T K₀ β 0 p = smoothCoupledInitial v)
    (hQ : ∀ k : J, Martingale (fun t p =>
      smoothCoupledMartingale T K₀ κ ℓ₀ v q rate β k t p *
        smoothCoupledMartingale T K₀ κ ℓ₀ v q rate β k t p -
        smoothCoupledCompensator T K₀ σ β k k t p)
      (canonicalPathNaturalFiltration T) μ) :
    ∀ᵐ p ∂μ, ∀ i j, ∀ t ∈ Icc 0 T, smoothCoupledPath T K₀ β t p (i, some j) =
      exponentialVarianceMemory (rate j) (fun r : ℝ =>
        smoothCoupledPath T K₀ β r.toNNReal p (i, none)) t := by
  let X := smoothCoupledPath (η := η) T K₀ β
  let M := smoothCoupledMartingale (η := η) T K₀ κ ℓ₀ v q rate β
  let A := smoothCoupledCompensator (η := η) T K₀ σ β
  have hX (p : CanonicalPath T S) : Continuous (fun t => X t p) :=
    continuous_translatedCanonicalState_time T
      (continuous_smoothCoupledImmigrationPrimitive T K₀ β hB hβ hβB) p
  have hZero (k : J) : M k 0 =ᵐ[μ] 0 := by
    filter_upwards [h0] with p hp
    have he := smoothCoupledPath_decomposition T K₀ κ ℓ₀ v q rate β hB hβ hβB 0 p k
    rw [hp] at he
    simpa [timeMeasureHorizon, M] using (show M k 0 p = 0 from by
      have he' : smoothCoupledInitial v k =
          smoothCoupledInitial v k + M k 0 p := by simpa [timeMeasureHorizon, M] using he
      linarith)
  have hMemZero (i : Option ι) (j : η) : ∀ᵐ p ∂μ, ∀ t ∈ Icc 0 T, M (i, some j) t p = 0 := by
    have hAZ (t : ℝ≥0) (p : CanonicalPath T S) : A (i, some j) (i, some j) t p = 0 := by
      simp [A, smoothCoupledCompensator, smoothCoupledCovariance_memory_zero]
    have hM2 := hQ (i, some j)
    change Martingale (fun t p => M (i, some j) t p * M (i, some j) t p -
      A (i, some j) (i, some j) t p) _ _ at hM2
    simp only [hAZ, sub_zero, ← pow_two] at hM2
    exact ae_eq_zero_of_square_martingale (T := T)
      (continuous_smoothCoupledMartingale_time T K₀ κ ℓ₀ v q rate β hB hβ hβB (i, some j))
      (hZero _) hM2
  have hall : ∀ᵐ p ∂μ, ∀ i j, ∀ t ∈ Icc 0 T, M (i, some j) t p = 0 :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun j => hMemZero i j
  filter_upwards [hall] with p hp i j
  apply exponentialVarianceMemory_eq_of_nnreal_integral
    ((continuous_apply (i, none)).comp (hX p)) ((continuous_apply (i, some j)).comp (hX p))
  intro t ht
  simpa [X, M, smoothCoupledInitial, smoothCoupledDrift_memory, smoothVariancePositive,
    smoothCoupledImmigration, min_eq_left ht.2, hp i j t ht] using
      (smoothCoupledPath_decomposition T K₀ κ ℓ₀ v q rate β hB hβ hβB t p (i, some j))

#print axioms RoughHeston.ae_eq_zero_of_square_martingale
#print axioms RoughHeston.exponentialVarianceMemory_eq_of_nnreal_integral
#print axioms RoughHeston.ae_smoothCoupled_memory_eq_exponential

end RoughHeston
