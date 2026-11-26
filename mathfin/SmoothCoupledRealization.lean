import SmoothCoupledNonnegative
import SmoothLiftInverseIdentity

/-! The realized coupled variances satisfy their exact deterministic
first-kind resolvent equations. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

open MathFin.ItoIntegralCLM

set_option maxHeartbeats 900000

variable {ι η : Type*} [Fintype ι] [Fintype η] [DecidableEq ι]

local notation "S" => SmoothCoupledState ι η
local notation "J" => Option ι × Option η

/-- Pathwise first-kind inversion for each variance coordinate of the
coupled finite-exponential lift. The martingale is rescaled by the atom
of the inverse measure. -/
theorem ae_smoothCoupled_inverse_eq_rescaled_martingale
    (T : ℝ≥0) (K₀ κ ℓ₀ : ℝ) (hK₀ : K₀ ≠ 0)
    (v : Option ι → ℝ) (q rate : η → ℝ) (β : Option ι → ℝ≥0 → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B)
    {μ : Measure (CanonicalPath T S)}
    (hNonneg : ∀ᵐ p ∂μ, ∀ i : Option ι, ∀ t ∈ Icc 0 T, 0 ≤ smoothCoupledPath T K₀ β t p (i, none))
    (hMemory : ∀ᵐ p ∂μ, ∀ i j, ∀ t ∈ Icc 0 T, smoothCoupledPath T K₀ β t p (i, some j) =
      exponentialVarianceMemory (rate j) (fun r : ℝ =>
        smoothCoupledPath T K₀ β r.toNNReal p (i, none)) t) :
    ∀ᵐ p ∂μ, ∀ i : Option ι, ∀ t ∈ Icc 0 T,
      smoothExponentialInverse K₀ ℓ₀ q rate (v i)
        (fun r : ℝ => smoothCoupledPath T K₀ β r.toNNReal p (i, none)) t =
      smoothCoupledMartingale T K₀ κ ℓ₀ v q rate β (i, none) t p / K₀ +
        ∫ r in (0 : ℝ)..(t : ℝ), (β i r.toNNReal -
          κ*smoothCoupledPath T K₀ β r.toNNReal p (i, none)) := by
  filter_upwards [hNonneg, hMemory] with p hp hm i t ht
  let Y := smoothCoupledPath (η := η) T K₀ β
  let f (r : ℝ) := Y r.toNNReal p (i, none)
  let g (r : ℝ) := β i r.toNNReal
  let M := smoothCoupledMartingale T K₀ κ ℓ₀ v q rate β (i, none) t p
  have hYc : Continuous (fun r => Y r p) :=
    continuous_translatedCanonicalState_time T
      (continuous_smoothCoupledImmigrationPrimitive T K₀ β hB hβ hβB) p
  have hf : Continuous f := (continuous_apply (i, none)).comp (hYc.comp continuous_real_toNNReal)
  have hTime (r : ℝ) (hr : r ∈ Icc (0 : ℝ) (t : ℝ)) : r.toNNReal ∈ Icc (0 : ℝ≥0) T :=
    ⟨zero_le, (show r.toNNReal ≤ t from by
      exact_mod_cast (Real.coe_toNNReal r hr.1).trans_le hr.2).trans ht.2⟩
  have hf₀ (r : ℝ) (hr : r ∈ Icc (0 : ℝ) (t : ℝ)) : 0 ≤ f r := hp i _ (hTime r hr)
  have hg : IntervalIntegrable g volume 0 (t : ℝ) := by
    rw [intervalIntegrable_iff]
    have hC : IntervalIntegrable (fun _ : ℝ => B) volume 0 (t : ℝ) := intervalIntegrable_const
    rw [intervalIntegrable_iff] at hC
    exact hC.mono' ((hβ i).comp continuous_real_toNNReal.measurable).stronglyMeasurable.aestronglyMeasurable
      (Eventually.of_forall fun r => hβB i r.toNNReal)
  change smoothExponentialInverse K₀ ℓ₀ q rate (v i) f t = M/K₀ +
    ∫ r in (0 : ℝ)..(t : ℝ), (g r - κ*f r)
  apply smoothExponentialInverse_eq_rescaled_martingale hK₀ t.coe_nonneg q rate hf hf₀ hg
  let d (r : ℝ≥0) := smoothCoupledDrift K₀ κ ℓ₀ v q rate r (Y r p) (i, none)
  let e (r : ℝ≥0) := smoothCoupledImmigration (η := η) K₀ β r (i, none)
  have hdc : Continuous d := by
    have hc : Continuous (fun w : ℝ≥0 × S => smoothCoupledDrift K₀ κ ℓ₀ v q rate w.1 w.2 (i, none)) :=
      continuous_smoothCoupledDrift K₀ κ ℓ₀ v q rate (i, none)
    have h := hc.comp (continuous_id.prodMk hYc)
    change Continuous d at h
    exact h
  have he : Measurable e := measurable_smoothCoupledImmigration (η := η) K₀ β hβ (i, none)
  have hEq := smoothCoupledPath_decomposition T K₀ κ ℓ₀ v q rate β hB hβ hβB t p (i, none)
  change Y t p (i, none) = smoothCoupledInitial (η := η) v (i, none) +
    (∫ r, (d r+e r) ∂timeMeasureHorizon (min t T)) + M at hEq
  have hde : Measurable (fun r : ℝ≥0 => d r + e r) := hdc.measurable.add he
  rw [min_eq_left ht.2, integral_timeMeasureHorizon_eq_intervalIntegral hde] at hEq
  rw [show f (t : ℝ) = Y t p (i, none) by simp [f], hEq, smoothCoupledInitial]
  congr 1
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le t.coe_nonneg] at hr
  have hclip : smoothVariancePositive (Y r.toNNReal p) i = f r :=
    max_eq_left (hf₀ r hr)
  have hmem (j : η) : Y r.toNNReal p (i, some j) = exponentialVarianceMemory (rate j) f r := by
    have h := hm i j _ (hTime r hr)
    rw [Real.coe_toNNReal r hr.1] at h
    exact h
  change d r.toNNReal + e r.toNNReal = _
  rw [show d r.toNNReal = K₀ * (v i * smoothExponentialResolvent ℓ₀ q rate r -
      (κ + smoothExponentialResolvent ℓ₀ q rate 0) * f r +
        ∑ j, q j * rate j * exponentialVarianceMemory (rate j) f r) by
    unfold d
    rw [smoothCoupledDrift_variance, Real.coe_toNNReal r hr.1, hclip]
    simp_rw [hmem] ]
  change _ + K₀*g r = _
  ring

/-- The actual coupled system exists, its physical coordinates are
nonnegative, and its memory and first-kind inverse equalities hold
simultaneously on the complete time interval. -/
theorem exists_nonnegative_smoothCoupled_realization {T : ℝ≥0} (hT : 0 < T)
    (K₀ κ ℓ₀ σ : ℝ) (v : Option ι → ℝ) (q rate : η → ℝ) (β : Option ι → ℝ≥0 → ℝ)
    (hK₀ : 0 < K₀) (hℓ₀ : 0 ≤ ℓ₀) (hv : ∀ i, 0 ≤ v i)
    (hq : ∀ j, 0 ≤ q j) (hrate : ∀ j, 0 ≤ rate j) (hβ₀ : ∀ i t, 0 ≤ β i t)
    {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B) :
    ∃ P : ProbabilityMeasure (CanonicalPath T S),
      MemLp (fun p : CanonicalPath T S => ‖p‖) 2 (P : Measure _) ∧
      (∀ᵐ p ∂(P : Measure (CanonicalPath T S)), smoothCoupledPath T K₀ β 0 p = smoothCoupledInitial v) ∧
      (∀ k : J, Martingale (smoothCoupledMartingale T K₀ κ ℓ₀ v q rate β k)
        (canonicalPathNaturalFiltration T) (P : Measure _)) ∧
      (∀ k l : J, Martingale (fun t p =>
        smoothCoupledMartingale T K₀ κ ℓ₀ v q rate β k t p *
          smoothCoupledMartingale T K₀ κ ℓ₀ v q rate β l t p -
          smoothCoupledCompensator T K₀ σ β k l t p)
        (canonicalPathNaturalFiltration T) (P : Measure _)) ∧
      (∀ᵐ p ∂(P : Measure (CanonicalPath T S)), ∀ i : Option ι, ∀ t ∈ Icc 0 T,
        0 ≤ smoothCoupledPath T K₀ β t p (i, none)) ∧
      (∀ᵐ p ∂(P : Measure (CanonicalPath T S)), ∀ i j, ∀ t ∈ Icc 0 T,
        smoothCoupledPath T K₀ β t p (i, some j) =
          exponentialVarianceMemory (rate j) (fun r : ℝ =>
            smoothCoupledPath T K₀ β r.toNNReal p (i, none)) t) ∧
      (∀ᵐ p ∂(P : Measure (CanonicalPath T S)), ∀ i : Option ι, ∀ t ∈ Icc 0 T,
        smoothExponentialInverse K₀ ℓ₀ q rate (v i)
          (fun r : ℝ => smoothCoupledPath T K₀ β r.toNNReal p (i, none)) t =
        smoothCoupledMartingale T K₀ κ ℓ₀ v q rate β (i, none) t p / K₀ +
          ∫ r in (0 : ℝ)..(t : ℝ), (β i r.toNNReal -
            κ*smoothCoupledPath T K₀ β r.toNNReal p (i, none))) := by
  obtain ⟨P, h₂, h0, hM, hQ⟩ :=
    exists_smoothCoupled_martingale_problem hT K₀ κ ℓ₀ σ v q rate β hrate hB hβ hβB
  have hN := ae_smoothCoupled_variances_nonnegative T K₀ κ ℓ₀ σ v q rate β hB hβ hβB
    hK₀.le hℓ₀ hv hq hrate hβ₀ h₂ h0 hM (fun k => hQ k k)
  have hMem := ae_smoothCoupled_memory_eq_exponential T K₀ κ ℓ₀ σ v q rate β hB hβ hβB h0
    (fun k => hQ k k)
  exact ⟨P, h₂, h0, hM, hQ, hN, hMem,
    ae_smoothCoupled_inverse_eq_rescaled_martingale T K₀ κ ℓ₀ hK₀.ne'
      v q rate β hB hβ hβB hN hMem⟩

#print axioms RoughHeston.ae_smoothCoupled_inverse_eq_rescaled_martingale
#print axioms RoughHeston.exists_nonnegative_smoothCoupled_realization

end RoughHeston
