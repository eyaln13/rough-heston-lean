import FractionalCoupledInverseLaw
import PhysicalAggregateCovariance
import CanonicalPhysicalFiniteSums

/-! Read the aggregate and its companion on a two-dimensional path space. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

open MathFin.ItoIntegralCLM

set_option maxHeartbeats 1200000

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
local notation "S" => CoupledPhysicalState ι
local notation "Ω" => CanonicalPath T S
local notation "Ω₂" => CanonicalPath T (ℝ × ℝ)
local notation "F" => canonicalPathNaturalFiltration (E := S) T
local notation "G" => canonicalPathNaturalFiltration (E := ℝ × ℝ) T

noncomputable def aggregatePairState : C(S, ℝ × ℝ) :=
  ⟨fun z => (∑ i : ι, z.1 (some i), z.1 none),
    (continuous_finsetSum _ fun i _ => (continuous_apply (some i)).comp continuous_fst).prodMk
      ((continuous_apply none).comp continuous_fst)⟩

noncomputable def canonicalAggregatePair (p : Ω) : Ω₂ := aggregatePairState.comp p

theorem continuous_canonicalAggregatePair : Continuous (canonicalAggregatePair (ι := ι) (T := T)) :=
  ContinuousMap.continuous_postcomp _

theorem filtration_measurable_canonicalAggregatePair (t : ℝ≥0) :
    Measurable[F t, G t] (canonicalAggregatePair (ι := ι)) := by
  apply filtration_measurable_canonicalPath_of_adapted
  intro u
  have he : StronglyAdapted F (canonicalPathEval T) := Filtration.stronglyAdapted_natural
    (fun s => (ContinuousMap.measurable_eval (canonicalEvalTime T s)).stronglyMeasurable)
  exact (aggregatePairState.continuous.comp_stronglyMeasurable (he u)).measurable

theorem canonicalPathEval_canonicalAggregatePair (t : ℝ≥0) (p : Ω) :
    canonicalPathEval T t (canonicalAggregatePair p) =
      (canonicalPhysicalAggregate T t p, canonicalPhysicalVariance T none t p) := rfl

theorem canonicalAggregatePair_nonnegative (p : Ω) (hp : p ∈ canonicalPhysicalNonnegative (ι := ι) T) :
    ∀ t ≤ T, 0 ≤ (canonicalPathEval T t (canonicalAggregatePair p)).1 ∧
      0 ≤ (canonicalPathEval T t (canonicalAggregatePair p)).2 := by
  have h (s : ℝ≥0) (i : Option ι) : 0 ≤ canonicalPhysicalVariance T i s p :=
    hp i (canonicalEvalTime T s)
  intro t _
  rw [canonicalPathEval_canonicalAggregatePair]
  exact ⟨Finset.sum_nonneg fun i _ => h t (some i), h t none⟩

/-- Immigration error of a row relative to the target constant drift.
It is frozen together with the canonical path after the observation horizon. -/
noncomputable def canonicalImmigrationShift (T : ℝ≥0) (b : ℝ) (β : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  b*((min t T : ℝ≥0):ℝ) - ∫ s in (0:ℝ)..((min t T : ℝ≥0):ℝ), β s.toNNReal

private theorem integrable_variance_reflected_L {α : ℝ} (hα' : α < 1)
    (i : Option ι) (p : Ω) {v : ℝ} (t : ℝ≥0) :
    IntegrableOn (fun s => fractionalL α ((t:ℝ)-s) * (canonicalPhysicalVariance T i s.toNNReal p-v))
      (Ioc 0 (t:ℝ)) := by
  let V (s : ℝ) := canonicalPhysicalVariance T i s.toNNReal p-v
  have hV : Continuous V :=
    (((canonicalPhysicalVariancePath T i p).continuous).comp (realTimeOnHorizon T).continuous).sub continuous_const
  let K (s : ℝ) := fractionalL α ((t:ℝ)-s)
  have hK : IntegrableOn K (Ioc 0 (t:ℝ)) := fractionalL_reflected_integrableOn_Ioc hα' t.coe_nonneg
  obtain ⟨D, hD⟩ := (isCompact_Icc (a := (0:ℝ)) (b := (t:ℝ))).exists_bound_of_continuousOn hV.continuousOn
  apply (hK.norm.mul_const D).mono' (hK.aestronglyMeasurable.mul hV.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  change ‖K s*V s‖ ≤ ‖K s‖*D
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hD s (Ioc_subset_Icc_self hs)) (norm_nonneg _)

private theorem intervalIntegrable_canonicalVariance (i : Option ι) (p : Ω) (t : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ => canonicalPhysicalVariance T i s.toNNReal p) volume 0 (t:ℝ) :=
  ((canonicalPhysicalVariancePath T i p).continuous.comp (realTimeOnHorizon T).continuous).intervalIntegrable _ _

private theorem intervalIntegrable_boundedRate {β : ℝ≥0 → ℝ} {B : ℝ}
    (hβ : Measurable β) (hβB : ∀ t, ‖β t‖ ≤ B) (t : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ => β s.toNNReal) volume 0 (t:ℝ) := by
  rw [intervalIntegrable_iff]
  have h : IntervalIntegrable (fun _ : ℝ => B) volume 0 (t:ℝ) := intervalIntegrable_const
  rw [intervalIntegrable_iff] at h
  exact h.mono' (hβ.comp continuous_real_toNNReal.measurable).aestronglyMeasurable
    (Eventually.of_forall fun r => hβB r.toNNReal)

/-- The two projected martingale candidates agree with the aggregate
residual and the companion residual through explicit immigration shifts. -/
theorem ae_canonicalAggregatePair_martingale_pullback
    {α v₀ κ θ : ℝ} (hα' : α < 1) (v : Option ι → ℝ) (β : Option ι → ℝ≥0 → ℝ)
    (hvX : (∑ i : ι, v (some i)) = v₀) (hvY : v none = v₀)
    {B : ℝ} (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B)
    {μ : Measure Ω}
    (hRows : ∀ i, ∀ᵐ p ∂μ, ∀ t ≤ T,
      volterraConvolution (fractionalL α) (fun s => canonicalPhysicalVariance T i s.toNNReal p-v i) (t:ℝ) =
        canonicalPhysicalResidual T i t p +
          ∫ r in (0:ℝ)..(t:ℝ), (β i r.toNNReal - κ*canonicalPhysicalVariance T i r.toNNReal p))
    (hNonneg : ∀ᵐ p ∂μ, p ∈ canonicalPhysicalNonnegative (ι := ι) T) :
    ∀ᵐ p ∂μ, ∀ t,
      canonicalVarianceMartingale T α v₀ κ θ canonicalFirstVariance t (canonicalAggregatePair p) +
        canonicalImmigrationShift T (κ*θ) (fun s => ∑ i : ι, β (some i) s) t =
          canonicalPhysicalAggregateResidual T t p ∧
      canonicalVarianceMartingale T α v₀ κ θ canonicalSecondVariance t (canonicalAggregatePair p) +
        canonicalImmigrationShift T (κ*θ) (β none) t = canonicalPhysicalResidual T none t p := by
  filter_upwards [ae_all_iff.mpr hRows,hNonneg] with p hp hn t
  let u := min t T
  have hu : u ≤ T := min_le_right _ _
  have hEval (s : ℝ≥0) : canonicalEvalTime T s = canonicalEvalTime T (min s T) :=
    Subtype.ext (min_eq_left (min_le_right s T)).symm
  have hX (s : ℝ) : canonicalFirstVariance (canonicalAggregatePair p (realTimeOnHorizon T s)) =
      ∑ i : ι, canonicalPhysicalVariance T (some i) s.toNNReal p := by
    change max 0 (∑ i : ι, canonicalPhysicalVariance T (some i) s.toNNReal p) = _
    exact max_eq_right (Finset.sum_nonneg fun i _ => hn (some i) (realTimeOnHorizon T s))
  have hY (s : ℝ) : canonicalSecondVariance (canonicalAggregatePair p (realTimeOnHorizon T s)) =
      canonicalPhysicalVariance T none s.toNNReal p := by
    change max 0 (canonicalPhysicalVariance T none s.toNNReal p) = _
    exact max_eq_right (hn none (realTimeOnHorizon T s))
  have hvI (i : Option ι) := intervalIntegrable_canonicalVariance i p u
  have hbI (i : Option ι) := intervalIntegrable_boundedRate (hβ i) (hβB i) u
  have hJ (i : Option ι) :
      volterraConvolution (fractionalL α) (fun s => canonicalPhysicalVariance T i s.toNNReal p-v i) (u:ℝ) =
        canonicalPhysicalResidual T i u p + (∫ s in (0:ℝ)..(u:ℝ), β i s.toNNReal) -
          κ*(∫ s in (0:ℝ)..(u:ℝ), canonicalPhysicalVariance T i s.toNNReal p) := by
    rw [hp i u hu, intervalIntegral.integral_sub (hbI i) ((hvI i).const_mul κ), intervalIntegral.integral_const_mul]
    ring
  have hFreeze (i : Option ι) : canonicalPhysicalResidual T i t p = canonicalPhysicalResidual T i u p := by
    simp only [canonicalPhysicalResidual, canonicalPathEval, hEval t, u]
  constructor
  · unfold canonicalVarianceMartingale recoveredVarianceMartingale canonicalImmigrationShift
    simp only [ContinuousMap.comp_apply, hX]
    change ((∫ s in Ioc (0:ℝ) (u:ℝ), fractionalL α ((u:ℝ)-s) *
          ((∑ i : ι, canonicalPhysicalVariance T (some i) s.toNNReal p)-v₀)) - κ*θ*(u:ℝ) +
        κ*(∫ s in Ioc (0:ℝ) (u:ℝ), (∑ i : ι, canonicalPhysicalVariance T (some i) s.toNNReal p))) +
          (κ*θ*(u:ℝ)-(∫ s in (0:ℝ)..(u:ℝ), (∑ i : ι, β (some i) s.toNNReal))) = _
    have hSum (s : ℝ) : fractionalL α ((u:ℝ)-s) *
        ((∑ i : ι, canonicalPhysicalVariance T (some i) s.toNNReal p)-v₀) =
          ∑ i : ι, fractionalL α ((u:ℝ)-s)*(canonicalPhysicalVariance T (some i) s.toNNReal p-v (some i)) := by
      rw [← hvX, ← Finset.sum_sub_distrib, Finset.mul_sum]
    set_option linter.tacticCheckInstances false in
      simp_rw [hSum]
    have hIntegrate := integral_finsetSum (μ := volume.restrict (Ioc (0:ℝ) (u:ℝ))) Finset.univ
      (fun i _ => integrable_variance_reflected_L hα' (some i) p (v := v (some i)) u)
    rw [hIntegrate, ← intervalIntegral.integral_of_le u.coe_nonneg]
    rw [intervalIntegral.integral_finsetSum (fun i _ => hvI (some i)),
      intervalIntegral.integral_finsetSum (fun i _ => hbI (some i))]
    simp only [canonicalPhysicalAggregateResidual, hFreeze]
    have hh (i : ι) := hJ (some i)
    change ((∑ i : ι, volterraConvolution (fractionalL α)
      (fun s => canonicalPhysicalVariance T (some i) s.toNNReal p - v (some i)) (u:ℝ)) - _ + _) + _ = _
    simp_rw [hh, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  · unfold canonicalVarianceMartingale recoveredVarianceMartingale canonicalImmigrationShift
    simp only [ContinuousMap.comp_apply, hY]
    change volterraConvolution (fractionalL α)
      (fun s => canonicalPhysicalVariance T none s.toNNReal p-v₀) (u:ℝ) - κ*θ*(u:ℝ) +
        κ*(∫ s in Ioc (0:ℝ) (u:ℝ), canonicalPhysicalVariance T none s.toNNReal p) +
          (κ*θ*(u:ℝ) - ∫ s in (0:ℝ)..(u:ℝ), β none s.toNNReal) = _
    rw [← hvY, hJ none, ← intervalIntegral.integral_of_le u.coe_nonneg, hFreeze]
    ring

#print axioms RoughHeston.ae_canonicalAggregatePair_martingale_pullback

end RoughHeston
