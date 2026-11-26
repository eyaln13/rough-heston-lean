import FractionalAggregatePair

/-! Canonical martingale tests for the projected aggregate model. -/

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

noncomputable def canonicalAggregatePairLaw (P : ProbabilityMeasure Ω) : ProbabilityMeasure Ω₂ :=
  ProbabilityMeasure.map P canonicalAggregatePair

theorem canonicalAggregatePairLaw_nonnegative (P : ProbabilityMeasure Ω)
    (hN : ∀ᵐ p ∂(P : Measure Ω), p ∈ canonicalPhysicalNonnegative (ι := ι) T) :
    ∀ᵐ p ∂(canonicalAggregatePairLaw P : Measure Ω₂), ∀ t ≤ T,
      0 ≤ (canonicalPathEval T t p).1 ∧ 0 ≤ (canonicalPathEval T t p).2 := by
  let Z : Set Ω₂ := {p | ∀ t ≤ T, 0 ≤ (canonicalPathEval T t p).1 ∧ 0 ≤ (canonicalPathEval T t p).2}
  have hZ : IsClosed Z := by
    have he : Z = ⋂ t, ⋂ _ : t ≤ T,
        {p | 0 ≤ (canonicalPathEval T t p).1 ∧ 0 ≤ (canonicalPathEval T t p).2} := by ext; simp [Z]
    rw [he]
    exact isClosed_iInter fun t => isClosed_iInter fun _ =>
      (isClosed_le continuous_const (continuous_canonicalPathEval T t).fst).inter
        (isClosed_le continuous_const (continuous_canonicalPathEval T t).snd)
  have hm : Measurable (canonicalAggregatePair (ι := ι) (T := T)) :=
    continuous_canonicalAggregatePair.measurable
  change ∀ᵐ p ∂Measure.map canonicalAggregatePair (P : Measure Ω), p ∈ Z
  apply (ae_map_iff hm.aemeasurable hZ.measurableSet).2
  exact hN.mono fun p hp => canonicalAggregatePair_nonnegative p hp

theorem martingale_canonicalAggregatePairLaw_of_ae_pullback
    (P : ProbabilityMeasure Ω) {M : ℝ≥0 → Ω → ℝ} {N : ℝ≥0 → Ω₂ → ℝ}
    (hM : Martingale M F (P : Measure Ω)) (hN : StronglyAdapted G N)
    (he : ∀ t, M t =ᵐ[(P : Measure Ω)] fun p => N t (canonicalAggregatePair p)) :
    Martingale N G (canonicalAggregatePairLaw P : Measure Ω₂) := by
  apply martingale_measure_map_of_filtration_measurable continuous_canonicalAggregatePair.measurable
    filtration_measurable_canonicalAggregatePair hN
  exact hM.congr (fun t => (hN t).comp_measurable (filtration_measurable_canonicalAggregatePair t)) he

private theorem canonicalVarianceCompensator_aggregatePair_eq
    (g : C(ℝ × ℝ, ℝ)) (t : ℝ≥0) (p : Ω) :
    canonicalVarianceCompensator T g t (canonicalAggregatePair p) =
      ∫ r, g (canonicalPathEval T r (canonicalAggregatePair p)) ∂timeMeasureHorizon (min t T) := by
  let a (r : ℝ≥0) := g (canonicalPathEval T r (canonicalAggregatePair p))
  have ha : Continuous a := g.continuous.comp
    ((canonicalAggregatePair p).continuous.comp ((continuous_id.min continuous_const).subtype_mk _))
  rw [integral_timeMeasureHorizon_eq_intervalIntegral ha.measurable,
    intervalIntegral.integral_of_le (min t T).coe_nonneg]
  rfl

theorem canonicalAggregatePair_compensators_eq
    (σ : ℝ) (p : Ω) (hN : p ∈ canonicalPhysicalNonnegative (ι := ι) T) (t : ℝ≥0) :
    let p₂ := canonicalAggregatePair p
    let f := canonicalFirstVariance
    let k := canonicalSecondVariance
    (∫ r, (∑ i : ι, ∑ j : ι, physicalCouplingDensity σ (some i) (some j) (canonicalPathEval T r p).1)
          ∂timeMeasureHorizon (min t T)) =
      canonicalVarianceCompensator T (canonicalVarianceCovariance σ f f) t p₂ ∧
    (∫ r, (∑ i : ι, physicalCouplingDensity σ (some i) none (canonicalPathEval T r p).1)
          ∂timeMeasureHorizon (min t T)) =
      canonicalVarianceCompensator T (canonicalVarianceCovariance σ f k) t p₂ ∧
    canonicalPhysicalCompensator T σ none none t p =
      canonicalVarianceCompensator T (canonicalVarianceCovariance σ k k) t p₂ := by
  intro p₂ f k
  have h (r : ℝ≥0) := physicalCouplingDensity_aggregate_eq_canonical σ (canonicalPathEval T r p).1
    (fun i => hN i (canonicalEvalTime T r))
  simp only [p₂, canonicalVarianceCompensator_aggregatePair_eq]
  exact ⟨integral_congr_ae (ae_of_all _ fun r => (h r).1),
    integral_congr_ae (ae_of_all _ fun r => (h r).2.1),
    integral_congr_ae (ae_of_all _ fun r => (h r).2.2)⟩

/-- The five martingale identities on the two-dimensional variance path,
with deterministic immigration shifts kept explicit. -/
theorem canonicalAggregatePairLaw_martingales
    {α v₀ κ θ σ : ℝ} (hα' : α < 1) (d e : ℝ≥0 → ℝ)
    (P : ProbabilityMeasure Ω)
    (hM : ∀ i : Option ι, Martingale (canonicalPhysicalResidual T i) F (P : Measure Ω))
    (hQ : ∀ i j : Option ι, Martingale (canonicalPhysicalCompensatedProduct T σ i j) F (P : Measure Ω))
    (hN : ∀ᵐ p ∂(P : Measure Ω), p ∈ canonicalPhysicalNonnegative (ι := ι) T)
    (hInv : ∀ᵐ p ∂(P : Measure Ω), ∀ t,
      canonicalVarianceMartingale T α v₀ κ θ canonicalFirstVariance t (canonicalAggregatePair p)+d t =
        canonicalPhysicalAggregateResidual T t p ∧
      canonicalVarianceMartingale T α v₀ κ θ canonicalSecondVariance t (canonicalAggregatePair p)+e t =
        canonicalPhysicalResidual T none t p) :
    let P₂ := (canonicalAggregatePairLaw P : Measure Ω₂)
    let f := canonicalFirstVariance
    let k := canonicalSecondVariance
    let M := fun t p => canonicalVarianceMartingale T α v₀ κ θ f t p + d t
    let N := fun t p => canonicalVarianceMartingale T α v₀ κ θ k t p + e t
    let A := canonicalVarianceCompensator T (canonicalVarianceCovariance σ f f)
    let C := canonicalVarianceCompensator T (canonicalVarianceCovariance σ f k)
    let D := canonicalVarianceCompensator T (canonicalVarianceCovariance σ k k)
    Martingale M G P₂ ∧ Martingale N G P₂ ∧
      Martingale (fun t p => M t p*M t p-A t p) G P₂ ∧
      Martingale (fun t p => M t p*N t p-C t p) G P₂ ∧
      Martingale (fun t p => N t p*N t p-D t p) G P₂ := by
  intro P₂ f k M N A C D
  have hMa : StronglyAdapted G M := fun t =>
    (stronglyAdapted_canonicalVarianceMartingale T hα' v₀ κ θ f t).add stronglyMeasurable_const
  have hNa : StronglyAdapted G N := fun t =>
    (stronglyAdapted_canonicalVarianceMartingale T hα' v₀ κ θ k t).add stronglyMeasurable_const
  have hAa : StronglyAdapted G A := stronglyAdapted_canonicalVarianceCompensator T _
  have hCa : StronglyAdapted G C := stronglyAdapted_canonicalVarianceCompensator T _
  have hDa : StronglyAdapted G D := stronglyAdapted_canonicalVarianceCompensator T _
  refine ⟨martingale_canonicalAggregatePairLaw_of_ae_pullback P
    (canonicalPhysicalAggregateResidual_martingale hM) hMa (fun t => hInv.mono fun p hp => (hp t).1.symm),
    martingale_canonicalAggregatePairLaw_of_ae_pullback P (hM none) hNa
      (fun t => hInv.mono fun p hp => (hp t).2.symm), ?_, ?_, ?_⟩
  · refine martingale_canonicalAggregatePairLaw_of_ae_pullback P
      (canonicalPhysicalAggregate_square_martingale σ hQ)
        (fun t => ((hMa t).mul (hMa t)).sub (hAa t)) ?_
    intro t
    filter_upwards [hInv,hN] with p hp hn
    change _ = M t (canonicalAggregatePair p)*M t (canonicalAggregatePair p)-A t (canonicalAggregatePair p)
    rw [show M t (canonicalAggregatePair p) = canonicalPhysicalAggregateResidual T t p from (hp t).1]
    exact congrArg (fun x => canonicalPhysicalAggregateResidual T t p * canonicalPhysicalAggregateResidual T t p-x)
      (canonicalAggregatePair_compensators_eq σ p hn t).1
  · refine martingale_canonicalAggregatePairLaw_of_ae_pullback P
      (canonicalPhysicalAggregate_companion_martingale σ hQ)
        (fun t => ((hMa t).mul (hNa t)).sub (hCa t)) ?_
    intro t
    filter_upwards [hInv,hN] with p hp hn
    change _ = M t (canonicalAggregatePair p)*N t (canonicalAggregatePair p)-C t (canonicalAggregatePair p)
    rw [show M t (canonicalAggregatePair p) = canonicalPhysicalAggregateResidual T t p from (hp t).1,
      show N t (canonicalAggregatePair p) = canonicalPhysicalResidual T none t p from (hp t).2]
    exact congrArg (fun x => canonicalPhysicalAggregateResidual T t p * canonicalPhysicalResidual T none t p-x)
      (canonicalAggregatePair_compensators_eq σ p hn t).2.1
  · refine martingale_canonicalAggregatePairLaw_of_ae_pullback P (hQ none none)
        (fun t => ((hNa t).mul (hNa t)).sub (hDa t)) ?_
    intro t
    filter_upwards [hInv,hN] with p hp hn
    change _ = N t (canonicalAggregatePair p)*N t (canonicalAggregatePair p)-D t (canonicalAggregatePair p)
    rw [show N t (canonicalAggregatePair p) = canonicalPhysicalResidual T none t p from (hp t).2]
    exact congrArg (fun x => canonicalPhysicalResidual T none t p * canonicalPhysicalResidual T none t p-x)
      (canonicalAggregatePair_compensators_eq σ p hn t).2.2

#print axioms RoughHeston.canonicalAggregatePairLaw_martingales

end RoughHeston
