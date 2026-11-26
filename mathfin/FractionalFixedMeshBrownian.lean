import FractionalFixedMeshLaw
import CanonicalFocalCovarianceData
import IndependentPulsedFocalDriver
import IndependentCommonDriver

/-! The aggregate and its companion have one actual Brownian driver
on a product extension of the complete focal path law. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

open MathFin.ItoLocalMartingale (nullAugmentation)

set_option maxHeartbeats 1600000

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
  {α κ σ : ℝ} {v : Option ι → ℝ} {β : Option ι → ℝ≥0 → ℝ}
local notation "S" => CoupledPhysicalState ι
local notation "Ω" => CanonicalPath T S
local notation "G" => canonicalPathNaturalFiltration (E := S) T
local notation "Ω'" => Ω × (ℝ≥0 → ℝ)

namespace FractionalFixedMeshLaw

variable (L : FractionalFixedMeshLaw T α κ σ v β)

/-- Return the Brownian together with both amplitude integrals, while
keeping the entire coupled cluster system in the first coordinate. -/
theorem aggregateBrownian_and_focal_choices (hσ : 0 ≤ σ) :
    let P := (L.law : Measure Ω).prod gaussianLimit
    let F := nullAugmentation (prodFiltration G canonicalAuxiliaryFiltration) P
    let lift (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (z : Ω') := X t z.1
    let X := fun t p => canonicalFirstVariance (canonicalPathEval T t (canonicalAggregatePair p))
    let Y := fun t p => canonicalSecondVariance (canonicalPathEval T t (canonicalAggregatePair p))
    (∃ B : ℝ≥0 → Ω' → ℝ, IsBrownianOn P F T B ∧
      Martingale B F P ∧ (∀ t, MemLp (B t) 2 P) ∧
      Martingale (fun t ω => B t ω^2-((min t T:ℝ≥0):ℝ)) F P ∧
      HasAmplitudeCutoffIntegral F P T B (lift (canonicalPhysicalAggregateResidual T))
        (lift fun t p => σ*Real.sqrt (X t p)) ∧
      HasAmplitudeCutoffIntegral F P T B (lift (canonicalPhysicalResidual T none))
        (lift fun t p => σ*Real.sqrt (Y t p))) ∧ (0<σ → ∀ i : ι, ∃ B Cf : ℝ≥0 → Ω' → ℝ, MathFinBridge.BrownianOn P F T B ∧
      Martingale B F P ∧ (∀ t, MemLp (B t) 2 P) ∧
      Martingale (fun t ω => B t ω^2-((min t T:ℝ≥0):ℝ)) F P ∧
      HasAmplitudeCutoffIntegral F P T B (lift (canonicalPhysicalAggregateResidual T))
        (lift fun t p => σ*Real.sqrt (X t p)) ∧
      HasAmplitudeCutoffIntegral F P T B (lift (canonicalPhysicalResidual T none))
        (lift fun t p => σ*Real.sqrt (Y t p)) ∧
      Martingale (fun t => B t * lift (canonicalPhysicalResidual T (some i)) (min t T) - Cf t) F P ∧
      (∀ t≤T, Cf t =ᵐ[P] fun z => ∫ s in (0:ℝ)..(t:ℝ),
        GirsanovPort.focalBracketDensity σ (lift (canonicalPhysicalVariance T (some i))) (lift X) s.toNNReal z)) := by
  intro P F lift X Y
  let Q := (L.law : Measure Ω)
  let M := canonicalPhysicalAggregateResidual (ι := ι) T
  let N := canonicalPhysicalResidual (ι := ι) T none
  let a := fun t p => σ*Real.sqrt (X t p)
  let b := fun t p => σ*Real.sqrt (Y t p)
  let Cp (g : C(ℝ × ℝ, ℝ)) := fun (t : ℝ≥0) (p : Ω) => canonicalVarianceCompensator T g t (canonicalAggregatePair p)
  let Cmm := Cp (canonicalVarianceCovariance σ canonicalFirstVariance canonicalFirstVariance)
  let Cmn := Cp (canonicalVarianceCovariance σ canonicalFirstVariance canonicalSecondVariance)
  let Cnn := Cp (canonicalVarianceCovariance σ canonicalSecondVariance canonicalSecondVariance)
  have hC (g : C(ℝ × ℝ, ℝ)) : StronglyAdapted G (Cp g) := fun t =>
    (stronglyAdapted_canonicalVarianceCompensator T g t).comp_measurable
      (filtration_measurable_canonicalAggregatePair t)
  have hM := canonicalPhysicalAggregateResidual_martingale L.residualMartingale
  have hN := L.residualMartingale none
  have hM₀ : M 0 =ᵐ[Q] 0 := by
    filter_upwards [L.starts] with p hp
    change canonicalPathEval T 0 p = (v,0) at hp
    simp [M, canonicalPhysicalAggregateResidual, canonicalPhysicalResidual, hp]
  have hN₀ : N 0 =ᵐ[Q] 0 := by
    filter_upwards [L.starts] with p hp
    change canonicalPathEval T 0 p = (v,0) at hp
    simp [N, canonicalPhysicalResidual, hp]
  have hTime (p : Ω) : Continuous (fun t => canonicalPathEval T t p) :=
    p.continuous.comp ((continuous_id.min continuous_const).subtype_mk _)
  have hR (i : Option ι) (p : Ω) : Continuous (fun t => canonicalPhysicalResidual T i t p) :=
    ((continuous_apply i).comp continuous_snd).comp (hTime p)
  have hMc : ∀ᵐ p ∂Q, ContinuousOn (fun t => M t p) (Iic T) :=
    ae_of_all _ fun p => (continuous_finsetSum Finset.univ (fun i _ => hR (some i) p)).continuousOn
  have hNc : ∀ᵐ p ∂Q, ContinuousOn (fun t => N t p) (Iic T) :=
    ae_of_all _ fun p => (hR none p).continuousOn
  have hXYa (f : C(ℝ × ℝ, ℝ)) : StronglyAdapted G
      (fun t p => σ*Real.sqrt (f (canonicalPathEval T t (canonicalAggregatePair p)))) := by
    intro t
    exact (((stronglyAdapted_canonicalVarianceCoordinate T f t).comp_measurable
      (filtration_measurable_canonicalAggregatePair t)).measurable.sqrt.const_mul σ).stronglyMeasurable
  have hTimePair (p : CanonicalPath T (ℝ × ℝ)) : Continuous (fun t => canonicalPathEval T t p) :=
    p.continuous.comp ((continuous_id.min continuous_const).subtype_mk _)
  have hac : ∀ᵐ p ∂Q, ContinuousOn (fun t => a t p) (Icc 0 T) := ae_of_all _ fun p =>
    (continuous_const.mul (Real.continuous_sqrt.comp (canonicalFirstVariance.continuous.comp
      (hTimePair (canonicalAggregatePair p))))).continuousOn
  have hbc : ∀ᵐ p ∂Q, ContinuousOn (fun t => b t p) (Icc 0 T) := ae_of_all _ fun p =>
    (continuous_const.mul (Real.continuous_sqrt.comp (canonicalSecondVariance.continuous.comp
      (hTimePair (canonicalAggregatePair p))))).continuousOn
  have hMM : Martingale (fun t p => M t p*M t p-Cmm t p) G Q := by
    refine (canonicalPhysicalAggregate_square_martingale σ L.productMartingale).congr
      (fun t => ((hM.stronglyAdapted t).mul (hM.stronglyAdapted t)).sub (hC _ t)) ?_
    intro t
    exact L.nonnegative.mono fun p hp => congrArg (fun x => M t p*M t p-x)
      (canonicalAggregatePair_compensators_eq σ p hp t).1
  have hMN : Martingale (fun t p => M t p*N t p-Cmn t p) G Q := by
    refine (canonicalPhysicalAggregate_companion_martingale σ L.productMartingale).congr
      (fun t => ((hM.stronglyAdapted t).mul (hN.stronglyAdapted t)).sub (hC _ t)) ?_
    intro t
    exact L.nonnegative.mono fun p hp => congrArg (fun x => M t p*N t p-x)
      (canonicalAggregatePair_compensators_eq σ p hp t).2.1
  have hNN : Martingale (fun t p => N t p*N t p-Cnn t p) G Q := by
    refine (L.productMartingale none none).congr
      (fun t => ((hN.stronglyAdapted t).mul (hN.stronglyAdapted t)).sub (hC _ t)) ?_
    intro t
    exact L.nonnegative.mono fun p hp => congrArg (fun x => N t p*N t p-x)
      (canonicalAggregatePair_compensators_eq σ p hp t).2.2
  have hComp (f g : C(ℝ × ℝ, ℝ)) (p : Ω) (t : ℝ≥0) (ht : t ≤ T) :
      Cp (canonicalVarianceCovariance σ f g) t p = ∫ s in (0:ℝ)..(t:ℝ),
        (σ*Real.sqrt (f (canonicalPathEval T s.toNNReal (canonicalAggregatePair p))))*
          (σ*Real.sqrt (g (canonicalPathEval T s.toNNReal (canonicalAggregatePair p)))) := by
    unfold Cp canonicalVarianceCompensator
    rw [min_eq_left ht, intervalIntegral.integral_of_le t.coe_nonneg]
    rfl
  have hClockM : ∀ᵐ p ∂Q, ∀ t ≤ T, Cmm t p = ∫ s in (0:ℝ)..(t:ℝ), a s.toNNReal p^2 := by
    exact ae_of_all _ fun p t ht => by
      simpa only [Cmm, a, X, pow_two] using hComp canonicalFirstVariance canonicalFirstVariance p t ht
  have hClockCross : ∀ᵐ p ∂Q, ∀ t ≤ T, Cmn t p = ∫ s in (0:ℝ)..(t:ℝ), a s.toNNReal p*b s.toNNReal p :=
    ae_of_all _ fun p t ht => hComp canonicalFirstVariance canonicalSecondVariance p t ht
  have hClockN : ∀ᵐ p ∂Q, ∀ t ≤ T, Cnn t p = ∫ s in (0:ℝ)..(t:ℝ), b s.toNNReal p^2 := by
    exact ae_of_all _ fun p t ht => by
      simpa only [Cnn, b, Y, pow_two] using hComp canonicalSecondVariance canonicalSecondVariance p t ht
  have ha₀ (t : ℝ≥0) (p : Ω) : 0 ≤ a t p := mul_nonneg hσ (Real.sqrt_nonneg _)
  have hb₀ (t : ℝ≥0) (p : Ω) : 0 ≤ b t p := mul_nonneg hσ (Real.sqrt_nonneg _)
  have hAdaptedA : StronglyAdapted G a := hXYa canonicalFirstVariance
  have hAdaptedB : StronglyAdapted G b := hXYa canonicalSecondVariance
  have hM₂ (t : ℝ≥0) : MemLp (M t) 2 Q := L.aggregateResidual_memLp t
  have hN₂ (t : ℝ≥0) : MemLp (N t) 2 Q := L.residual_memLp t
  have hBrownian := rank_one_pair_has_common_brownian_on_product_with_compensator
    (μ := Q) (𝒢 := G) (M := M) (N := N) (Cmm := Cmm) (Cmn := Cmn) (Cnn := Cnn)
    (a := a) (b := b) T hM hN hM₂ hN₂ hMc hNc hM₀ hN₀ hMM hMN hNN
    hAdaptedA hAdaptedB hac hbc ha₀ hb₀ hClockM hClockCross hClockN
  refine ⟨hBrownian,?_⟩
  intro hσpos i
  let U := canonicalPhysicalVariance T (some i)
  let J := canonicalPhysicalResidual T (some i)
  let Cx := canonicalPhysicalCompensator T σ (some i) (some i)
  let Cy := canonicalPhysicalCompensator T σ none (some i)
  have hXc (p : Ω) : Continuous (fun t => X t p) :=
    canonicalFirstVariance.continuous.comp (hTimePair (canonicalAggregatePair p))
  have hYc (p : Ω) : Continuous (fun t => Y t p) :=
    canonicalSecondVariance.continuous.comp (hTimePair (canonicalAggregatePair p))
  have hXa : StronglyAdapted G X := fun t =>
    (stronglyAdapted_canonicalVarianceCoordinate T canonicalFirstVariance t).comp_measurable
      (filtration_measurable_canonicalAggregatePair t)
  have hXp : IsStronglyPredictable G X := hXa.isStronglyPredictable_of_leftContinuous
    (fun p t => (hXc p).continuousAt.continuousWithinAt)
  have hUp : IsStronglyPredictable G U := (canonicalPhysicalVariance_adapted (some i)).isStronglyPredictable_of_leftContinuous
    (fun p t => (canonicalPhysicalVariance_time_continuous (some i) p).continuousAt.continuousWithinAt)
  have hXeq (p : Ω) (hp : p ∈ canonicalPhysicalNonnegative T) (t : ℝ≥0) :
      X t p=canonicalPhysicalAggregate T t p := by
    change max 0 (canonicalPhysicalAggregate T t p)=_
    exact max_eq_right (Finset.sum_nonneg (fun j _ => hp (some j) (canonicalEvalTime T t)))
  have hYeq (p : Ω) (hp : p ∈ canonicalPhysicalNonnegative T) (t : ℝ≥0) :
      Y t p=canonicalPhysicalVariance T none t p := max_eq_right (hp none (canonicalEvalTime T t))
  have hCx : ∀ᵐ p ∂Q, ∀ t≤T, Cx t p=∫ s in (0:ℝ)..(t:ℝ),σ^2*U s.toNNReal p := by
    filter_upwards [L.nonnegative] with p hp t ht
    change canonicalPhysicalCompensator T σ (some i) (some i) t p=_
    rw [canonicalPhysical_diagonal_clock,min_eq_left ht]
    have hpos (r : ℝ≥0) : 0≤canonicalPhysicalVariance T (some i) r p := hp (some i) (canonicalEvalTime T r)
    simp only [U,max_eq_left (hpos _)]
  have hCy : ∀ᵐ p ∂Q, ∀ t≤T, Cy t p=∫ s in (0:ℝ)..(t:ℝ),
      σ^2*U s.toNNReal p*Real.sqrt (Y s.toNNReal p)/Real.sqrt (X s.toNNReal p) := by
    filter_upwards [L.nonnegative] with p hp t ht
    simp_rw [hXeq p hp,hYeq p hp]
    exact canonicalPhysical_companion_focal_clock σ i hp t ht
  have hParts : ∀ᵐ p ∂Q, ∀ t≤T, 0≤U t p ∧ U t p≤X t p := by
    filter_upwards [L.nonnegative] with p hp t ht
    rw [hXeq p hp]
    exact ⟨hp (some i) (canonicalEvalTime T t),Finset.single_le_sum
      (f := fun j => canonicalPhysicalVariance T (some j) t p)
      (fun j _ => hp (some j) (canonicalEvalTime T t)) (Finset.mem_univ i)⟩
  exact pulsed_pair_has_common_brownian_on_product_with_focal T hM hN hM₂ hN₂ hMc hNc hM₀ hN₀
    hMM hMN hNN hAdaptedA hAdaptedB hac hbc ha₀ hb₀ hClockM hClockCross hClockN hσpos
    (show a=GirsanovPort.varianceAmplitude σ X from rfl) (show b=GirsanovPort.varianceAmplitude σ Y from rfl)
    (L.residualMartingale (some i)) (fun t => L.residual_memLp t)
    (ae_of_all Q fun p => (canonicalPhysicalResidual_time_continuous (some i) p).continuousOn)
    (canonicalPhysicalResidual_zero_ae L.starts (some i)) (canonicalPhysicalAggregate_focal_martingale σ i L.productMartingale)
    (L.productMartingale none (some i)) hCx hCy (hXp.mono ((G).predictable_le_prod)).measurable
    (hUp.mono ((G).predictable_le_prod)).measurable (ae_of_all Q fun p => (hXc p).continuousOn)
    (ae_of_all Q fun p => (hYc p).continuousOn)
    (ae_of_all Q fun p => (canonicalPhysicalVariance_time_continuous (some i) p).continuousOn) hParts

theorem exists_aggregate_commonBrownian (hσ : 0 ≤ σ) :
    let P := (L.law : Measure Ω).prod gaussianLimit
    let F := nullAugmentation (prodFiltration G canonicalAuxiliaryFiltration) P
    let lift (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (z : Ω') := X t z.1
    let X := fun t p => canonicalFirstVariance (canonicalPathEval T t (canonicalAggregatePair p))
    let Y := fun t p => canonicalSecondVariance (canonicalPathEval T t (canonicalAggregatePair p))
    ∃ B : ℝ≥0 → Ω' → ℝ, IsBrownianOn P F T B ∧
      Martingale B F P ∧ (∀ t, MemLp (B t) 2 P) ∧
      Martingale (fun t ω => B t ω^2-((min t T:ℝ≥0):ℝ)) F P ∧
      HasAmplitudeCutoffIntegral F P T B (lift (canonicalPhysicalAggregateResidual T))
        (lift fun t p => σ*Real.sqrt (X t p)) ∧
      HasAmplitudeCutoffIntegral F P T B (lift (canonicalPhysicalResidual T none))
        (lift fun t p => σ*Real.sqrt (Y t p)) := (L.aggregateBrownian_and_focal_choices hσ).1

theorem exists_aggregate_commonBrownian_with_focal (hσ : 0 < σ) :
    let P := (L.law : Measure Ω).prod gaussianLimit
    let F := nullAugmentation (prodFiltration G canonicalAuxiliaryFiltration) P
    let lift (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (z : Ω') := X t z.1
    let X := fun t p => canonicalFirstVariance (canonicalPathEval T t (canonicalAggregatePair p))
    let Y := fun t p => canonicalSecondVariance (canonicalPathEval T t (canonicalAggregatePair p))
    ∀ i : ι, ∃ B Cf : ℝ≥0 → Ω' → ℝ, MathFinBridge.BrownianOn P F T B ∧
      Martingale B F P ∧ (∀ t, MemLp (B t) 2 P) ∧
      Martingale (fun t ω => B t ω^2-((min t T:ℝ≥0):ℝ)) F P ∧
      HasAmplitudeCutoffIntegral F P T B (lift (canonicalPhysicalAggregateResidual T))
        (lift fun t p => σ*Real.sqrt (X t p)) ∧
      HasAmplitudeCutoffIntegral F P T B (lift (canonicalPhysicalResidual T none))
        (lift fun t p => σ*Real.sqrt (Y t p)) ∧
      Martingale (fun t => B t * lift (canonicalPhysicalResidual T (some i)) (min t T) - Cf t) F P ∧
      (∀ t≤T, Cf t =ᵐ[P] fun z => ∫ s in (0:ℝ)..(t:ℝ),
        GirsanovPort.focalBracketDensity σ (lift (canonicalPhysicalVariance T (some i))) (lift X) s.toNNReal z) :=
  (L.aggregateBrownian_and_focal_choices hσ.le).2 hσ

end FractionalFixedMeshLaw

#print axioms RoughHeston.FractionalFixedMeshLaw.exists_aggregate_commonBrownian
#print axioms RoughHeston.FractionalFixedMeshLaw.exists_aggregate_commonBrownian_with_focal

end RoughHeston
