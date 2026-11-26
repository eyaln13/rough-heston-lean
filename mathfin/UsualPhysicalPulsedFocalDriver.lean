import FractionalFixedMeshBrownian
import PulsedCommonBrownianFocal
import CanonicalFocalCovarianceData
import CanonicalUsualModels

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

open MathFin.ItoLocalMartingale (nullAugmentation)

set_option maxHeartbeats 1800000

section Product

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {G : Filtration ℝ≥0 m}

local notation "Paths" => (ℝ≥0 → ℝ)
local notation "P" => (μ.prod gaussianLimit)
local notation "Q" => (physicalCompletedMeasure P)
local notation "𝓕c" => (physicalUsualFiltration P (nullAugmentation (prodFiltration G canonicalAuxiliaryFiltration) P))

/-- Lift an all-time continuous martingale on the physical coordinates to the
completed product with the usual augmentation. -/
theorem martingale_usual_physical_product_fst [IsProbabilityMeasure μ]
    {M : ℝ≥0 → Ω → ℝ} (hm : Martingale M G μ)
    (hc : ∀ᵐ p ∂μ, Continuous (fun t => M t p)) :
    Martingale (fun t (z : Ω × Paths) => M t z.1) 𝓕c Q :=
  martingale_physical_usual (martingale_physical_nullAugmentation
    (martingale_prod_fst (G := canonicalAuxiliaryFiltration) (ν := gaussianLimit) hm))
    ((measurePreserving_fst (μ := μ) (ν := gaussianLimit)).quasiMeasurePreserving.ae hc)

/-- The independent coordinate is a continuous, square-integrable auxiliary
martingale on the usual completed physical product. -/
theorem usual_physical_product_auxiliary_driver [IsProbabilityMeasure μ] (𝒜 : Filtration ℝ≥0 m)
    (H : ℝ≥0) :
    let F := physicalUsualFiltration P (nullAugmentation (prodFiltration 𝒜 canonicalAuxiliaryFiltration) P)
    let W (t : ℝ≥0) (z : Ω × Paths) := brownian (min t H) z.2
    Martingale W F Q ∧ (∀ t, MemLp (W t) 2 Q) ∧ (W 0 =ᵐ[Q] 0) ∧
    (∀ z, Continuous (fun t => W t z)) ∧
    Martingale (fun t z => W t z * W t z - ((min t H : ℝ≥0) : ℝ)) F Q := by
  intro F W
  obtain ⟨hm, h₂, h₀, hc, hs⟩ := canonical_auxiliary_driver H
  have hWc (z : Ω × Paths) : Continuous (fun t => W t z) := hc z.2
  refine ⟨martingale_physical_usual (martingale_physical_nullAugmentation
      (martingale_prod_snd (F := 𝒜) (μ := μ) hm))
    (ae_of_all _ hWc), fun t => physical_completion_memLp ((h₂ t).comp_snd μ), ?_, hWc, ?_⟩
  · change W 0 =ᵐ[P] 0
    exact (measurePreserving_snd (μ := μ) (ν := gaussianLimit)).quasiMeasurePreserving.ae h₀
  · apply martingale_physical_usual
    · apply martingale_physical_nullAugmentation
      simpa only [pow_two] using (martingale_prod_snd (F := 𝒜) (μ := μ) hs)
    · exact ae_of_all _ fun z => ((hWc z).mul (hWc z)).sub
        (NNReal.continuous_coe.comp (continuous_id.min continuous_const))

/-- Independence from the original coordinates survives completion and
right-continuous augmentation of the joint filtration. -/
theorem usual_physical_product_auxiliary_orthogonal [IsProbabilityMeasure μ]
    (H : ℝ≥0) {J : ℝ≥0 → Ω → ℝ} (hJ : Martingale J G μ)
    (hc : ∀ᵐ p ∂μ, Continuous (fun t => J t p)) :
    Martingale (fun t (z : Ω × Paths) => brownian (min t H) z.2 * J t z.1) 𝓕c Q := by
  obtain ⟨hW, _, _, hWc, _⟩ := canonical_auxiliary_driver H
  have hLift : ∀ᵐ z : Ω × Paths ∂P, Continuous (fun t => J t z.1) :=
    (measurePreserving_fst (μ := μ) (ν := gaussianLimit)).quasiMeasurePreserving.ae hc
  apply martingale_physical_usual
  · apply martingale_physical_nullAugmentation
    simpa only [mul_comm] using (martingale_prod_mul hJ hW)
  · exact hLift.mono fun z hz => (hWc z.2).mul hz

end Product

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
  {α κ σ : ℝ} {v : Option ι → ℝ} {β : Option ι → ℝ≥0 → ℝ}
local notation "S" => CoupledPhysicalState ι
local notation "Ω" => CanonicalPath T S
local notation "G" => canonicalPathNaturalFiltration (E := S) T
local notation "Ω'" => Ω × (ℝ≥0 → ℝ)

namespace FractionalFixedMeshLaw

variable (L : FractionalFixedMeshLaw T α κ σ v β)

/-- Realize both aggregate residuals with one Brownian driver on the usual
completed physical product up to any smaller horizon. The focal mixed
compensator on this same space retains the original focal density. -/
theorem exists_usual_aggregate_commonBrownian_with_focal (hσ : 0 < σ)
    (H : ℝ≥0) (hHT : H ≤ T) (i : ι) :
    let P := (L.law : Measure Ω).prod gaussianLimit
    let Q := physicalCompletedMeasure P
    let F := physicalUsualFiltration P (nullAugmentation (prodFiltration G canonicalAuxiliaryFiltration) P)
    let lift (f : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (z : Ω') := f t z.1
    let X := fun t p => canonicalFirstVariance (canonicalPathEval T t (canonicalAggregatePair p))
    let Y := fun t p => canonicalSecondVariance (canonicalPathEval T t (canonicalAggregatePair p))
    ∃ B Cf : ℝ≥0 → Ω' → ℝ, MathFinBridge.BrownianOn Q F H B ∧
      Martingale B F Q ∧ (∀ t, MemLp (B t) 2 Q) ∧
      Martingale (fun t z => B t z^2-((min t H:ℝ≥0):ℝ)) F Q ∧
      HasAmplitudeCutoffIntegral F Q H B (lift (canonicalPhysicalAggregateResidual T))
        (lift fun t p => σ*Real.sqrt (X t p)) ∧
      HasAmplitudeCutoffIntegral F Q H B (lift (canonicalPhysicalResidual T none))
        (lift fun t p => σ*Real.sqrt (Y t p)) ∧
      Martingale (fun t => B t * lift (canonicalPhysicalResidual T (some i)) (min t H) - Cf t) F Q ∧
      (∀ t≤H, Cf t =ᵐ[Q] fun z => ∫ s in (0:ℝ)..(t:ℝ),
        GirsanovPort.focalBracketDensity σ (lift (canonicalPhysicalVariance T (some i))) (lift X) s.toNNReal z) := by
  intro P Q F lift X Y
  let μ := (L.law : Measure Ω)
  let W (t : ℝ≥0) (z : Ω') := brownian (min t H) z.2
  have liftM {f : ℝ≥0 → Ω → ℝ} (hf : Martingale f G μ) (hc : ∀ p, Continuous (fun t => f t p)) :
      Martingale (lift f) F Q :=
    martingale_usual_physical_product_fst hf (ae_of_all _ hc)
  have liftA {f : ℝ≥0 → Ω → ℝ} (hf : StronglyAdapted G f) :
      StronglyAdapted F (lift f) :=
    StronglyAdapted.physicalUsual (P := P) (F := nullAugmentation (prodFiltration G canonicalAuxiliaryFiltration) P)
      (fun t => ((hf t).comp_measurable (@measurable_fst Ω (ℝ≥0 → ℝ) (G t)
        (canonicalAuxiliaryFiltration t))).mono le_sup_left)
  have liftP {p : Ω → Prop} (hp : ∀ᵐ x ∂μ, p x) : ∀ᵐ z ∂Q, p z.1 := by
    change ∀ᵐ z ∂P, p z.1
    exact (measurePreserving_fst (μ := μ) (ν := gaussianLimit)).quasiMeasurePreserving.ae hp
  have lift₂ {f : Ω → ℝ} (hf : MemLp f 2 μ) : MemLp (fun z : Ω' => f z.1) 2 Q :=
    physical_completion_memLp (hf.comp_fst gaussianLimit)
  have liftJoint {f : ℝ≥0 → Ω → ℝ} (hf : Measurable (Function.uncurry f)) :
      @Measurable (ℝ≥0 × Ω') ℝ
        (@Prod.instMeasurableSpace ℝ≥0 Ω' _ (physicalCompletedSpace P)) _
        (Function.uncurry (lift f)) := by
    have hfst : @Measurable Ω' Ω (physicalCompletedSpace P) _ Prod.fst :=
      measurable_fst.mono (physical_ambient_le_completion P) le_rfl
    exact hf.comp (measurable_fst.prodMk (hfst.comp measurable_snd))
  have orthogonal {f : ℝ≥0 → Ω → ℝ} (hf : Martingale f G μ)
      (hc : ∀ p, Continuous (fun t => f t p)) :
      Martingale (fun t => W t * lift f t) F Q :=
    usual_physical_product_auxiliary_orthogonal H hf (ae_of_all _ hc)
  obtain ⟨hw, hw₂, _, hwc, hws⟩ := usual_physical_product_auxiliary_driver (μ := μ) G H
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
  have hM₀ : M 0 =ᵐ[μ] 0 := by
    filter_upwards [L.starts] with p hp
    change canonicalPathEval T 0 p = (v,0) at hp
    simp [M, canonicalPhysicalAggregateResidual, canonicalPhysicalResidual, hp]
  have hN₀ : N 0 =ᵐ[μ] 0 := by
    filter_upwards [L.starts] with p hp
    change canonicalPathEval T 0 p = (v,0) at hp
    simp [N, canonicalPhysicalResidual, hp]
  have hTime (p : Ω) : Continuous (fun t => canonicalPathEval T t p) :=
    p.continuous.comp ((continuous_id.min continuous_const).subtype_mk _)
  have hR (i : Option ι) (p : Ω) : Continuous (fun t => canonicalPhysicalResidual T i t p) :=
    ((continuous_apply i).comp continuous_snd).comp (hTime p)
  have hMc (p : Ω) : Continuous (fun t => M t p) :=
    continuous_finsetSum Finset.univ (fun i _ => hR (some i) p)
  have hNc (p : Ω) : Continuous (fun t => N t p) := hR none p
  have hXYa (f : C(ℝ × ℝ, ℝ)) : StronglyAdapted G
      (fun t p => σ*Real.sqrt (f (canonicalPathEval T t (canonicalAggregatePair p)))) := by
    intro t
    exact (((stronglyAdapted_canonicalVarianceCoordinate T f t).comp_measurable
      (filtration_measurable_canonicalAggregatePair t)).measurable.sqrt.const_mul σ).stronglyMeasurable
  have hTimePair (p : CanonicalPath T (ℝ × ℝ)) : Continuous (fun t => canonicalPathEval T t p) :=
    p.continuous.comp ((continuous_id.min continuous_const).subtype_mk _)
  have hac : ∀ᵐ p ∂μ, ContinuousOn (fun t => a t p) (Icc 0 H) := ae_of_all _ fun p =>
    (continuous_const.mul (Real.continuous_sqrt.comp (canonicalFirstVariance.continuous.comp
      (hTimePair (canonicalAggregatePair p))))).continuousOn
  have hbc : ∀ᵐ p ∂μ, ContinuousOn (fun t => b t p) (Icc 0 H) := ae_of_all _ fun p =>
    (continuous_const.mul (Real.continuous_sqrt.comp (canonicalSecondVariance.continuous.comp
      (hTimePair (canonicalAggregatePair p))))).continuousOn
  have hMM : Martingale (fun t p => M t p*M t p-Cmm t p) G μ := by
    refine (canonicalPhysicalAggregate_square_martingale σ L.productMartingale).congr
      (fun t => ((hM.stronglyAdapted t).mul (hM.stronglyAdapted t)).sub (hC _ t)) ?_
    intro t
    exact L.nonnegative.mono fun p hp => congrArg (fun x => M t p*M t p-x)
      (canonicalAggregatePair_compensators_eq σ p hp t).1
  have hMN : Martingale (fun t p => M t p*N t p-Cmn t p) G μ := by
    refine (canonicalPhysicalAggregate_companion_martingale σ L.productMartingale).congr
      (fun t => ((hM.stronglyAdapted t).mul (hN.stronglyAdapted t)).sub (hC _ t)) ?_
    intro t
    exact L.nonnegative.mono fun p hp => congrArg (fun x => M t p*N t p-x)
      (canonicalAggregatePair_compensators_eq σ p hp t).2.1
  have hNN : Martingale (fun t p => N t p*N t p-Cnn t p) G μ := by
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
  have hClockM : ∀ᵐ p ∂μ, ∀ t ≤ H, Cmm t p = ∫ s in (0:ℝ)..(t:ℝ), a s.toNNReal p^2 := by
    exact ae_of_all _ fun p t ht => by
      simpa only [Cmm, a, X, pow_two] using hComp canonicalFirstVariance canonicalFirstVariance p t (ht.trans hHT)
  have hClockCross : ∀ᵐ p ∂μ, ∀ t ≤ H, Cmn t p = ∫ s in (0:ℝ)..(t:ℝ), a s.toNNReal p*b s.toNNReal p :=
    ae_of_all _ fun p t ht => hComp canonicalFirstVariance canonicalSecondVariance p t (ht.trans hHT)
  have hClockN : ∀ᵐ p ∂μ, ∀ t ≤ H, Cnn t p = ∫ s in (0:ℝ)..(t:ℝ), b s.toNNReal p^2 := by
    exact ae_of_all _ fun p t ht => by
      simpa only [Cnn, b, Y, pow_two] using hComp canonicalSecondVariance canonicalSecondVariance p t (ht.trans hHT)
  have ha₀ (t : ℝ≥0) (p : Ω) : 0 ≤ a t p := mul_nonneg hσ.le (Real.sqrt_nonneg _)
  have hb₀ (t : ℝ≥0) (p : Ω) : 0 ≤ b t p := mul_nonneg hσ.le (Real.sqrt_nonneg _)
  have hAdaptedA : StronglyAdapted G a := hXYa canonicalFirstVariance
  have hAdaptedB : StronglyAdapted G b := hXYa canonicalSecondVariance
  have hM₂ (t : ℝ≥0) : MemLp (M t) 2 μ := L.aggregateResidual_memLp t
  have hN₂ (t : ℝ≥0) : MemLp (N t) 2 μ := L.residual_memLp t
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
  have hCx : ∀ᵐ p ∂μ, ∀ t≤H, Cx t p=∫ s in (0:ℝ)..(t:ℝ),σ^2*U s.toNNReal p := by
    filter_upwards [L.nonnegative] with p hp t ht
    change canonicalPhysicalCompensator T σ (some i) (some i) t p=_
    rw [canonicalPhysical_diagonal_clock,min_eq_left (ht.trans hHT)]
    have hpos (r : ℝ≥0) : 0≤canonicalPhysicalVariance T (some i) r p := hp (some i) (canonicalEvalTime T r)
    simp only [U,max_eq_left (hpos _)]
  have hCy : ∀ᵐ p ∂μ, ∀ t≤H, Cy t p=∫ s in (0:ℝ)..(t:ℝ),
      σ^2*U s.toNNReal p*Real.sqrt (Y s.toNNReal p)/Real.sqrt (X s.toNNReal p) := by
    filter_upwards [L.nonnegative] with p hp t ht
    simp_rw [hXeq p hp,hYeq p hp]
    exact canonicalPhysical_companion_focal_clock σ i hp t (ht.trans hHT)
  have hParts : ∀ᵐ p ∂μ, ∀ t≤H, 0≤U t p ∧ U t p≤X t p := by
    filter_upwards [L.nonnegative] with p hp t ht
    rw [hXeq p hp]
    exact ⟨hp (some i) (canonicalEvalTime T t),Finset.single_le_sum
      (f := fun j => canonicalPhysicalVariance T (some j) t p)
      (fun j _ => hp (some j) (canonicalEvalTime T t)) (Finset.mem_univ i)⟩
  have hCp (g : C(ℝ × ℝ, ℝ)) (p : Ω) : Continuous (fun t => Cp g t p) := by
    let f (s : ℝ) := g ((canonicalAggregatePair p) (realTimeOnHorizon T s))
    have hfc : Continuous f :=
      g.continuous.comp ((canonicalAggregatePair p).continuous.comp (realTimeOnHorizon T).continuous)
    have hprim := intervalIntegral.continuous_primitive (μ := volume)
      (fun a b => hfc.intervalIntegrable a b) 0
    apply (hprim.comp (NNReal.continuous_coe.comp (continuous_id.min continuous_const))).congr
    intro t
    exact intervalIntegral.integral_of_le (NNReal.coe_nonneg (min t T))
  have hsquare {X C : ℝ≥0 → Ω → ℝ} (hX : ∀ t, MemLp (X t) 2 μ)
      (hC : Martingale (fun t => X t * X t - C t) G μ) : Integrable (C H) μ := by
    have hprod := ((hX H).mul (hX H) : MemLp (X H * X H) 1 μ).integrable le_rfl
    simpa only [sub_sub_cancel] using hprod.sub (hC.integrable H)
  have hae : Integrable (fun p => ∫ s in (0 : ℝ)..(H : ℝ), a s.toNNReal p ^ 2) μ :=
    (hsquare hM₂ hMM).congr (hClockM.mono fun p hp => hp H le_rfl)
  have hbe : Integrable (fun p => ∫ s in (0 : ℝ)..(H : ℝ), b s.toNNReal p ^ 2) μ :=
    (hsquare hN₂ hNN).congr (hClockN.mono fun p hp => hp H le_rfl)
  have ham := amplitude_mass_integrable_of_energy hAdaptedA hac hae
  have hbm := amplitude_mass_integrable_of_energy hAdaptedB hbc hbe
  have liftI {f : Ω → ℝ} (hf : Integrable f μ) : Integrable (fun z : Ω' => f z.1) Q :=
    physical_completion_integrable (hf.comp_fst gaussianLimit)
  have hMM' : Martingale (fun t => lift M t * lift M t - lift Cmm t) F Q :=
    liftM hMM fun p => ((hMc p).mul (hMc p)).sub (hCp _ p)
  have hMN' : Martingale (fun t => lift M t * lift N t - lift Cmn t) F Q :=
    liftM hMN fun p => ((hMc p).mul (hNc p)).sub (hCp _ p)
  have hNN' : Martingale (fun t => lift N t * lift N t - lift Cnn t) F Q :=
    liftM hNN fun p => ((hNc p).mul (hNc p)).sub (hCp _ p)
  have hJc (p : Ω) : Continuous (fun t => J t p) := canonicalPhysicalResidual_time_continuous (some i) p
  have hXJ : Martingale (fun t => lift M t * lift J t - lift Cx t) F Q :=
    liftM (canonicalPhysicalAggregate_focal_martingale σ i L.productMartingale)
      fun p => ((hMc p).mul (hJc p)).sub (canonicalPhysicalCompensator_time_continuous σ _ _ p)
  have hYJ : Martingale (fun t => lift N t * lift J t - lift Cy t) F Q :=
    liftM (L.productMartingale none (some i))
      fun p => ((hNc p).mul (hJc p)).sub (canonicalPhysicalCompensator_time_continuous σ _ _ p)
  have hNull (E : Set Ω') (_ : MeasurableSet[physicalCompletedSpace P] E) (hE : Q E=0) :
      MeasurableSet[F 0] E :=
    Filtration.IsComplete.measurableSet_of_null (𝓕 := F) hE 0
  exact GirsanovPort.pulsed_pair_has_common_brownian_with_focal
    (X := lift X) (Y := lift Y) (U := lift U) (J := lift J) (Cx := lift Cx) (Cy := lift Cy)
    H (liftM hM hMc) (liftM hN hNc) hw (fun t => lift₂ (hM₂ t)) (fun t => lift₂ (hN₂ t)) hw₂
    (ae_of_all _ fun z => (hMc z.1).continuousOn) (ae_of_all _ fun z => (hNc z.1).continuousOn)
    (ae_of_all _ hwc) (liftP hM₀) (liftP hN₀) hMM' hMN' hNN' (orthogonal hM hMc) (orthogonal hN hNc) hws
    (liftA hAdaptedA) (liftA hAdaptedB) (liftP hac) (liftP hbc) (fun t z => ha₀ t z.1) (fun t z => hb₀ t z.1)
    (liftP hClockM) (liftP hClockCross) (liftP hClockN) (liftI ham) (liftI hbm)
    hσ rfl rfl (liftM (L.residualMartingale (some i)) hJc) (fun t => lift₂ (L.residual_memLp (i := some i) t))
    (ae_of_all _ fun z => (hJc z.1).continuousOn) (liftP (canonicalPhysicalResidual_zero_ae L.starts (some i)))
    hXJ hYJ (orthogonal (L.residualMartingale (some i)) hJc) (liftP hCx) (liftP hCy)
    (liftJoint (hXp.mono ((G).predictable_le_prod)).measurable)
    (liftJoint (hUp.mono ((G).predictable_le_prod)).measurable)
    (ae_of_all _ fun z => (hXc z.1).continuousOn) (ae_of_all _ fun z => (hYc z.1).continuousOn)
    (ae_of_all _ fun z => (canonicalPhysicalVariance_time_continuous (some i) z.1).continuousOn) (liftP hParts) hNull

end FractionalFixedMeshLaw

#print axioms martingale_usual_physical_product_fst
#print axioms usual_physical_product_auxiliary_driver
#print axioms usual_physical_product_auxiliary_orthogonal
#print axioms FractionalFixedMeshLaw.exists_usual_aggregate_commonBrownian_with_focal

end RoughHeston
