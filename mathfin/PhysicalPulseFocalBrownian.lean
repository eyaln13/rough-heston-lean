import UsualPhysicalPulsedFocalDriver
import PhysicalPulseCoordinates

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

open MathFin.ItoLocalMartingale (nullAugmentation)

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {F : Filtration ℝ≥0 m} {S : ℝ≥0}

theorem HasAmplitudeCutoffIntegral.congr_amplitude
    {B M a b : ℝ≥0 → Ω → ℝ}
    (h : HasAmplitudeCutoffIntegral F μ S B M a)
    (he : ∀ᵐ ω ∂μ, ∀ t, a t ω = b t ω) :
    HasAmplitudeCutoffIntegral F μ S B M b := by
  obtain ⟨J, hJ, hJ₂, hgrid, hlimit⟩ := h
  refine ⟨J, hJ, hJ₂, fun n t ht => (hgrid n t ht).congr (fun j => ?_), hlimit⟩
  apply eLpNorm_congr_ae
  filter_upwards [he] with ω hω
  simp only [gridIntegralProcess, stochasticStep, Finset.sum_apply, Pi.mul_apply, Pi.sub_apply, hω]

section FixedMesh

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
  {α κ σ : ℝ} {v : Option ι → ℝ} {β : Option ι → ℝ≥0 → ℝ}
local notation "State" => CoupledPhysicalState ι
local notation "Path" => CanonicalPath T State
local notation "Past" => canonicalPathNaturalFiltration (E := State) T
local notation "ProductPath" => Path × (ℝ≥0 → ℝ)

namespace FractionalFixedMeshLaw

variable (L : FractionalFixedMeshLaw T α κ σ v β)

set_option maxHeartbeats 1200000 in
/-- The physical model has one Brownian driver, with the focal mixed clock
expressed using the continuous birth coordinates and the companion amplitude
expressed using its regular canonical version. -/
theorem exists_usual_birth_focal_brownian {i : ι} {τ H r : ℝ≥0} {ε d : ℝ}
    (hα : α < 1) (hκ : 0 ≤ κ) (hσ : 0 < σ)
    (horizon : τ + H ≤ T) (hr : r ≤ H) (hv : v (some i) = 0)
    (hβ : β (some i) = translatedPulseRate τ ε d) :
    let P := (L.law : Measure Path).prod gaussianLimit
    let Q := physicalCompletedMeasure P
    let F := physicalUsualFiltration P (nullAugmentation (prodFiltration Past canonicalAuxiliaryFiltration) P)
    let lift (f : ℝ≥0 → Path → ℝ) (t : ℝ≥0) (z : ProductPath) := f t z.1
    let S := τ + r
    let J := fun t : ℝ≥0 => lift (canonicalPhysicalResidual T (some i)) (min t S)
    let U := fun t : ℝ≥0 => lift (canonicalBirthFocalVariance T τ i) (min t (τ + H))
    let X := lift (canonicalBirthDominatingAggregate T τ i)
    let Y := lift (canonicalRegularVariance T none (v none))
    let q := GirsanovPort.focalBracketDensity σ U X
    ∃ B Cf : ℝ≥0 → ProductPath → ℝ, MathFinBridge.BrownianOn Q F S B ∧
      Martingale B F Q ∧ (∀ t, MemLp (B t) 2 Q) ∧
      Martingale (fun t z => B t z^2 - ((min t S : ℝ≥0) : ℝ)) F Q ∧
      HasAmplitudeCutoffIntegral F Q S B (lift (canonicalPhysicalAggregateResidual T))
        (GirsanovPort.varianceAmplitude σ X) ∧
      HasAmplitudeCutoffIntegral F Q S B (lift (canonicalPhysicalResidual T none))
        (GirsanovPort.varianceAmplitude σ Y) ∧
      Martingale J F Q ∧ (∀ t, MemLp (J t) 2 Q) ∧
      Martingale (fun t => B t * J t - Cf t) F Q ∧
      (∀ t ≤ S, Cf t =ᵐ[Q] fun z => ∫ s in (0 : ℝ)..(t : ℝ), q s.toNNReal z) ∧
      IsStronglyPredictable F U ∧ IsStronglyPredictable F X ∧ IsStronglyPredictable F q ∧
      (∀ᵐ z ∂Q, ∀ t ≤ S, IntervalIntegrable (fun s : ℝ => q s.toNNReal z) volume 0 (t : ℝ)) := by
  intro P Q F lift S J U X Y q
  have hs : S ≤ τ + H := add_le_add le_rfl hr
  have ht : S ≤ T := hs.trans horizon
  have hτ : τ ≤ T := (le_self_add).trans horizon
  obtain ⟨B, Cf, hB, hBm, hB₂, hBs, hAcut, hYcut, hMix, hCf⟩ :=
    L.exists_usual_aggregate_commonBrownian_with_focal hσ S ht i
  have hLift {p : Path → Prop} (hp : ∀ᵐ x ∂(L.law : Measure Path), p x) :
      ∀ᵐ z ∂Q, p z.1 := by
    change ∀ᵐ z ∂P, p z.1
    exact (measurePreserving_fst (μ := (L.law : Measure Path)) (ν := gaussianLimit)).quasiMeasurePreserving.ae hp
  have hUaLift {f : ℝ≥0 → Path → ℝ} (hf : StronglyAdapted Past f) :
      StronglyAdapted F (lift f) :=
    StronglyAdapted.physicalUsual (P := P)
      (F := nullAugmentation (prodFiltration Past canonicalAuxiliaryFiltration) P)
      (fun t => ((hf t).comp_measurable (@measurable_fst Path (ℝ≥0 → ℝ) (Past t)
        (canonicalAuxiliaryFiltration t))).mono le_sup_left)
  have hJs : Martingale J F Q := martingale_freeze_at
    (martingale_usual_physical_product_fst (L.residualMartingale (some i))
      (ae_of_all _ (canonicalPhysicalResidual_time_continuous (some i)))) S
  have hJ₂ (t : ℝ≥0) : MemLp (J t) 2 Q :=
    physical_completion_memLp ((L.residual_memLp (i := some i) (min t S)).comp_fst gaussianLimit)
  have hBirth := hLift (L.birthCoordinates_ae hα hκ hτ hv hβ)
  have hAamp : ∀ᵐ z ∂Q, ∀ t, σ * Real.sqrt
      (canonicalFirstVariance (canonicalPathEval T t (canonicalAggregatePair z.1))) =
      GirsanovPort.varianceAmplitude σ X t z := by
    filter_upwards [hBirth] with z hz t
    change _ = σ * Real.sqrt (canonicalBirthDominatingAggregate T τ i t z.1)
    rw [hz.2.1 t]
  have hYamp : ∀ᵐ z ∂Q, ∀ t, σ * Real.sqrt
      (canonicalSecondVariance (canonicalPathEval T t (canonicalAggregatePair z.1))) =
      GirsanovPort.varianceAmplitude σ Y t z := by
    filter_upwards [hLift (canonicalRegularVariance_ae_paths L.starts L.nonnegative none), hLift L.nonnegative]
      with z hz hn t
    change σ * Real.sqrt (max 0 (canonicalPhysicalVariance T none t z.1)) =
      σ * Real.sqrt (canonicalRegularVariance T none (v none) t z.1)
    have hp : 0 ≤ canonicalPhysicalVariance T none t z.1 := hn none (canonicalEvalTime T t)
    rw [hz t, max_eq_right hp]
  obtain ⟨hUad, hUc, hUn⟩ := canonicalBirthFocal_data (T := T) τ i
  obtain ⟨hXad, hXc, hUX⟩ := canonicalBirthDominatingAggregate_data (T := T) τ i
  have hUad' : StronglyAdapted F U := fun t => (hUaLift hUad (min t (τ + H))).mono
    (F.mono (min_le_left _ _))
  have hUp : IsStronglyPredictable F U := hUad'.isStronglyPredictable_of_leftContinuous
    (fun z t => ((hUc z.1).comp (continuous_id.min continuous_const)).continuousAt.continuousWithinAt)
  have hXp : IsStronglyPredictable F X := (hUaLift hXad).isStronglyPredictable_of_leftContinuous
    (fun z t => (hXc z.1).continuousAt.continuousWithinAt)
  have hq := GirsanovPort.focalBracketDensity_predictable (σ := σ) hUp hXp
  have hReal (a : ℝ≥0) (u : ℝ) (hu : u ∈ Icc 0 (a : ℝ)) : u.toNNReal ≤ a := by
    exact_mod_cast (Real.coe_toNNReal _ hu.1).le.trans hu.2
  refine ⟨B, Cf, hB, hBm, hB₂, hBs, hAcut.congr_amplitude hAamp, hYcut.congr_amplitude hYamp,
    hJs, hJ₂, hMix, ?_, hUp, hXp, hq, ?_⟩
  · intro t hts
    filter_upwards [hCf t hts, hBirth] with z hcz hz
    rw [hcz]
    apply intervalIntegral.integral_congr
    intro s hst
    rw [uIcc_of_le t.coe_nonneg] at hst
    have hdom := (hReal t s hst).trans (hts.trans hs)
    change σ * canonicalPhysicalVariance T (some i) s.toNNReal z.1 /
        Real.sqrt (canonicalFirstVariance (canonicalPathEval T s.toNNReal (canonicalAggregatePair z.1))) =
      σ * canonicalBirthFocalVariance T τ i (min s.toNNReal (τ + H)) z.1 /
        Real.sqrt (canonicalBirthDominatingAggregate T τ i s.toNNReal z.1)
    rw [min_eq_left hdom, hz.1, hz.2.1]
  · refine .of_forall fun z t hts => ?_
    have hUr : Continuous (fun s : ℝ => U s.toNNReal z) :=
      (hUc z.1).comp ((continuous_id.min continuous_const).comp continuous_real_toNNReal)
    have hXr : Continuous (fun s : ℝ => X s.toNNReal z) := (hXc z.1).comp continuous_real_toNNReal
    apply (GirsanovPort.continuousOn_focalBracketRatio hUr.continuousOn hXr.continuousOn hσ.le
      (s := Icc 0 (t : ℝ)) ?_).intervalIntegrable_of_Icc t.coe_nonneg
    intro s hst
    have hdom := (hReal t s hst).trans (hts.trans hs)
    exact ⟨hUn _ _, by
      change canonicalBirthFocalVariance T τ i (min s.toNNReal (τ + H)) z.1 ≤
        canonicalBirthDominatingAggregate T τ i s.toNNReal z.1
      rw [min_eq_left hdom]
      exact hUX _ _⟩

end FractionalFixedMeshLaw

end FixedMesh

#print axioms HasAmplitudeCutoffIntegral.congr_amplitude
#print axioms FractionalFixedMeshLaw.exists_usual_birth_focal_brownian

end RoughHeston
