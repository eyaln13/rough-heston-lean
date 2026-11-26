import AggregateFixedMeshPathData
import AggregateSamplewiseForward

/-! Both original aggregate rows satisfy their direct fractional equations
under one Brownian motion. Their deterministic immigration can be
centered out for uniform estimates across meshes. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

open MathFin.ItoLocalMartingale (nullAugmentation)
open GirsanovPort

set_option maxHeartbeats 2000000

/-- The exact centered equation together with the chosen L² version of
its continuous variance row. -/
structure CenteredHestonRowData {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (T : ℝ≥0) (α κ σ : ℝ) (hα : 1/2 < α)
    (B U : ℝ≥0 → Ω → ℝ) (hB₂ : ∀ t, MemLp (B t) 2 P) (D : ℝ → ℝ) where
  predictable : IsStronglyPredictable F U
  continuous_paths : ∀ ω, Continuous (fun t => U t ω)
  nonnegative : ∀ t ω, 0 ≤ U t ω
  integrable : ∀ t, Integrable (U t) P
  meanBound : ℝ
  meanLe : ∀ t, (∫ ω, U t ω ∂P) ≤ meanBound
  pathLp : ℝ → Lp ℝ 2 P
  continuous_pathLp : Continuous pathLp
  rep : ∀ s, ⇑(pathLp s) =ᵐ[P] U s.toNNReal
  forward : ∀ s ∈ Icc 0 (T:ℝ), pathLp s = clusterDeterministicInputLp P D s +
    volterraSmulConvolution (hestonKernel α) (fun r => (-κ:ℝ) • pathLp r) s +
      σ • fixedHestonConvolutionLp (T := T) hα hB₂ predictable nonnegative integrable meanLe s

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
  {α κ σ : ℝ} {v : Option ι → ℝ} {β : Option ι → ℝ≥0 → ℝ}
local notation "Ω" => CanonicalPath T (CoupledPhysicalState ι)
local notation "Ω'" => Ω × (ℝ≥0 → ℝ)
local notation "G" => canonicalPathNaturalFiltration (E := CoupledPhysicalState ι) T

namespace FractionalFixedMeshLaw

variable (L : FractionalFixedMeshLaw T α κ σ v β)
local notation "Physμ" => (L.law : Measure Ω)
local notation "Extμ" => Measure.prod (L.law : Measure Ω) gaussianLimit
local notation "ExtF" => nullAugmentation (prodFiltration G canonicalAuxiliaryFiltration) Extμ

/-- The direct fractional equation persists in the chosen Brownian extension
with the deterministic forcing shifted by the actual rectangular rates. -/
theorem liftedAggregateRow_centered_data
    (hT : 0 < T) (hα : 1/2 < α) (hα' : α < 1) (hσ : 0 ≤ σ)
    {f : C(ℝ × ℝ, ℝ)} (hf : f = canonicalFirstVariance ∨ f = canonicalSecondVariance)
    {v₀ : ℝ} {βR : ℝ → ℝ} {βN : ℝ≥0 → ℝ} (hRN : ∀ s ≥ 0, βR s = βN s.toNNReal)
    (hβR : Measurable βR) {D : ℝ} (hDR : ∀ s, ‖βR s‖ ≤ D)
    (hDC : Continuous (volterraConvolution (fractionalK α) βR))
    {B : ℝ≥0 → Ω' → ℝ} (hB₂ : ∀ t, MemLp (B t) 2 Extμ) (hB : Martingale B ExtF Extμ)
    (hClock : Martingale (fun t z => B t z^2-((min t T:ℝ≥0):ℝ)) ExtF Extμ)
    {M : ℝ≥0 → Ω → ℝ}
    (hInv : ∀ᵐ p ∂Physμ, ∀ t,
      canonicalVarianceMartingale T α v₀ κ 0 f t (canonicalAggregatePair p)+
        canonicalImmigrationShift T 0 βN t = M t p)
    (hcut : HasAmplitudeCutoffIntegral ExtF Extμ T B (fun t z => M t z.1)
      (fun t z => σ*Real.sqrt (liftedAggregateVariance (ι := ι) (T := T) f t z))) :
    Nonempty (CenteredHestonRowData Extμ ExtF T α κ σ hα B
      (liftedAggregateVariance (ι := ι) (T := T) f) hB₂
      (fun s => v₀+volterraConvolution (fractionalK α) βR s)) := by
  obtain ⟨hUp,hUa,hUc,hUn,hUi,⟨A,hAm⟩,⟨w,hw,hRep⟩⟩ := L.liftedAggregateVariance_L2_data hf
  have hI := L.liftedAggregateVariance_inverse_of_pullback hRN hβR hDR hInv
  have hForward := aggregate_samplewise_forward_centered_L2 hα hα' hT hσ hβR hDR hDC
    hB₂ hB hClock hUp hUa (ae_of_all _ fun _ => (hUc _).continuousOn) hUn hUi hAm
    hcut w hw.stronglyMeasurable hw.continuousOn hRep hI
  refine ⟨⟨hUp,hUc,hUn,hUi,A,hAm,w,hw,hRep,?_⟩⟩
  intro s hs
  have h := hForward s hs
  unfold clusterDeterministicInputLp at h ⊢
  rw [add_smul]
  rw [sub_eq_iff_eq_add.mp (sub_eq_iff_eq_add.mp h)]
  abel

/-- The actual coupled aggregate and companion share one Brownian and
have direct fractional equations for their two prescribed rates. -/
theorem exists_aggregateCommonBrownian_with_forward
    (hT : 0 < T) (hα : 1/2 < α) (hα' : α < 1) (hσ : 0 ≤ σ)
    {v₀ : ℝ} (hvX : (∑ i : ι, v (some i)) = v₀) (hvY : v none = v₀)
    {D : ℝ} (hβ : ∀ i, Measurable (β i)) (hβD : ∀ i t, ‖β i t‖ ≤ D)
    {γ δ : ℝ → ℝ} (hγ : Measurable γ) (hδ : Measurable δ)
    {Dγ Dδ : ℝ} (hγD : ∀ s, ‖γ s‖ ≤ Dγ) (hδD : ∀ s, ‖δ s‖ ≤ Dδ)
    (hγE : ∀ s ≥ 0, γ s = ∑ i : ι, β (some i) s.toNNReal)
    (hδE : ∀ s ≥ 0, δ s = β none s.toNNReal)
    (hγC : Continuous (volterraConvolution (fractionalK α) γ))
    (hδC : Continuous (volterraConvolution (fractionalK α) δ)) :
    ∃ (B : ℝ≥0 → Ω' → ℝ) (hB₂ : ∀ t, MemLp (B t) 2 Extμ),
      IsBrownianOn Extμ ExtF T B ∧ Martingale B ExtF Extμ ∧
      Martingale (fun t z => B t z^2-((min t T:ℝ≥0):ℝ)) ExtF Extμ ∧
      Nonempty (CenteredHestonRowData Extμ ExtF T α κ σ hα B
        (liftedAggregateVariance (ι := ι) (T := T) canonicalFirstVariance) hB₂
        (fun s => v₀+volterraConvolution (fractionalK α) γ s)) ∧
      Nonempty (CenteredHestonRowData Extμ ExtF T α κ σ hα B
        (liftedAggregateVariance (ι := ι) (T := T) canonicalSecondVariance) hB₂
        (fun s => v₀+volterraConvolution (fractionalK α) δ s)) := by
  obtain ⟨B,hBw,hBm,hB₂,hClock,hX,hY⟩ := L.exists_aggregate_commonBrownian hσ
  have hInv := ae_canonicalAggregatePair_martingale_pullback (θ := 0) hα' v β hvX hvY hβ hβD L.inverse L.nonnegative
  have hInvX : ∀ᵐ p ∂Physμ, ∀ t,
      canonicalVarianceMartingale T α v₀ κ 0 canonicalFirstVariance t (canonicalAggregatePair p)+
        canonicalImmigrationShift T 0 (fun s => ∑ i : ι, β (some i) s) t =
          canonicalPhysicalAggregateResidual T t p := by
    simpa only [mul_zero] using (hInv.mono fun p hp t => (hp t).1)
  have hInvY : ∀ᵐ p ∂Physμ, ∀ t,
      canonicalVarianceMartingale T α v₀ κ 0 canonicalSecondVariance t (canonicalAggregatePair p)+
        canonicalImmigrationShift T 0 (β none) t = canonicalPhysicalResidual T none t p := by
    simpa only [mul_zero] using (hInv.mono fun p hp t => (hp t).2)
  exact ⟨B,hB₂,hBw,hBm,hClock,
    L.liftedAggregateRow_centered_data hT hα hα' hσ (Or.inl rfl) hγE hγ hγD hγC hB₂ hBm hClock hInvX hX,
    L.liftedAggregateRow_centered_data hT hα hα' hσ (Or.inr rfl) hδE hδ hδD hδC hB₂ hBm hClock hInvY hY⟩

end FractionalFixedMeshLaw

#print axioms RoughHeston.FractionalFixedMeshLaw.exists_aggregateCommonBrownian_with_forward

end RoughHeston
