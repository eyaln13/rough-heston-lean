import BridgeCappedGirsanovTransport
import StoppedPredictableEnergy
import StoppedClusterEnvelope
import StoppedEntropyBound

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped NNReal ENNReal

namespace RoughHeston.GirsanovPort

open SHEStochastic

variable {Ω : Type*} [m : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {F : Filtration ℝ≥0 m} {H : ℝ≥0} {B : ℝ≥0 → Ω → ℝ}

/-- Agreement of a native coordinate with the original Brownian motion on a
single full-measure event for the whole horizon. -/
private theorem nativeFamily_on_one_event (hb : MathFinBridge.BrownianOn Q F H B)
    (hc : SHE.NullCompleteFiltration.ContainsNullSets F Q) :
    ∃ P : FiniteScalarIto.Family F Q H Unit, ∀ᵐ ω ∂Q, ∀ t ≤ H, P.W () t ω = B t ω := by
  obtain ⟨P, hp⟩ := exists_scalarNativeFamily_of_brownianOn hb (fun A _ hA => hc 0 A hA)
  obtain ⟨D, hD, hd⟩ := exists_countable_dense (Icc (0 : ℝ≥0) H)
  have h := indistinguishable_of_ae_eq_on_dense (μ := Q)
    (X := fun t : Icc (0 : ℝ≥0) H => P.W () t) (Y := fun t : Icc (0 : ℝ≥0) H => B t)
    hD hd (ae_of_all _ fun ω => (P.continuous () ω).comp continuous_subtype_val)
    (hb.continuous_paths.mono fun _ hω => continuousOn_iff_continuous_domRestrict.mp hω)
    (fun t _ => hp t t.2.2)
  exact ⟨P, h.mono fun ω hω t ht => hω ⟨t, zero_le, ht⟩⟩

/-- Properties of the change from Q to R, with the sign convention
Bᴿ = Bᑫ + ∫g ds. Both stochastic integration maps use F. -/
def IsStoppedDriftChange (birth : ℝ≥0) (δ : ℝ) (g : ℝ≥0 → Ω → ℝ)
    (hB₂ : ∀ s, MemLp (B s) 2 Q) (R : Measure Ω) (N : ℝ≥0 → Ω → ℝ) : Prop :=
  ∃ (_ : IsProbabilityMeasure R), Q ≪ R ∧ R ≪ Q ∧ MathFinBridge.BrownianOn R F H N ∧
    (∀ A, MeasurableSet[F birth] A → R.real A = Q.real A) ∧
    (∀ A, MeasurableSet A → |R.real A - Q.real A| ≤ Real.sqrt δ / 2) ∧
    (∀ᵐ ω ∂Q, ∀ t ≤ H, N t ω = B t ω + ∫ s, g s ω ∂hestonTimeMeasure t) ∧
    ∃ (u : Lp ℝ 2 (jointPredictableMeasure F Q H)) (hN₂ : ∀ s, MemLp (N s) 2 R),
      Martingale N F R ∧ Martingale (fun t ω => N t ω ^ 2 - ((min t H : ℝ≥0) : ℝ)) F R ∧
      u =ᵐ[jointPredictableMeasure F Q H] Function.uncurry g ∧
      R = Q.withDensity (fun ω => ENNReal.ofReal (Real.exp (-jointItoIntegralCLM H hB₂ u ω -
        (∫ s, g s ω ^ 2 ∂hestonTimeMeasure H) / 2))) ∧
      ∀ (v : Lp ℝ 2 (jointPredictableMeasure F Q H)) (w : Lp ℝ 2 (jointPredictableMeasure F R H))
        (f : ℝ≥0 × Ω → ℝ), v =ᵐ[jointPredictableMeasure F Q H] f →
        v =ᵐ[jointPredictableMeasure F Q H] w → jointItoIntegralCLM H hN₂ w =ᵐ[R]
          fun ω => jointItoIntegralCLM H hB₂ v ω + ∫ s, f (s, ω) * g s ω ∂hestonTimeMeasure H

theorem exists_drift_change_of_stopped_energy
    (hb : MathFinBridge.BrownianOn Q F H B) (hnull : SHE.NullCompleteFiltration.ContainsNullSets F Q)
    (hB₂ : ∀ t, MemLp (B t) 2 Q) (hB : Martingale B F Q)
    (hclock : Martingale (fun t ω => B t ω ^ 2 - ((min t H : ℝ≥0) : ℝ)) F Q)
    {birth : ℝ≥0} (hbirth : birth ≤ H) {δ : ℝ} (hδ : 0 ≤ δ) {g : ℝ≥0 → Ω → ℝ}
    (hg : IsStronglyPredictable F g) (hzero : ∀ s ≤ birth, ∀ ω, g s ω = 0)
    (hpath : ∀ᵐ ω ∂Q, Integrable (fun s => g s ω ^ 2) (hestonTimeMeasure H))
    (hcap : ∀ᵐ ω ∂Q, (∫ s, g s ω ^ 2 ∂hestonTimeMeasure H) ≤ δ) :
    ∃ R N, IsStoppedDriftChange (F := F) (H := H) birth δ g hB₂ R N := by
  obtain ⟨P, hP⟩ := nativeFamily_on_one_event hb hnull
  have hi := memLp_two_joint_of_pathwise_energy_cap (F := F) (g := Function.uncurry g) hg hpath hcap
  let u := hi.toLp (Function.uncurry g)
  have hu : u =ᵐ[jointPredictableMeasure F Q H] Function.uncurry g := hi.coeFn_toLp
  let R := NativeGirsanovTilt.measure P scalarHilbertBasis u
  obtain ⟨hR, N, hN₂, hd, hRQ, hQR, hn, hNm, hNclock, hshift, htransport⟩ :=
    jointCappedGirsanov P hnull hB₂ hB hclock hP u (Function.uncurry g) hu δ hδ hcap
  let _ : IsProbabilityMeasure R := hR
  have henergy := nativeEnergy_ae_eq_hestonEnergy u (Function.uncurry g) hu
  simp only [Function.uncurry_apply_pair, Real.norm_eq_abs, sq_abs] at henergy
  have hEI := (NativeEnergy.integrable u).congr henergy
  obtain ⟨_, hpast, _⟩ := nativeTilt_preserves_past_and_bounds_events P scalarHilbertBasis
    birth hbirth u (hu.mono (fun p hp hs => hp.trans (hzero p.1 hs p.2))) δ hδ
    (henergy.le.trans hcap)
  exact ⟨R, N, hR, hQR, hRQ, hn, hpast,
    fun _ hA => event_diff_le_sqrt_stopped_energy H hB₂ hB hclock u hEI hδ hcap R hd hA,
    hshift, u, hN₂, hNm, hNclock, hu, hd, htransport⟩

/-- The stopped Girsanov change in the coupling, for a supplied envelope
stopping time and the original variance and focal mass paths under Q. -/
theorem exists_stopped_competitor_girsanov
    (hb : MathFinBridge.BrownianOn Q F H B) (hnull : SHE.NullCompleteFiltration.ContainsNullSets F Q)
    (hB₂ : ∀ t, MemLp (B t) 2 Q) (hB : Martingale B F Q)
    (hclock : Martingale (fun t ω => B t ω ^ 2 - ((min t H : ℝ≥0) : ℝ)) F Q)
    {birth : ℝ≥0} (hbirth : birth ≤ H) {δ σ : ℝ} (hδ : 0 ≤ δ)
    {U Z X Y : ℝ≥0 → Ω → ℝ} {γ : Ω → ℝ≥0} (hg : IsStoppingTime F (fun ω => (γ ω : WithTop ℝ≥0)))
    (hu : IsStronglyPredictable F U) (hz : IsStronglyPredictable F Z)
    (hx : IsStronglyPredictable F X) (hy : IsStronglyPredictable F Y)
    (huc : ∀ ω, ContinuousOn (fun s => U s ω) (Icc 0 H))
    (hzc : ∀ ω, ContinuousOn (fun s => Z s ω) (Icc 0 H))
    (hzpos : ∀ s ≤ H, ∀ ω, 0 < Z s ω) (hun : ∀ s ≤ H, ∀ ω, 0 ≤ U s ω)
    (hux : ∀ s ≤ H, ∀ ω, U s ω ≤ X s ω) :
    let h := competitorAfterBirth birth σ U Z X Y
    ∃ τ : Ω → ℝ≥0, IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)) ∧
      (∀ ω, τ ω ≤ H ∧ τ ω ≤ γ ω) ∧
      (∀ ω, τ ω < H → H ≤ γ ω → δ ≤ controlEnergyClock H (controlThrough h γ) H ω) ∧
      (∀ ω, (∫ s, controlThrough h τ s ω ^ 2 ∂hestonTimeMeasure H) =
        min δ (controlEnergyClock H (controlThrough h γ) H ω)) ∧
      ∃ R N, IsStoppedDriftChange (F := F) (H := H) birth δ (controlThrough h τ) hB₂ R N := by
  dsimp only
  obtain ⟨τ, ht, hle, hp, hexit, he⟩ := exists_stopped_competitor_control (σ := σ) H birth hδ hg hu hz
    hx hy huc hzc hzpos hun hux
  refine ⟨τ, ht, hle, hexit, fun ω => (he ω).2, exists_drift_change_of_stopped_energy hb hnull hB₂ hB
    hclock hbirth hδ hp ?_ (ae_of_all _ fun ω => (he ω).1) ?_⟩
  · intro s hs ω
    simp [controlThrough, competitorAfterBirth, not_lt.mpr hs]
  · exact ae_of_all _ fun ω => (he ω).2.le.trans (min_le_left _ _)

/-- Both stopping times, the equivalent law, and the shifted Brownian motion
are constructed on the same filtration. The supplied processes are the
coupling under the birth-conditioned, size-biased law Q. -/
theorem stopped_competitor_change_at_envelope [F.IsComplete Q] [F.IsRightContinuous]
    (hb : MathFinBridge.BrownianOn Q F H B)
    (hB₂ : ∀ t, MemLp (B t) 2 Q) (hB : Martingale B F Q)
    (hclock : Martingale (fun t ω => B t ω ^ 2 - ((min t H : ℝ≥0) : ℝ)) F Q)
    {birth : ℝ≥0} (hbirth : birth ≤ H) {δ σ p C : ℝ} (hδ : 0 ≤ δ) (hp : 0 < p) (hC : 0 ≤ C)
    {U Z X Y : ℝ≥0 → Ω → ℝ}
    (hu : IsStronglyPredictable F U) (hz : IsStronglyPredictable F Z)
    (hx : IsStronglyPredictable F X) (hy : IsStronglyPredictable F Y)
    (huc : ∀ ω, ContinuousOn (fun s => U s ω) (Icc 0 H))
    (hzc : ∀ ω, ContinuousOn (fun s => Z s ω) (Icc 0 H))
    (hzpos : ∀ s ≤ H, ∀ ω, 0 < Z s ω) (hun : ∀ s ≤ H, ∀ ω, 0 ≤ U s ω)
    (hux : ∀ s ≤ H, ∀ ω, U s ω ≤ X s ω) :
    let h := competitorAfterBirth birth σ U Z X Y
    let γ := envelopeStop H C (clusterEnvelopeValue birth σ p U Z)
    ∃ τ : Ω → ℝ≥0, IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)) ∧
      (∀ ω, τ ω ≤ H ∧ τ ω ≤ γ ω) ∧
      (∀ ω, τ ω < H → H ≤ γ ω → δ ≤ controlEnergyClock H (controlThrough h γ) H ω) ∧
      (∀ ω, (∫ s, controlThrough h τ s ω ^ 2 ∂hestonTimeMeasure H) =
        min δ (controlEnergyClock H (controlThrough h γ) H ω)) ∧
      (∀ ω s, birth < s → s ≤ τ ω → h s ω ^ 2 ≤ C / ((s : ℝ) - birth)^p) ∧
      ∃ R N, IsStoppedDriftChange (F := F) (H := H) birth δ (controlThrough h τ) hB₂ R N := by
  dsimp only
  have hnull : SHE.NullCompleteFiltration.ContainsNullSets F Q := fun t _ h =>
    Filtration.IsComplete.measurableSet_of_null h t
  have hγ := envelopeStop_isStoppingTime Q H C (clusterEnvelopeValue_predictable birth σ p hu hz)
  obtain ⟨τ, ht, hle, hexit, he, R, N, hRN⟩ := exists_stopped_competitor_girsanov (σ := σ) hb
    hnull hB₂ hB hclock hbirth hδ hγ hu hz hx hy huc hzc hzpos hun hux
  refine ⟨τ, ht, hle, hexit, he, ?_, R, N, hRN⟩
  intro ω s hbs hsτ
  exact competitor_cost_before_envelopeStop birth H σ hp hC U Z X Y ω (huc ω) (hzc ω)
    (fun t ht => hzpos t ht ω) (fun t ht => hun t ht ω) (fun t ht => hux t ht ω)
    hbs (hsτ.trans (hle ω).2)

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.exists_drift_change_of_stopped_energy
#print axioms RoughHeston.GirsanovPort.exists_stopped_competitor_girsanov

#print axioms RoughHeston.GirsanovPort.stopped_competitor_change_at_envelope
