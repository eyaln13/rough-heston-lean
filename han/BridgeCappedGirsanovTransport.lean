import NativeCappedChangeWithShift
import NativeBrownianMartingales
import BridgeGirsanovDensityToJoint

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston
namespace GirsanovPort

open SHEStochastic

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} {H : ℝ≥0} {M : ℝ≥0 → Ω → ℝ}

local notation "ν" => jointPredictableMeasure F μ H

private theorem scalarNativeCross_eq_physical (v u : Lp ℝ 2 ν) (f g : ℝ≥0 × Ω → ℝ)
    (hf : v =ᵐ[ν] f) (hg : u =ᵐ[ν] g) :
    NativeCrossEnergy.cross v u =ᵐ[μ]
      (fun ω => ∫ r, f (r, ω) * g (r, ω) ∂hestonTimeMeasure H) := by
  have hfv := NativeSimpleTransport.path_ae (F := F) (H := H) _ _ hf
  have hgu := NativeSimpleTransport.path_ae (F := F) (H := H) _ _ hg
  filter_upwards [hfv, hgu] with ω hvω huω
  rw [hestonTimeMeasure_eq_horizon]
  apply integral_congr_ae
  filter_upwards [hvω, huω] with r hr₁ hr₂
  exact (Real.inner_apply _ _).trans (congrArg₂ (· * ·) hr₁ hr₂)

private theorem scalarNativeShift_eq_physical (P : FiniteScalarIto.Family F μ H Unit)
    (u : Lp ℝ 2 ν) (g : ℝ≥0 × Ω → ℝ) (hg : u =ᵐ[ν] g) :
    ∀ᵐ ω ∂μ, ∀ t ≤ H,
      ScalarGirsanovCoordinateShift.shift P scalarHilbertBasis
        (NativeInputEquiv.inverse F μ H u) () t ω =
      P.W () t ω + ∫ r, g (r, ω) ∂hestonTimeMeasure t := by
  let U := NativeInputEquiv.inverse F μ H u
  let u' := FiniteCylindricalIto.processTransport U
  have hu : u' = u := NativeInputEquiv.transport_inverse F μ H u
  have hu' : u' =ᵐ[ν] g := by rw [hu]; exact hg
  have hgu := NativeSimpleTransport.path_ae (F := F) (H := H) _ _ hu'
  filter_upwards [ScalarGirsanovCoordinateShift.primitive P scalarHilbertBasis U (), hgu]
    with ω hω hgω t ht
  rw [hω t ht, hestonTimeMeasure_eq_horizon]
  congr 1
  calc
    _ = ∫ r, (Iio t).indicator (fun r => g (r, ω)) r ∂MathFin.ItoIntegralCLM.timeMeasure_T H := by
      apply integral_congr_ae
      filter_upwards [hgω] with r hr
      change (Iio t).indicator (fun r => inner ℝ (scalarHilbertBasis ()) (u' (r, ω))) r = _
      by_cases hrt : r ∈ Iio t
      · simp only [indicator_of_mem hrt, Real.inner_apply, scalarHilbertBasis_apply, one_mul]
        exact hr
      · simp only [indicator_of_notMem hrt]
    _ = _ := NativeClockIntegral.before H t ht _

private theorem frozenNativeCoordinate_brownianOn {η : Measure Ω} [IsProbabilityMeasure η]
    (R : FiniteScalarIto.Family F η H Unit) :
    MathFinBridge.BrownianOn η F H (fun t => R.W () (min t H)) := by
  have hb := nativeCoordinate_brownianOn R ()
  refine ⟨(nativeCoordinate_frozen_martingales R ()).2.1.stronglyAdapted, ?_, ?_, ?_, ?_⟩
  · simpa only [min_eq_left (show (0 : ℝ≥0) ≤ H from zero_le)] using hb.zero_at_start
  · exact ae_of_all _ fun ω =>
      ((R.continuous () ω).comp (continuous_id.min continuous_const)).continuousOn
  · intro s t hst ht
    simpa only [min_eq_left ht, min_eq_left (hst.trans ht)] using hb.normal_increment s t hst ht
  · intro s t hst ht
    simpa only [min_eq_left ht, min_eq_left (hst.trans ht)] using hb.independent_of_past s t hst ht

/-- The capped change of measure on the original filtration gives the
actual shifted Brownian motion, its unit clock, and the transport of
the project's joint L² Itô integrals. The time integrals use the
physical time measure on their respective horizons. -/
theorem jointCappedGirsanov (P : FiniteScalarIto.Family F μ H Unit)
    (hnull : SHE.NullCompleteFiltration.ContainsNullSets F μ)
    (hM₂ : ∀ t, MemLp (M t) 2 μ) (hM : Martingale M F μ)
    (hclock : Martingale (fun t ω => M t ω ^ 2 - ((min t H : ℝ≥0) : ℝ)) F μ)
    (hagree : ∀ᵐ ω ∂μ, ∀ t ≤ H, P.W () t ω = M t ω)
    (u : Lp ℝ 2 ν) (g : ℝ≥0 × Ω → ℝ) (hg : u =ᵐ[ν] g)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hcap : ∀ᵐ ω ∂μ, (∫ r, g (r, ω) ^ 2 ∂hestonTimeMeasure H) ≤ δ) :
    let Q := NativeGirsanovTilt.measure P scalarHilbertBasis u
    ∃ (_ : IsProbabilityMeasure Q) (N : ℝ≥0 → Ω → ℝ) (hN₂ : ∀ t, MemLp (N t) 2 Q),
      Q = μ.withDensity (fun ω => ENNReal.ofReal (Real.exp (-jointItoIntegralCLM H hM₂ u ω -
        (∫ r, g (r, ω) ^ 2 ∂hestonTimeMeasure H) / 2))) ∧
      Q ≪ μ ∧ μ ≪ Q ∧ MathFinBridge.BrownianOn Q F H N ∧ Martingale N F Q ∧
      Martingale (fun t ω => N t ω ^ 2 - ((min t H : ℝ≥0) : ℝ)) F Q ∧
      (∀ᵐ ω ∂μ, ∀ t ≤ H, N t ω = M t ω + ∫ r, g (r, ω) ∂hestonTimeMeasure t) ∧
      ∀ (v : Lp ℝ 2 ν) (w : Lp ℝ 2 (jointPredictableMeasure F Q H)) (f : ℝ≥0 × Ω → ℝ),
        v =ᵐ[ν] f → v =ᵐ[ν] w → jointItoIntegralCLM H hN₂ w =ᵐ[Q]
          (fun ω => jointItoIntegralCLM H hM₂ v ω + ∫ r, f (r, ω) * g (r, ω) ∂hestonTimeMeasure H) := by
  dsimp only
  let Q := NativeGirsanovTilt.measure P scalarHilbertBasis u
  have hcap' : ∀ᵐ ω ∂μ, NativeEnergy.energy u ω ≤ δ := by
    filter_upwards [nativeEnergy_ae_eq_hestonEnergy u g hg, hcap] with ω he hω
    simpa only [he, Real.norm_eq_abs, sq_abs] using hω
  obtain ⟨hQ, R, hAC, hrev, hRshift, hRaw⟩ :=
    native_cap_change_with_shift P scalarHilbertBasis hnull u δ hδ hcap'
  letI : IsProbabilityMeasure Q := hQ
  let N (t : ℝ≥0) := R.W () (min t H)
  obtain ⟨hN₂, hNm, hNclock⟩ := nativeCoordinate_frozen_martingales R ()
  have hagree' (t : ℝ≥0) (ht : t ≤ H) : P.W () t =ᵐ[μ] M t :=
    hagree.mono fun _ hω => hω t ht
  have hQeq := nativeScalarTilt_eq_jointWithDensity P hM₂ hM hclock hagree' u g hg
  refine ⟨hQ, N, hN₂, hQeq, hAC, hrev, frozenNativeCoordinate_brownianOn R, hNm, hNclock, ?_, ?_⟩
  · filter_upwards [hRshift (), scalarNativeShift_eq_physical P u g hg, hagree] with ω hR hS hOrig t ht
    rw [show N t ω = R.W () t ω by simp [N, min_eq_left ht], hR t, hS t ht, hOrig t ht]
  · intro v w f hf hvw
    have hSame (t : ℝ≥0) (ht : t ≤ H) : R.W () t =ᵐ[Q] N t :=
      ae_of_all _ fun ω => by simp [N, min_eq_left ht]
    have hleft := scalarNativeIntegral_eq_joint R.toCoordinates hN₂ hNm hNclock hSame w
    have hright := scalarNativeIntegral_eq_joint P.toCoordinates hM₂ hM hclock hagree' v
    have h := hRaw v w hvw
    rw [hleft, hright] at h
    filter_upwards [h, hAC.ae_eq (scalarNativeCross_eq_physical v u f g hf hg)] with ω hω hcross
    exact hω.trans (congrArg (jointItoIntegralCLM H hM₂ v ω + ·) hcross)

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.jointCappedGirsanov
