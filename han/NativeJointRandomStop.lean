import BridgeScalarNative
import JointStoppedFlatClock
import SHEStochastic.NativeRandomStopLocality
import SHEStochastic.FiniteCylindricalLocality
import SHEStochastic.FiniteCylindricalParameterVersions
import SHE.PredictableTime

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston.GirsanovPort

open SHEStochastic SHE SHE.PredictableL2

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} [Approximable F μ]
  {H : ℝ≥0} {B M : ℝ≥0 → Ω → ℝ}

set_option maxHeartbeats 900000 in
/-- Cutting a predictable row pointwise at a bounded random time gives
the same joint integral as evaluating its continuous process at the stop. -/
theorem native_joint_integral_random_stop
    (P : FiniteScalarIto.Family F μ H Unit)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hB₂ : ∀ t, MemLp (B t) 2 μ) (hB : Martingale B F μ)
    (hBclock : Martingale (fun t ω => B t ω ^ 2 - ((min t H : ℝ≥0) : ℝ)) F μ)
    (hAgree : ∀ t ≤ H, P.W () t =ᵐ[μ] B t)
    (u v : Process (E := ℝ) F μ H)
    (hM : StronglyAdapted F M) (hMc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hRep : ∀ q, M q =ᵐ[μ] ((FiniteCylindricalIto.terminalIto P.toCoordinates scalarHilbertBasis).integral
      (StoppedItoInputs.stop F μ H q u) : Ω → ℝ))
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτH : ∀ ω, τ ω ≤ H)
    (hv : v =ᵐ[energyMeasure μ H] fun p => if p.1 ≤ τ p.2 then u p else 0) :
    (fun ω => M (τ ω) ω) =ᵐ[μ] jointItoIntegralCLM H hB₂ (FiniteCylindricalIto.processTransport v) := by
  let e := scalarHilbertBasis
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  let S (ω : Ω) : WithTop ℝ≥0 := τ ω
  have hSH (ω : Ω) : S ω ≤ (H : WithTop ℝ≥0) := WithTop.coe_le_coe.mpr (hτH ω)
  have hlocal := FiniteCylindricalIto.pastLocality P e
  have hV := FiniteCylindricalIto.continuousStoppedVersions P e
  obtain ⟨N,hNc,hNrep'⟩ := hV v
  have hNrep (t : ℝ≥0) : N t =ᵐ[μ] (J.integral (StoppedItoInputs.stop F μ H t v) : Ω → ℝ) :=
    hNrep' t
  have hNa : StronglyAdapted F N := by
    apply NullCompleteFiltration.stronglyAdapted_of_versions F μ hnull
    intro t
    obtain ⟨Z,hZ,hE⟩ := StoppedItoInputs.stopped_integral_adapted F μ H J t v
    exact ⟨Z,hZ,(hNrep t).trans hE⟩
  have hNm : Martingale N F μ := ConditionalBracket.martingale J hlocal v hNa hNrep
  have hJn : MemLp (J.integral (StoppedItoInputs.stop F μ H H v) : Ω → ℝ) 2 μ :=
    Lp.memLp _
  have hN₂ : MemLp (N H) 2 μ := (memLp_congr_ae (hNrep H).symm).mp hJn
  have hEbefore : ∀ᵐ p ∂energyMeasure μ H, (p.1 : WithTop ℝ≥0) < S p.2 → u p = v p := by
    filter_upwards [hv] with p hp ht
    have ht' : p.1 ≤ τ p.2 := WithTop.coe_le_coe.mp ht.le
    simpa only [ite_eq_left ht'] using hp.symm
  have hSE := NativeRandomStopLocality.stopped_eq F μ H J hlocal hnull u v M N hM hNa
    hMc (ae_of_all _ hNc) hRep hNrep S hτ hEbefore H
  let A := PredictableBracket.energy v
  have hComp := PredictableBracket.square_compensator_martingale J hlocal v hNa hNrep
  have hAc : ∀ᵐ ω ∂μ, Continuous (fun t => A t ω) :=
    (PredictableBracket.continuous_monotone v).mono fun _ h => h.1
  have hflat : stoppedProcess A S H =ᵐ[μ] A H := by
    have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae hv
    filter_upwards [Measure.ae_ae_of_ae_prod hswap] with ω hω
    change A (min (H : WithTop ℝ≥0) (S ω)).untopA ω = A H ω
    rw [min_eq_right (hSH ω)]
    simp only [S, WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
    unfold A PredictableBracket.energy
    apply integral_congr_ae
    filter_upwards [hω, (timeMeasure H).ae_ne (τ ω)] with t ht hne
    change v (t, ω) = (if t ≤ τ ω then u (t, ω) else 0) at ht
    by_cases h : t < τ ω
    · simp only [Set.indicator_of_mem (show t ∈ Iio (τ ω) from h),
        Set.indicator_of_mem (show t ∈ Iio H from h.trans_le (hτH ω))]
    · have hgt : ¬t ≤ τ ω := fun hl => h (lt_of_le_of_ne hl hne)
      have hz : v (t, ω) = 0 := by simpa only [ite_eq_right hgt] using ht
      simp [Set.indicator_apply, h, hz]
  have hDone := martingale_terminal_eq_stopped_of_flat_clock hnull hNm hNc hN₂ hComp hAc hτ
    hSH (PredictableBracket.integrable v H) hflat
  have hVH : StoppedItoInputs.stop F μ H H v = v := by
    have ht : ∀ᵐ r ∂timeMeasure H, r < H := by
      filter_upwards [timeMeasure_ae_mem H, (timeMeasure H).ae_ne H] with r hr hne
      exact lt_of_le_of_ne hr.2 hne
    have hp : ∀ᵐ p : ℝ≥0 × Ω ∂energyMeasure μ H, p.1 < H :=
      Measure.quasiMeasurePreserving_fst.ae ht
    apply PastItoAlgebra.eq_of_ambient_ae F μ H
    filter_upwards [StoppedItoInputs.stop_ae F μ H H v, hp] with p hs ht
    rw [hs, indicator_of_mem (show p ∈ StoppedItoInputs.before (Ω := Ω) H from by exact_mod_cast ht)]
  have hNfin := hNrep H
  rw [hVH] at hNfin
  have hFin : J.integral v = jointItoIntegralCLM H hB₂ (FiniteCylindricalIto.processTransport v) :=
    scalarNativeIntegral_eq_joint P.toCoordinates hB₂ hB hBclock hAgree _
  rw [hFin] at hNfin
  have hEval : (fun ω => M (τ ω) ω) =ᵐ[μ] stoppedProcess N S H := by
    filter_upwards [hSE] with ω hω
    have hmin : min (H : WithTop ℝ≥0) (S ω) = (τ ω : WithTop ℝ≥0) :=
      min_eq_right (hSH ω)
    change M (min (H : WithTop ℝ≥0) (S ω)).untopA ω =
      N (min (H : WithTop ℝ≥0) (S ω)).untopA ω at hω
    change M (τ ω) ω = N (min (H : WithTop ℝ≥0) (S ω)).untopA ω
    rw [hmin, WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe] at hω ⊢
    exact hω
  exact hEval.trans (hDone.symm.trans hNfin)

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.native_joint_integral_random_stop
