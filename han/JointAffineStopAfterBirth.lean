import NativeJointRandomStop
import SHEStochastic.NativeTimeCut
import SHEStochastic.FilteredStoppedIto

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston.GirsanovPort

open SHEStochastic SHE SHE.PredictableL2

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} [Approximable F μ] {H : ℝ≥0}
  {B M : ℝ≥0 → Ω → ℝ}

local notation "ν" => jointPredictableMeasure F μ H

set_option maxHeartbeats 950000 in
/-- A common predictable joint row and its time-prefix representation
determine its old-law stopped integral, including the given full
filtration at the stopping time. -/
theorem jointIto_random_stop_of_prefix
    (P : FiniteScalarIto.Family F μ H Unit)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hB₂ : ∀ t, MemLp (B t) 2 μ) (hB : Martingale B F μ)
    (hBclock : Martingale (fun t ω => B t ω ^ 2 - ((min t H : ℝ≥0) : ℝ)) F μ)
    (hAgree : ∀ t ≤ H, P.W () t =ᵐ[μ] B t)
    (hM : StronglyAdapted F M) (hMc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (u v : Lp ℝ 2 ν)
    (hRep : ∀ t, M t =ᵐ[μ] jointItoIntegralCLM H hB₂ (NativeTimeCut.prior t u))
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτH : ∀ ω, τ ω ≤ H)
    (hv : ⇑v =ᵐ[ν] fun p => if p.1 ≤ τ p.2 then u p else 0) :
    (fun ω => M (τ ω) ω) =ᵐ[μ] jointItoIntegralCLM H hB₂ v := by
  let e := scalarHilbertBasis
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  have hν : ν = (energyMeasure μ H).trim F.predictable_le_prod :=
    (FilteredScalarIto.processMeasure_eq (𝓖 := F) (μ := μ) H
      (B := fun _ _ => (0 : ℝ)) (fun _ => measurable_const)).symm
  let A (z : Lp ℝ 2 ν) : Process (E := ℝ) F μ H :=
    (show MemLp (⇑z) 2 ((energyMeasure μ H).trim F.predictable_le_prod) from
      hν ▸ Lp.memLp z).toLp (⇑z)
  have hA (z : Lp ℝ 2 ν) : ⇑(A z) =ᵐ[ν] z := by
    have hh : ⇑(A z) =ᵐ[(energyMeasure μ H).trim F.predictable_le_prod] (⇑z : ℝ≥0 × Ω → ℝ) :=
      (show MemLp (⇑z) 2 ((energyMeasure μ H).trim F.predictable_le_prod) from
        hν ▸ Lp.memLp z).coeFn_toLp
    exact hh.filter_mono (le_of_eq (congrArg (fun η => ae η) hν))
  have hAv : ⇑(A v) =ᵐ[energyMeasure μ H] fun p => if p.1 ≤ τ p.2 then A u p else 0 := by
    have h : ⇑(A v) =ᵐ[ν] fun p => if p.1 ≤ τ p.2 then A u p else 0 := by
      filter_upwards [hA v, hA u,hv] with p h₁ h₂ h₃
      rw [h₁,h₃,h₂]
    rw [hν] at h
    exact ae_eq_of_ae_eq_trim h
  have hRep' (q : ℝ≥0) : M q =ᵐ[μ]
      (J.integral (StoppedItoInputs.stop F μ H q (A u)) : Ω → ℝ) := by
    let Aq := StoppedItoInputs.stop F μ H q (A u)
    have hAq : ⇑Aq =ᵐ[ν] (StoppedItoInputs.before (Ω := Ω) q).indicator (A u) := by
      rw [hν]
      exact ((Lp.memLp (A u)).indicator (StoppedItoInputs.before_measurable F q).nullMeasurableSet).coeFn_toLp
    have hne : ∀ᵐ p ∂ν, p.1 ≠ q := FilteredScalarIto.trim_ae_fst_ne (𝓖 := F) (μ := μ) H q
      (B := fun _ _ => (0 : ℝ)) (fun _ => measurable_const)
    have he : FiniteCylindricalIto.processTransport Aq = NativeTimeCut.prior q u := by
      apply Lp.ext
      filter_upwards [FiniteCylindricalIto.processTransport_ae Aq, hAq,
        NativeTimeCut.prior_ae q u, hA u,hne] with p h₁ h₂ h₃ h₄ hn
      rw [h₁,h₂,h₃]
      rcases lt_or_gt_of_ne hn with h | h
      · rw [indicator_of_mem (show p ∈ StoppedItoInputs.before (Ω := Ω) q from by exact_mod_cast h),
          ite_eq_right (not_lt_of_ge h.le)]
        exact h₄
      · rw [indicator_of_notMem (show p ∉ StoppedItoInputs.before (Ω := Ω) q from by
          exact_mod_cast (not_lt_of_ge h.le)), ite_eq_left h]
    have hJ : J.integral Aq = jointItoIntegralCLM H hB₂ (NativeTimeCut.prior q u) := by
      rw [← he]
      exact scalarNativeIntegral_eq_joint P.toCoordinates hB₂ hB hBclock hAgree _
    change M q =ᵐ[μ] (J.integral Aq : Ω → ℝ)
    rw [hJ]
    exact hRep q
  have h := native_joint_integral_random_stop P hnull hB₂ hB hBclock hAgree (A u) (A v)
    hM hMc hRep' hτ hτH hAv
  have hvE : FiniteCylindricalIto.processTransport (A v) = v :=
    Lp.ext ((FiniteCylindricalIto.processTransport_ae (A v)).trans (hA v))
  rwa [hvE] at h

set_option maxHeartbeats 650000 in
/-- Subtracting the birth prefix leaves exactly the predictable row
between the birth time and the random observation. -/
theorem jointIto_random_stop_after_birth
    (P : FiniteScalarIto.Family F μ H Unit)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hB₂ : ∀ t, MemLp (B t) 2 μ) (hB : Martingale B F μ)
    (hBclock : Martingale (fun t ω => B t ω ^ 2 - ((min t H : ℝ≥0) : ℝ)) F μ)
    (hAgree : ∀ t ≤ H, P.W () t =ᵐ[μ] B t)
    (hM : StronglyAdapted F M) (hMc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (u v w : Lp ℝ 2 ν)
    (hRep : ∀ t, M t =ᵐ[μ] jointItoIntegralCLM H hB₂ (NativeTimeCut.prior t u))
    {b : ℝ≥0} {τ : Ω → ℝ≥0} (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτb : ∀ ω, b ≤ τ ω) (hτH : ∀ ω, τ ω ≤ H)
    (hv : ⇑v =ᵐ[ν] fun p => if p.1 ≤ τ p.2 then u p else 0)
    (hw : ⇑w =ᵐ[ν] fun p => if b < p.1 ∧ p.1 ≤ τ p.2 then u p else 0) :
    (fun ω => M (τ ω) ω) =ᵐ[μ] fun ω => M b ω + jointItoIntegralCLM H hB₂ w ω := by
  have hStop := jointIto_random_stop_of_prefix P hnull hB₂ hB hBclock hAgree hM hMc u v
    hRep hτ hτH hv
  let p : Lp ℝ 2 ν := NativeTimeCut.prior b u
  have he : v = p + w := by
    apply Lp.ext
    filter_upwards [hv,hw, Lp.coeFn_add p w, NativeTimeCut.prior_ae b u] with z h₁ h₂ h₃ h₄
    change p z = (if b < z.1 then 0 else u z) at h₄
    rw [h₁,h₃, Pi.add_apply,h₄,h₂]
    by_cases hb : b < z.1
    · simp [hb]
    · have ht : z.1 ≤ τ z.2 := (le_of_not_gt hb).trans (hτb z.2)
      simp [hb,ht]
  let J := jointItoIntegralCLM (𝒢 := F) H hB₂
  have hJ : J v = J p + J w := by rw [he,map_add]
  filter_upwards [hStop,hRep b,Lp.coeFn_add (J p) (J w)] with ω h₁ h₂ h₃
  change M (τ ω) ω = J v ω at h₁
  change M b ω = J p ω at h₂
  change M (τ ω) ω = M b ω + J w ω
  rw [h₁,hJ,h₃, Pi.add_apply,h₂]

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.jointIto_random_stop_of_prefix
#print axioms RoughHeston.GirsanovPort.jointIto_random_stop_after_birth
