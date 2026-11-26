import BridgeScalarNative
import FixedHestonHorizon
import HestonFubiniKernel
import SHEStochastic.FilteredStoppedIto
import SHEStochastic.FiniteCylindricalTerminalIto

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston.GirsanovPort

open SHEStochastic SHE SHE.PredictableL2

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} {H : ℝ≥0} {B M a : ℝ≥0 → Ω → ℝ}

local notation "ν" => jointPredictableMeasure F μ H

set_option maxHeartbeats 750000 in
/-- The variance martingale's original cutoff integrals give the
ordinary native predictable amplitude and its same-filtration prefix
integrals, with no new Brownian noise or representation assumption. -/
theorem native_amplitude_of_joint_prefix
    (P : FiniteScalarIto.Family F μ H Unit)
    (hB₂ : ∀ s, MemLp (B s) 2 μ) (hB : Martingale B F μ)
    (hBclock : Martingale (fun t ω => B t ω ^ 2 - ((min t H : ℝ≥0) : ℝ)) F μ)
    (hAgree : ∀ t ≤ H, P.W () t =ᵐ[μ] B t)
    (ha₂ : MemLp (Function.uncurry a) 2 ν)
    (hJoint : ∀ t ≤ H, M t =ᵐ[μ]
      (jointItoIntegralCLM H hB₂ (jointAmplitudeSectionLp t ha₂) : Ω → ℝ)) :
    ∃ A : Process (E := ℝ) F μ H,
      (⇑A =ᵐ[energyMeasure μ H] Function.uncurry a) ∧
      ∀ t ≤ H, M t =ᵐ[μ] ⇑((FiniteCylindricalIto.terminalIto P.toCoordinates scalarHilbertBasis).integral
        (StoppedItoInputs.stop F μ H t A)) := by
  let e := scalarHilbertBasis
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  have hν : ν = (energyMeasure μ H).trim F.predictable_le_prod :=
    (FilteredScalarIto.processMeasure_eq (𝓖 := F) (μ := μ) H
      (B := fun _ _ => (0 : ℝ)) (fun _ => measurable_const)).symm
  have hA₂ : MemLp (Function.uncurry a) 2 ((energyMeasure μ H).trim F.predictable_le_prod) :=
    by rw [← hν]; exact ha₂
  let A : Process (E := ℝ) F μ H := hA₂.toLp (Function.uncurry a)
  have hAtrim : ⇑A =ᵐ[(energyMeasure μ H).trim F.predictable_le_prod] Function.uncurry a :=
    hA₂.coeFn_toLp
  have hAa : ⇑A =ᵐ[ν] Function.uncurry a := by rw [hν]; exact hAtrim
  refine ⟨A, ae_eq_of_ae_eq_trim hAtrim, ?_⟩
  intro t ht
  let v := StoppedItoInputs.stop F μ H t A
  let p := jointAmplitudeSectionLp t ha₂
  have hp : ⇑p =ᵐ[ν] (Ioc (0 : ℝ≥0) t ×ˢ (univ : Set Ω)).indicator (Function.uncurry a) :=
    jointAmplitudeSectionLp_ae t ha₂
  have hvA : ⇑v =ᵐ[ν] (StoppedItoInputs.before (Ω := Ω) t).indicator (⇑A) := by
    rw [hν]
    exact ((Lp.memLp A).indicator (StoppedItoInputs.before_measurable F t).nullMeasurableSet).coeFn_toLp
  have hne : ∀ᵐ p ∂ν, p.1 ≠ t :=
    FilteredScalarIto.trim_ae_fst_ne (𝓖 := F) (μ := μ) H t
      (B := fun _ _ => (0 : ℝ)) (fun _ => measurable_const)
  have he : FiniteCylindricalIto.processTransport v = p := by
    apply Lp.ext
    filter_upwards [FiniteCylindricalIto.processTransport_ae v, hvA, hAa, hp, hne,
      ae_fst_mem_Ioo_jointPredictableMeasure (𝒢 := F) (μ := μ) H] with z h₁ h₂ h₃ h₄ hn htime
    rw [h₁,h₂]
    change (StoppedItoInputs.before (Ω := Ω) t).indicator (⇑A) z = p z
    rw [h₄]
    by_cases hz : z.1 < t
    · have hu : z ∈ StoppedItoInputs.before (Ω := Ω) t := by exact_mod_cast hz
      have ha : z ∈ Ioc (0 : ℝ≥0) t ×ˢ (univ : Set Ω) :=
        ⟨⟨htime.1,hz.le⟩,mem_univ _⟩
      rw [indicator_of_mem hu, indicator_of_mem ha, h₃]
    · have hu : z ∉ StoppedItoInputs.before (Ω := Ω) t := by exact_mod_cast hz
      have ha : z ∉ Ioc (0 : ℝ≥0) t ×ˢ (univ : Set Ω) :=
        fun h => hz (lt_of_le_of_ne h.1.2 hn)
      rw [indicator_of_notMem hu, indicator_of_notMem ha]
  have hJ : J.integral v = jointItoIntegralCLM H hB₂ p := by
    rw [← he]
    exact scalarNativeIntegral_eq_joint P.toCoordinates hB₂ hB hBclock hAgree _
  change M t =ᵐ[μ] (J.integral v : Ω → ℝ)
  rw [hJ]
  exact hJoint t ht


set_option maxHeartbeats 750000 in
/-- The variance martingale's original cutoff integrals give the
ordinary native predictable amplitude and its same-filtration prefix
integrals, with no new Brownian noise or representation assumption. -/
theorem native_variance_amplitude_of_cutoff
    (P : FiniteScalarIto.Family F μ H Unit)
    (hB₂ : ∀ s, MemLp (B s) 2 μ) (hB : Martingale B F μ)
    (hBclock : Martingale (fun t ω => B t ω ^ 2 - ((min t H : ℝ≥0) : ℝ)) F μ)
    (hAgree : ∀ t ≤ H, P.W () t =ᵐ[μ] B t)
    (ha : IsStronglyPredictable F a) (haa : StronglyAdapted F a)
    (haCon : ∀ᵐ ω ∂μ, ContinuousOn (fun t => a t ω) (Icc 0 H))
    (ha₀ : ∀ t ω, 0 ≤ a t ω) (ha₂ : MemLp (Function.uncurry a) 2 ν)
    (hCut : HasAmplitudeCutoffIntegral F μ H B M a) :
    ∃ A : Process (E := ℝ) F μ H,
      (⇑A =ᵐ[energyMeasure μ H] Function.uncurry a) ∧
      ∀ t ≤ H, M t =ᵐ[μ] ⇑((FiniteCylindricalIto.terminalIto P.toCoordinates scalarHilbertBasis).integral
        (StoppedItoInputs.stop F μ H t A)) := by
  apply native_amplitude_of_joint_prefix P hB₂ hB hBclock hAgree ha₂
  intro t ht
  exact hCut.ae_eq_jointIto_fixed_horizon ht hB hB₂ hBclock haa ha
    (haCon.mono fun _ hc => hc.mono (Icc_subset_Icc_right ht)) ha₀ ha₂

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.native_amplitude_of_joint_prefix
#print axioms RoughHeston.GirsanovPort.native_variance_amplitude_of_cutoff
