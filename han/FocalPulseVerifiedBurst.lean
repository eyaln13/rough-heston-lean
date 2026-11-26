import RectangularPulseMomentLaw
import ClusterPulseBurstOfEquation
import ClusterFocalAmplitude
import ClusterPulseSamplewiseInverse
import FocalPulseRegularity

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Interval

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {M C U W : ℝ≥0 → Ω → ℝ}

set_option maxHeartbeats 1000000 in
/-- The inverse cluster dynamics give the size-biased burst with constants
uniform in both the immigration mesh and the choice of observation time. -/
theorem rectangularPulse_uniform_burst_of_regular_inverse
    {T : ℝ≥0} {α κ σ ε d : ℝ} (hα : 1/2 < α) (hα' : α < 1)
    (hε : 0 < ε) (hd : 0 < d) (hdT : d ≤ (T : ℝ) / 8)
    (hεd : ε = d ^ α) (hσ : 0 < σ)
    (hnull : ∀ N : Set Ω, MeasurableSet N → P N=0 → MeasurableSet[F 0] N)
    (hUp : IsStronglyPredictable F U) (hUa : StronglyAdapted F U)
    (hUc : ∀ᵐ ω ∂P, Continuous (fun s => U s ω)) (hU₀ : ∀ s ω, 0 ≤ U s ω)
    (hReg : FocalPulseRegularity P U)
    (hComp : ∀ s ∈ Ioc 0 (T : ℝ),
      fractionalK α s / 2 ≤ fractionalSecondKindResolvent α κ s ∧
        fractionalSecondKindResolvent α κ s ≤ 2 * fractionalK α s)
    (hM : Martingale M F P) (hM₂ : ∀ t, MemLp (M t) 2 P)
    (hMc : ∀ᵐ ω ∂P, ContinuousOn (fun t => M t ω) (Iic T))
    (hM₀ : M 0 =ᵐ[P] 0) (hCsq : Martingale (fun t => M t * M t - C t) F P)
    (hCe : ∀ᵐ ω ∂P, ∀ t ≤ T, C t ω = ∫ s in (0 : ℝ)..(t : ℝ), σ ^ 2 * U s.toNNReal ω)
    (hW : Martingale W F P) (hW₂ : ∀ t, MemLp (W t) 2 P)
    (hWc : ∀ᵐ ω ∂P, Continuous (fun t => W t ω))
    (hWsq : Martingale (fun t ω => W t ω * W t ω - ((min t T : ℝ≥0) : ℝ)) F P)
    (hWM : Martingale (fun t => W t * M t) F P)
    (hInv : ∀ u : ℝ≥0, u ≤ T →
      (fun ω => ∫ s in Ioc (0 : ℝ) (u : ℝ), fractionalL α ((u : ℝ) - s) * U s.toNNReal ω) =ᵐ[P]
      (fun ω => (∫ s in Ioc (0 : ℝ) (u : ℝ), rectangularPulseRate ε d s - κ * U s.toNNReal ω) + M u ω))
    (hZ : ∀ᵐ ω ∂P, 0 ≤ ε + M T ω)
    :
    let C₄ := 1+focalPulseMomentConstant α σ 2
    let Z (ω : Ω) := ε + M T ω
    let Q := sizeBiasedLaw P Z ε
    let a := σ ^ 2 / (16 * (Real.Gamma α) ^ 2)
    let z := 1 + σ ^ 2 * (4 / α) / (Real.Gamma α * α)
    let c := Real.sqrt (C₄ * z)
    IsProbabilityMeasure Q ∧
      a ^ 2 / (8 * c) ≤ Q.real {ω |
        (a / 2) * (T : ℝ) ^ (2 * α - 1) ≤ U T ω ∧
          Z ω ≤ (8 * c * (z+1) / a ^ 2) * (T : ℝ) ^ α} := by
  let C₄ := 1+focalPulseMomentConstant α σ 2
  have hC₄ : 0<C₄ := by dsimp [C₄]; linarith [focalPulseMomentConstant_nonneg α σ 2]
  have hUm (t : ℝ≥0) : Measurable (U t) := (hUa t).measurable.mono (F.le t) le_rfl
  obtain ⟨hUi,⟨_,hMean⟩,v,hvC,hvRep⟩ := hReg
  have hUci : ∀ᵐ ω ∂P, ContinuousOn (fun t => U t ω) (Icc 0 T) :=
    hUc.mono fun _ h => h.continuousOn
  obtain ⟨B, hB₂, hB, hB₀, hBc, hBclock, hcut, g, hg, hMt⟩ :=
    focal_cluster_has_own_unit_clock_driver hσ.le hM hM₂ hMc hM₀ hCsq hCe
      hW hW₂ hWc hWsq hWM hUp hUa hUci hU₀ hUi hMean
  have hT : 0 < T := NNReal.coe_pos.mp (by linarith)
  have hEq := rectangularPulse_L2_equation_of_samplewise_inverse hα hα' hT hε.le hd hσ.le
    hB₂ hB hBclock hUp hUa hUci hU₀ hUi hMean hcut v hvC.stronglyMeasurable hvC.continuousOn hvRep hInv
  have ha : 0<α := by linarith
  have hcomp' (s : ℝ) (hs : s∈Ioc 0 (T:ℝ)) :
      0≤fractionalSecondKindResolvent α κ s ∧
      fractionalSecondKindResolvent α κ s≤2*fractionalK α s := by
    have hK : 0 ≤ fractionalK α s := by
      rw [fractionalK,ite_eq_right (not_le.mpr hs.1)]
      exact div_nonneg (Real.rpow_nonneg hs.1.le _) (Real.Gamma_pos_of_pos ha).le
    exact ⟨(by linarith [(hComp s hs).1] : 0≤fractionalSecondKindResolvent α κ s), (hComp s hs).2⟩
  have ht : 0<(T:ℝ) := by exact_mod_cast hT
  have hraw := rectangularPulse_cluster_dyadic_moments hα hα'.le hd hεd
    (show d≤(T:ℝ) by linarith) (show (T:ℝ)≤2*(T:ℝ) by linarith)
    hnull hB₂ hB hBc hB₀ hBclock hUp hU₀ hUi hMean hcomp' v hvC.stronglyMeasurable
    hvC.continuousOn (fun s _ => hvRep s) hEq 2 T hT le_rfl
  norm_num only [Nat.reducePow,Nat.cast_ofNat] at hraw
  have hU₄ : MemLp (U T) 4 P := hraw.1
  let β := 2*α-1
  have hpow : (T:ℝ)^(α-1)*(T:ℝ)^(3*β)=(T:ℝ)^(4*β)/(T:ℝ)^α := by
    rw [← Real.rpow_add ht, ← Real.rpow_sub ht]; congr 1; dsimp [β]; ring
  have hc' : focalPulseMomentConstant α σ 2 ≤ C₄ := by dsimp [C₄]; linarith
  have hFour : (∫ ω, U T ω^4 ∂P) ≤ ε*C₄*((T:ℝ)^β)^4/(T:ℝ)^α := by
    have hz := hraw.2
    change (∫ ω, U T ω^4 ∂P) ≤ focalPulseMomentConstant α σ 2*ε*
      (T:ℝ)^(α-1)*(T:ℝ)^(3*β) at hz
    calc
      _ ≤ focalPulseMomentConstant α σ 2*ε*((T:ℝ)^(α-1)*(T:ℝ)^(3*β)) := hz.trans_eq (by ring)
      _ ≤ C₄*ε*((T:ℝ)^(α-1)*(T:ℝ)^(3*β)) := by gcongr
      _ = _ := by
        rw [hpow,show (T:ℝ)^(4*β)=((T:ℝ)^β)^4 by
          rw [mul_comm (4:ℝ) β]; exact Real.rpow_mul_natCast ht.le β 4]
        ring
  have hC0 : C 0 =ᵐ[P] 0 := hCe.mono fun ω hω => by simpa using hω 0 (show (0 : ℝ≥0) ≤ T from zero_le)
  have hCT : C T =ᵐ[P] fun ω => ∫ s in (0 : ℝ)..(T : ℝ), σ ^ 2 * U s.toNNReal ω :=
    hCe.mono fun ω hω => hω T le_rfl
  exact rectangularPulse_cluster_burst_of_equation hα hα'.le hε hd hdT hεd hσ hC₄
    hB₂ hB hBclock hUp hU₀ hUi hMean hComp v hvC.stronglyMeasurable hvC.continuousOn
    (fun s _ => hvRep s) hEq hM hCsq (hM₂ T) hM₀ hC0 hCT g hg hMt hZ hU₄ hFour

theorem rectangularPulse_uniform_burst_of_inverse
    {T : ℝ≥0} {α κ σ ε d : ℝ} (hα : 1/2 < α) (hα' : α < 1)
    (hε : 0 < ε) (hd : 0 < d) (hdT : d ≤ (T : ℝ) / 8)
    (hεd : ε = d ^ α) (hσ : 0 < σ)
    (hnull : ∀ N : Set Ω, MeasurableSet N → P N=0 → MeasurableSet[F 0] N)
    (hUp : IsStronglyPredictable F U) (hUa : StronglyAdapted F U)
    (hUc : ∀ᵐ ω ∂P, Continuous (fun s => U s ω)) (hU₀ : ∀ s ω, 0 ≤ U s ω)
    {D : Ω → ℝ} (hD : MemLp D 2 P) (hDU : ∀ᵐ ω ∂P, ∀ s, ‖U s ω‖ ≤ ‖D ω‖)
    (hComp : ∀ s ∈ Ioc 0 (T : ℝ),
      fractionalK α s / 2 ≤ fractionalSecondKindResolvent α κ s ∧
        fractionalSecondKindResolvent α κ s ≤ 2 * fractionalK α s)
    (hM : Martingale M F P) (hM₂ : ∀ t, MemLp (M t) 2 P)
    (hMc : ∀ᵐ ω ∂P, ContinuousOn (fun t => M t ω) (Iic T))
    (hM₀ : M 0 =ᵐ[P] 0) (hCsq : Martingale (fun t => M t * M t - C t) F P)
    (hCe : ∀ᵐ ω ∂P, ∀ t ≤ T, C t ω = ∫ s in (0 : ℝ)..(t : ℝ), σ ^ 2 * U s.toNNReal ω)
    (hW : Martingale W F P) (hW₂ : ∀ t, MemLp (W t) 2 P)
    (hWc : ∀ᵐ ω ∂P, Continuous (fun t => W t ω))
    (hWsq : Martingale (fun t ω => W t ω * W t ω - ((min t T : ℝ≥0) : ℝ)) F P)
    (hWM : Martingale (fun t => W t * M t) F P)
    (hInv : ∀ u : ℝ≥0, u ≤ T →
      (fun ω => ∫ s in Ioc (0 : ℝ) (u : ℝ), fractionalL α ((u : ℝ) - s) * U s.toNNReal ω) =ᵐ[P]
      (fun ω => (∫ s in Ioc (0 : ℝ) (u : ℝ), rectangularPulseRate ε d s - κ * U s.toNNReal ω) + M u ω))
    (hZ : ∀ᵐ ω ∂P, 0 ≤ ε + M T ω)
    :
    let C₄ := 1+focalPulseMomentConstant α σ 2
    let Z (ω : Ω) := ε + M T ω
    let Q := sizeBiasedLaw P Z ε
    let a := σ ^ 2 / (16 * (Real.Gamma α) ^ 2)
    let z := 1 + σ ^ 2 * (4 / α) / (Real.Gamma α * α)
    let c := Real.sqrt (C₄ * z)
    IsProbabilityMeasure Q ∧
      a ^ 2 / (8 * c) ≤ Q.real {ω |
        (a / 2) * (T : ℝ) ^ (2 * α - 1) ≤ U T ω ∧
          Z ω ≤ (8 * c * (z+1) / a ^ 2) * (T : ℝ) ^ α} := by
  have hReg := FocalPulseRegularity.of_dominated hD
    (fun t => (hUa t).measurable.mono (F.le t) le_rfl) hUc hDU
  exact rectangularPulse_uniform_burst_of_regular_inverse hα hα' hε hd hdT hεd hσ hnull
    hUp hUa hUc hU₀ hReg hComp hM hM₂ hMc hM₀ hCsq hCe hW hW₂ hWc hWsq hWM hInv hZ

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.rectangularPulse_uniform_burst_of_regular_inverse
#print axioms RoughHeston.GirsanovPort.rectangularPulse_uniform_burst_of_inverse
