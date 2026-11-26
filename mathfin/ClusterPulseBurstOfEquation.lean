import ClusterPulseHorizonConsistency
import ClusterPulseTiltMeans
import ClusterPulseMeanUpper
import ClusterBurstAssembly

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Interval

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {B M C U : ℝ≥0 → Ω → ℝ}

/-- The model equation and focal bracket yield a burst event at age T,
given the old fourth moment bound at that age. All first and second
moments in the size-biased argument follow from the equation. -/
theorem rectangularPulse_cluster_burst_of_equation
    {T : ℝ≥0} {α κ σ ε d C₄ : ℝ} (hα : 1/2 < α) (hα' : α ≤ 1)
    (hε : 0 < ε) (hd : 0 < d) (hdT : d ≤ (T : ℝ) / 8)
    (hεd : ε = d ^ α) (hσ : 0 < σ) (hC₄ : 0 < C₄)
    (hB₂ : ∀ r, MemLp (B r) 2 P)
    (hB : Martingale B F P)
    (hBclock : Martingale (fun r ω => B r ω ^ 2 - ((min r T : ℝ≥0) : ℝ)) F P)
    (hU : IsStronglyPredictable F U) (hU₀ : ∀ s ω, 0 ≤ U s ω)
    (hUi : ∀ s, Integrable (U s) P) {A : ℝ} (hMean : ∀ s, (∫ ω, U s ω ∂P) ≤ A)
    (hComp : ∀ s ∈ Ioc 0 (T : ℝ),
      fractionalK α s / 2 ≤ fractionalSecondKindResolvent α κ s ∧
        fractionalSecondKindResolvent α κ s ≤ 2 * fractionalK α s)
    (v : ℝ → Lp ℝ 2 P) (hvM : StronglyMeasurable v) (hvC : ContinuousOn v (Icc 0 (T : ℝ)))
    (hvU : ∀ s ∈ Ioc (0 : ℝ) (T : ℝ), ⇑(v s) =ᵐ[P] U s.toNNReal)
    (hEq : ∀ s ∈ Icc 0 (T : ℝ), v s =
      volterraSmulConvolution (fractionalK α)
        (fun u => clusterDeterministicInputLp P (rectangularPulseRate ε d) u - κ • v u) s +
        σ • fixedHestonConvolutionLp (T := T) hα hB₂ hU hU₀ hUi hMean s)
    (hM : Martingale M F P) (hC : Martingale (fun t => M t * M t - C t) F P)
    (hM₂ : MemLp (M T) 2 P) (hM₀ : M 0 =ᵐ[P] 0) (hC₀ : C 0 =ᵐ[P] 0)
    (hCeq : C T =ᵐ[P] fun ω => ∫ s in (0 : ℝ)..(T : ℝ), σ ^ 2 * U s.toNNReal ω)
    (g : Lp ℝ 2 (jointPredictableMeasure F P T))
    (hg : ⇑g =ᵐ[jointPredictableMeasure F P T] fun p => σ * Real.sqrt (U p.1 p.2))
    (hMt : M T =ᵐ[P] jointItoIntegralCLM T hB₂ g)
    (hZ : ∀ᵐ ω ∂P, 0 ≤ ε + M T ω)
    (hU₄ : MemLp (U T) 4 P)
    (hFour : (∫ ω, U T ω ^ 4 ∂P) ≤ ε * C₄ * ((T : ℝ) ^ (2 * α - 1)) ^ 4 / ((T : ℝ) ^ α)) :
    let Z (ω : Ω) := ε + M T ω
    let Q := sizeBiasedLaw P Z ε
    let a := σ ^ 2 / (16 * (Real.Gamma α) ^ 2)
    let z := 1 + σ ^ 2 * (4 / α) / (Real.Gamma α * α)
    let c := Real.sqrt (C₄ * z)
    IsProbabilityMeasure Q ∧
      a ^ 2 / (8 * c) ≤ Q.real {ω |
        (a / 2) * (T : ℝ) ^ (2 * α - 1) ≤ U T ω ∧
          Z ω ≤ (8 * c * (z+1) / a ^ 2) * (T : ℝ) ^ α} := by
  let R := fractionalSecondKindResolvent α κ
  let m (s : ℝ) := ∫ ω, U s.toNNReal ω ∂P
  let Z (ω : Ω) := ε + M T ω
  let Q := sizeBiasedLaw P Z ε
  have hR : Measurable R := fractionalSecondKindResolvent_measurable α κ
  have hTreal : 0 < (T : ℝ) := by linarith
  have hT : 0 < T := NNReal.coe_pos.mp hTreal
  have hαp : 0 < α := by linarith
  have hRnonneg (s : ℝ) (hs : s ∈ Ioc 0 (T : ℝ)) : 0 ≤ R s := by
    have hK : 0 ≤ fractionalK α s := by
      rw [fractionalK, ite_eq_right (not_le_of_gt hs.1)]
      exact div_nonneg (Real.rpow_nonneg hs.1.le _) (Real.Gamma_pos_of_pos hαp).le
    exact (div_nonneg hK (by norm_num)).trans (hComp s hs).1
  have hRloc (s : ℝ) (hs : s ∈ Ioc 0 (T : ℝ)) : |R s| ≤ 2 * fractionalK α s := by
    rw [abs_of_nonneg (hRnonneg s hs)]
    exact (hComp s hs).2
  have hm := rectangularPulse_resolvent_old_means_on_horizon hα hα' hB₂ hB hBclock hU hU₀
    hUi hMean hRloc v hvM hvC hvU hEq
  have hvUt : ⇑(v (T : ℝ)) =ᵐ[P] U T := by
    simpa only [Real.toNNReal_coe] using hvU (T : ℝ) ⟨hTreal, le_rfl⟩
  obtain ⟨hQ, -, hEU, hEZ⟩ := rectangularPulse_sizeBiased_realTime_means hα hα' hT
    hB₂ hB hBclock hU hU₀ hUi hMean hRloc v hvM hvC hvUt hEq
    hM hC hM₂ hM₀ hC₀ hCeq g hg hMt hε hZ
  have : IsProbabilityMeasure Q := hQ
  have hUm : Measurable (U T) :=
    (hU.mono F.predictable_le_prod).measurable.comp (measurable_const.prodMk measurable_id)
  have hZm : Measurable Z := measurable_const.add ((hM.stronglyAdapted T).measurable.mono (F.le T) le_rfl)
  have hZ₂ : MemLp Z 2 P := (memLp_const ε).add hM₂
  have hMids (s : ℝ) (hs : s ∈ Icc ((T : ℝ)/4) ((T : ℝ)/2)) :
      m s = volterraConvolution R (rectangularPulseRate ε d) s :=
    hm s ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hmUp (s : ℝ) (hs : s ∈ Ioc 0 (T : ℝ)) : m s ≤ (4/α)*ε*fractionalK α s := by
    change (∫ ω, U s.toNNReal ω ∂P) ≤ _
    rw [hm s hs]
    exact rectangularPulse_resolvent_mean_upper hαp hα' hε.le hd hs hR
      (fun r hr => ⟨hRnonneg r hr, (hComp r hr).2⟩)
  obtain ⟨hmI,hCovI⟩ := cluster_resolvent_mean_integrable hαp hR hRloc hU hU₀ hMean
  refine ⟨hQ, ?_⟩
  exact rectangularPulse_cluster_burst (A := 4/α) hα hα' hε hd hdT hεd hσ
    (div_nonneg (by norm_num) hαp.le) hC₄ hR hComp (fun s _ => integral_nonneg (hU₀ _))
    hMids hCovI hmI hmUp hUm (hU₀ T) hU₄ hZm hZ hZ₂ hEU hEZ hFour

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.rectangularPulse_cluster_burst_of_equation
