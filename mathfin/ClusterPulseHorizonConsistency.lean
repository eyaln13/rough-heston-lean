import ClusterResolventPulseMeans

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {B U : ℝ≥0 → Ω → ℝ}

private theorem jointIto_of_driver_eq {B' : ℝ≥0 → Ω → ℝ} (he : B = B')
    (t : ℝ≥0) (h₂ : ∀ r, MemLp (B r) 2 P) (h₂' : ∀ r, MemLp (B' r) 2 P)
    (w : Lp ℝ 2 (jointPredictableMeasure F P t)) :
    jointItoIntegralCLM t h₂ w = jointItoIntegralCLM t h₂' w := by
  subst B'
  rfl

private theorem fixedHestonConvolutionLp_eq_at {T : ℝ≥0} {α : ℝ} (hα : 1/2 < α)
    (hB₂ : ∀ r, MemLp (B r) 2 P) (hB : Martingale B F P)
    (hBclock : Martingale (fun r ω => B r ω ^ 2 - ((min r T : ℝ≥0) : ℝ)) F P)
    (hU : IsStronglyPredictable F U) (hU₀ : ∀ s ω, 0 ≤ U s ω)
    (hUi : ∀ s, Integrable (U s) P) {A : ℝ} (hMean : ∀ s, (∫ ω, U s ω ∂P) ≤ A)
    {x : ℝ} (hx : x.toNNReal ≤ T) :
    let w := Function.uncurry (hestonConvolutionWeight α x.toNNReal U)
    let hw := heston_convolution_weight_memLp_two_joint hα x.toNNReal hU hU₀ hUi hMean
    fixedHestonConvolutionLp (T := T) hα hB₂ hU hU₀ hUi hMean x =
      jointItoIntegralCLM (M := fun r => B (min r x.toNNReal)) x.toNNReal
        (fun r => hB₂ (min r x.toNNReal)) (hw.toLp w) := by
  dsimp only
  let u : Icc (0 : ℝ≥0) T := ⟨x.toNNReal, zero_le, hx⟩
  let v : Icc (0 : ℝ≥0) T := ⟨min x.toNNReal T, zero_le, min_le_right _ _⟩
  have hv : v = u := Subtype.ext (min_eq_left hx)
  change jointItoIntegralCLM T hB₂ (hestonKernelFamilyLp hα hU hU₀ hUi hMean v) = _
  rw [hv, ← jointBandExtend_hestonKernelFamilyLp u hα hU hU₀ hUi hMean]
  exact (jointItoIntegralCLM_cross_horizon F P hx hB₂ hB hBclock _).symm

/-- The larger-horizon convolution has the same fixed-time L²
value when the Brownian martingale is frozen at a smaller horizon. -/
theorem fixedHestonConvolutionLp_horizon_agrees {T t : ℝ≥0} (ht : t ≤ T) {α : ℝ} (hα : 1/2 < α)
    (hB₂ : ∀ r, MemLp (B r) 2 P) (hB : Martingale B F P)
    (hBclock : Martingale (fun r ω => B r ω ^ 2 - ((min r T : ℝ≥0) : ℝ)) F P)
    (hU : IsStronglyPredictable F U) (hU₀ : ∀ s ω, 0 ≤ U s ω)
    (hUi : ∀ s, Integrable (U s) P) {A : ℝ} (hMean : ∀ s, (∫ ω, U s ω ∂P) ≤ A)
    {x : ℝ} (hx : x.toNNReal ≤ t) :
    fixedHestonConvolutionLp (T := T) hα hB₂ hU hU₀ hUi hMean x =
      fixedHestonConvolutionLp (T := t) (B := fun r => B (min r t))
        hα (fun r => hB₂ (min r t)) hU hU₀ hUi hMean x := by
  have hBt : Martingale (fun r => B (min r t)) F P := martingale_freeze_at hB t
  have hBct : Martingale (fun r ω => B (min r t) ω ^ 2 - ((min r t : ℝ≥0) : ℝ)) F P := by
    simpa only [min_assoc, min_eq_left ht] using martingale_freeze_at hBclock t
  rw [fixedHestonConvolutionLp_eq_at hα hB₂ hB hBclock hU hU₀ hUi hMean (hx.trans ht),
      fixedHestonConvolutionLp_eq_at hα (fun r => hB₂ (min r t)) hBt hBct hU hU₀ hUi hMean hx]
  have hb : (fun r => B (min (min r x.toNNReal) t)) = fun r => B (min r x.toNNReal) := by
    funext r
    rw [min_assoc, min_eq_left hx]
  exact jointIto_of_driver_eq hb.symm _ _ _ _

/-- The full-horizon equation gives the resolvent Brownian row and
its deterministic mean at every positive age. -/
theorem rectangularPulse_resolvent_rows_on_horizon
    {T : ℝ≥0} {α κ σ ε d : ℝ} (hα : 1/2 < α) (hα' : α ≤ 1)
    (hB₂ : ∀ r, MemLp (B r) 2 P)
    (hB : Martingale B F P)
    (hBclock : Martingale (fun r ω => B r ω ^ 2 - ((min r T : ℝ≥0) : ℝ)) F P)
    (hU : IsStronglyPredictable F U) (hU₀ : ∀ s ω, 0 ≤ U s ω)
    (hUi : ∀ s, Integrable (U s) P) {A : ℝ} (hMean : ∀ s, (∫ ω, U s ω ∂P) ≤ A)
    (hLoc : ∀ s ∈ Ioc 0 (T : ℝ), |fractionalSecondKindResolvent α κ s| ≤
      2 * fractionalK α s)
    (v : ℝ → Lp ℝ 2 P) (hvM : StronglyMeasurable v) (hvC : ContinuousOn v (Icc 0 (T : ℝ)))
    (hvU : ∀ s ∈ Ioc (0 : ℝ) (T : ℝ), ⇑(v s) =ᵐ[P] U s.toNNReal)
    (hEq : ∀ s ∈ Icc 0 (T : ℝ), v s =
      volterraSmulConvolution (fractionalK α)
        (fun u => clusterDeterministicInputLp P (rectangularPulseRate ε d) u - κ • v u) s +
        σ • fixedHestonConvolutionLp (T := T) hα hB₂ hU hU₀ hUi hMean s) :
    ∀ s ∈ Ioc (0 : ℝ) (T : ℝ),
      let t := s.toNNReal
      let R := fractionalSecondKindResolvent α κ
      let I := volterraConvolution R (rectangularPulseRate ε d) s
      ∃ f : Lp ℝ 2 (jointPredictableMeasure F P t),
        (⇑f =ᵐ[jointPredictableMeasure F P t] fun p =>
          (σ*R (s-(p.1:ℝ)))*Real.sqrt (U p.1 p.2)) ∧
        (U t =ᵐ[P] fun ω => I+jointItoIntegralCLM t (fun r => hB₂ (min r t)) f ω) ∧
        (∫ ω, U t ω ∂P) = I := by
  intro s hs
  let t := s.toNNReal
  have hst : (t : ℝ) = s := Real.coe_toNNReal s hs.1.le
  have ht : t ≤ T := NNReal.coe_le_coe.mp (hst.trans_le hs.2)
  have htp : 0 < t := NNReal.coe_pos.mp (by rw [hst]; exact hs.1)
  have hBt : Martingale (fun r => B (min r t)) F P := martingale_freeze_at hB t
  have hBct : Martingale (fun r ω => B (min r t) ω ^ 2 - ((min r t : ℝ≥0) : ℝ)) F P := by
    simpa only [min_assoc, min_eq_left ht] using martingale_freeze_at hBclock t
  have hvUt : ⇑(v (t : ℝ)) =ᵐ[P] U t := by rw [hst]; exact hvU s hs
  have hEqShort (x : ℝ) (hx : x ∈ Icc 0 (t : ℝ)) : v x =
      volterraSmulConvolution (fractionalK α)
        (fun u => clusterDeterministicInputLp P (rectangularPulseRate ε d) u - κ • v u) x +
        σ • fixedHestonConvolutionLp (T := t) (B := fun r => B (min r t))
          hα (fun r => hB₂ (min r t)) hU hU₀ hUi hMean x := by
    have hxt : x.toNNReal ≤ t := NNReal.coe_le_coe.mp ((Real.coe_toNNReal x hx.1).trans_le hx.2)
    rw [← fixedHestonConvolutionLp_horizon_agrees ht hα hB₂ hB hBclock hU hU₀ hUi hMean hxt]
    exact hEq x (Icc_subset_Icc_right (NNReal.coe_le_coe.mpr ht) hx)
  have him :=  rectangularPulse_resolvent_equation_and_mean hα hα' htp
    (fun r => hB₂ (min r t)) hBt hBct hU hU₀ hUi hMean
    (fun r hr => hLoc r (Ioc_subset_Ioc_right (NNReal.coe_le_coe.mpr ht) hr)) v hvM
    (hvC.mono (Icc_subset_Icc_right (NNReal.coe_le_coe.mpr ht))) hvUt hEqShort
  simpa only [hst] using him

/-- One full-horizon cluster equation determines the un-tilted mean at
every positive age in that horizon. -/
theorem rectangularPulse_resolvent_old_means_on_horizon
    {T : ℝ≥0} {α κ σ ε d : ℝ} (hα : 1/2 < α) (hα' : α ≤ 1)
    (hB₂ : ∀ r, MemLp (B r) 2 P)
    (hB : Martingale B F P)
    (hBclock : Martingale (fun r ω => B r ω ^ 2 - ((min r T : ℝ≥0) : ℝ)) F P)
    (hU : IsStronglyPredictable F U) (hU₀ : ∀ s ω, 0 ≤ U s ω)
    (hUi : ∀ s, Integrable (U s) P) {A : ℝ} (hMean : ∀ s, (∫ ω, U s ω ∂P) ≤ A)
    (hLoc : ∀ s ∈ Ioc 0 (T : ℝ), |fractionalSecondKindResolvent α κ s| ≤
      2 * fractionalK α s)
    (v : ℝ → Lp ℝ 2 P) (hvM : StronglyMeasurable v) (hvC : ContinuousOn v (Icc 0 (T : ℝ)))
    (hvU : ∀ s ∈ Ioc (0 : ℝ) (T : ℝ), ⇑(v s) =ᵐ[P] U s.toNNReal)
    (hEq : ∀ s ∈ Icc 0 (T : ℝ), v s =
      volterraSmulConvolution (fractionalK α)
        (fun u => clusterDeterministicInputLp P (rectangularPulseRate ε d) u - κ • v u) s +
        σ • fixedHestonConvolutionLp (T := T) hα hB₂ hU hU₀ hUi hMean s) :
    ∀ s ∈ Ioc (0 : ℝ) (T : ℝ),
      (∫ ω, U s.toNNReal ω ∂P) =
        volterraConvolution (fractionalSecondKindResolvent α κ) (rectangularPulseRate ε d) s := by
  intro s hs
  obtain ⟨_,_,_,hm⟩ := rectangularPulse_resolvent_rows_on_horizon hα hα' hB₂ hB hBclock
    hU hU₀ hUi hMean hLoc v hvM hvC hvU hEq s hs
  exact hm

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.fixedHestonConvolutionLp_horizon_agrees
#print axioms RoughHeston.GirsanovPort.rectangularPulse_resolvent_rows_on_horizon
#print axioms RoughHeston.GirsanovPort.rectangularPulse_resolvent_old_means_on_horizon
