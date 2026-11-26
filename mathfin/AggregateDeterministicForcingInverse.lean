import ClusterPulseInverse

/-! Splitting off the explicit deterministic convolution in the
fractional inverse equation. The drift may depend on the entire
aggregate variance, and the deterministic immigration may jump. -/

open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston.GirsanovPort

set_option maxHeartbeats 1100000

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {B U : ℝ≥0 → Ω → ℝ}

/-- An arbitrary deterministic input can be subtracted before applying
fractional inversion. Keeping it separate is useful for tightness of
approximations with uneven immigration rates. -/
theorem heston_L2_centered_of_inverse
    {T : ℝ≥0} {α σ : ℝ} (hα : 1/2 < α) (hα' : α < 1) (hT : 0 < T)
    (hB₂ : ∀ r, MemLp (B r) 2 P) (hB : Martingale B F P)
    (hClock : Martingale (fun r ω => B r ω^2-((min r T : ℝ≥0):ℝ)) F P)
    (hU : IsStronglyPredictable F U) (hU₀ : ∀ s ω, 0 ≤ U s ω) (hUi : ∀ s, Integrable (U s) P)
    {A : ℝ} (hMean : ∀ s, (∫ ω, U s ω ∂P) ≤ A)
    {v g j : ℝ → Lp ℝ 2 P}
    (hv : StronglyMeasurable v) (hvc : ContinuousOn v (Icc 0 (T:ℝ)))
    (hg : StronglyMeasurable g) (hgc : ContinuousOn g (Icc 0 (T:ℝ)))
    (hj : StronglyMeasurable j) (hjI : ∀ u ≤ T, IntegrableOn j (Ioc 0 (u:ℝ)))
    (hD : Continuous (volterraSmulConvolution (fractionalK α) j))
    (hInv : ∀ u : ℝ≥0, u ≤ T →
      let ha := sqrt_variance_memLp_joint T hU hU₀ hUi hMean
      volterraSmulConvolution (fractionalL α) v (u:ℝ) =
        (∫ s in Ioc (0:ℝ) (u:ℝ), j s+g s) +
        σ • jointItoIntegralCLM T hB₂
          (jointAmplitudeSectionLp (a := fun s ω => Real.sqrt (U s ω)) u ha)) :
    ∀ t ∈ Icc (0:ℝ) T,
      v t - volterraSmulConvolution (fractionalK α) j t =
        volterraSmulConvolution (hestonKernel α) g t +
        σ • fixedHestonConvolutionLp (T := T) hα hB₂ hU hU₀ hUi hMean t := by
  let D := volterraSmulConvolution (fractionalK α) j
  let R := fun s => v s-D s
  have hRc : ContinuousOn R (Icc 0 (T:ℝ)) := hvc.sub hD.continuousOn
  have hRm : StronglyMeasurable R := hv.sub hD.stronglyMeasurable
  apply heston_L2_of_inverse hα hα' hT hB₂ hB hClock hU hU₀ hUi hMean hRm hRc hg hgc
  intro u hu
  let ν := volume.restrict (Ioc (0:ℝ) (u:ℝ))
  have hSub : Icc 0 (u:ℝ) ⊆ Icc 0 (T:ℝ) := Icc_subset_Icc_right (NNReal.coe_le_coe.mpr hu)
  have hK := fractionalL_reflected_integrableOn_Ioc hα' u.coe_nonneg
  have hvK := pulse_weighted_reflected_integrableOn (fractionalL_measurable α) hK hv (hvc.mono hSub)
  have hDK := pulse_weighted_reflected_integrableOn (fractionalL_measurable α) hK
    hD.stronglyMeasurable hD.continuousOn
  have hI : IntegrableOn g (Ioc 0 (u:ℝ)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le u.coe_nonneg).1
      ((hgc.mono hSub).intervalIntegrable_of_Icc u.coe_nonneg)
  have hDKIdentity : volterraSmulConvolution (fractionalL α) D (u:ℝ) = ∫ s, j s ∂ν :=
    fractional_volterra_smul_inverts_drift (by linarith : 0 < α) hα' hj (hjI u hu)
  have hR : volterraSmulConvolution (fractionalL α) R (u:ℝ) =
      volterraSmulConvolution (fractionalL α) v (u:ℝ) -
      volterraSmulConvolution (fractionalL α) D (u:ℝ) := by
    unfold volterraSmulConvolution
    simp only [R, smul_sub]
    exact integral_sub hvK hDK
  have h := hInv u hu
  dsimp only at h
  rw [hR, h, hDKIdentity, integral_add (hjI u hu) hI]
  abel

#print axioms RoughHeston.GirsanovPort.heston_L2_centered_of_inverse

end RoughHeston.GirsanovPort
