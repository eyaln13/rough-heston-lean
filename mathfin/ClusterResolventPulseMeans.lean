import ClusterResolventRepresentation
import ClusterResolventCovariance
import FractionalResolventIdentity
import RectangularPulseMeasure

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Interval

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {B M C U : ℝ≥0 → Ω → ℝ}

noncomputable def clusterDeterministicInputLp (P : Measure Ω) [IsProbabilityMeasure P]
    (j : ℝ → ℝ) (s : ℝ) : Lp ℝ 2 P :=
  j s • (memLp_const (1 : ℝ)).toLp (fun _ => 1)

theorem fractionalSecondKindResolvent_measurable (α κ : ℝ) :
    Measurable (fractionalSecondKindResolvent α κ) :=
  Measurable.tsum fun n => (fractionalK_measurable (((n : ℝ) + 1) * α)).const_mul ((-κ)^n)

private theorem clusterDeterministicInputLp_conv_eq {R j : ℝ → ℝ} {t : ℝ} :
    volterraSmulConvolution R (clusterDeterministicInputLp P j) t =
      clusterDeterministicInputLp P (volterraConvolution R j) t := by
  unfold volterraSmulConvolution clusterDeterministicInputLp volterraConvolution
  simp_rw [smul_smul]
  exact integral_smul_const _ _

private theorem clusterDeterministicInputLp_ae (j : ℝ → ℝ) (s : ℝ) :
    ⇑(clusterDeterministicInputLp P j s) =ᵐ[P] fun _ => j s := by
  let One : Lp ℝ 2 P := (memLp_const (1 : ℝ)).toLp (fun _ => 1)
  have hOne : ⇑One =ᵐ[P] fun _ => 1 := (memLp_const (1 : ℝ)).coeFn_toLp
  filter_upwards [Lp.coeFn_smul (j s) One, hOne] with ω he hω
  change (j s • One) ω = _
  rw [he]
  simp only [Pi.smul_apply, smul_eq_mul, hω, mul_one]

/-- The rectangular pulse produces the deterministic part of the
actual cluster equation, with a centered joint Itô remainder. -/
theorem rectangularPulse_resolvent_equation_and_mean
    {T : ℝ≥0} {α κ σ ε d : ℝ} (hα : 1/2 < α) (hα' : α ≤ 1) (hT : 0 < T)
    (hB₂ : ∀ r, MemLp (B r) 2 P)
    (hB : Martingale B F P)
    (hBclock : Martingale (fun r ω => B r ω ^ 2 - ((min r T : ℝ≥0) : ℝ)) F P)
    (hU : IsStronglyPredictable F U) (hU₀ : ∀ s ω, 0 ≤ U s ω)
    (hUi : ∀ s, Integrable (U s) P) {A : ℝ} (hMean : ∀ s, (∫ ω, U s ω ∂P) ≤ A)
    (hLoc : ∀ s ∈ Ioc 0 (T : ℝ), |fractionalSecondKindResolvent α κ s| ≤
      2 * fractionalK α s)
    (v : ℝ → Lp ℝ 2 P) (hvM : StronglyMeasurable v) (hvC : ContinuousOn v (Icc 0 (T : ℝ)))
    (hvU : ⇑(v (T : ℝ)) =ᵐ[P] U T)
    (hEq : ∀ s ∈ Icc 0 (T : ℝ), v s =
      volterraSmulConvolution (fractionalK α)
        (fun u => clusterDeterministicInputLp P (rectangularPulseRate ε d) u - κ • v u) s +
        σ • fixedHestonConvolutionLp (T := T) hα hB₂ hU hU₀ hUi hMean s) :
    let R := fractionalSecondKindResolvent α κ
    let u := volterraConvolution R (rectangularPulseRate ε d) (T : ℝ)
    ∃ f : Lp ℝ 2 (jointPredictableMeasure F P T),
      (⇑f =ᵐ[jointPredictableMeasure F P T] fun p =>
        (σ * R ((T : ℝ) - (p.1 : ℝ))) * Real.sqrt (U p.1 p.2)) ∧
      (U T =ᵐ[P] fun ω => u + jointItoIntegralCLM T hB₂ f ω) ∧
      (∫ ω, U T ω ∂P) = u := by
  let R := fractionalSecondKindResolvent α κ
  let j := rectangularPulseRate ε d
  let u := volterraConvolution R j (T : ℝ)
  let One : Lp ℝ 2 P := (memLp_const (1 : ℝ)).toLp (fun _ => 1)
  have hj : Measurable j := measurable_const.indicator measurableSet_Ioc
  have hjB (s : ℝ) (hs : s ∈ Icc 0 (T : ℝ)) :
      ‖clusterDeterministicInputLp P j s‖ ≤ |ε/d| * ‖One‖ := by
    change ‖j s • One‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    by_cases h : s ∈ Ioc (0 : ℝ) d
    · simp [j, rectangularPulseRate, indicator_of_mem h]
    · simp [j, rectangularPulseRate, indicator_of_notMem h]
  have hαp : 0 < α := by linarith
  obtain ⟨W, hW, hV⟩ := cluster_resolvent_representation_of_fractional_equation hα hα' T hT
    hB₂ hU hU₀ hUi hMean (fractionalSecondKindResolvent_measurable α κ) hLoc
    (fun s hs => fractionalSecondKindResolvent_identity hαp hs.1)
    v (clusterDeterministicInputLp P j) hvM hvC
    (hj.stronglyMeasurable.smul stronglyMeasurable_const) hjB hEq
  let f := σ • W
  have hf : ⇑f =ᵐ[jointPredictableMeasure F P T] fun p =>
      (σ * R ((T : ℝ) - (p.1 : ℝ))) * Real.sqrt (U p.1 p.2) := by
    filter_upwards [Lp.coeFn_smul σ W, hW] with p hp hp'
    change (σ • W) p = _
    rw [hp, Pi.smul_apply, smul_eq_mul, hp', mul_assoc]
  let I := jointItoIntegralCLM (𝒢 := F) T hB₂
  have hV' : v (T : ℝ) = clusterDeterministicInputLp P (volterraConvolution R j) (T : ℝ) + I f := by
    rw [hV, clusterDeterministicInputLp_conv_eq]
    change _ = _ + I (σ • W)
    rw [map_smul]
  have hUt : U T =ᵐ[P] fun ω => u + I f ω := by
    refine hvU.symm.trans ?_
    rw [hV']
    filter_upwards [Lp.coeFn_add
      (clusterDeterministicInputLp P (volterraConvolution R j) (T : ℝ)) (I f),
      clusterDeterministicInputLp_ae (P := P) (volterraConvolution R j) (T : ℝ)] with ω ha hb
    rw [ha, Pi.add_apply, hb]
  refine ⟨f, hf, hUt, ?_⟩
  have hi : Integrable (⇑(I f)) P := (Lp.memLp (I f)).integrable (by norm_num)
  rw [integral_congr_ae hUt, integral_add (integrable_const u) hi, integral_const,
    integral_jointItoIntegralCLM_eq_zero T hB₂ hB hBclock f]
  simp [u, R, j]

/-- Transfer the mean pairing from the fixed nonnegative clock to
the real-time interval used by the analytic pulse estimates. -/
theorem cluster_covariance_integral_realTime {T : ℝ≥0} {R : ℝ → ℝ} (hR : Measurable R)
    (hU : IsStronglyPredictable F U) :
    (∫ s, R ((T : ℝ) - s) * (∫ ω, U s ω ∂P) ∂hestonTimeMeasure T) =
    ∫ s in Ioc (0 : ℝ) (T : ℝ), R ((T : ℝ) - s) * (∫ ω, U s.toNNReal ω ∂P) := by
  have hUm : Measurable (fun s => ∫ ω, U s ω ∂P) :=
    (hU.mono F.predictable_le_prod).integral_prod_right'.measurable
  have hg : Measurable (fun s : ℝ≥0 => R ((T : ℝ) - s) * (∫ ω, U s ω ∂P)) :=
    (hR.comp (measurable_const.sub measurable_subtype_coe)).mul hUm
  rw [hestonTimeMeasure, integral_map continuous_real_toNNReal.measurable.aemeasurable
    hg.aestronglyMeasurable, Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [Real.coe_toNNReal _ hs.1.le]

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.fractionalSecondKindResolvent_measurable
#print axioms RoughHeston.GirsanovPort.rectangularPulse_resolvent_equation_and_mean
#print axioms RoughHeston.GirsanovPort.cluster_covariance_integral_realTime
