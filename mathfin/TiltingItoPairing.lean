import JointItoAssembly
import DensityMartingalePairing
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! The stochastic part of a preterminal size-biased expectation. -/

open MeasureTheory ProbabilityTheory Filter
open scoped MeasureTheory NNReal ENNReal InnerProductSpace

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  [IsFiniteMeasure μ] {𝒢 : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}

private theorem real_l2_inner_eq_integral {X : Type*} {mX : MeasurableSpace X}
    {ν : Measure X} (f g : Lp ℝ 2 ν) :
    ⟪f, g⟫_ℝ = ∫ x, f x * g x ∂ν := by
  rw [L2.inner_def]
  congr 1
  funext x
  change g x * f x = f x * g x
  exact mul_comm _ _

/-- Polarizing the fixed-horizon joint Itô isometry gives the scalar
pairing identity for arbitrary square-integrable predictable integrands. -/
theorem integral_jointItoIntegralCLM_product (T : ℝ≥0)
    (hM₂ : ∀ t, MemLp (M t) 2 μ) (hM : Martingale M 𝒢 μ)
    (hclock : Martingale (fun t ω => M t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) 𝒢 μ)
    (f g : Lp ℝ 2 (jointPredictableMeasure 𝒢 μ T)) :
    (∫ ω, jointItoIntegralCLM T hM₂ f ω * jointItoIntegralCLM T hM₂ g ω ∂μ) =
      ∫ z, f z * g z ∂jointPredictableMeasure 𝒢 μ T := by
  let I : Lp ℝ 2 (jointPredictableMeasure 𝒢 μ T) →ₗᵢ[ℝ] Lp ℝ 2 μ :=
    { toLinearMap := (jointItoIntegralCLM T hM₂).toLinearMap
      norm_map' := jointItoIntegralCLM_norm T hM₂ hM hclock }
  have hI (x : Lp ℝ 2 (jointPredictableMeasure 𝒢 μ T)) :
      I x = jointItoIntegralCLM T hM₂ x := rfl
  simpa only [hI, real_l2_inner_eq_integral] using I.inner_map_map f g

private theorem integral_jointItoSimple_eq_zero
    (hM₂ : ∀ t, MemLp (M t) 2 μ) (hM : Martingale M 𝒢 μ)
    (V : SimpleProcess ℝ 𝒢) :
    (∫ ω, jointItoSimple M V ω ∂μ) = 0 := by
  have hWeight₂ (p : ℝ≥0 × ℝ≥0) : MemLp (V.value p) 2 μ :=
    (memLp_top_of_bound ((V.measurable_value p).mono (𝒢.le p.1) le_rfl).aestronglyMeasurable
      V.valueBound (Eventually.of_forall fun ω => by
        simpa only [Real.norm_eq_abs] using V.value_le_valueBound p ω)).mono_exponent le_top
  let term (p : ℝ≥0 × ℝ≥0) (ω : Ω) := V.value p ω * (M p.2 ω - M p.1 ω)
  have hTerm (p : ℝ≥0 × ℝ≥0) : Integrable (term p) μ :=
    (hWeight₂ p).integrable_mul ((hM₂ p.2).sub (hM₂ p.1))
  change (∫ ω, ∑ p ∈ V.value.support, term p ω ∂μ) = 0
  rw [integral_finsetSum _ (fun p _ => hTerm p)]
  apply Finset.sum_eq_zero
  intro p hp
  have ha : Integrable (fun ω => V.value p ω * M p.1 ω) μ :=
    (hWeight₂ p).integrable_mul (hM₂ p.1)
  have hb : Integrable (fun ω => V.value p ω * M p.2 ω) μ :=
    (hWeight₂ p).integrable_mul (hM₂ p.2)
  simp only [term, mul_sub]
  rw [integral_sub hb ha, sub_eq_zero]
  simpa only [mul_comm] using integral_martingale_mul_past_of_memLp_two hM
    (V.le_of_mem_support_value p hp) (V.measurable_value p).stronglyMeasurable.aestronglyMeasurable
    (hWeight₂ p) (hM₂ p.2)

/-- The completed Itô integral has mean zero, by continuity of its
(L^2) pairing with the constant one function and density. -/
theorem integral_jointItoIntegralCLM_eq_zero (T : ℝ≥0)
    (hM₂ : ∀ t, MemLp (M t) 2 μ) (hM : Martingale M 𝒢 μ)
    (hclock : Martingale (fun t ω => M t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) 𝒢 μ)
    (f : Lp ℝ 2 (jointPredictableMeasure 𝒢 μ T)) :
    (∫ ω, jointItoIntegralCLM T hM₂ f ω ∂μ) = 0 := by
  let One : Lp ℝ 2 μ := (memLp_const (1 : ℝ)).toLp (fun _ => 1)
  have hOne : ⇑One =ᵐ[μ] fun _ => 1 := (memLp_const (1 : ℝ)).coeFn_toLp
  have hInner (g : Lp ℝ 2 μ) : ⟪g, One⟫_ℝ = ∫ ω, g ω ∂μ := by
    rw [real_l2_inner_eq_integral]
    apply integral_congr_ae
    filter_upwards [hOne] with ω hω
    simp [hω]
  rw [← hInner]
  refine DenseRange.induction_on (jointSimpleAssembly_denseRange (μ := μ) T 𝒢)
    (p := fun x => ⟪jointItoIntegralCLM T hM₂ x, One⟫_ℝ = 0) f ?_ ?_
  · exact isClosed_eq ((jointItoIntegralCLM T hM₂).continuous.inner continuous_const)
      continuous_const
  · intro V
    rw [jointItoIntegralCLM_agrees T hM₂ hM hclock, hInner]
    calc
      _ = ∫ ω, jointItoSimple M V.val ω ∂μ :=
        integral_congr_ae (memLp_jointItoSimple hM₂ V.val).coeFn_toLp
      _ = 0 := integral_jointItoSimple_eq_zero hM₂ hM V.val

/-- The fixed-horizon Itô integral is measurable in the joint filtration
at the endpoint. -/
theorem aestronglyMeasurable_jointItoIntegralCLM (T : ℝ≥0)
    (hM₂ : ∀ t, MemLp (M t) 2 μ) (hM : Martingale M 𝒢 μ)
    (hclock : Martingale (fun t ω => M t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) 𝒢 μ)
    (f : Lp ℝ 2 (jointPredictableMeasure 𝒢 μ T)) :
    AEStronglyMeasurable[𝒢 T] (jointItoIntegralCLM T hM₂ f) μ := by
  refine DenseRange.induction_on (jointSimpleAssembly_denseRange (μ := μ) T 𝒢)
    (p := fun x => AEStronglyMeasurable[𝒢 T] (jointItoIntegralCLM T hM₂ x) μ) f ?_ ?_
  · exact IsClosed.preimage (jointItoIntegralCLM T hM₂).continuous
      (isClosed_aestronglyMeasurable (p := (2 : ℝ≥0∞)) (F := ℝ) (μ := μ) (𝒢.le T))
  · intro A
    rw [jointItoIntegralCLM_agrees T hM₂ hM hclock]
    have hSimple : StronglyMeasurable[𝒢 T] (jointItoSimple M A.val) := by
      change StronglyMeasurable[𝒢 T]
        (fun ω => ∑ p ∈ A.val.value.support, A.val.value p ω * (M p.2 ω - M p.1 ω))
      refine Finset.stronglyMeasurable_fun_sum _ fun p hp => ?_
      have hb := A.property p hp
      have ha := (A.val.le_of_mem_support_value p hp).trans hb
      exact ((A.val.measurable_value p).stronglyMeasurable.mono (𝒢.mono ha)).mul
        (((hM.stronglyMeasurable p.2).mono (𝒢.mono hb)).sub
          ((hM.stronglyMeasurable p.1).mono (𝒢.mono ha)))
    exact hSimple.aestronglyMeasurable.congr (memLp_jointItoSimple hM₂ A.val).coeFn_toLp.symm

/-- Pairing `σ I(f)` with a density represented by `1 - σ I(g)`
produces exactly minus `σ²` times the predictable pairing. -/
theorem integral_density_mul_jointItoIntegralCLM (T : ℝ≥0)
    (hM₂ : ∀ t, MemLp (M t) 2 μ) (hM : Martingale M 𝒢 μ)
    (hclock : Martingale (fun t ω => M t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) 𝒢 μ)
    (σ : ℝ) (f g : Lp ℝ 2 (jointPredictableMeasure 𝒢 μ T))
    {D : Ω → ℝ} (hD : D =ᵐ[μ] fun ω => 1 - σ * jointItoIntegralCLM T hM₂ g ω) :
    (∫ ω, D ω * (σ * jointItoIntegralCLM T hM₂ f ω) ∂μ) =
      -(σ ^ 2) * (∫ z, g z * f z ∂jointPredictableMeasure 𝒢 μ T) := by
  let I := jointItoIntegralCLM (𝒢 := 𝒢) T hM₂
  have hf : Integrable (fun ω => I f ω) μ := (Lp.memLp (I f)).integrable one_le_two
  have hgf : Integrable (fun ω => I g ω * I f ω) μ :=
    (Lp.memLp (I g)).integrable_mul (Lp.memLp (I f))
  have hσf : Integrable (fun ω => σ * I f ω) μ := hf.const_mul σ
  have hσgf : Integrable (fun ω => σ ^ 2 * (I g ω * I f ω)) μ := hgf.const_mul (σ ^ 2)
  calc
    _ = ∫ ω, σ * I f ω - σ ^ 2 * (I g ω * I f ω) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hD] with ω hω
      rw [hω]
      change (1 - σ * I g ω) * (σ * I f ω) = _
      ring
    _ = _ := by
      rw [integral_sub hσf hσgf, integral_const_mul, integral_const_mul]
      dsimp only [I]
      rw [integral_jointItoIntegralCLM_eq_zero T hM₂ hM hclock,
        integral_jointItoIntegralCLM_product T hM₂ hM hclock]
      ring

/-- Fubini converts the predictable pairing to a time integral of the
current density paired with the variance. The deterministic functions
`k` and `w` can be the two backward kernels at the respective horizons. -/
theorem integral_jointHeston_predictable_pairing (T : ℝ≥0)
    (f g : Lp ℝ 2 (jointPredictableMeasure 𝒢 μ T))
    (k w : ℝ≥0 → ℝ) (D V : ℝ≥0 → Ω → ℝ) (hV : ∀ u ω, 0 ≤ V u ω)
    (hf : ⇑f =ᵐ[jointPredictableMeasure 𝒢 μ T] fun z => k z.1 * Real.sqrt (V z.1 z.2))
    (hg : ⇑g =ᵐ[jointPredictableMeasure 𝒢 μ T]
      fun z => D z.1 z.2 * w z.1 * Real.sqrt (V z.1 z.2))
    (hfmeas : StronglyMeasurable[𝒢.predictable]
      (fun z => k z.1 * Real.sqrt (V z.1 z.2)))
    (hgmeas : StronglyMeasurable[𝒢.predictable]
      (fun z => D z.1 z.2 * w z.1 * Real.sqrt (V z.1 z.2))) :
    (∫ z, g z * f z ∂jointPredictableMeasure 𝒢 μ T) =
      ∫ u, (k u * w u) * (∫ ω, D u ω * V u ω ∂μ)
        ∂MathFin.ItoIntegralCLM.timeMeasureHorizon T := by
  let F : ℝ≥0 × Ω → ℝ := fun z => k z.1 * Real.sqrt (V z.1 z.2)
  let G : ℝ≥0 × Ω → ℝ := fun z => D z.1 z.2 * w z.1 * Real.sqrt (V z.1 z.2)
  let H : ℝ≥0 × Ω → ℝ := fun z => G z * F z
  have hAE : (fun z => g z * f z) =ᵐ[jointPredictableMeasure 𝒢 μ T] H := hg.mul hf
  have hITrim : Integrable H (jointPredictableMeasure 𝒢 μ T) :=
    ((Lp.memLp g).integrable_mul (Lp.memLp f)).congr hAE
  have hIProd : Integrable H ((MathFin.ItoIntegralCLM.timeMeasureHorizon T).prod μ) :=
    integrable_of_integrable_trim 𝒢.predictable_le_prod hITrim
  calc
    _ = ∫ z, H z ∂jointPredictableMeasure 𝒢 μ T := integral_congr_ae hAE
    _ = ∫ z, H z ∂(MathFin.ItoIntegralCLM.timeMeasureHorizon T).prod μ :=
      (integral_trim 𝒢.predictable_le_prod (hgmeas.mul hfmeas)).symm
    _ = ∫ u, ∫ ω, H (u, ω) ∂μ ∂MathFin.ItoIntegralCLM.timeMeasureHorizon T :=
      integral_prod H hIProd
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with u
      have hFactor (ω : Ω) : H (u, ω) = (k u * w u) * (D u ω * V u ω) := by
        dsimp [H, G, F]
        calc
          _ = (k u * w u) * (D u ω * (Real.sqrt (V u ω)) ^ 2) := by ring
          _ = _ := by rw [Real.sq_sqrt (hV u ω)]
      simp only [hFactor, integral_const_mul]

/-- The stochastic part of the tilted mean at a preterminal horizon.
Here `f` represents `k √V` and `g` represents `D w √V`. -/
theorem integral_density_mul_heston_stochastic_term (T : ℝ≥0)
    (hM₂ : ∀ t, MemLp (M t) 2 μ) (hM : Martingale M 𝒢 μ)
    (hclock : Martingale (fun t ω => M t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) 𝒢 μ)
    (σ : ℝ) (f g : Lp ℝ 2 (jointPredictableMeasure 𝒢 μ T))
    (k w : ℝ≥0 → ℝ) (D V : ℝ≥0 → Ω → ℝ) (hV : ∀ u ω, 0 ≤ V u ω)
    (hD : D T =ᵐ[μ] fun ω => 1 - σ * jointItoIntegralCLM T hM₂ g ω)
    (hf : ⇑f =ᵐ[jointPredictableMeasure 𝒢 μ T] fun z => k z.1 * Real.sqrt (V z.1 z.2))
    (hg : ⇑g =ᵐ[jointPredictableMeasure 𝒢 μ T]
      fun z => D z.1 z.2 * w z.1 * Real.sqrt (V z.1 z.2))
    (hfmeas : StronglyMeasurable[𝒢.predictable]
      (fun z => k z.1 * Real.sqrt (V z.1 z.2)))
    (hgmeas : StronglyMeasurable[𝒢.predictable]
      (fun z => D z.1 z.2 * w z.1 * Real.sqrt (V z.1 z.2))) :
    (∫ ω, D T ω * (σ * jointItoIntegralCLM T hM₂ f ω) ∂μ) =
      -(σ ^ 2) * (∫ u, (k u * w u) * (∫ ω, D u ω * V u ω ∂μ)
        ∂MathFin.ItoIntegralCLM.timeMeasureHorizon T) := by
  rw [integral_density_mul_jointItoIntegralCLM T hM₂ hM hclock σ f g hD,
    integral_jointHeston_predictable_pairing T f g k w D V hV hf hg hfmeas hgmeas]

/-- Under the terminal density measure, the expectation of the stochastic
term equals its preterminal pairing. -/
theorem integral_densityTilt_jointItoIntegralCLM (T t : ℝ≥0) (hTt : T ≤ t)
    (hM₂ : ∀ u, MemLp (M u) 2 μ) (hM : Martingale M 𝒢 μ)
    (hclock : Martingale (fun u ω => M u ω ^ 2 - ((min u T : ℝ≥0) : ℝ)) 𝒢 μ)
    (σ : ℝ) (f g : Lp ℝ 2 (jointPredictableMeasure 𝒢 μ T))
    {D : ℝ≥0 → Ω → ℝ} (hD : Martingale D 𝒢 μ) (hDt₂ : MemLp (D t) 2 μ)
    (hNonneg : ∀ᵐ ω ∂μ, 0 ≤ D t ω)
    (hDRep : D T =ᵐ[μ] fun ω => 1 - σ * jointItoIntegralCLM T hM₂ g ω) :
    (∫ ω, σ * jointItoIntegralCLM T hM₂ f ω ∂μ.withDensity (fun ω => ENNReal.ofReal (D t ω))) =
      -(σ ^ 2) * (∫ z, g z * f z ∂jointPredictableMeasure 𝒢 μ T) := by
  have hX : AEStronglyMeasurable[𝒢 T] (fun ω => σ * jointItoIntegralCLM T hM₂ f ω) μ :=
    aestronglyMeasurable_const.mul (aestronglyMeasurable_jointItoIntegralCLM T hM₂ hM hclock f)
  have hX₂ : MemLp (fun ω => σ * jointItoIntegralCLM T hM₂ f ω) 2 μ :=
    (Lp.memLp (jointItoIntegralCLM T hM₂ f)).const_mul σ
  rw [integral_densityTilt_past hD hTt hNonneg hX (hDt₂.integrable_mul hX₂)]
  exact integral_density_mul_jointItoIntegralCLM T hM₂ hM hclock σ f g hDRep

#print axioms RoughHeston.integral_jointItoIntegralCLM_product
#print axioms RoughHeston.integral_jointItoIntegralCLM_eq_zero
#print axioms RoughHeston.integral_density_mul_jointItoIntegralCLM
#print axioms RoughHeston.integral_jointHeston_predictable_pairing

#print axioms RoughHeston.integral_density_mul_heston_stochastic_term

#print axioms RoughHeston.aestronglyMeasurable_jointItoIntegralCLM
#print axioms RoughHeston.integral_densityTilt_jointItoIntegralCLM

end RoughHeston
