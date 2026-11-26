import TiltingItoPairing
import HestonFubiniKernel

open MeasureTheory ProbabilityTheory Set Filter
open scoped MeasureTheory ProbabilityTheory NNReal ENNReal

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℝ≥0 m} {M D V : ℝ≥0 → Ω → ℝ}

/-- The preterminal mean under a bounded density martingale satisfies
the tilted integral equation. The drift uses the conditional expectation
of the terminal density and the noise uses the joint Itô pairing. -/
theorem tiltedVarianceMean_integral_equation [IsProbabilityMeasure μ] (T : ℝ≥0)
    (hM₂ : ∀ u, MemLp (M u) 2 μ) (hM : Martingale M 𝒢 μ)
    (hclock : Martingale (fun u ω => M u ω ^ 2 - ((min u T : ℝ≥0) : ℝ)) 𝒢 μ)
    (hD : Martingale D 𝒢 μ) {C : ℝ} (hDbdd : ∀ᵐ ω ∂μ, ‖D T ω‖ ≤ C)
    (hDmean : (∫ ω, D T ω ∂μ) = 1)
    (hVm : StronglyAdapted 𝒢 V) (hVi : ∀ u, Integrable (V u) μ)
    (hVnonneg : ∀ u ω, 0 ≤ V u ω) (σ κ b v₀ : ℝ)
    (k w : ℝ≥0 → ℝ) (X Y : Lp ℝ 2 (jointPredictableMeasure 𝒢 μ T))
    (hDrep : D T =ᵐ[μ] fun ω => 1 - σ * jointItoIntegralCLM T hM₂ Y ω)
    (hX : ⇑X =ᵐ[jointPredictableMeasure 𝒢 μ T] fun z => k z.1 * Real.sqrt (V z.1 z.2))
    (hY : ⇑Y =ᵐ[jointPredictableMeasure 𝒢 μ T]
      fun z => D z.1 z.2 * w z.1 * Real.sqrt (V z.1 z.2))
    (hXm : StronglyMeasurable[𝒢.predictable] (fun z => k z.1 * Real.sqrt (V z.1 z.2)))
    (hYm : StronglyMeasurable[𝒢.predictable]
      (fun z => D z.1 z.2 * w z.1 * Real.sqrt (V z.1 z.2))) :
    let ν := MathFin.ItoIntegralCLM.timeMeasureHorizon T
    let φ (u : ℝ≥0) := ∫ ω, D u ω * V u ω ∂μ
    Integrable (fun z : ℝ≥0 × Ω => k z.1 * (b-κ*V z.1 z.2)) (ν.prod μ) →
    (V T =ᵐ[μ] fun ω =>
      v₀ + (∫ u, k u * (b-κ*V u ω) ∂ν) + σ * jointItoIntegralCLM T hM₂ X ω) →
    φ T = v₀ + (∫ u, k u * (b-κ*φ u) ∂ν) -
      σ^2 * (∫ u, (k u*w u)*φ u ∂ν) := by
  dsimp only
  intro hJoint hVrep
  let ν := MathFin.ItoIntegralCLM.timeMeasureHorizon T
  let φ (u : ℝ≥0) := ∫ ω, D u ω * V u ω ∂μ
  let F (u : ℝ≥0) (ω : Ω) := b-κ*V u ω
  let J (ω : Ω) := ∫ u, k u * F u ω ∂ν
  let N (ω : Ω) := σ * jointItoIntegralCLM T hM₂ X ω
  have hJ : Integrable J μ := hJoint.integral_prod_right
  have hN : Integrable N μ :=
    ((Lp.memLp (jointItoIntegralCLM T hM₂ X)).integrable one_le_two).const_mul σ
  have hDm : AEStronglyMeasurable (D T) μ := ((hD.stronglyMeasurable T).mono (𝒢.le T)).aestronglyMeasurable
  have hDJ : Integrable (fun ω => D T ω * J ω) μ := hJ.bdd_mul hDm hDbdd
  have hDN : Integrable (fun ω => D T ω * N ω) μ := hN.bdd_mul hDm hDbdd
  have hDc := (hD.integrable T).mul_const v₀
  have hDyn : (∫ ω, D T ω * J ω ∂μ) =
      ∫ u, k u * (b-κ*φ u) ∂ν := by
    have hInside : ∀ᵐ u ∂ν, u ≤ T := by
      simpa only [hestonTimeMeasure_eq_horizon] using
        (ae_time_lt_hestonTimeMeasure T).mono fun _ h => h.le
    have hPast : ∀ᵐ u ∂ν, u ≤ T ∧ AEStronglyMeasurable[𝒢 u] (F u) μ ∧ Integrable (F u) μ := by
      filter_upwards [hInside] with u hu
      exact ⟨hu, (stronglyMeasurable_const.sub ((hVm u).const_mul κ)).aestronglyMeasurable,
        (integrable_const b).sub ((hVi u).const_mul κ)⟩
    rw [integral_time_weighted_martingale_pairing_of_bounded ν hD T k hPast hDbdd hJoint]
    apply integral_congr_ae
    filter_upwards [hInside] with u hu
    have hVD : Integrable (fun ω => D u ω * V u ω) μ := by
      have hmul : Integrable (D T * V u) μ := (hVi u).bdd_mul hDm hDbdd
      exact integrable_condExp.congr
        (condExp_martingale_mul_past hD hu (hVm u).aestronglyMeasurable hmul)
    have hnorm : (∫ ω, D u ω ∂μ) = 1 := by
      calc
        _ = ∫ ω, μ[D T | 𝒢 u] ω ∂μ := integral_congr_ae (hD.condExp_ae_eq hu).symm
        _ = _ := (integral_condExp (𝒢.le u)).trans hDmean
    congr 1
    change (∫ ω, D u ω * (b-κ*V u ω) ∂μ) = b-κ*φ u
    calc
      _ = ∫ ω, b * D u ω - κ*(D u ω * V u ω) ∂μ :=
        integral_congr_ae (Eventually.of_forall fun _ => by ring)
      _ = _ := by
        rw [integral_sub ((hD.integrable u).const_mul b) (hVD.const_mul κ),
          integral_const_mul, integral_const_mul, hnorm, mul_one]
  have hNoise : (∫ ω, D T ω * N ω ∂μ) =
      -(σ^2) * (∫ u, (k u*w u)*φ u ∂ν) :=
    integral_density_mul_heston_stochastic_term T hM₂ hM hclock σ X Y k w
      D V hVnonneg hDrep hX hY hXm hYm
  change φ T = _
  calc
    _ = ∫ ω, (D T ω * v₀ + D T ω * J ω) + D T ω * N ω ∂μ := by
      apply integral_congr_ae
      filter_upwards [hVrep] with ω hω
      change V T ω = v₀ + J ω + N ω at hω
      rw [hω]
      ring
    _ = _ := by
      have hI := integral_add (hDc.add hDJ) hDN
      simp only [Pi.add_apply] at hI
      rw [hI, integral_add hDc hDJ, integral_mul_const, hDmean, one_mul, hDyn, hNoise]
      ring

end RoughHeston

#print axioms RoughHeston.tiltedVarianceMean_integral_equation
