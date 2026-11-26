import FixedHestonHorizon
import HestonFubiniIntegrability

open MeasureTheory Filter Set
open scoped MeasureTheory Topology NNReal

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℝ≥0 m} {B V : ℝ≥0 → Ω → ℝ} {α v₀ κ θ σ : ℝ}

/-- The cutoff-limit definition is invariant under almost sure equality
of the candidate terminal convolutions. -/
theorem IsHestonConvolutionAt.congr_ae {t : ℝ≥0} {z z' : Ω → ℝ}
    (h : IsHestonConvolutionAt μ α t B V z) (heq : z =ᵐ[μ] z') :
    IsHestonConvolutionAt μ α t B V z' := by
  obtain ⟨hz, J, hJ, hj⟩ := h
  exact ⟨hz.ae_eq heq, J, hJ, hj.congr fun n =>
    eLpNorm_congr_ae (EventuallyEq.rfl.sub heq)⟩

/-- The deterministic drift term in the direct variance equation. -/
noncomputable def hestonVarianceDrift (α κ θ : ℝ) (V : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ s in (0 : ℝ)..(t : ℝ), hestonKernel α ((t : ℝ) - s) * (κ * (θ - V s.toNNReal ω))

/-- If the direct equation holds almost surely at each fixed time with
the specified Itô convolution, the residual of the variance path gives
a version of the convolution for which the equation holds simultaneously
throughout the horizon. -/
theorem isHestonVarianceSolution_of_fixed_time_equations {T : ℝ≥0}
    (hσ : σ ≠ 0) (hVa : StronglyAdapted 𝒢 V)
    (hVc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => V t ω) (Icc 0 T))
    (hVn : ∀ᵐ ω ∂μ, ∀ t ≤ T, 0 ≤ V t ω)
    (hZ : ∀ t ≤ T, ∃ z : Ω → ℝ, IsHestonConvolutionAt μ α t B V z ∧
      V t =ᵐ[μ] fun ω => v₀ + hestonVarianceDrift α κ θ V t ω + σ * z ω) :
    IsHestonVarianceSolution μ 𝒢 T α v₀ κ θ σ B V := by
  let Z (t : ℝ≥0) (ω : Ω) :=
    (V t ω - (v₀ + hestonVarianceDrift α κ θ V t ω)) / σ
  refine ⟨hVa, hVc, hVn, Z, ?_, ?_⟩
  · intro t ht
    obtain ⟨z, hiz, hz⟩ := hZ t ht
    apply hiz.congr_ae
    filter_upwards [hz] with ω hω
    change z ω = (V t ω - (v₀ + hestonVarianceDrift α κ θ V t ω)) / σ
    apply (eq_div_iff hσ).2
    linarith
  · exact ae_of_all μ fun ω t _ => by
      change V t ω = v₀ + hestonVarianceDrift α κ θ V t ω + σ * Z t ω
      have hx : Z t ω * σ = V t ω - (v₀ + hestonVarianceDrift α κ θ V t ω) :=
        (div_mul_cancel₀ _ hσ)
      linarith

open MathFin.StochasticFubini in
/-- Weighted time integration of a Bochner L² path is represented by
integration along sample paths. The weight may be singular and integrable. -/
theorem coeFn_integral_weighted_L2_path_ae {S : Type*} [MeasurableSpace S]
    {ν : Measure S} [SFinite ν] [IsFiniteMeasure μ]
    {A : S → Lp ℝ 2 μ} {a : S → Ω → ℝ} {k : S → ℝ} (hk : Measurable k)
    (ha : Measurable (Function.uncurry a))
    (hA : Integrable (fun s => k s • A s) ν)
    (hrep : ∀ s, ⇑(A s) =ᵐ[μ] a s) :
    ⇑(∫ s, k s • A s ∂ν) =ᵐ[μ] fun ω => ∫ s, k s * a s ω ∂ν := by
  let F (s : S) := k s • A s
  let f (s : S) (ω : Ω) := k s * a s ω
  have hf : Measurable (Function.uncurry f) := (hk.comp measurable_fst).mul ha
  have hF (s : S) : ⇑(F s) =ᵐ[μ] f s := by
    filter_upwards [Lp.coeFn_smul (k s) (A s), hrep s] with ω hω haω
    simpa only [F, f, Pi.smul_apply, smul_eq_mul, haω] using hω
  exact coeFn_integral_ae_eq F hA f
    (jointIntegrable_of_integrable_L2_family F hA hf.aestronglyMeasurable (ae_of_all ν hF)) hF

end RoughHeston

#print axioms RoughHeston.IsHestonConvolutionAt.congr_ae
#print axioms RoughHeston.isHestonVarianceSolution_of_fixed_time_equations

#print axioms RoughHeston.coeFn_integral_weighted_L2_path_ae
