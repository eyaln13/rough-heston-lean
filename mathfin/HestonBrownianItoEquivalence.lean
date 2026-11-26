import VarianceSolutionOfIto
import FiniteBrownianFrozenMartingales

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} {T : ℝ≥0} {B V : ℝ≥0 → Ω → ℝ}
  {α v₀ κ θ σ : ℝ}

/-- The Heston convolution of a regular variance row is the ordinary
predictable L² Itô integral of its fractional-kernel section, extended by
zero to the observation horizon. Only the driver values up to that horizon
enter the integral. -/
noncomputable def hestonBrownianItoConvolution
    (hB : MathFinBridge.BrownianOn μ F T B) (hα : 1 / 2 < α)
    (hVp : IsStronglyPredictable F V)
    (hVn : ∀ t ω, 0 ≤ V t ω) (hVi : ∀ t, Integrable (V t) μ)
    {C : ℝ} (hMean : ∀ t, (∫ ω, V t ω ∂μ) ≤ C) (u : Icc (0 : ℝ≥0) T) : Ω → ℝ :=
  jointItoIntegralCLM T (fun s => GirsanovPort.finiteBrownianOn_memLp hB
    (min s T) (min_le_right _ _) 2 (by simp))
    (hestonKernelFamilyLp hα hVp hVn hVi hMean u)

/-- The two dyadic limits in the variance statement have exactly the
same almost sure value as the Brownian Itô integral. The equivalence
uses the Brownian motion on the specified filtration. -/
theorem isHestonConvolutionAt_iff_brownianIto
    (hB : MathFinBridge.BrownianOn μ F T B) (hα : 1 / 2 < α) (hα' : α ≤ 1)
    (hVp : IsStronglyPredictable F V) (hVa : StronglyAdapted F V)
    (hVc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => V t ω) (Icc 0 T))
    (hVn : ∀ t ω, 0 ≤ V t ω) (hVi : ∀ t, Integrable (V t) μ)
    {C : ℝ} (hMean : ∀ t, (∫ ω, V t ω ∂μ) ≤ C) (u : Icc (0 : ℝ≥0) T)
    {z : Ω → ℝ} :
    IsHestonConvolutionAt μ α u B V z ↔
      z =ᵐ[μ] hestonBrownianItoConvolution hB hα hVp hVn hVi hMean u := by
  let hB₂ (s : ℝ≥0) := GirsanovPort.finiteBrownianOn_memLp hB
    (min s T) (min_le_right _ _) 2 (by simp)
  obtain ⟨_, hBm, hBs⟩ := GirsanovPort.finiteBrownianOn_frozen_martingales hB
  have hVct : ∀ᵐ ω ∂μ, ContinuousOn (fun t => V t ω) (Icc 0 (u : ℝ≥0)) :=
    hVc.mono fun _ h => h.mono (Icc_subset_Icc le_rfl u.property.2)
  have hF := isHestonConvolutionAt_jointIto_fixed_horizon
    u hα hα' hBm hB₂ hBs hVp hVa hVct hVn hVi hMean
  have hConvolution : IsHestonConvolutionAt μ α u B V
      (hestonBrownianItoConvolution hB hα hVp hVn hVi hMean u) :=
    hF.congr_driver_on fun s hs => Eventually.of_forall fun ω =>
      congrFun (congrArg B (min_eq_left (hs.trans u.property.2))) ω
  exact ⟨fun h => h.ae_unique hConvolution, fun he => hConvolution.congr_ae he.symm⟩

/-- The exact variance-solution predicate agrees with an Itô convolution
version satisfying the displayed Volterra equation simultaneously at all
times outside one null event. -/
theorem isHestonVarianceSolution_iff_brownianIto
    (hB : MathFinBridge.BrownianOn μ F T B) (hα : 1 / 2 < α) (hα' : α ≤ 1)
    (hVp : IsStronglyPredictable F V) (hVa : StronglyAdapted F V)
    (hVc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => V t ω) (Icc 0 T))
    (hVn : ∀ t ω, 0 ≤ V t ω) (hVi : ∀ t, Integrable (V t) μ)
    {C : ℝ} (hMean : ∀ t, (∫ ω, V t ω ∂μ) ≤ C) :
    IsHestonVarianceSolution μ F T α v₀ κ θ σ B V ↔
      ∃ Z : ℝ≥0 → Ω → ℝ,
        (∀ t : Icc (0 : ℝ≥0) T, Z t =ᵐ[μ]
          hestonBrownianItoConvolution hB hα hVp hVn hVi hMean t) ∧
        ∀ᵐ ω ∂μ, ∀ t ≤ T,
          V t ω = v₀ + hestonVarianceDrift α κ θ V t ω + σ * Z t ω := by
  constructor
  · rintro ⟨_, _, _, Z, hZ, he⟩
    exact ⟨Z, fun u => (isHestonConvolutionAt_iff_brownianIto hB hα hα' hVp hVa hVc
      hVn hVi hMean u).mp (hZ u u.property.2), he⟩
  · rintro ⟨Z, hZ, he⟩
    refine ⟨hVa, hVc, Eventually.of_forall (fun ω t _ => hVn t ω), Z, ?_, he⟩
    intro t ht
    let u : Icc (0 : ℝ≥0) T := ⟨t, zero_le, ht⟩
    exact (isHestonConvolutionAt_iff_brownianIto hB hα hα' hVp hVa hVc hVn hVi hMean u).mpr (hZ u)

/-- The fixed-time identity uses the canonical L² Itô representative
directly. The preceding equivalence gives a simultaneous version. -/
theorem IsHestonVarianceSolution.ae_eq_brownianIto
    (h : IsHestonVarianceSolution μ F T α v₀ κ θ σ B V)
    (hB : MathFinBridge.BrownianOn μ F T B) (hα : 1 / 2 < α) (hα' : α ≤ 1)
    (hVp : IsStronglyPredictable F V)
    (hVn : ∀ t ω, 0 ≤ V t ω) (hVi : ∀ t, Integrable (V t) μ)
    {C : ℝ} (hMean : ∀ t, (∫ ω, V t ω ∂μ) ≤ C) (u : Icc (0 : ℝ≥0) T) :
    V u =ᵐ[μ] fun ω => v₀ + hestonVarianceDrift α κ θ V u ω +
      σ * hestonBrownianItoConvolution hB hα hVp hVn hVi hMean u ω := by
  obtain ⟨Z, hZ, he⟩ :=
    (isHestonVarianceSolution_iff_brownianIto hB hα hα' hVp h.1 h.2.1 hVn hVi hMean).mp h
  filter_upwards [hZ u, he] with ω hω heω
  rw [heω u u.property.2, hω]

#print axioms hestonBrownianItoConvolution
#print axioms isHestonConvolutionAt_iff_brownianIto
#print axioms isHestonVarianceSolution_iff_brownianIto
#print axioms IsHestonVarianceSolution.ae_eq_brownianIto

end RoughHeston
