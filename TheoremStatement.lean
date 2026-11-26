import StochasticCompletion
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic

/-!
Statement of the variance assertion of Theorem 1.1.

The stochastic convolution is specified using actual dyadic sums against
the named driver, L² limits for bounded continuous cutoffs, and then an
L² limit as the cutoff is removed. The equivalence of this specification
with the usual Brownian Itô integral requires a separate proof.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal MeasureTheory ProbabilityTheory

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- Brownian motion on the specified filtration and finite time interval.
The increment is independent of the entire sigma-algebra at its start. -/
structure IsBrownianOn (μ : Measure Ω) (𝒢 : Filtration ℝ≥0 m)
    (T : ℝ≥0) (B : ℝ≥0 → Ω → ℝ) : Prop where
  adapted : StronglyAdapted 𝒢 B
  zero_at_start : B 0 =ᵐ[μ] 0
  continuous_paths : ∀ᵐ ω ∂μ, ContinuousOn (fun t => B t ω) (Set.Icc 0 T)
  normal_increment : ∀ s t, s ≤ t → t ≤ T →
    Measure.map (fun ω => B t ω - B s ω) μ = gaussianReal 0 (t - s)
  independent_of_past : ∀ s t, s ≤ t → t ≤ T →
    Indep (MeasurableSpace.comap (fun ω => B t ω - B s ω) (borel ℝ)) (𝒢 s) μ

/-- The fractional kernel in equation (1.1), with its endpoint value
specified separately. -/
noncomputable def hestonKernel (α u : ℝ) : ℝ :=
  if 0 < u then u ^ (α - 1) / Real.Gamma α else 0

theorem hestonKernel_measurable (α : ℝ) : Measurable (hestonKernel α) := by
  apply Measurable.ite (measurableSet_lt measurable_const measurable_id)
  · exact (measurable_id.pow_const (α - 1)).div_const _
  · exact measurable_const

/-- The fractional kernel belongs to L² on the time interval used in
the model once its exponent is greater than one half. -/
theorem hestonKernel_memLp_two {α : ℝ} (hα : 1 / 2 < α) (T : ℝ≥0) :
    MemLp (hestonKernel α) 2 (volume.restrict (Set.Ioc 0 (T : ℝ))) := by
  apply (memLp_two_iff_integrable_sq (hestonKernel_measurable α).aestronglyMeasurable).2
  let r := (α - 1) * 2
  have hr : -1 < r := by dsimp [r]; linarith
  have hpow := (intervalIntegrable_iff_integrableOn_Ioc_of_le (NNReal.coe_nonneg T)).mp
    (intervalIntegral.intervalIntegrable_rpow' hr)
  have hi := hpow.const_mul (Real.Gamma α ^ 2)⁻¹
  refine hi.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  rw [hestonKernel, ite_eq_left hu.1, div_pow, div_eq_mul_inv, mul_comm]
  congr 1
  exact (Real.rpow_mul hu.1.le _ _).trans (Real.rpow_two _)

/-- At level n, discard the endpoint singularity at scale 1/(n+1) and
clip the square-root integrand at n+1. -/
noncomputable def hestonCutoffWeight (α : ℝ) (t : ℝ≥0)
    (V : ℝ≥0 → Ω → ℝ) (n : ℕ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  hestonKernel α (max ((n : ℝ) + 1)⁻¹ ((t : ℝ) - (s : ℝ))) *
    min (Real.sqrt (V s ω)) ((n : ℝ) + 1)


/-- The uncut integrand, evaluated at a time and a sample point. -/
noncomputable def hestonConvolutionWeight (α : ℝ) (t : ℝ≥0)
    (V : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  hestonKernel α ((t : ℝ) - (s : ℝ)) * Real.sqrt (V s ω)

private theorem heston_kernel_nonneg {α u : ℝ} (hα : 0 < α) :
    0 ≤ hestonKernel α u := by
  by_cases hu : 0 < u
  · rw [hestonKernel, ite_eq_left hu]
    exact div_nonneg (Real.rpow_nonneg hu.le _) (Real.Gamma_pos_of_pos hα).le
  · simp [hestonKernel, hu]

private theorem heston_kernel_antitone {α u v : ℝ}
    (hα : 0 < α) (hα' : α ≤ 1) (hu : 0 < u) (huv : u ≤ v) :
    hestonKernel α v ≤ hestonKernel α u := by
  simp only [hestonKernel, ite_eq_left hu, ite_eq_left (hu.trans_le huv)]
  exact div_le_div_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos hu huv (sub_nonpos.mpr hα')) (Real.Gamma_pos_of_pos hα).le

private theorem heston_cutoff_weight_bounds {α : ℝ} {s t : ℝ≥0}
    (hα : 0 < α) (hα' : α ≤ 1) (hst : s < t) (V : ℝ≥0 → Ω → ℝ) (ω : Ω) (n : ℕ) :
    0 ≤ hestonCutoffWeight α t V n s ω ∧
      hestonCutoffWeight α t V n s ω ≤ hestonConvolutionWeight α t V s ω := by
  let u : ℝ := (t : ℝ) - (s : ℝ)
  have hu : 0 < u := sub_pos.mpr (NNReal.coe_lt_coe.mpr hst)
  let r : ℝ := (n : ℝ) + 1
  have hr : 0 ≤ r := by dsimp [r]; positivity
  let q := min (Real.sqrt (V s ω)) r
  have hq : 0 ≤ q := le_min (Real.sqrt_nonneg _) hr
  have hk := heston_kernel_antitone hα hα' hu (le_max_right r⁻¹ u)
  exact ⟨mul_nonneg (heston_kernel_nonneg hα) hq, mul_le_mul hk (min_le_left _ _)
    hq (heston_kernel_nonneg hα)⟩

private theorem heston_cutoff_weight_eventually_eq {α : ℝ} {s t : ℝ≥0}
    (hst : s < t) (V : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    ∀ᶠ n : ℕ in atTop,
      hestonCutoffWeight α t V n s ω = hestonConvolutionWeight α t V s ω := by
  let u : ℝ := (t : ℝ) - (s : ℝ)
  have hu : 0 < u := sub_pos.mpr (NNReal.coe_lt_coe.mpr hst)
  have hr : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun _ => le_add_of_nonneg_right zero_le_one) tendsto_natCast_atTop_atTop
  have hδ : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hr
  filter_upwards [hδ.eventually_lt_const hu, hr.eventually (eventually_ge_atTop (Real.sqrt (V s ω)))]
    with n hn hrn
  have hu' : ((n : ℝ) + 1)⁻¹ ≤ (t : ℝ) - (s : ℝ) := hn.le
  simp only [hestonCutoffWeight, hestonConvolutionWeight, max_eq_right hu', min_eq_left hrn]

/-- Removing the regularization gives convergence in the predictable
energy norm whenever the target convolution weight is square integrable.
The measure can be Lebesgue time times probability, restricted to s<t. -/
theorem heston_cutoff_weight_L2 {ν : Measure (ℝ≥0 × Ω)}
    {α : ℝ} (hα : 0 < α) (hα' : α ≤ 1) (t : ℝ≥0) {V : ℝ≥0 → Ω → ℝ}
    (hV : Measurable (fun p : ℝ≥0 × Ω => V p.1 p.2))
    (hs : ∀ᵐ p ∂ν, p.1 < t)
    (hweight : MemLp (fun p : ℝ≥0 × Ω => hestonConvolutionWeight α t V p.1 p.2) 2 ν) :
    Tendsto (fun n => eLpNorm
      (fun p : ℝ≥0 × Ω => hestonCutoffWeight α t V n p.1 p.2 -
        hestonConvolutionWeight α t V p.1 p.2) 2 ν) atTop (𝓝 0) := by
  let f := fun p : ℝ≥0 × Ω => hestonConvolutionWeight α t V p.1 p.2
  let g := fun n (p : ℝ≥0 × Ω) => hestonCutoffWeight α t V n p.1 p.2
  let d := fun n => g n - f
  have hg (n : ℕ) : Measurable (g n) := by
    have htime : Measurable (fun p : ℝ≥0 × Ω => (p.1 : ℝ)) :=
      measurable_subtype_coe.comp measurable_fst
    have hw : Measurable (fun p : ℝ≥0 × Ω => max ((n : ℝ) + 1)⁻¹ ((t : ℝ) - (p.1 : ℝ))) :=
      measurable_const.max (measurable_const.sub htime)
    exact ((hestonKernel_measurable α).comp hw).mul
      ((Real.continuous_sqrt.measurable.comp hV).min measurable_const)
  have hbound (n : ℕ) : ∀ᵐ p ∂ν, ‖d n p‖ ≤ ‖f p‖ := by
    filter_upwards [hs] with p hp
    obtain ⟨h₁, h₂⟩ := heston_cutoff_weight_bounds hα hα' hp V p.2 n
    have h₁' : 0 ≤ g n p := h₁
    have h₂' : g n p ≤ f p := h₂
    have hf : 0 ≤ f p := h₁'.trans h₂'
    rw [Real.norm_eq_abs, Real.norm_of_nonneg hf]
    change |g n p - f p| ≤ f p
    rw [abs_of_nonpos (sub_nonpos.mpr h₂')]
    linarith
  have hd (n : ℕ) : MemLp (d n) 2 ν :=
    hweight.mono ((hg n).aestronglyMeasurable.sub hweight.aestronglyMeasurable) (hbound n)
  have hsq : Integrable (fun p => f p ^ 2) ν :=
    (memLp_two_iff_integrable_sq hweight.aestronglyMeasurable).mp hweight
  have hsquares : Tendsto (fun n => ∫ p, (d n p)^2 ∂ν) atTop (𝓝 0) := by
    have hlim : ∀ᵐ p ∂ν, Tendsto (fun n => (d n p)^2) atTop (𝓝 ((0 : ℝ≥0 × Ω → ℝ) p)) := by
      filter_upwards [hs] with p hp
      apply tendsto_const_nhds.congr'
      filter_upwards [heston_cutoff_weight_eventually_eq hp V p.2] with n hn
      change (0 : ℝ) = (g n p - f p)^2
      rw [show g n p = f p from hn, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    have hdom (n : ℕ) : ∀ᵐ p ∂ν, ‖(d n p)^2‖ ≤ f p ^ 2 := by
      filter_upwards [hbound n] with p hp
      rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs (d n p), ← sq_abs (f p)]
      exact pow_le_pow_left₀ (abs_nonneg _)
        (by simpa only [Real.norm_eq_abs] using hp) 2
    simpa only [Pi.zero_apply, Pi.pow_apply, integral_zero] using tendsto_integral_of_dominated_convergence
      (fun p => f p ^ 2) (fun n => (hd n).aestronglyMeasurable.pow _) hsq hdom hlim
  have hn : Tendsto (fun n => ‖(hd n).toLp (d n)‖) atTop (𝓝 0) := by
    have ht := (Real.continuous_sqrt.tendsto 0).comp hsquares
    have he (n : ℕ) : Real.sqrt (∫ p, (d n p) ^ 2 ∂ν) = ‖(hd n).toLp (d n)‖ := by
      rw [← norm_toLp_two_sq (hd n), Real.sqrt_sq (norm_nonneg _)]
    simpa only [Function.comp_def, Real.sqrt_zero, he] using ht
  have he (n : ℕ) : ENNReal.ofReal ‖(hd n).toLp (d n)‖ = eLpNorm (d n) 2 ν := by
    rw [← dist_zero_right, ← Lp.edist_dist, Lp.edist_toLp_zero]
  have h : Tendsto (fun n => eLpNorm (d n) 2 ν) atTop (𝓝 0) := by
    simpa only [Function.comp_def, he, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hn
  simpa only [d, g, f, Pi.sub_def] using h

/-- The dyadic sums specify the stochastic convolution at one fixed
observation time. The inner limit refines the time grid and the outer
limit removes the kernel and square-root cutoffs. -/
def IsHestonConvolutionAt (μ : Measure Ω) (α : ℝ) (t : ℝ≥0)
    (B V : ℝ≥0 → Ω → ℝ) (z : Ω → ℝ) : Prop :=
  let G := uniformDyadicGrids t
  MemLp z 2 μ ∧ ∃ J : ℕ → Ω → ℝ,
    (∀ n, MemLp (J n) 2 μ ∧
      Tendsto (fun j => eLpNorm
        (dyadicTerminal G j (fun k => hestonCutoffWeight α t V n (G.grid j k)) B - J n)
        2 μ) atTop (𝓝 0)) ∧
    Tendsto (fun n => eLpNorm (J n - z) 2 μ) atTop (𝓝 0)

/-- One rough Heston variance solution with the specified driver,
including the integral equation outside a single null event. -/
def IsHestonVarianceSolution (μ : Measure Ω) (𝒢 : Filtration ℝ≥0 m)
    (T : ℝ≥0) (α v₀ κ θ σ : ℝ) (B V : ℝ≥0 → Ω → ℝ) : Prop :=
  StronglyAdapted 𝒢 V ∧ (∀ᵐ ω ∂μ, ContinuousOn (fun t => V t ω) (Set.Icc 0 T)) ∧
    (∀ᵐ ω ∂μ, ∀ t ≤ T, 0 ≤ V t ω) ∧
    ∃ Z : ℝ≥0 → Ω → ℝ, (∀ t ≤ T, IsHestonConvolutionAt μ α t B V (Z t)) ∧
      ∀ᵐ ω ∂μ, ∀ t ≤ T,
        V t ω = v₀ + (∫ s in (0 : ℝ)..(t : ℝ),
          hestonKernel α ((t : ℝ) - s) * (κ * (θ - V s.toNNReal ω))) + σ * Z t ω

/-- The two limits defining the stochastic convolution give zero at
time zero because every driver increment in the grid sum is zero. -/
theorem heston_convolution_zero {μ : Measure Ω} {α : ℝ}
    {B V : ℝ≥0 → Ω → ℝ} {z : Ω → ℝ}
    (h : IsHestonConvolutionAt μ α 0 B V z) : z =ᵐ[μ] 0 := by
  obtain ⟨hz, J, hJ, hconv⟩ := h
  have htime (j k : ℕ) : (uniformDyadicGrids 0).grid j k = 0 := by
    change (k : ℝ≥0) * 0 / (2 ^ j : ℝ≥0) = 0
    simp
  have hJ0 (n : ℕ) : J n =ᵐ[μ] 0 := by
    have hlim : Tendsto (fun _ : ℕ => eLpNorm (J n) 2 μ) atTop (𝓝 0) := by
      simpa only [dyadicTerminal, gridIntegral, runningSum, htime, sub_self, mul_zero,
        Finset.sum_const_zero, zero_sub, eLpNorm_neg] using (hJ n).2
    have he : eLpNorm (J n) 2 μ = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
    exact (eLpNorm_eq_zero_iff (by norm_num : (2 : ENNReal) ≠ 0)).mp he
  have he (n : ℕ) : eLpNorm (J n - z) 2 μ = eLpNorm z 2 μ := by
    have heq : J n - z =ᵐ[μ] (0 : Ω → ℝ) - z := (hJ0 n).sub EventuallyEq.rfl
    rw [eLpNorm_congr_ae heq, zero_sub, eLpNorm_neg]
  have hl : Tendsto (fun _ : ℕ => eLpNorm z 2 μ) atTop (𝓝 0) := by
    simpa only [he] using hconv
  exact (eLpNorm_eq_zero_iff (by norm_num : (2 : ENNReal) ≠ 0)).mp
    (tendsto_nhds_unique tendsto_const_nhds hl)

/-- The direct equation forces the specified common starting value. -/
theorem heston_variance_initial {μ : Measure Ω} {𝒢 : Filtration ℝ≥0 m}
    {T : ℝ≥0} {α v₀ κ θ σ : ℝ} {B V : ℝ≥0 → Ω → ℝ}
    (h : IsHestonVarianceSolution μ 𝒢 T α v₀ κ θ σ B V) :
    V 0 =ᵐ[μ] fun _ => v₀ := by
  obtain ⟨_, _, _, Z, hZ, hV⟩ := h
  filter_upwards [hV, heston_convolution_zero (hZ 0 (zero_le))] with ω hω hz
  simpa only [NNReal.coe_zero, intervalIntegral.integral_same, Pi.zero_apply,
    hz, mul_zero, add_zero] using hω 0 (zero_le)

/-- Exact existence-and-separation target for the variance equation.
Both solutions use the same probability measure, filtration and Brownian
motion. No coupled approximation or separation hypothesis is assumed. -/
def Theorem1_1 : Prop :=
  ∀ (T : ℝ≥0) (α v₀ κ θ σ : ℝ),
    0 < T → 1 / 2 < α → α < 1 → 0 < v₀ → 0 < κ → 0 < θ → 0 < σ →
      ∃ (Ω : Type) (m : MeasurableSpace Ω) (μ : @Measure Ω m)
        (𝒢 : Filtration ℝ≥0 m) (B X Y : ℝ≥0 → Ω → ℝ),
        IsProbabilityMeasure μ ∧ IsBrownianOn μ 𝒢 T B ∧
          IsHestonVarianceSolution μ 𝒢 T α v₀ κ θ σ B X ∧
          IsHestonVarianceSolution μ 𝒢 T α v₀ κ θ σ B Y ∧
          0 < μ {ω | ∃ t ≤ T, X t ω ≠ Y t ω}

end RoughHeston

#check RoughHeston.Theorem1_1
#print axioms RoughHeston.Theorem1_1
#print axioms RoughHeston.hestonKernel_memLp_two
#print axioms RoughHeston.heston_variance_initial
#print axioms RoughHeston.heston_cutoff_weight_L2
