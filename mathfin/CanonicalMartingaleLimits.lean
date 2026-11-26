import CanonicalPathIntegrals
import DeterministicMartingaleShift
import CompensatedProductShift
import WeakLimitTimeMoments

open MeasureTheory Filter Set
open scoped MeasureTheory Topology NNReal

namespace RoughHeston

variable {I : Type*} {l : Filter I} [NeBot l] {T : ℝ≥0}
  {Pn : I → ProbabilityMeasure (CanonicalPath T (ℝ × ℝ))}
  {P : ProbabilityMeasure (CanonicalPath T (ℝ × ℝ))}
  {α v₀ κ θ : ℝ}

/-- Inverse Volterra reconstruction from a coordinate of the joint path. -/
noncomputable def canonicalVarianceMartingale (T : ℝ≥0) (α v₀ κ θ : ℝ)
    (f : C(ℝ × ℝ, ℝ)) (t : ℝ≥0) (p : CanonicalPath T (ℝ × ℝ)) : ℝ :=
  recoveredVarianceMartingale T α v₀ κ θ ((min t T : ℝ≥0) : ℝ) (f.comp p)

/-- Canonical compensator with a continuous density of the two variance coordinates. -/
noncomputable def canonicalVarianceCompensator (T : ℝ≥0)
    (g : C(ℝ × ℝ, ℝ)) (t : ℝ≥0) (p : CanonicalPath T (ℝ × ℝ)) : ℝ :=
  ∫ s in Ioc (0 : ℝ) ((min t T : ℝ≥0) : ℝ), g (p (realTimeOnHorizon T s))

/-- A canonical martingale candidate is held constant after the
observation horizon, along with the canonical filtration. -/
theorem stronglyAdapted_canonicalVarianceMartingale (T : ℝ≥0)
    {α : ℝ} (hα : α < 1) (v₀ κ θ : ℝ) (f : C(ℝ × ℝ, ℝ)) :
    StronglyAdapted (canonicalPathNaturalFiltration T)
      (canonicalVarianceMartingale T α v₀ κ θ f) :=
  fun t => (stronglyAdapted_pair_recoveredVarianceMartingale T hα v₀ κ θ f (min t T)).mono
    ((canonicalPathNaturalFiltration (E := ℝ × ℝ) T).mono (min_le_left t T))

theorem stronglyAdapted_canonicalVarianceCompensator (T : ℝ≥0) (g : C(ℝ × ℝ, ℝ)) :
    StronglyAdapted (canonicalPathNaturalFiltration T) (canonicalVarianceCompensator T g) :=
  fun t => (stronglyAdapted_pair_path_time_integral T g (min t T)).mono
    ((canonicalPathNaturalFiltration (E := ℝ × ℝ) T).mono (min_le_left t T))

/-- The reconstructed martingale property passes to the weak limit of
the joint variance laws when the deterministic input error tends to zero. -/
theorem canonicalVarianceMartingale_of_weak_limit
    (hα : α < 1) (hweak : Tendsto Pn l (𝓝 P)) (f : C(ℝ × ℝ, ℝ))
    {d : I → ℝ≥0 → ℝ} (hd : ∀ t, Tendsto (fun i => d i t) l (𝓝 0))
    (hshift : ∀ i, Martingale
      (fun t p => canonicalVarianceMartingale T α v₀ κ θ f t p + d i t)
      (canonicalPathNaturalFiltration T) (Pn i : Measure _))
    (hmoment : ∀ t, ∃ C : ℝ, ∀ i,
      MemLp (canonicalVarianceMartingale T α v₀ κ θ f t) 2 (Pn i : Measure _) ∧
      (∫ p, (canonicalVarianceMartingale T α v₀ κ θ f t p) ^ 2 ∂(Pn i : Measure _)) ≤ C) :
    Martingale (canonicalVarianceMartingale T α v₀ κ θ f)
      (canonicalPathNaturalFiltration T) (P : Measure _) := by
  have hAlg := canonicalPathNaturalFiltration_eq_comap_stopped (E := ℝ × ℝ) T
  exact martingale_of_weak_limit_of_uniform_time_sq_moments hweak
    (stronglyAdapted_canonicalVarianceMartingale T hα v₀ κ θ f)
    (fun t => (continuous_recoveredVarianceMartingale T hα v₀ κ θ (min t T).prop).comp
      (ContinuousMap.continuous_postcomp f))
    (continuous_canonicalStoppedPath T) hAlg
    (tendsto_boundedContinuous_past_tests_of_deterministic_shift hd hshift hAlg)
    hmoment

/-- Transmission of the compensated products to the limiting variance law,
using the two coordinate selectors and the corresponding bracket density. -/
theorem canonicalVarianceCompensatedProduct_of_weak_limit
    (hα : α < 1) (hweak : Tendsto Pn l (𝓝 P)) (f k g : C(ℝ × ℝ, ℝ))
    {d e : I → ℝ≥0 → ℝ} (hd : ∀ t, Tendsto (fun i => d i t) l (𝓝 0))
    (he : ∀ t, Tendsto (fun i => e i t) l (𝓝 0)) :
    let M := canonicalVarianceMartingale T α v₀ κ θ f
    let N := canonicalVarianceMartingale T α v₀ κ θ k
    let A := canonicalVarianceCompensator T g
    let F := fun t p => M t p * N t p - A t p
    (∀ i, Martingale (fun t p => (M t p + d i t) * (N t p + e i t) - A t p)
      (canonicalPathNaturalFiltration T) (Pn i : Measure _)) →
    (∀ i t, Integrable (M t) (Pn i : Measure _)) →
    (∀ i t, Integrable (N t) (Pn i : Measure _)) →
    (∀ t, ∃ C : ℝ, ∀ i, (∫ p, ‖M t p‖ ∂(Pn i : Measure _)) ≤ C) →
    (∀ t, ∃ C : ℝ, ∀ i, (∫ p, ‖N t p‖ ∂(Pn i : Measure _)) ≤ C) →
    (∀ t, ∃ C : ℝ, ∀ i, MemLp (F t) 2 (Pn i : Measure _) ∧
      (∫ p, (F t p) ^ 2 ∂(Pn i : Measure _)) ≤ C) →
    Martingale F (canonicalPathNaturalFiltration T) (P : Measure _) := by
  intro M N A F hshift hMint hNint hMb hNb hmoment
  have hAlg := canonicalPathNaturalFiltration_eq_comap_stopped (E := ℝ × ℝ) T
  have hFadapted : StronglyAdapted (canonicalPathNaturalFiltration T) F := fun t =>
    ((stronglyAdapted_canonicalVarianceMartingale T hα v₀ κ θ f t).mul
      (stronglyAdapted_canonicalVarianceMartingale T hα v₀ κ θ k t)).sub
      (stronglyAdapted_canonicalVarianceCompensator T g t)
  have hFcontinuous (t : ℝ≥0) : Continuous (F t) := by
    have hM : Continuous (M t) :=
      (continuous_recoveredVarianceMartingale T hα v₀ κ θ (min t T).prop).comp
        (ContinuousMap.continuous_postcomp f)
    have hN : Continuous (N t) :=
      (continuous_recoveredVarianceMartingale T hα v₀ κ θ (min t T).prop).comp
        (ContinuousMap.continuous_postcomp k)
    exact (hM.mul hN).sub (continuous_pair_path_time_integral T (min t T) g)
  exact martingale_of_weak_limit_of_uniform_time_sq_moments hweak
    hFadapted hFcontinuous (continuous_canonicalStoppedPath T) hAlg
    (tendsto_boundedContinuous_compensated_product_past_tests_of_deterministic_shift
      hd he hshift hMint hNint hMb hNb hAlg)
    hmoment

end RoughHeston

#print axioms RoughHeston.canonicalVarianceMartingale_of_weak_limit
#print axioms RoughHeston.canonicalVarianceCompensatedProduct_of_weak_limit
