import SmoothCoupledNonnegative

/-! Residual covariance densities on the common physical state space.
They are independent of the number of exponential memories. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

open MathFin.ItoIntegralCLM

variable {ι η : Type*} [Fintype ι] [Fintype η] [DecidableEq ι]

/-- Continuous covariance density of the physical cluster martingales,
with the smooth-kernel value at zero already divided out. -/
noncomputable def physicalCouplingDensity (σ : ℝ) (i j : Option ι) (v : Option ι → ℝ) : ℝ :=
  eulerCovarianceCoefficient (smoothCoupledDiffusion (η := Empty) 1 σ)
    (i, none) (j, none) 0 (fun a => v a.1)

theorem continuous_physicalCouplingDensity (σ : ℝ) (i j : Option ι) :
    Continuous (physicalCouplingDensity σ i j) := by
  unfold physicalCouplingDensity eulerCovarianceCoefficient
  have hv : Continuous (fun v : Option ι → ℝ => ((0 : ℝ≥0), fun a : Option ι × Option Empty => v a.1)) :=
    continuous_const.prodMk (continuous_pi fun a => continuous_apply a.1)
  apply continuous_finsetSum
  intro k _
  exact ((continuous_smoothCoupledDiffusion (η := Empty) 1 σ (i, none) k).comp hv).mul
    ((continuous_smoothCoupledDiffusion (η := Empty) 1 σ (j, none) k).comp hv)

theorem physicalCouplingDensity_diagonal (σ : ℝ) (i : Option ι) (v : Option ι → ℝ) :
    physicalCouplingDensity σ i i v = σ^2 * max (v i) 0 := by
  rw [physicalCouplingDensity, smoothCoupledCovariance_variance_diagonal]
  simp [smoothVariancePositive]

theorem smoothCoupledPhysicalDiffusion_project (K₀ σ : ℝ) (t : ℝ≥0)
    (z : SmoothCoupledState ι η) (i a : Option ι) :
    smoothCoupledDiffusion K₀ σ t z (i, none) a =
      K₀ * smoothCoupledDiffusion (η := Empty) 1 σ 0
        (fun k => z (k.1, none)) (i, none) a := by
  cases i <;> cases a <;>
    simp only [smoothCoupledDiffusion, smoothClusterUnit, smoothClusterTotal, smoothVariancePositive,
      one_mul, mul_zero] <;> ring

/-- Projecting out all memories and rescaling gives a density function on
the same physical state space for every approximating kernel. -/
theorem smoothCoupledCovariance_physical_project (K₀ σ : ℝ) (t : ℝ≥0)
    (z : SmoothCoupledState ι η) (i j : Option ι) :
    eulerCovarianceCoefficient (smoothCoupledDiffusion K₀ σ) (i, none) (j, none) t z =
      K₀^2 * physicalCouplingDensity σ i j (fun a => z (a, none)) := by
  unfold physicalCouplingDensity eulerCovarianceCoefficient
  simp_rw [smoothCoupledPhysicalDiffusion_project K₀ σ t z, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Normalizing the physical residuals compensates their product by the
projected continuous density, on the original coupling filtration. -/
theorem martingale_rescaledSmoothCoupledPhysicalProduct
    (T : ℝ≥0) (K₀ κ ℓ₀ σ : ℝ) (hK : K₀ ≠ 0) (v : Option ι → ℝ)
    (q rate : η → ℝ) (β : Option ι → ℝ≥0 → ℝ) (i j : Option ι)
    {μ : Measure (CanonicalPath T (SmoothCoupledState ι η))}
    (hQ : Martingale (fun t p =>
      smoothCoupledMartingale T K₀ κ ℓ₀ v q rate β (i, none) t p *
        smoothCoupledMartingale T K₀ κ ℓ₀ v q rate β (j, none) t p -
      smoothCoupledCompensator T K₀ σ β (i, none) (j, none) t p)
      (canonicalPathNaturalFiltration T) μ) :
    Martingale (fun t p =>
      (smoothCoupledMartingale T K₀ κ ℓ₀ v q rate β (i, none) t p / K₀) *
        (smoothCoupledMartingale T K₀ κ ℓ₀ v q rate β (j, none) t p / K₀) -
      ∫ r, physicalCouplingDensity σ i j (fun a => smoothCoupledPath T K₀ β r p (a, none))
        ∂timeMeasureHorizon (min t T)) (canonicalPathNaturalFiltration T) μ := by
  have h := hQ.smul ((K₀^2)⁻¹)
  convert h using 1
  funext t p
  simp only [Pi.smul_apply, smul_eq_mul, smoothCoupledCompensator,
    smoothCoupledCovariance_physical_project, integral_const_mul]
  field_simp

/-- Normalized scalar residuals preserve the martingale property. -/
theorem martingale_rescaledSmoothCoupledPhysicalCoordinate
    {T : ℝ≥0} {K₀ κ ℓ₀ : ℝ} {v : Option ι → ℝ} {q rate : η → ℝ}
    {β : Option ι → ℝ≥0 → ℝ} {i : Option ι}
    {μ : Measure (CanonicalPath T (SmoothCoupledState ι η))}
    (hM : Martingale (smoothCoupledMartingale T K₀ κ ℓ₀ v q rate β (i, none))
      (canonicalPathNaturalFiltration T) μ) :
    Martingale (fun t p => smoothCoupledMartingale T K₀ κ ℓ₀ v q rate β (i, none) t p / K₀)
      (canonicalPathNaturalFiltration T) μ := by
  convert hM.smul K₀⁻¹ using 1
  funext t p
  simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

#print axioms RoughHeston.continuous_physicalCouplingDensity
#print axioms RoughHeston.martingale_rescaledSmoothCoupledPhysicalProduct
#print axioms RoughHeston.martingale_rescaledSmoothCoupledPhysicalCoordinate

end RoughHeston
