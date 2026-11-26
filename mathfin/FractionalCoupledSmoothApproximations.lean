import FractionalApproximationResolvent
import SmoothCoupledForward

/-! The explicit smooth approximating joint laws for any prescribed
finite cluster family and any bounded measurable nonnegative input rates. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev FractionalCoupledSmoothState (ι : Type*) (n : ℕ) :=
  SmoothCoupledState ι (Fin (fractionalApproximationOrder n))

noncomputable abbrev fractionalCoupledSmoothPath (T : ℝ≥0) (α : ℝ) (n : ℕ)
    (β : Option ι → ℝ≥0 → ℝ) :
    ℝ≥0 → CanonicalPath T (FractionalCoupledSmoothState ι n) → FractionalCoupledSmoothState ι n :=
  smoothCoupledPath T (fractionalExponentialApproximation α n 0) β

/-- All focal cluster coordinates are present on the same canonical law.
The distinguished coordinate of index none is Y. -/
structure FractionalCoupledSmoothLaw (T : ℝ≥0) (α : ℝ) (n : ℕ) (κ σ : ℝ)
    (v : Option ι → ℝ) (β : Option ι → ℝ≥0 → ℝ) where
  ℓ₀ : ℝ
  q : Fin (fractionalApproximationOrder n) → ℝ
  rate : Fin (fractionalApproximationOrder n) → ℝ
  law : ProbabilityMeasure (CanonicalPath T (FractionalCoupledSmoothState ι n))
  supMoment : MemLp (fun p : CanonicalPath T (FractionalCoupledSmoothState ι n) => ‖p‖) 2 (law : Measure _)
  initial : ∀ᵐ p ∂(law : Measure (CanonicalPath T (FractionalCoupledSmoothState ι n))),
    fractionalCoupledSmoothPath T α n β 0 p = smoothCoupledInitial v
  nonneg : ∀ᵐ p ∂(law : Measure (CanonicalPath T (FractionalCoupledSmoothState ι n))),
    ∀ i : Option ι, ∀ t ∈ Icc 0 T, 0 ≤ fractionalCoupledSmoothPath T α n β t p (i, none)
  martingale : ∀ k, Martingale (smoothCoupledMartingale T (fractionalExponentialApproximation α n 0) κ ℓ₀ v q rate β k)
    (canonicalPathNaturalFiltration T) (law : Measure _)
  compProduct : ∀ k l, Martingale (fun t p =>
    smoothCoupledMartingale T (fractionalExponentialApproximation α n 0) κ ℓ₀ v q rate β k t p *
      smoothCoupledMartingale T (fractionalExponentialApproximation α n 0) κ ℓ₀ v q rate β l t p -
      smoothCoupledCompensator T (fractionalExponentialApproximation α n 0) σ β k l t p)
    (canonicalPathNaturalFiltration T) (law : Measure _)
  inverse : ∀ᵐ p ∂(law : Measure (CanonicalPath T (FractionalCoupledSmoothState ι n))), ∀ i : Option ι, ∀ t ∈ Icc 0 T,
    smoothExponentialInverse (fractionalExponentialApproximation α n 0) ℓ₀ q rate (v i)
      (fun r : ℝ => fractionalCoupledSmoothPath T α n β r.toNNReal p (i, none)) t =
    smoothCoupledMartingale T (fractionalExponentialApproximation α n 0) κ ℓ₀ v q rate β (i, none) t p / fractionalExponentialApproximation α n 0 +
      ∫ r in (0 : ℝ)..(t : ℝ), (β i r.toNNReal - κ*fractionalCoupledSmoothPath T α n β r.toNNReal p (i, none))
  resolves : ∀ t : ℝ, 0 ≤ t →
    (1 / fractionalExponentialApproximation α n 0) * fractionalExponentialApproximation α n t +
      volterraConvolution (smoothExponentialResolvent ℓ₀ q rate)
        (fractionalExponentialApproximation α n) t = 1
  forward : ∀ᵐ p ∂(law : Measure (CanonicalPath T (FractionalCoupledSmoothState ι n))), ∀ i : Option ι, ∀ t ∈ Icc 0 T,
    fractionalCoupledSmoothPath T α n β t p (i, none) = v i +
      (∫ r in (0 : ℝ)..(t : ℝ), fractionalExponentialApproximation α n ((t : ℝ)-r)*
        (β i r.toNNReal - κ*fractionalCoupledSmoothPath T α n β r.toNNReal p (i, none))) +
      smoothKernelMartingaleConvolution (fractionalApproximationFinWeight α n)
        (fractionalApproximationFinRate n)
        (fun r : ℝ => smoothCoupledMartingale T (fractionalExponentialApproximation α n 0) κ ℓ₀ v q rate β
          (i, none) r.toNNReal p / fractionalExponentialApproximation α n 0) t

/-- Existence at every finite-exponential stage for the actual
fractional approximating kernels and all fixed deterministic pulse rates. -/
theorem exists_fractionalCoupledSmoothLaw {T : ℝ≥0} (hT : 0 < T)
    {α : ℝ} (hα : 0 < α) (hα' : α < 1) (n : ℕ)
    (κ σ : ℝ) (v : Option ι → ℝ) (β : Option ι → ℝ≥0 → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hβ₀ : ∀ i t, 0 ≤ β i t) {B : ℝ} (hB : 0 ≤ B)
    (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B) :
    Nonempty (FractionalCoupledSmoothLaw T α n κ σ v β) := by
  have hK := fractionalExponentialApproximation_pos_at_zero hα hα' n
  obtain ⟨ℓ₀, q, rate, hℓ₀, hq, hr, hL⟩ := exists_fractionalApproximation_positive_resolvent hα hα' n
  obtain ⟨P, h₂, h₀, hM, hQ, hN, hMem, hI⟩ :=
    exists_nonnegative_smoothCoupled_realization hT (fractionalExponentialApproximation α n 0) κ ℓ₀ σ v q rate β
      hK hℓ₀.le hv (fun j => (hq j).le) (fun j => (hr j).le) hβ₀ hB hβ hβB
  have hF := ae_smoothCoupled_pointwise_forward hT (fractionalExponentialApproximation α n 0) κ ℓ₀ hK.ne' v q rate β
    (fractionalApproximationFinWeight α n) (fractionalApproximationFinRate n) hB hβ hβB
    (fun s hs => by
      have hKeq : smoothExponentialKernel (fractionalApproximationFinWeight α n)
          (fractionalApproximationFinRate n) = fractionalExponentialApproximation α n :=
        funext (smoothExponentialKernel_eq_fractionalExponentialApproximation α n)
      rw [hKeq]
      exact hL s hs.1) hI
  simp_rw [smoothExponentialKernel_eq_fractionalExponentialApproximation] at hF
  exact ⟨⟨ℓ₀, q, rate, P, h₂, h₀, hN, hM, hQ, hI, hL, hF⟩⟩

#print axioms RoughHeston.exists_fractionalCoupledSmoothLaw

end RoughHeston
