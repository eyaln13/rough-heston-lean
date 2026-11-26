import FractionalCoupledIntegratedLimits
import CanonicalPhysicalWeakMartingaleLimit

/-! First weak limit at a fixed immigration mesh. The only quantitative
inputs are the uniform moment and increment estimates for the smooth laws. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "J" => CoupledPhysicalState ι

theorem continuous_canonicalPhysicalResidual (T : ℝ≥0) (i : Option ι) (t : ℝ≥0) :
    Continuous (canonicalPhysicalResidual T i t) :=
  ((continuous_apply i).comp continuous_snd).comp (continuous_canonicalPathEval T t)

noncomputable def canonicalPhysicalCompensatedProduct (T : ℝ≥0) (σ : ℝ)
    (i j : Option ι) (t : ℝ≥0) (p : CanonicalPath T J) : ℝ :=
  canonicalPhysicalResidual T i t p * canonicalPhysicalResidual T j t p -
    canonicalPhysicalCompensator T σ i j t p

theorem continuous_canonicalPhysicalCompensatedProduct (T : ℝ≥0) (σ : ℝ)
    (i j : Option ι) (t : ℝ≥0) :
    Continuous (canonicalPhysicalCompensatedProduct T σ i j t) :=
  ((continuous_canonicalPhysicalResidual T i t).mul (continuous_canonicalPhysicalResidual T j t)).sub
    (continuous_canonicalPhysicalCompensator T σ i j t)

theorem stronglyAdapted_canonicalPhysicalCompensatedProduct (T : ℝ≥0) (σ : ℝ)
    (i j : Option ι) :
    StronglyAdapted (canonicalPathNaturalFiltration (E := J) T)
      (canonicalPhysicalCompensatedProduct T σ i j) :=
  fun t => ((stronglyAdapted_canonicalPhysicalResidual T i t).mul
    (stronglyAdapted_canonicalPhysicalResidual T j t)).sub
      (stronglyAdapted_canonicalPhysicalCompensator T σ i j t)

def uniformPhysicalSecondMoment {T : ℝ≥0}
    (Pn : ℕ → ProbabilityMeasure (CanonicalPath T J))
    (M : ℝ≥0 → CanonicalPath T J → ℝ) : Prop :=
  ∀ t, ∃ C : ℝ, ∀ n, MemLp (M t) 2 (Pn n : Measure _) ∧
    (∫ p, (M t p)^2 ∂(Pn n : Measure _)) ≤ C

/-- With uniform smooth increment and timewise moments, the explicit
approximations converge along a subsequence to a joint nonnegative
fractional martingale law, with every focal coordinate retained. -/
theorem exists_fixed_mesh_fractionalCoupled_limit_of_uniform_moments
    {T : ℝ≥0} (hT : 0 < T) {α κ σ : ℝ} (hα : 0 < α) (hα' : α < 1)
    {v : Option ι → ℝ} {β : Option ι → ℝ≥0 → ℝ}
    (L : ∀ n, FractionalCoupledSmoothLaw T α n κ σ v β)
    {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B)
    {p e : ℝ} (hp : 0 < p) (he : 1 < e) {C : ℝ≥0∞} (hC : C ≠ ⊤) :
    let Pn := fun n => (L n).fixedPhysicalLaw hB hβ hβB
    (∀ n (s t : CanonicalPathTime T),
      (∫⁻ f : CanonicalPath T J, edist (f s) (f t)^p ∂(Pn n : Measure _)) ≤ C*edist s t^e) →
    (∀ i, uniformPhysicalSecondMoment Pn (canonicalPhysicalResidual T i)) →
    (∀ i j, uniformPhysicalSecondMoment Pn (canonicalPhysicalCompensatedProduct T σ i j)) →
    ∃ (P : ProbabilityMeasure (CanonicalPath T J)) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto (Pn ∘ φ) atTop (𝓝 P) ∧
      (∀ᵐ f ∂(P : Measure _), f ∈ canonicalPhysicalInitialSet T v) ∧
      (∀ᵐ f ∂(P : Measure _), f ∈ canonicalPhysicalNonnegative (ι := ι) T) ∧
      (∀ i : Option ι, Martingale (canonicalPhysicalResidual T i) (canonicalPathNaturalFiltration T) (P : Measure _)) ∧
      (∀ i j : Option ι, Martingale (canonicalPhysicalCompensatedProduct T σ i j)
        (canonicalPathNaturalFiltration T) (P : Measure _)) ∧
      (∀ i (t : CanonicalPathTime T), canonicalPhysicalIntegratedError T (v i) κ i (hβ i) (hβB i)
        (hestonKernel α) t =ᵐ[(P : Measure _)] 0) := by
  intro Pn hInc hMr hPr
  have hI (n : ℕ) := (L n).ae_fixedPhysical_initial hB hβ hβB
  have hStart (n : ℕ) :
      (Pn n : Measure (CanonicalPath T J)) {f | ‖(v, (0 : Option ι → ℝ))‖ <
        ‖f (canonicalEvalTime T 0)‖} = 0 := by
    have hS : ∀ᵐ f ∂(Pn n : Measure (CanonicalPath T J)),
        ¬ ‖(v, (0 : Option ι → ℝ))‖ < ‖f (canonicalEvalTime T 0)‖ := by
      filter_upwards [hI n] with f hf
      change canonicalPathEval T 0 f = (v, 0) at hf
      change ¬ ‖(v, (0 : Option ι → ℝ))‖ < ‖canonicalPathEval T 0 f‖
      rw [hf]
      exact lt_irrefl _
    simpa only [not_not] using ae_iff.mp hS
  obtain ⟨P, φ, hφ, hWeak⟩ := canonicalProperPath_subsequence_of_increment_moments hT p e
    ‖(v, (0 : Option ι → ℝ))‖ hp he Pn C hC hStart hInc
  refine ⟨P, φ, hφ, hWeak, ?_, ?_, ?_, ?_, ?_⟩
  · exact ae_mem_closed_of_probability_weak_limit hWeak (isClosed_canonicalPhysicalInitialSet T v)
      (fun n => hI (φ n))
  · exact ae_mem_closed_of_probability_weak_limit hWeak (isClosed_canonicalPhysicalNonnegative (ι := ι) T)
      (fun n => (L (φ n)).ae_fixedPhysical_nonnegative hB hβ hβB)
  · intro i
    apply canonicalPhysical_martingale_of_weak_limit hWeak (continuous_canonicalPhysicalResidual T i)
      (stronglyAdapted_canonicalPhysicalResidual T i)
      (fun n => (L (φ n)).fixedPhysical_residual_martingale hB hβ hβB i)
    intro t
    obtain ⟨A, hA⟩ := hMr i t
    exact ⟨A, fun n => hA (φ n)⟩
  · intro i j
    apply canonicalPhysical_martingale_of_weak_limit hWeak
      (continuous_canonicalPhysicalCompensatedProduct T σ i j)
      (stronglyAdapted_canonicalPhysicalCompensatedProduct T σ i j)
      (fun n => (L (φ n)).fixedPhysical_compensatedProduct_martingale hB hβ hβB
        (fractionalExponentialApproximation_pos_at_zero hα hα' (φ n)).ne' i j)
    intro t
    obtain ⟨A, hA⟩ := hPr i j t
    exact ⟨A, fun n => hA (φ n)⟩
  · intro i t
    exact ae_canonicalPhysicalIntegratedError_of_weak T (v i) κ i (hβ i) (hβB i) t
      hWeak (hestonKernel_integrableOn_reflected_Ioc hα t.val.coe_nonneg)
      (fun n => fractionalExponentialApproximation_integrableOn_reflected_Ioc hα hα' (φ n))
      ((fractionalExponentialApproximation_tendsto_reflected_L1 hα hα' t.val.coe_nonneg).comp
        hφ.tendsto_atTop)
      (fun n => (L (φ n)).ae_fixedPhysical_integrated_zero hα hα' hB hβ hβB i t)

#print axioms RoughHeston.exists_fixed_mesh_fractionalCoupled_limit_of_uniform_moments

end RoughHeston
