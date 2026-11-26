import FractionalCoupledFixedMeshExistence

/-! Uniform quantitative smooth-law estimates survive taking the actual
fixed-mesh fractional limit. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston

set_option maxHeartbeats 1400000

theorem lintegral_ofReal_le_of_probability_weak_limit {Ω : Type*}
    [TopologicalSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    {Q : ℕ → ProbabilityMeasure Ω} {P : ProbabilityMeasure Ω} (hW : Tendsto Q atTop (𝓝 P))
    {f : Ω → ℝ} (hC : Continuous f) (h₀ : 0 ≤ f) (C : ℝ≥0∞)
    (hb : ∀ n, (∫⁻ p, ENNReal.ofReal (f p) ∂(Q n : Measure Ω)) ≤ C) :
    (∫⁻ p, ENNReal.ofReal (f p) ∂(P : Measure Ω)) ≤ C := by
  have h := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure hC h₀
    (fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hW hG)
  apply h.trans
  apply liminf_le_of_le (by isBoundedDefault)
  intro b hb'
  obtain ⟨n, hn⟩ := hb'.exists
  exact hn.trans (hb n)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
  {α κ σ : ℝ} {v : Option ι → ℝ} {β : Option ι → ℝ≥0 → ℝ}
local notation "Ω" => CanonicalPath T (CoupledPhysicalState ι)

theorem uniform_fixedPhysicalLaw_variance_dyadic_powers
    (hα : 1/2 < α) (hα' : α < 1) (hκ : 0 ≤ κ) (hv : ∀ i, 0 ≤ v i)
    (L : ∀ n, FractionalCoupledSmoothLaw T α n κ σ v β)
    {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B)
    (j : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ n i u, u ≤ T →
      (∫⁻ p, ENNReal.ofReal (max (canonicalPhysicalVariance T i u p) 0)^(2^j:ℕ)
        ∂((L n).fixedPhysicalLaw hB hβ hβB : Measure Ω)) ≤ C := by
  obtain ⟨C,hC,hV⟩ := uniform_fractionalSmooth_variance_dyadic_powers hα hα' hκ hv L hB hβ hβB j
  refine ⟨C,hC,?_⟩
  intro n i u hu
  let ψ := (L n).fixedPhysicalPath hB hβ hβB
  let F (p : Ω) := ENNReal.ofReal (max (canonicalPhysicalVariance T i u p) 0)^(2^j:ℕ)
  have hVc : Continuous (canonicalPhysicalVariance T i u) :=
    ((continuous_apply i).comp continuous_fst).comp (continuous_canonicalPathEval T u)
  have hF : Measurable F := ((hVc.measurable.max measurable_const).ennreal_ofReal).pow_const _
  change (∫⁻ p, F p ∂Measure.map ψ ((L n).law : Measure _)) ≤ C
  rw [lintegral_map hF ((L n).measurable_fixedPhysicalPath hB hβ hβB)]
  have hEq (p : CanonicalPath T (FractionalCoupledSmoothState ι n)) :
      F (ψ p) = ENNReal.ofReal (max ((L n).variance i u p) 0)^(2^j:ℕ) := by
    unfold F canonicalPhysicalVariance ψ
    rw [(L n).canonicalPathEval_fixedPhysicalPath hB hβ hβB]
  rw [lintegral_congr hEq]
  exact hV n i u hu

/-- The actual fixed-mesh law retains finite moments at all dyadic
orders of each variance and a finite fourth moment of each residual. -/
theorem exists_fixed_mesh_fractionalCoupled_limit_with_row_bounds
    (hT : 0 < T) (hα : 1/2 < α) (hα' : α < 1) (hκ : 0 ≤ κ)
    (hv : ∀ i, 0 ≤ v i) (hβ₀ : ∀ i t, 0 ≤ β i t)
    {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B) :
    ∃ (P : ProbabilityMeasure Ω),
      (∀ᵐ f ∂(P : Measure Ω), f ∈ canonicalPhysicalInitialSet T v) ∧
      (∀ᵐ f ∂(P : Measure Ω), f ∈ canonicalPhysicalNonnegative (ι := ι) T) ∧
      (∀ i : Option ι, Martingale (canonicalPhysicalResidual T i) (canonicalPathNaturalFiltration T) (P : Measure Ω)) ∧
      (∀ i j : Option ι, Martingale (canonicalPhysicalCompensatedProduct T σ i j)
        (canonicalPathNaturalFiltration T) (P : Measure Ω)) ∧
      (∀ i (t : CanonicalPathTime T), canonicalPhysicalIntegratedError T (v i) κ i (hβ i) (hβB i)
        (hestonKernel α) t =ᵐ[(P : Measure Ω)] 0) ∧
      (∀ j : ℕ, ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ i u, u ≤ T →
        (∫⁻ p, ENNReal.ofReal (max (canonicalPhysicalVariance T i u p) 0)^(2^j:ℕ) ∂(P : Measure Ω)) ≤ C) ∧
      (∃ CM : ℝ≥0∞, CM ≠ ⊤ ∧ ∀ i t,
        (∫⁻ p, ‖canonicalPhysicalResidual T i t p‖ₑ^4 ∂(P : Measure Ω)) ≤ CM) := by
  let L (n : ℕ) : FractionalCoupledSmoothLaw T α n κ σ v β := Classical.choice
      (exists_fractionalCoupledSmoothLaw hT (by linarith : 0 < α) hα' n κ σ v β hv hβ₀ hB hβ hβB)
  let Pn := fun n => (L n).fixedPhysicalLaw hB hβ hβB
  obtain ⟨CV, CM, hCV, hCM, hV, hM⟩ := fixedPhysicalLaw_row_pow_bounds hα hα' hκ hv L hB hβ hβB
  obtain ⟨hMr, hPr⟩ := uniformPhysicalSecondMoment_of_row_powers Pn σ hCV hCM hV hM
  have hα₀ : 0 < 2*α-1 := by linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (1/(2*α-1))
  let j := k+1
  have hj : 1 ≤ j := by dsimp [j]; omega
  have hkp : (k:ℝ) < ((2^j:ℕ):ℝ) := by
    exact_mod_cast (Nat.lt_succ_self k).trans j.lt_two_pow_self
  have he : 1 < (2*α-1)*((2^j:ℕ):ℝ) := by
    rw [mul_comm]
    exact (div_lt_iff₀ hα₀).mp (hk.trans hkp)
  have hp : 0 < ((2*(2^j:ℕ):ℕ):ℝ) := by positivity
  obtain ⟨C, hC, hInc⟩ := uniform_fixedPhysicalLaw_increment_moment hα hα' hκ hv L hB hβ hβB j hj
  obtain ⟨P, φ, hφ, hWeak, hI, hN, hMart, hComp, hEq⟩ :=
    exists_fixed_mesh_fractionalCoupled_limit_of_uniform_moments hT (by linarith : 0 < α) hα' L
      hB hβ hβB hp he hC hInc hMr hPr
  refine ⟨P, hI, hN, hMart, hComp, hEq, ?_, CM, hCM, ?_⟩
  · intro k
    obtain ⟨A, hA, hMom⟩ := uniform_fixedPhysicalLaw_variance_dyadic_powers hα hα' hκ hv L hB hβ hβB k
    refine ⟨A,hA,?_⟩
    intro i u hu
    let f (p : Ω) := (max (canonicalPhysicalVariance T i u p) 0)^(2^k:ℕ)
    have hf : Continuous (canonicalPhysicalVariance T i u) :=
      ((continuous_apply i).comp continuous_fst).comp (continuous_canonicalPathEval T u)
    have hnn (p : Ω) : 0 ≤ max (canonicalPhysicalVariance T i u p) 0 := le_max_right _ _
    have h0 : 0 ≤ f := fun p => pow_nonneg (hnn p) _
    have hc : Continuous f := (hf.max continuous_const).pow _
    have h := lintegral_ofReal_le_of_probability_weak_limit hWeak hc h0 A (fun n => by
      simpa only [f, Function.comp_apply, ENNReal.ofReal_pow (hnn _)] using hMom (φ n) i u hu)
    simpa only [f, ENNReal.ofReal_pow (hnn _)] using h
  · intro i t
    let f (p : Ω) := ‖canonicalPhysicalResidual T i t p‖^4
    have h0 : 0 ≤ f := fun p => pow_nonneg (norm_nonneg _) _
    have hc : Continuous f := (continuous_canonicalPhysicalResidual T i t).norm.pow _
    have h := lintegral_ofReal_le_of_probability_weak_limit hWeak hc h0 CM (fun n => by
      simpa only [f, Function.comp_apply, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] using hM (φ n) i t)
    simpa only [f, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] using h

#print axioms RoughHeston.lintegral_ofReal_le_of_probability_weak_limit
#print axioms RoughHeston.exists_fixed_mesh_fractionalCoupled_limit_with_row_bounds

end RoughHeston
