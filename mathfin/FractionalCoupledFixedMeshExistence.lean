import CanonicalPhysicalUniformSecondMoments
import FractionalSmoothJointTightnessInput

/-! The smooth-to-fractional limit for a finite deterministic immigration
mesh, including every focal cluster and the companion variance. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston

set_option maxHeartbeats 1500000

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
  {α κ σ : ℝ} {v : Option ι → ℝ} {β : Option ι → ℝ≥0 → ℝ}
local notation "J" => CoupledPhysicalState ι
local notation "Ω" => CanonicalPath T J

theorem fixedPhysicalLaw_row_pow_bounds
    (hα : 1/2 < α) (hα' : α < 1) (hκ : 0 ≤ κ) (hv : ∀ i, 0 ≤ v i)
    (L : ∀ n, FractionalCoupledSmoothLaw T α n κ σ v β)
    {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B) :
    let Pn := fun n => (L n).fixedPhysicalLaw hB hβ hβB
    ∃ CV CM : ℝ≥0∞, CV ≠ ⊤ ∧ CM ≠ ⊤ ∧
      (∀ n i u, u ≤ T →
        (∫⁻ p, ENNReal.ofReal (max (canonicalPhysicalVariance T i u p) 0)^2 ∂(Pn n : Measure Ω)) ≤ CV) ∧
      (∀ n i t, (∫⁻ p, ‖canonicalPhysicalResidual T i t p‖ₑ^4 ∂(Pn n : Measure Ω)) ≤ CM) := by
  intro Pn
  obtain ⟨CV, hCV, hV₂⟩ := uniform_fractionalSmooth_variance_dyadic_powers hα hα' hκ hv L hB hβ hβB 1
  simp only [pow_one] at hV₂
  let e : ℝ := (2*α-1)*(2:ℝ)
  let CM : ℝ≥0∞ := boundedMartingaleEvenPowerConstant 2 * ENNReal.ofReal (σ^2)^2 *
    ENNReal.ofReal ((T:ℝ)^((2-2*α)*(2:ℝ))) * CV * ENNReal.ofReal ((T:ℝ)^e)
  have hBd := boundedMartingaleEvenPowerConstant_ne_top 2 (by decide)
  have hCM : CM ≠ ⊤ := by dsimp [CM]; finiteness
  refine ⟨CV, CM, hCV, hCM, ?_, ?_⟩
  · intro n i u hu
    let ψ := (L n).fixedPhysicalPath hB hβ hβB
    let F (p : Ω) := ENNReal.ofReal (max (canonicalPhysicalVariance T i u p) 0)^2
    have hV : Continuous (canonicalPhysicalVariance T i u) :=
      ((continuous_apply i).comp continuous_fst).comp (continuous_canonicalPathEval T u)
    have hF : Measurable F := ((hV.measurable.max measurable_const).ennreal_ofReal).pow_const _
    change (∫⁻ p, F p ∂Measure.map ψ ((L n).law : Measure _)) ≤ CV
    rw [lintegral_map hF ((L n).measurable_fixedPhysicalPath hB hβ hβB)]
    have hEq (p : CanonicalPath T (FractionalCoupledSmoothState ι n)) :
        F (ψ p) = ENNReal.ofReal (max ((L n).variance i u p) 0)^2 := by
      unfold F canonicalPhysicalVariance ψ
      rw [(L n).canonicalPathEval_fixedPhysicalPath hB hβ hβB]
    rw [lintegral_congr hEq]
    exact hV₂ n i u hu
  · intro n i t
    let u := min t T
    let ψ := (L n).fixedPhysicalPath hB hβ hβB
    have hu : u ≤ T := min_le_right _ _
    have hFreeze (p : Ω) : canonicalPhysicalResidual T i t p = canonicalPhysicalResidual T i u p := by
      have he : canonicalEvalTime T t = canonicalEvalTime T u := by
        apply Subtype.ext
        exact (min_eq_left hu).symm
      simp only [canonicalPhysicalResidual, canonicalPathEval, he]
    let F (p : Ω) := ‖canonicalPhysicalResidual T i t p‖ₑ^4
    have hF : Measurable F := ((continuous_canonicalPhysicalResidual T i t).measurable.enorm).pow_const _
    change (∫⁻ p, F p ∂Measure.map ψ ((L n).law : Measure _)) ≤ CM
    rw [lintegral_map hF ((L n).measurable_fixedPhysicalPath hB hβ hβB)]
    have hEq (p : CanonicalPath T (FractionalCoupledSmoothState ι n)) :
        F (ψ p) = ‖(L n).residual i u p‖ₑ^4 := by
      dsimp only [F]
      rw [hFreeze, canonicalPhysicalResidual]
      unfold ψ
      rw [(L n).canonicalPathEval_fixedPhysicalPath hB hβ hβB]
    rw [lintegral_congr hEq]
    have h := (L n).residual_increment_even_moment_le hα hα' i hB hβ hβB
      (s := 0) (show 0 ≤ u from zero_le) hu 2 (by decide) (hV₂ n i)
    have heq : (∫⁻ p, ‖(L n).residual i u p-(L n).residual i 0 p‖ₑ^(2*2 : ℕ)
        ∂((L n).law : Measure _)) = ∫⁻ p, ‖(L n).residual i u p‖ₑ^4 ∂((L n).law : Measure _) := by
      apply lintegral_congr_ae
      filter_upwards [(L n).residual_starts_zero i hB hβ hβB] with p hp
      change (L n).residual i 0 p = 0 at hp
      rw [hp, sub_zero]
    rw [heq] at h
    apply h.trans
    simp only [NNReal.coe_zero, sub_zero]
    apply mul_right_mono
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow u.coe_nonneg (NNReal.coe_le_coe.mpr hu)
      (mul_nonneg (by linarith) (by norm_num)))

/-- A finite pulse mesh admits an actual joint fractional law on a
canonical continuous path space. The variance coordinates are
nonnegative and all covariation identities are retained. -/
theorem exists_fixed_mesh_fractionalCoupled_limit
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
        (hestonKernel α) t =ᵐ[(P : Measure Ω)] 0) := by
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
  exact ⟨P, hI, hN, hMart, hComp, hEq⟩

#print axioms RoughHeston.fixedPhysicalLaw_row_pow_bounds
#print axioms RoughHeston.exists_fixed_mesh_fractionalCoupled_limit

end RoughHeston
