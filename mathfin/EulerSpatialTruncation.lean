import EulerObservableCompactLimits

/-! Radial truncation for the fixed-smooth finite-dimensional coefficients. -/

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace RoughHeston

section Truncation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Continuous radial projection onto the closed ball of radius R. -/
noncomputable def radialTruncation (R : ℝ) (x : E) : E :=
  (R / max R ‖x‖) • x

theorem continuous_radialTruncation {R : ℝ} (hR : 0 < R) :
    Continuous (radialTruncation (E := E) R) := by
  apply Continuous.smul _ continuous_id
  apply continuous_const.div (continuous_const.max continuous_norm)
  intro x
  exact (hR.trans_le (le_max_left _ _)).ne'

theorem radialTruncation_eq_of_norm_le {R : ℝ} (hR : 0 < R)
    {x : E} (hx : ‖x‖ ≤ R) : radialTruncation R x = x := by
  rw [radialTruncation, max_eq_left hx, div_self hR.ne', one_smul]

theorem norm_radialTruncation_le_radius {R : ℝ} (hR : 0 < R) (x : E) :
    ‖radialTruncation R x‖ ≤ R := by
  have hm : 0 < max R ‖x‖ := hR.trans_le (le_max_left _ _)
  have hr : 0 ≤ R / max R ‖x‖ := div_nonneg hR.le hm.le
  rw [radialTruncation, norm_smul, Real.norm_of_nonneg hr]
  exact (mul_le_mul_of_nonneg_left (le_max_right _ _) hr).trans_eq
    (div_mul_cancel₀ _ hm.ne')

theorem norm_radialTruncation_le_norm {R : ℝ} (hR : 0 < R) (x : E) :
    ‖radialTruncation R x‖ ≤ ‖x‖ := by
  have hm : 0 < max R ‖x‖ := hR.trans_le (le_max_left _ _)
  have hr : 0 ≤ R / max R ‖x‖ := div_nonneg hR.le hm.le
  rw [radialTruncation, norm_smul, Real.norm_of_nonneg hr]
  exact (mul_le_mul_of_nonneg_right
    ((div_le_one₀ hm).2 (le_max_left _ _)) (norm_nonneg _)).trans_eq (one_mul _)

/-- Composing with a radial projection preserves the original linear-growth
constant and gives a uniform bound depending on the cutoff radius. -/
theorem norm_comp_radialTruncation_le {R L : ℝ} (hR : 0 < R) (hL : 0 ≤ L)
    {c : ℝ≥0 → E → ℝ} (hc : ∀ t x, ‖c t x‖ ≤ L * (1 + ‖x‖)) (t : ℝ≥0) (x : E) :
    ‖c t (radialTruncation R x)‖ ≤ L * (1 + min R ‖x‖) := by
  apply (hc _ _).trans
  exact mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (le_min (norm_radialTruncation_le_radius hR x)
      (norm_radialTruncation_le_norm hR x))) hL

theorem continuous_comp_radialTruncation {R : ℝ} (hR : 0 < R) {c : ℝ≥0 → E → ℝ}
    (hc : Continuous (Function.uncurry c)) :
    Continuous (fun z : ℝ≥0 × E => c z.1 (radialTruncation R z.2)) :=
  hc.comp (continuous_fst.prodMk ((continuous_radialTruncation hR).comp continuous_snd))

end Truncation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E]

theorem canonicalCoefficientIntegral_comp_radialTruncation_eq
    (T t : ℝ≥0) {R : ℝ} (hR : 0 < R) (c : ℝ≥0 → E → ℝ) (p : CanonicalPath T E)
    (hp : ∀ s ≤ min t T, ‖canonicalPathEval T s p‖ ≤ R) :
    canonicalCoefficientIntegral T (fun r x => c r (radialTruncation R x)) t p =
      canonicalCoefficientIntegral T c t p := by
  unfold canonicalCoefficientIntegral
  apply integral_congr_ae
  have h : ∀ᵐ r ∂MathFin.ItoIntegralCLM.timeMeasureHorizon (min t T),
      r ∈ Ioc 0 (min t T) := ae_restrict_mem measurableSet_Ioc
  filter_upwards [h] with r hr
  rw [radialTruncation_eq_of_norm_le hR (hp r hr.2)]

/-- On any compact family of paths, all sufficiently large radial
truncations give exactly the original coefficient integral at every time. -/
theorem canonicalCoefficientIntegral_eventually_eq_radialTruncation_on_compact
    (T : ℝ≥0) (c : ℝ≥0 → E → ℝ) {K : Set (CanonicalPath T E)} (hK : IsCompact K) :
    ∃ R₀ : ℝ, ∀ R ≥ R₀, ∀ p ∈ K, ∀ t,
      canonicalCoefficientIntegral T (fun r x => c r (radialTruncation R x)) t p =
        canonicalCoefficientIntegral T c t p := by
  let f (z : CanonicalPathTime T × CanonicalPath T E) := ‖z.2 z.1‖
  have hCont : Continuous f := continuous_norm.comp (continuous_eval.comp
    (continuous_snd.prodMk continuous_fst))
  have hComp := (isCompact_univ.prod hK).image hCont
  obtain ⟨A, hA⟩ := hComp.bddAbove
  refine ⟨max 1 A, fun R hR p hp t => ?_⟩
  have hpos : 0 < R := (show (0 : ℝ) < 1 by norm_num).trans_le ((le_max_left _ _).trans hR)
  refine canonicalCoefficientIntegral_comp_radialTruncation_eq T t hpos c p fun s _ => ?_
  have hs : (canonicalEvalTime T s, p) ∈ (univ : Set (CanonicalPathTime T)) ×ˢ K := ⟨trivial, hp⟩
  exact (hA (mem_image_of_mem f hs)).trans ((le_max_right _ _).trans hR)

#print axioms RoughHeston.continuous_radialTruncation
#print axioms RoughHeston.norm_comp_radialTruncation_le
#print axioms RoughHeston.canonicalCoefficientIntegral_eventually_eq_radialTruncation_on_compact

end RoughHeston
