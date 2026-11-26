import CanonicalApproximationProof

/-! Recovering tightness after adding a uniformly convergent sequence
of deterministic immigration convolutions. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston

set_option maxHeartbeats 1000000

variable {T : ℝ≥0}
local notation "Ω" => CanonicalPath T (ℝ × ℝ)

/-- Shift weak limits by deterministic paths which converge uniformly. -/
theorem tendsto_probabilityMeasure_map_add_of_tendsto
    {P : ProbabilityMeasure Ω} {Pn : ℕ → ProbabilityMeasure Ω} (hP : Tendsto Pn atTop (𝓝 P))
    {b : Ω} {bn : ℕ → Ω} (hb : Tendsto bn atTop (𝓝 b)) :
    Tendsto (fun n => (Pn n).map (fun p => p+bn n)) atTop (𝓝 (P.map (fun p => p+b))) := by
  let g (u : Ω) (p : Ω) := p+u
  have hg (u : Ω) : Continuous (g u) := continuous_id.add continuous_const
  have hWeak := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous Pn P hP (hg b)
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro f hFb hFL
  obtain ⟨D,hD⟩ := hFb
  obtain ⟨L,hL⟩ := hFL
  have hfc : Continuous f := hL.continuous
  have hi (u : Ω) (Q : ProbabilityMeasure Ω) : Integrable (fun p => f (g u p)) (Q : Measure Ω) := by
    refine (integrable_const (D+‖f 0‖)).mono' (hfc.comp (hg u)).aestronglyMeasurable ?_
    apply Eventually.of_forall
    intro p
    rw [← dist_zero_right]
    exact (dist_triangle (f (g u p)) (f 0) 0).trans
      (add_le_add (hD _ _) (le_of_eq (dist_zero_right _)))
  have hT := tendsto_iff_forall_lipschitz_integral_tendsto.mp hWeak f ⟨D,hD⟩ ⟨L,hL⟩
  have hLdist (n : ℕ) (p : Ω) : ‖f (g (bn n) p)-f (g b p)‖ ≤ (L:ℝ)*dist (bn n) b := by
    rw [← dist_eq_norm]
    simpa only [g, dist_add_left] using hL.dist_le_mul (g (bn n) p) (g b p)
  have hBound (n : ℕ) :
      ‖(∫ p, f p ∂((Pn n).map (g (bn n)) : Measure Ω)) -
        (∫ p, f p ∂((Pn n).map (g b) : Measure Ω))‖ ≤ (L:ℝ)*dist (bn n) b := by
    change ‖(∫ p, f p ∂Measure.map (g (bn n)) (Pn n : Measure Ω)) -
      (∫ p, f p ∂Measure.map (g b) (Pn n : Measure Ω))‖ ≤ _
    rw [integral_map (hg (bn n)).measurable.aemeasurable hfc.aestronglyMeasurable,
      integral_map (hg b).measurable.aemeasurable hfc.aestronglyMeasurable, ← integral_sub (hi _ _) (hi _ _)]
    have h := norm_integral_le_of_norm_le_const (μ := (Pn n : Measure Ω)) (ae_of_all _ (hLdist n))
    simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one, Function.comp_apply] using h
  have hzero : Tendsto (fun n => (L:ℝ)*dist (bn n) b) atTop (𝓝 0) := by
    simpa only [dist_self, mul_zero] using (hb.dist (tendsto_const_nhds (x := b))).const_mul (L:ℝ)
  have hdiff : Tendsto (fun n => (∫ p, f p ∂((Pn n).map (g (bn n)) : Measure Ω)) -
      (∫ p, f p ∂((Pn n).map (g b) : Measure Ω))) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun _ => norm_nonneg _) hBound hzero)
  convert hdiff.add hT using 1
  · funext n
    exact (sub_add_cancel _ _).symm
  · rw [zero_add]

/-- The moment and the weak subsequence apply to the original path laws
when Kolmogorov estimates are available only after deterministic centering. -/
theorem canonicalPairPath_subsequence_of_centered_increment_moments
    (hT : 0 < T) (p β A : ℝ) (hp : 2 ≤ p) (hβ : 1 < β)
    (Pn : ℕ → ProbabilityMeasure Ω) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    {b : Ω} {bn : ℕ → Ω} (hb : Tendsto bn atTop (𝓝 b)) :
    let Qn := fun n => (Pn n).map (fun p => p-bn n)
    (∀ n, (Qn n : Measure Ω) {f | A < ‖f (canonicalEvalTime T 0)‖} = 0) →
    (∀ n (s t : CanonicalPathTime T),
      (∫⁻ f : Ω, edist (f s) (f t)^p ∂(Qn n : Measure Ω)) ≤ C*edist s t^β) →
    ∃ P : ProbabilityMeasure Ω, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (Pn ∘ φ) atTop (𝓝 P) ∧
      MemLp (fun f : Ω => ‖f‖) 2 (P : Measure Ω) := by
  intro Qn hstart hInc
  obtain ⟨Q, φ, hφ, hQ⟩ := canonicalPairPath_subsequence_of_increment_moments hT p β A
    (by linarith) hβ Qn C hC hstart hInc
  obtain ⟨D,hD⟩ := uniform_canonicalPath_sup_sq_moment hT p β A hp hβ Qn C hC hstart hInc
  have hMoment := (weak_limit_canonicalPath_sup_sq_moment hQ (fun n => hD.2 (φ n))).1
  let P := Q.map (fun p => p+b)
  have hSub := tendsto_probabilityMeasure_map_add_of_tendsto hQ (hb.comp hφ.tendsto_atTop)
  have hEq (n : ℕ) : ((Qn ∘ φ) n).map (fun p => p+(bn ∘ φ) n) = Pn (φ n) := by
    apply ProbabilityMeasure.toMeasure_injective
    let f (p : Ω) := p-bn (φ n)
    let g (p : Ω) := p+bn (φ n)
    have hf : Measurable f := (continuous_id.sub continuous_const).measurable
    have hg : Measurable g := (continuous_id.add continuous_const).measurable
    change Measure.map g (Measure.map f (Pn (φ n) : Measure Ω)) = (Pn (φ n) : Measure Ω)
    rw [Measure.map_map hg hf]
    have he : g ∘ f = id := funext fun p => sub_add_cancel p (bn (φ n))
    rw [he, Measure.map_id]
  refine ⟨P, φ, hφ, hSub.congr (fun n => hEq n), ?_⟩
  let g (p : Ω) := p+b
  have hg : Measurable g := (continuous_id.add continuous_const).measurable
  change MemLp (fun p : Ω => ‖p‖) 2 (Measure.map g (Q : Measure Ω))
  apply (memLp_map_measure_iff continuous_norm.aestronglyMeasurable hg.aemeasurable).2
  have hm : MemLp (fun p : Ω => ‖p‖+‖b‖) 2 (Q : Measure Ω) := hMoment.add (memLp_const _)
  apply hm.mono ((continuous_norm.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
  apply Eventually.of_forall
  intro p
  change ‖‖p+b‖‖ ≤ ‖‖p‖+‖b‖‖
  rw [norm_norm, Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact norm_add_le _ _

#print axioms RoughHeston.tendsto_probabilityMeasure_map_add_of_tendsto
#print axioms RoughHeston.canonicalPairPath_subsequence_of_centered_increment_moments

end RoughHeston
