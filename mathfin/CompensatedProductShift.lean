import DeterministicMartingaleShift
import Mathlib.Analysis.Normed.Ring.Lemmas

open MeasureTheory Filter
open scoped MeasureTheory BoundedContinuousFunction Topology

namespace RoughHeston

variable {Ω ι I : Type*} {mΩ : MeasurableSpace Ω} [Preorder ι]
  {𝒢 : Filtration ι mΩ} {M N C : ι → Ω → ℝ}
  {Pn : I → ProbabilityMeasure Ω} {l : Filter I} {d e : I → ι → ℝ}

private theorem bounded_weighted_integrals {Z W : Ω → ℝ} {A B : ℝ} (hB : 0 ≤ B)
    (hZ : ∀ i, Integrable Z (Pn i : Measure Ω))
    (hb : ∀ i, (∫ ω, ‖Z ω‖ ∂(Pn i : Measure Ω)) ≤ A) (hW : ∀ ω, ‖W ω‖ ≤ B) :
    IsBoundedUnder (· ≤ ·) l (norm ∘ fun i => ∫ ω, Z ω * W ω ∂(Pn i : Measure Ω)) := by
  refine isBoundedUnder_of ⟨B * A, fun i => ?_⟩
  change ‖∫ ω, Z ω * W ω ∂(Pn i : Measure Ω)‖ ≤ B * A
  calc
    _ ≤ ∫ ω, B * ‖Z ω‖ ∂(Pn i : Measure Ω) := by
      refine norm_integral_le_of_norm_le ((hZ i).norm.const_mul B) ?_
      refine Eventually.of_forall fun ω => ?_
      rw [norm_mul, mul_comm B]
      exact mul_le_mul_of_nonneg_left (hW ω) (norm_nonneg _)
    _ = B * ∫ ω, ‖Z ω‖ ∂(Pn i : Measure Ω) := integral_const_mul B _
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb i) hB

/-- Deterministic shifts of the factors in a compensated-product
martingale contribute vanishing errors to each bounded past test. -/
theorem tendsto_weighted_compensated_product_tests_of_deterministic_shift
    (hd : ∀ r, Tendsto (fun i => d i r) l (𝓝 0))
    (he : ∀ r, Tendsto (fun i => e i r) l (𝓝 0))
    (hshift : ∀ i, Martingale
      (fun r ω => (M r ω + d i r) * (N r ω + e i r) - C r ω)
      𝒢 (Pn i : Measure Ω))
    (hMint : ∀ i r, Integrable (M r) (Pn i : Measure Ω))
    (hNint : ∀ i r, Integrable (N r) (Pn i : Measure Ω))
    (hMb : ∀ r, ∃ A : ℝ, ∀ i, (∫ ω, ‖M r ω‖ ∂(Pn i : Measure Ω)) ≤ A)
    (hNb : ∀ r, ∃ A : ℝ, ∀ i, (∫ ω, ‖N r ω‖ ∂(Pn i : Measure Ω)) ≤ A)
    {s t : ι} (hst : s ≤ t) {W : Ω → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hW : StronglyMeasurable[𝒢 s] W) (hbound : ∀ ω, ‖W ω‖ ≤ B) :
    Tendsto (fun i => ∫ ω,
      ((M t ω * N t ω - C t ω) - (M s ω * N s ω - C s ω)) * W ω ∂(Pn i : Measure Ω))
      l (𝓝 0) := by
  let R (i : I) (r : ι) (ω : Ω) := d i r * N r ω + e i r * M r ω + d i r * e i r
  let J (r : ι) (i : I) := ∫ ω, R i r ω * W ω ∂(Pn i : Measure Ω)
  let G (i : I) (r : ι) (ω : Ω) := (M r ω + d i r) * (N r ω + e i r) - C r ω
  have hWa (i : I) : AEStronglyMeasurable W (Pn i : Measure Ω) :=
    (hW.mono (𝒢.le s)).aestronglyMeasurable
  have hWi (i : I) : Integrable W (Pn i : Measure Ω) :=
    (integrable_const B).mono' (hWa i) (Eventually.of_forall hbound)
  have hRi (i : I) (r : ι) : Integrable (R i r) (Pn i : Measure Ω) :=
    (((hNint i r).const_mul (d i r)).add ((hMint i r).const_mul (e i r))).add
      (integrable_const (d i r * e i r))
  have hRwt (i : I) (r : ι) : Integrable (fun ω => R i r ω * W ω) (Pn i : Measure Ω) :=
    (hRi i r).mul_bdd (hWa i) (Eventually.of_forall hbound)
  have hJ (r : ι) : Tendsto (J r) l (𝓝 0) := by
    obtain ⟨A, hA⟩ := hMb r
    obtain ⟨D, hD⟩ := hNb r
    have hMb' : IsBoundedUnder (· ≤ ·) l
        (norm ∘ fun i => ∫ ω, M r ω * W ω ∂(Pn i : Measure Ω)) :=
      bounded_weighted_integrals hB (fun i => hMint i r) hA hbound
    have hNb' : IsBoundedUnder (· ≤ ·) l
        (norm ∘ fun i => ∫ ω, N r ω * W ω ∂(Pn i : Measure Ω)) :=
      bounded_weighted_integrals hB (fun i => hNint i r) hD hbound
    have hWb' : IsBoundedUnder (· ≤ ·) l
        (norm ∘ fun i => ∫ ω, W ω ∂(Pn i : Measure Ω)) := by
      refine isBoundedUnder_of ⟨B, fun i => ?_⟩
      simpa using norm_integral_le_of_norm_le_const (μ := (Pn i : Measure Ω))
        (Eventually.of_forall hbound)
    have hdN := (hd r).zero_mul_isBoundedUnder_le hNb'
    have heM := (he r).zero_mul_isBoundedUnder_le hMb'
    have hde : Tendsto (fun i => d i r * e i r) l (𝓝 0) := by
      have hh : Tendsto (fun i => d i r * e i r) l (𝓝 ((0 : ℝ) * 0)) := (hd r).mul (he r)
      simpa only [zero_mul] using hh
    have hdeW := hde.zero_mul_isBoundedUnder_le hWb'
    have hsum : Tendsto (fun i => d i r * (∫ ω, N r ω * W ω ∂(Pn i : Measure Ω)) +
        e i r * (∫ ω, M r ω * W ω ∂(Pn i : Measure Ω)) +
        (d i r * e i r) * (∫ ω, W ω ∂(Pn i : Measure Ω))) l (𝓝 ((0 : ℝ) + 0 + 0)) :=
      (hdN.add heM).add hdeW
    rw [add_zero, add_zero] at hsum
    refine hsum.congr fun i => ?_
    have h₁ : Integrable (fun ω => d i r * (N r ω * W ω)) (Pn i : Measure Ω) :=
      ((hNint i r).mul_bdd (hWa i) (Eventually.of_forall hbound)).const_mul _
    have h₂ : Integrable (fun ω => e i r * (M r ω * W ω)) (Pn i : Measure Ω) :=
      ((hMint i r).mul_bdd (hWa i) (Eventually.of_forall hbound)).const_mul _
    have h₃ : Integrable (fun ω => (d i r * e i r) * W ω) (Pn i : Measure Ω) :=
      (hWi i).const_mul _
    have h₁₂ : Integrable (fun ω => d i r * (N r ω * W ω) + e i r * (M r ω * W ω))
        (Pn i : Measure Ω) := h₁.add h₂
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
      ← integral_add h₁ h₂, ← integral_add h₁₂ h₃]
    exact integral_congr_ae (Eventually.of_forall fun ω => by simp only [R]; ring)
  have hlim : Tendsto (fun i => J s i - J t i) l (𝓝 0) := by
    have h : Tendsto (fun i => J s i - J t i) l (𝓝 ((0 : ℝ) - 0)) := (hJ s).sub (hJ t)
    simpa only [sub_zero] using h
  refine hlim.congr fun i => ?_
  have hGdiff : Integrable (fun ω => (G i t ω - G i s ω) * W ω) (Pn i : Measure Ω) :=
    (((hshift i).integrable t).sub ((hshift i).integrable s)).mul_bdd
      (hWa i) (Eventually.of_forall hbound)
  have hRdiff : Integrable (fun ω => (R i t ω - R i s ω) * W ω) (Pn i : Measure Ω) :=
    ((hRi i t).sub (hRi i s)).mul_bdd (hWa i) (Eventually.of_forall hbound)
  have hzero : (∫ ω, (G i t ω - G i s ω) * W ω ∂(Pn i : Measure Ω)) = 0 := by
    have hG : Martingale (fun r ω => G i r ω + (fun _ : ι => (0 : ℝ)) r)
        𝒢 (Pn i : Measure Ω) := by simpa only [add_zero] using hshift i
    simpa only [sub_self, zero_mul] using
      integral_weighted_increment_of_deterministic_shift hG hst hW hbound
  have hRdiffJ : (∫ ω, (R i t ω - R i s ω) * W ω ∂(Pn i : Measure Ω)) = J t i - J s i := by
    change _ = (∫ ω, R i t ω * W ω ∂(Pn i : Measure Ω)) -
      (∫ ω, R i s ω * W ω ∂(Pn i : Measure Ω))
    rw [← integral_sub (hRwt i t) (hRwt i s)]
    exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
  symm
  calc
    _ = ∫ ω, (G i t ω - G i s ω) * W ω - (R i t ω - R i s ω) * W ω ∂(Pn i : Measure Ω) :=
      integral_congr_ae (Eventually.of_forall fun ω => by simp only [G, R]; ring)
    _ = _ := by
      rw [integral_sub hGdiff hRdiff, hzero, hRdiffJ]
      ring

/-- The compensated-product test error vanishes for all bounded
continuous functions of the supplied past statistic. -/
theorem tendsto_boundedContinuous_compensated_product_past_tests_of_deterministic_shift
    {E : Type*} [TopologicalSpace E] [mE : MeasurableSpace E] [OpensMeasurableSpace E]
    (hd : ∀ r, Tendsto (fun i => d i r) l (𝓝 0))
    (he : ∀ r, Tendsto (fun i => e i r) l (𝓝 0))
    (hshift : ∀ i, Martingale
      (fun r ω => (M r ω + d i r) * (N r ω + e i r) - C r ω) 𝒢 (Pn i : Measure Ω))
    (hMint : ∀ i r, Integrable (M r) (Pn i : Measure Ω))
    (hNint : ∀ i r, Integrable (N r) (Pn i : Measure Ω))
    (hMb : ∀ r, ∃ A : ℝ, ∀ i, (∫ ω, ‖M r ω‖ ∂(Pn i : Measure Ω)) ≤ A)
    (hNb : ∀ r, ∃ A : ℝ, ∀ i, (∫ ω, ‖N r ω‖ ∂(Pn i : Measure Ω)) ≤ A)
    {past : ι → Ω → E} (hpastAlg : ∀ s, 𝒢 s = mE.comap (past s)) :
    ∀ s t, s ≤ t → ∀ f : E →ᵇ ℝ,
      Tendsto (fun i => ∫ ω,
        ((M t ω * N t ω - C t ω) - (M s ω * N s ω - C s ω)) * f (past s ω) ∂(Pn i : Measure Ω))
        l (𝓝 0) := by
  intro s t hst f
  have hs : @Measurable Ω E (𝒢 s) mE (past s) := by
    rw [hpastAlg s]
    exact comap_measurable (past s)
  have hf : StronglyMeasurable[𝒢 s] (fun ω => f (past s ω)) :=
    (f.continuous.measurable.comp hs).stronglyMeasurable
  exact tendsto_weighted_compensated_product_tests_of_deterministic_shift
    hd he hshift hMint hNint hMb hNb hst (norm_nonneg f) hf
    (fun ω => f.norm_coe_le_norm (past s ω))

end RoughHeston

#print axioms RoughHeston.tendsto_weighted_compensated_product_tests_of_deterministic_shift
#print axioms RoughHeston.tendsto_boundedContinuous_compensated_product_past_tests_of_deterministic_shift
