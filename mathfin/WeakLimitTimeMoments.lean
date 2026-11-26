import WeakLimitMartingale

open MeasureTheory Filter
open scoped MeasureTheory BoundedContinuousFunction Topology ENNReal

namespace RoughHeston

/-- Approximate bounded continuous past tests imply the martingale
property under a weak limit when each time coordinate has uniformly
bounded second moments under the approximating laws. -/
theorem martingale_of_weak_limit_of_uniform_time_sq_moments
    {Ω E ι I : Type*} [TopologicalSpace Ω] [mΩ : MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] [PseudoMetricSpace E] [mE : MeasurableSpace E]
    [BorelSpace E] [Preorder ι] {l : Filter I} [NeBot l]
    {Pn : I → ProbabilityMeasure Ω} {P : ProbabilityMeasure Ω}
    (hweak : Tendsto Pn l (𝓝 P)) {𝒢 : Filtration ι mΩ}
    {M : ι → Ω → ℝ} (hMadapted : StronglyAdapted 𝒢 M)
    (hMcontinuous : ∀ t, Continuous (M t))
    {past : ι → Ω → E} (hpastContinuous : ∀ s, Continuous (past s))
    (hpastAlg : ∀ s, 𝒢 s = mE.comap (past s))
    (htest : ∀ s t, s ≤ t → ∀ f : E →ᵇ ℝ,
      Tendsto (fun i => ∫ ω, (M t ω - M s ω) * f (past s ω) ∂(Pn i : Measure Ω)) l (𝓝 0))
    (hmoment : ∀ r, ∃ C : ℝ, ∀ i, MemLp (M r) 2 (Pn i : Measure Ω) ∧
      (∫ ω, M r ω ^ 2 ∂(Pn i : Measure Ω)) ≤ C) :
    Martingale M 𝒢 (P : Measure Ω) := by
  have hMint (r : ι) : Integrable (M r) (P : Measure Ω) := by
    obtain ⟨A, hA⟩ := hmoment r
    exact (weak_limit_memLp_two_and_sq_moment_bound hweak (hMcontinuous r)
      (fun i => (hA i).1) (fun i => (hA i).2)).1.integrable one_le_two
  refine martingale_of_weak_limit_of_boundedContinuous_past_tests hweak hMadapted
    hMcontinuous hMint hpastContinuous hpastAlg htest ?_
  intro s t _ f
  obtain ⟨Cs, hCs⟩ := hmoment s
  obtain ⟨Ct, hCt⟩ := hmoment t
  let D : ℝ := 2 * ‖f‖ ^ 2
  have hD : 0 ≤ D := mul_nonneg zero_le_two (sq_nonneg _)
  let W (ω : Ω) := f (past s ω)
  have hW : Measurable W := f.continuous.measurable.comp (hpastContinuous s).measurable
  refine ⟨D * (Ct + Cs), fun i => ?_⟩
  have hWtop : MemLp W ⊤ (Pn i : Measure Ω) :=
    memLp_top_of_bound hW.aestronglyMeasurable ‖f‖
      (Eventually.of_forall fun ω => f.norm_coe_le_norm (past s ω))
  have ht := (hCt i).1
  have hs := (hCs i).1
  have htestLp : MemLp (fun ω => (M t ω - M s ω) * W ω) 2 (Pn i : Measure Ω) :=
    (ht.sub hs).mul hWtop
  refine ⟨htestLp, ?_⟩
  have hpoint (ω : Ω) : ((M t ω - M s ω) * W ω) ^ 2 ≤
      D * (M t ω ^ 2 + M s ω ^ 2) := by
    have hWa : |W ω| ≤ ‖f‖ := by
      simpa only [W, Real.norm_eq_abs] using f.norm_coe_le_norm (past s ω)
    have hWsq : W ω ^ 2 ≤ ‖f‖ ^ 2 := by
      rw [← sq_abs (W ω)]
      exact pow_le_pow_left₀ (abs_nonneg _) hWa 2
    have hdiff : (M t ω - M s ω) ^ 2 ≤ 2 * (M t ω ^ 2 + M s ω ^ 2) := by
      nlinarith [sq_nonneg (M t ω + M s ω)]
    calc
      _ = (M t ω - M s ω) ^ 2 * W ω ^ 2 := mul_pow _ _ _
      _ ≤ (M t ω - M s ω) ^ 2 * ‖f‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hWsq (sq_nonneg _)
      _ ≤ (2 * (M t ω ^ 2 + M s ω ^ 2)) * ‖f‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hdiff (sq_nonneg _)
      _ = D * (M t ω ^ 2 + M s ω ^ 2) := by dsimp [D]; ring
  have hdom : Integrable (fun ω => D * (M t ω ^ 2 + M s ω ^ 2)) (Pn i : Measure Ω) :=
    (ht.integrable_sq.add hs.integrable_sq).const_mul D
  calc
    _ ≤ ∫ ω, D * (M t ω ^ 2 + M s ω ^ 2) ∂(Pn i : Measure Ω) :=
      integral_mono htestLp.integrable_sq hdom hpoint
    _ = D * ((∫ ω, M t ω ^ 2 ∂(Pn i : Measure Ω)) +
        ∫ ω, M s ω ^ 2 ∂(Pn i : Measure Ω)) := by
      rw [integral_const_mul, integral_add ht.integrable_sq hs.integrable_sq]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add (hCt i).2 (hCs i).2) hD

end RoughHeston

#print axioms RoughHeston.martingale_of_weak_limit_of_uniform_time_sq_moments
