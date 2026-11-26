import OrthogonalDeterministicConvolution
import EulerSecondMomentEnergy

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace RoughHeston

variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
  {ν : Measure S} [IsFiniteMeasure ν] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- Deterministic k-weighted integration maps uniformly square-integrable
paths to L² when the weight itself is square-integrable over the time band. -/
theorem weighted_path_memLp_two {M : S→Ω→ℝ} {k : S→ℝ}
    (hm : Measurable (Function.uncurry M)) (hk : Measurable k) (hk₂ : MemLp k 2 ν)
    (hm₂ : ∀ s,MemLp (M s) 2 μ)
    {C : ℝ} (hC : 0≤C) (hmC : ∀ᵐ s ∂ν,(∫ ω,(M s ω)^2 ∂μ)≤C) :
    MemLp (fun ω => ∫ s,k s*M s ω ∂ν) 2 μ := by
  let f (p : S×Ω) := k p.1*M p.1 p.2
  have hf : Measurable f := (hk.comp measurable_fst).mul hm
  have hfs : Measurable (fun p => f p ^ 2) := hf.pow_const _
  have hi : Integrable (fun p => f p^2) (ν.prod μ) := by
    refine (integrable_prod_iff hfs.aestronglyMeasurable).2 ⟨ae_of_all _ ?_,?_⟩
    · intro s
      simpa only [f,mul_pow] using ((hm₂ s).integrable_sq.const_mul ((k s)^2))
    · refine (hk₂.integrable_sq.mul_const C).mono'
        (hfs.stronglyMeasurable.norm.integral_prod_right').aestronglyMeasurable ?_
      filter_upwards [hmC] with s hs
      have hnn (ω : Ω) : 0≤(k s * M s ω)^2 := sq_nonneg _
      change ‖∫ ω,‖(k s * M s ω)^2‖ ∂μ‖ ≤ (k s)^2*C
      simp_rw [Real.norm_of_nonneg (hnn _),mul_pow]
      rw [integral_const_mul,Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _))]
      exact mul_le_mul_of_nonneg_left hs (sq_nonneg _)
  have hsm : StronglyMeasurable (fun ω => ∫ s,f (s,ω) ∂ν) :=
    hf.stronglyMeasurable.integral_prod_left'
  refine (memLp_two_iff_integrable_sq hsm.aestronglyMeasurable).2 ?_
  refine (hi.integral_prod_right.const_mul (ν.real univ)).mono' (hsm.pow 2).aestronglyMeasurable ?_
  filter_upwards [hi.prod_left_ae] with ω hω
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact integral_sq_le_measure_mul_sqIntegral
    ((memLp_two_iff_integrable_sq (hf.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).2 hω)

#print axioms weighted_path_memLp_two

end RoughHeston
