import FractionalCoupledPathLaw

/-! Finite-vector moment estimates on the common physical path space. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston

theorem enorm_pi_pow_le_sum {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) (m : ℕ) : ‖x‖ₑ^m ≤ ∑ i, ‖x i‖ₑ^m := by
  classical
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ (fun i => ‖x i‖) Finset.univ_nonempty
  have hx : ‖x‖ ≤ ‖x k‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    fun i => hk i (Finset.mem_univ i)
  have he : ‖x‖ₑ ≤ ‖x k‖ₑ := by simp only [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal hx
  exact (pow_le_pow_left' he m).trans
    (Finset.single_le_sum (f := fun i => ‖x i‖ₑ^m) (fun _ _ => zero_le) (Finset.mem_univ k))

theorem enorm_pair_pi_pow_le_sum {ι : Type*} [Fintype ι] [Nonempty ι]
    (x y : ι → ℝ) (m : ℕ) :
    ‖(x,y)‖ₑ^m ≤ (∑ i, ‖x i‖ₑ^m) + ∑ i, ‖y i‖ₑ^m := by
  have h : ‖(x,y)‖ₑ = max ‖x‖ₑ ‖y‖ₑ := by rw [← ofReal_norm, Prod.norm_def]; simp only [ENNReal.ofReal_max, ofReal_norm]
  rw [h]
  rcases le_total ‖x‖ₑ ‖y‖ₑ with hxy | hyx
  · rw [max_eq_right hxy]
    exact (enorm_pi_pow_le_sum y m).trans le_add_self
  · rw [max_eq_left hyx]
    exact (enorm_pi_pow_le_sum x m).trans le_self_add

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The joint path increments are bounded by the finite sum of scalar
variance and residual increments, without dimension-dependent exponents. -/
theorem canonicalPhysical_edist_pow_le_scalar_sum
    (T : ℝ≥0) (s t : CanonicalPathTime T) (p : CanonicalPath T (CoupledPhysicalState ι))
    (m : ℕ) :
    edist (p s) (p t)^m ≤
      (∑ i : Option ι, ‖canonicalPhysicalVariance T i t p-canonicalPhysicalVariance T i s p‖ₑ^m) +
      (∑ i : Option ι, ‖canonicalPhysicalResidual T i t p-canonicalPhysicalResidual T i s p‖ₑ^m) := by
  have hs : canonicalEvalTime T s = s := Subtype.ext (min_eq_left s.property.2)
  have ht : canonicalEvalTime T t = t := Subtype.ext (min_eq_left t.property.2)
  rw [edist_comm, edist_eq_enorm_sub]
  simp only [canonicalPhysicalVariance, canonicalPhysicalResidual, canonicalPathEval, hs, ht]
  exact enorm_pair_pi_pow_le_sum ((p t).1-(p s).1) ((p t).2-(p s).2) m

theorem canonicalPhysical_lintegral_edist_pow_le_of_rows
    {T : ℝ≥0} {μ : Measure (CanonicalPath T (CoupledPhysicalState ι))}
    (s t : CanonicalPathTime T) (m : ℕ) {CV CM : ℝ≥0∞}
    (hV : ∀ i, (∫⁻ p, ‖canonicalPhysicalVariance T i t p-canonicalPhysicalVariance T i s p‖ₑ^m ∂μ) ≤ CV)
    (hM : ∀ i, (∫⁻ p, ‖canonicalPhysicalResidual T i t p-canonicalPhysicalResidual T i s p‖ₑ^m ∂μ) ≤ CM) :
    (∫⁻ p : CanonicalPath T (CoupledPhysicalState ι), edist (p s) (p t)^m ∂μ) ≤
      (Fintype.card (Option ι) : ℝ≥0∞)*(CV+CM) := by
  let U (i : Option ι) (p : CanonicalPath T (CoupledPhysicalState ι)) :=
    ‖canonicalPhysicalVariance T i t p-canonicalPhysicalVariance T i s p‖ₑ^m
  let V (i : Option ι) (p : CanonicalPath T (CoupledPhysicalState ι)) :=
    ‖canonicalPhysicalResidual T i t p-canonicalPhysicalResidual T i s p‖ₑ^m
  have hVc (i : Option ι) (r : ℝ≥0) : Continuous (canonicalPhysicalVariance T i r) :=
    ((continuous_apply i).comp continuous_fst).comp (continuous_canonicalPathEval T r)
  have hMc (i : Option ι) (r : ℝ≥0) : Continuous (canonicalPhysicalResidual T i r) :=
    ((continuous_apply i).comp continuous_snd).comp (continuous_canonicalPathEval T r)
  have hUm (i : Option ι) : Measurable (U i) :=
    (((hVc i t).sub (hVc i s)).measurable.enorm).pow_const _
  have hVm (i : Option ι) : Measurable (V i) :=
    (((hMc i t).sub (hMc i s)).measurable.enorm).pow_const _
  have hh := lintegral_mono (μ := μ) fun p => canonicalPhysical_edist_pow_le_scalar_sum T s t p m
  change _ ≤ ∫⁻ p, (∑ i, U i p)+(∑ i, V i p) ∂μ at hh
  rw [lintegral_add_left (Finset.measurable_sum _ fun i _ => hUm i),
    lintegral_finsetSum _ (fun i _ => hUm i), lintegral_finsetSum _ (fun i _ => hVm i)] at hh
  refine hh.trans ?_
  have hA := add_le_add (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hV i))
    (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hM i))
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_add] using hA

#print axioms RoughHeston.canonicalPhysical_lintegral_edist_pow_le_of_rows

end RoughHeston
