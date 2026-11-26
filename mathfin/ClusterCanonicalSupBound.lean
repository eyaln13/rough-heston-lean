import ClusterSupremumMoment

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston

/-- The Kolmogorov supremum bound, with the moment coefficient and the length
of the physical time interval retained explicitly. -/
theorem canonical_sup_power_of_increments {n : ℕ} (hn : 0<n) {γ : ℝ} (hγ : 1<γ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (T : ℝ≥0) (_ : 0<T)
      (μ : Measure (CanonicalPath T (ℝ × ℝ))) (C : ℝ≥0∞) (_ : C ≠ ⊤),
      (∀ᵐ f ∂μ, f (canonicalEvalTime T 0) = 0) →
      (∀ s t : CanonicalPathTime T,
        (∫⁻ f : CanonicalPath T (ℝ × ℝ), edist (f s) (f t)^(n:ℝ) ∂μ) ≤ C*edist s t^γ) →
      Integrable (fun f => ‖f‖^n) μ ∧ (∫ f, ‖f‖^n ∂μ) ≤ K*C.toReal*(T:ℝ)^γ := by
  obtain ⟨r,q,hr,hr1,hq,hgeom⟩ := canonical_dyadic_geometric_factors
    (n:ℝ) γ (by exact_mod_cast hn) hγ
  let G := 1+2*(r:ℝ)/(1-r)
  let L := ((1-2*(q:ℝ≥0∞))⁻¹).toReal
  have hG : 0 ≤ G := by dsimp [G]; have : (r:ℝ) < 1 := hr1; positivity
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  refine ⟨2^(n-1)*G^n*L, by positivity, ?_⟩
  intro T hT μ C hC hzero hinc
  have hz : (fun f : CanonicalPath T (ℝ × ℝ) => ‖f (canonicalEvalTime T 0)‖^n)
      =ᵐ[μ] fun _ => (0:ℝ) := hzero.mono fun f hf => by simp [hf, hn.ne']
  have hi : Integrable (fun f : CanonicalPath T (ℝ × ℝ) => ‖f (canonicalEvalTime T 0)‖^n) μ :=
    (integrable_zero _ _ _).congr hz.symm
  have hq' : 2*(q:ℝ≥0∞)<1 := by exact_mod_cast hq
  obtain ⟨hint,hest⟩ := canonical_sup_same_power_of_dyadic_moments hT hn hr hr1
    (ENNReal.mul_ne_top hC ENNReal.coe_ne_top) hq' hi (hgeom T μ C hinc)
  refine ⟨hint, hest.trans_eq ?_⟩
  rw [integral_congr_ae hz,integral_zero,zero_add,ENNReal.toReal_mul,ENNReal.toReal_mul]
  change 2^(n-1)*(G^n*(C.toReal*((T^γ:ℝ≥0):ℝ)*L)) = _
  rw [NNReal.coe_rpow]
  ring

#print axioms canonical_sup_power_of_increments

end RoughHeston
