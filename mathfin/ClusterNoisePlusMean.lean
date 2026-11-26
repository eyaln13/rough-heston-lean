import ClusterRealMomentTransfer

open MeasureTheory Filter
open scoped ENNReal

namespace RoughHeston

/-- Add the deterministic cluster mean to a noise moment estimate. -/
theorem cluster_moment_of_mean_and_noise {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X N : Ω → ℝ} {v c : ℝ} {p : ℕ}
    (hv : 0 ≤ v) (hx : ∀ ω, 0 ≤ X ω)
    (he : X =ᵐ[P] fun ω => v+N ω)
    (hN : MemLp N (p : ℝ≥0∞) P) (hc : (∫ ω, ‖N ω‖^p ∂P) ≤ c) :
    MemLp X (p : ℝ≥0∞) P ∧
      (∫ ω, X ω^p ∂P) ≤ (2:ℝ)^(p-1)*(v^p+c) := by
  have hXp : MemLp X (p:ℝ≥0∞) P :=
    ((memLp_const v).add hN).ae_eq he.symm
  refine ⟨hXp,?_⟩
  have hXi : Integrable (fun ω => X ω^p) P := by
    simpa only [Real.norm_of_nonneg (hx _)] using hXp.integrable_norm_pow'
  have hNi := hN.integrable_norm_pow'
  have hbound : (fun ω => X ω^p) ≤ᵐ[P] fun ω => (2:ℝ)^(p-1)*(v^p+‖N ω‖^p) := by
    filter_upwards [he] with ω hw
    have h' : X ω ≤ v+‖N ω‖ := by rw [hw]; simpa only [Real.norm_eq_abs] using (show v+N ω ≤ v+|N ω| by linarith [le_abs_self (N ω)])
    exact (pow_le_pow_left₀ (hx ω) h' p).trans (add_pow_le hv (norm_nonneg _) p)
  have hconst : Integrable (fun _ : Ω => v^p) P := integrable_const _
  have hi := integral_mono_ae hXi ((hconst.add hNi).const_mul _) hbound
  rw [integral_const_mul] at hi
  simp only [Pi.add_apply] at hi
  rw [integral_add hconst hNi, integral_const, probReal_univ, one_smul] at hi
  exact hi.trans (mul_le_mul_of_nonneg_left (by linarith only [hc]) (by positivity))

#print axioms cluster_moment_of_mean_and_noise

end RoughHeston
