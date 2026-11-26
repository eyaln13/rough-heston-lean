import HestonAffineTransformIdentity
import FractionalKernelIncrements

open MeasureTheory Set Filter

namespace RoughHeston

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The inverse-kernel part of the input reproduces the initial state at
every positive time. Its defining Bochner integral is absolutely integrable. -/
theorem affine_initial_input_convolution {α t : ℝ} (hα : 0 < α) (hα' : α < 1)
    (ht : 0 < t) (x : E) :
    IntegrableOn (fun s => fractionalK α (t-s) * fractionalL α s) (Ioc 0 t) ∧
    volterraSmulConvolution (fractionalK α) (fun s => fractionalL α s • x) t = x := by
  have h := (volterraConvolution_comm_at (f := fractionalK α) (g := fractionalL α) ht.le).trans
    (fractional_causal_kernel_inverse hα hα' ht)
  change (∫ s in Ioc 0 t, fractionalK α (t-s) * fractionalL α s) = 1 at h
  refine ⟨?_, ?_⟩
  · by_contra hn
    rw [integral_undef hn] at h
    exact zero_ne_one h
  · unfold volterraSmulConvolution
    simp_rw [smul_smul, integral_smul_const, h, one_smul]

/-- For positive observation times the affine input and the manuscript's
additive initial-value formulation give the same direct equation. At
time zero the initial state is prescribed separately by the model. -/
theorem affine_input_drift_convolution {α t κ : ℝ} (hα : 0 < α) (hα' : α < 1)
    (ht : 0 < t) (x : E) (b v : ℝ → E)
    (hb : IntegrableOn (fun s => fractionalK α (t-s) • (b s - κ • v s)) (Ioc 0 t)) :
    volterraSmulConvolution (fractionalK α) (fun s => b s + fractionalL α s • x - κ • v s) t =
      x + volterraSmulConvolution (fractionalK α) (fun s => b s - κ • v s) t := by
  obtain ⟨hi, hx⟩ := affine_initial_input_convolution hα hα' ht x
  have he (s : ℝ) : fractionalK α (t-s) • (b s + fractionalL α s • x - κ • v s) =
      (fractionalK α (t-s) * fractionalL α s) • x + fractionalK α (t-s) • (b s - κ • v s) := by
    rw [← smul_smul, ← smul_add]
    abel
  unfold volterraSmulConvolution at hx ⊢
  simp_rw [smul_smul] at hx
  simp_rw [he]
  rw [integral_add (hi.smul_const x) hb, hx]

end RoughHeston

#print axioms RoughHeston.affine_initial_input_convolution
#print axioms RoughHeston.affine_input_drift_convolution
