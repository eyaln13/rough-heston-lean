import FractionalExponentialApproximation
import SmoothExponentialConvolutionDerivative
import SmoothCoupledDrift

/-! The right-endpoint approximants have exactly the positive
finite-exponential resolvents used by the coupled lifts. -/

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RoughHeston

def fractionalApproximationOrder (n : ℕ) : ℕ := (n+1)^2-1

theorem fractionalApproximationOrder_succ (n : ℕ) :
    fractionalApproximationOrder n + 1 = (n+1)^2 := by
  unfold fractionalApproximationOrder
  exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (Nat.succ_ne_zero n)))

noncomputable def fractionalApproximationFinWeight (α : ℝ) (n : ℕ)
    (j : Fin (fractionalApproximationOrder n + 1)) : ℝ :=
  fractionalApproximationWeight α n (j.val+1)

noncomputable def fractionalApproximationFinRate (n : ℕ)
    (j : Fin (fractionalApproximationOrder n + 1)) : ℝ :=
  fractionalApproximationRate n (j.val+1)

private theorem fractionalApproximationFin_mem {n : ℕ}
    (j : Fin (fractionalApproximationOrder n + 1)) :
    j.val+1 ∈ fractionalApproximationIndices n := by
  rw [fractionalApproximationIndices, Finset.mem_Icc, ← fractionalApproximationOrder_succ]
  exact ⟨by omega, j.isLt⟩

theorem fractionalApproximationFinRate_pos (n : ℕ) (j : Fin (fractionalApproximationOrder n + 1)) :
    0 < fractionalApproximationFinRate n j :=
  fractionalApproximationRate_pos (fractionalApproximationFin_mem j)

theorem strictMono_fractionalApproximationFinRate (n : ℕ) :
    StrictMono (fractionalApproximationFinRate n) := by
  intro i j hij
  unfold fractionalApproximationFinRate fractionalApproximationRate
  apply div_lt_div_of_pos_right _ (by positivity)
  exact_mod_cast (show i.val+1 < j.val+1 from Nat.succ_lt_succ hij)

theorem fractionalApproximationFinWeight_pos {α : ℝ} (hα : 0 < α) (hα' : α < 1)
    (n : ℕ) (j : Fin (fractionalApproximationOrder n + 1)) :
    0 < fractionalApproximationFinWeight α n j :=
  fractionalApproximationWeight_pos hα hα' (fractionalApproximationFin_mem j)

theorem smoothExponentialKernel_eq_fractionalExponentialApproximation
    (α : ℝ) (n : ℕ) (t : ℝ) :
    smoothExponentialKernel (fractionalApproximationFinWeight α n) (fractionalApproximationFinRate n) t =
      fractionalExponentialApproximation α n t := by
  unfold smoothExponentialKernel fractionalExponentialApproximation
  apply Finset.sum_bij (fun j _ => j.val+1)
  · intro j _
    exact fractionalApproximationFin_mem j
  · intro i _ j _ h
    exact Fin.ext (Nat.succ.inj h)
  · intro j hj
    rw [fractionalApproximationIndices, Finset.mem_Icc, ← fractionalApproximationOrder_succ] at hj
    refine ⟨⟨j-1, by omega⟩, Finset.mem_univ _, by simp only; omega⟩
  · intro j _
    simp [fractionalApproximationFinWeight, fractionalApproximationFinRate,
      mul_comm (fractionalApproximationRate _ _) _]

theorem fractionalExponentialApproximation_pos_at_zero {α : ℝ} (hα : 0 < α) (hα' : α < 1) (n : ℕ) :
    0 < fractionalExponentialApproximation α n 0 := by
  rw [← smoothExponentialKernel_eq_fractionalExponentialApproximation]
  simp only [smoothExponentialKernel, mul_zero, neg_zero, Real.exp_zero, mul_one]
  exact Finset.sum_pos (fun j _ => fractionalApproximationFinWeight_pos hα hα' n j)
    ⟨0, Finset.mem_univ _⟩

/-- The direct-kernel and positive resolvent identity for each explicitly
defined fractional approximation. -/
theorem exists_fractionalApproximation_positive_resolvent {α : ℝ} (hα : 0 < α) (hα' : α < 1)
    (n : ℕ) :
    ∃ (ℓ₀ : ℝ) (q rate : Fin (fractionalApproximationOrder n) → ℝ),
      0 < ℓ₀ ∧ (∀ j, 0 < q j) ∧ (∀ j, 0 < rate j) ∧
      ∀ t : ℝ, 0 ≤ t →
      (1 / fractionalExponentialApproximation α n 0) * fractionalExponentialApproximation α n t +
        volterraConvolution (smoothExponentialResolvent ℓ₀ q rate)
          (fractionalExponentialApproximation α n) t = 1 := by
  let c := fractionalApproximationFinWeight α n
  let x := fractionalApproximationFinRate n
  obtain ⟨r, a, w, hr₀, hr, _, hw, h⟩ := positive_exponential_resolvent_time_domain
    (fractionalApproximationFinWeight_pos hα hα' n) (fractionalApproximationFinRate_pos n)
    (strictMono_fractionalApproximationFinRate n)
  let q (j : Fin (fractionalApproximationOrder n)) := w (some j)
  let rate (j : Fin (fractionalApproximationOrder n)) := -r (some j)
  have ha := exponential_resolvent_atom_of_time_domain c x w r a h
  refine ⟨w none, q, rate, hw _, fun j => hw _, fun j => neg_pos.mpr (hr j), ?_⟩
  intro t ht
  have hL (s : ℝ) : (∑ j, w j * Real.exp (r j * s)) = smoothExponentialResolvent (w none) q rate s := by
    rw [Fintype.sum_option]
    simp [smoothExponentialResolvent, hr₀, q, rate]
  have h0 : (∑ i, c i) = fractionalExponentialApproximation α n 0 := by
    rw [← smoothExponentialKernel_eq_fractionalExponentialApproximation]
    simp [smoothExponentialKernel, c]
  rw [h0] at ha
  specialize h t
  simp_rw [hL, ha] at h
  have hK (s : ℝ) : (∑ i, c i * Real.exp (-(x i * s))) = fractionalExponentialApproximation α n s :=
    smoothExponentialKernel_eq_fractionalExponentialApproximation α n s
  have hh : (1 / fractionalExponentialApproximation α n 0) *
      (∑ i, c i * Real.exp (-(x i*t))) +
        (∫ s in (0 : ℝ)..t, smoothExponentialResolvent (w none) q rate (t-s)*
          (∑ i, c i * Real.exp (-(x i*s)))) = 1 := h
  simp_rw [hK] at hh
  simpa only [volterraConvolution, intervalIntegral.integral_of_le ht] using hh

#print axioms RoughHeston.smoothExponentialKernel_eq_fractionalExponentialApproximation
#print axioms RoughHeston.exists_fractionalApproximation_positive_resolvent

end RoughHeston
