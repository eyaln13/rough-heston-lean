import DyadicStepApproximation
import StochasticProcess

open Set Filter
open scoped BigOperators NNReal Topology

namespace RoughHeston

/-- Clip every vertex of the uniform dyadic grid at the observation time. -/
noncomputable def clippedDyadicGrid (T t : ℝ≥0) (n : ℕ) : ℕ →o ℝ≥0 where
  toFun k := min ((uniformDyadicGrids T).grid n k) t
  monotone' := fun _ _ h => min_le_min_right _ (((uniformDyadicGrids T).grid n).monotone h)

@[simp] theorem clippedDyadicGrid_apply (T t : ℝ≥0) (n k : ℕ) :
    clippedDyadicGrid T t n k = min ((uniformDyadicGrids T).grid n k) t := rfl

@[simp] theorem clippedDyadicGrid_first_vertex (T t : ℝ≥0) (n : ℕ) :
    clippedDyadicGrid T t n 0 = 0 := by
  rw [clippedDyadicGrid_apply, uniform_dyadic_first_vertex, min_eq_left zero_le]

/-- A grid clipped at an observation time within the horizon ends at that time. -/
theorem clippedDyadicGrid_terminal_vertex {T t : ℝ≥0} (ht : t ≤ T) (n : ℕ) :
    clippedDyadicGrid T t n (2 ^ n) = t := by
  rw [clippedDyadicGrid_apply, uniform_dyadic_terminal_vertex, min_eq_right ht]

/-- Clipping leaves the cells unchanged at points on the clipped horizon. -/
theorem mem_Ioc_clippedDyadicGrid_iff {T t s : ℝ≥0} (hs : s ≤ t) (n k : ℕ) :
    s ∈ Ioc (clippedDyadicGrid T t n k) (clippedDyadicGrid T t n (k + 1)) ↔
      s ∈ Ioc ((uniformDyadicGrids T).grid n k) ((uniformDyadicGrids T).grid n (k + 1)) := by
  simp only [mem_Ioc, clippedDyadicGrid_apply, min_lt_iff, le_min_iff]
  simp [not_lt_of_ge hs, hs]

/-- On the clipped horizon the sampled step weights are those of the
original grid with the time argument of the coefficient stopped. -/
theorem clippedDyadicGrid_step_eq {T t s : ℝ≥0} (hs : s ≤ t) (n : ℕ) (H : ℝ≥0 → ℝ) :
    (∑ k ∈ Finset.range (2 ^ n),
      (Ioc (clippedDyadicGrid T t n k) (clippedDyadicGrid T t n (k + 1))).indicator
        (fun _ => H (clippedDyadicGrid T t n k)) s) =
      uniformDyadicStep T n (fun r => H (min r t)) s := by
  classical
  unfold uniformDyadicStep
  refine Finset.sum_congr rfl ?_
  intro k _
  let G := (uniformDyadicGrids T).grid n
  change (Ioc (clippedDyadicGrid T t n k) (clippedDyadicGrid T t n (k + 1))).indicator
      (fun _ => H (clippedDyadicGrid T t n k)) s =
    (Ioc (G k) (G (k + 1))).indicator (fun _ => H (min (G k) t)) s
  have he := mem_Ioc_clippedDyadicGrid_iff (T := T) hs n k
  by_cases h : s ∈ Ioc (G k) (G (k + 1))
  · rw [indicator_of_mem (he.mpr h), indicator_of_mem h]
    rfl
  · simp only [indicator_of_notMem h, indicator_of_notMem (h.comp he.mp)]

/-- The sampled coefficients on a clipped horizon converge pointwise
to a continuous time weight on that horizon. -/
theorem tendsto_clippedDyadicGrid_step {T t s : ℝ≥0} (ht : t ≤ T) (hs : s ∈ Ioc 0 t)
    {H : ℝ≥0 → ℝ} (hH : ContinuousOn H (Icc 0 t)) :
    Tendsto (fun n => ∑ k ∈ Finset.range (2 ^ n),
      (Ioc (clippedDyadicGrid T t n k) (clippedDyadicGrid T t n (k + 1))).indicator
        (fun _ => H (clippedDyadicGrid T t n k)) s) atTop (𝓝 (H s)) := by
  have hmin : Continuous (fun r : ℝ≥0 => min r t) := continuous_id.min continuous_const
  have hc : ContinuousOn (fun r : ℝ≥0 => H (min r t)) (Icc 0 T) :=
    hH.comp hmin.continuousOn (fun r _ => ⟨zero_le, min_le_right r t⟩)
  have hp := tendsto_uniformDyadicStep hc (show s ∈ Ioc 0 T from ⟨hs.1, hs.2.trans ht⟩)
  rw [min_eq_left hs.2] at hp
  exact hp.congr (fun n => (clippedDyadicGrid_step_eq hs.2 n H).symm)

variable {Ω : Type*}

/-- The ordinary sum on the clipped grid equals the stopped integral
on the original grid. Cells starting at or after the observation time
make zero contribution. -/
theorem gridIntegral_clippedDyadicGrid_eq_stopped (T t : ℝ≥0) (n : ℕ)
    (H B : ℝ≥0 → Ω → ℝ) :
    gridIntegral (clippedDyadicGrid T t n) (fun k => H (clippedDyadicGrid T t n k)) B (2 ^ n) =
      gridIntegralProcess ((uniformDyadicGrids T).grid n)
        (fun k => H ((uniformDyadicGrids T).grid n k)) B (2 ^ n) t := by
  let G := (uniformDyadicGrids T).grid n
  unfold gridIntegral runningSum gridIntegralProcess
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  ext ω
  change H (min (G k) t) ω * (B (min (G (k + 1)) t) ω - B (min (G k) t) ω) =
    H (G k) ω * (B (min t (G (k + 1))) ω - B (min t (G k)) ω)
  rw [min_comm t (G (k + 1)), min_comm t (G k)]
  by_cases h : G k ≤ t
  · rw [min_eq_left h]
  · have hleft : t ≤ G k := le_of_not_ge h
    have hright : t ≤ G (k + 1) := hleft.trans (G.monotone k.le_succ)
    simp only [min_eq_right hleft, min_eq_right hright, sub_self, mul_zero]

end RoughHeston

#print axioms RoughHeston.clippedDyadicGrid_terminal_vertex
#print axioms RoughHeston.mem_Ioc_clippedDyadicGrid_iff
#print axioms RoughHeston.clippedDyadicGrid_step_eq
#print axioms RoughHeston.tendsto_clippedDyadicGrid_step
#print axioms RoughHeston.gridIntegral_clippedDyadicGrid_eq_stopped
