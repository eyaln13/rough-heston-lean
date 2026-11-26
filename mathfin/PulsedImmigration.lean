import FractionalKernelIncrements

open MeasureTheory Filter Set
open scoped MeasureTheory Topology BigOperators

namespace RoughHeston

/-- The cumulative pulse input. Cells have length `ε / b`, each pulse
has width `d`, and its total mass is `ε`. -/
noncomputable def cumulativePulsedInput (ε b d t : ℝ) : ℝ :=
  let Δ := ε / b
  let n := Nat.floor (t / Δ)
  ε * (n : ℝ) + ε * min 1 ((t - (n : ℝ) * Δ) / d)

/-- The departure from the constant immigration clock is at most one
pulse mass, uniformly over all positive observation times. -/
theorem cumulativePulsedInput_error_le {ε b d t : ℝ}
    (hε : 0 < ε) (hb : 0 < b) (hd : 0 < d) (ht : 0 ≤ t) :
    |cumulativePulsedInput ε b d t - b * t| ≤ ε := by
  let Δ := ε / b
  let n := Nat.floor (t / Δ)
  let u := t - (n : ℝ) * Δ
  have hΔ : 0 < Δ := div_pos hε hb
  have hn : (n : ℝ) ≤ t / Δ := Nat.floor_le (div_nonneg ht hΔ.le)
  have hu₀ : 0 ≤ u := sub_nonneg.mpr ((le_div_iff₀ hΔ).1 hn)
  have hnext : t / Δ < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have huΔ : u < Δ := by
    have hm := (div_lt_iff₀ hΔ).1 hnext
    dsimp [u]
    linarith
  have hclock : b * Δ = ε := by dsimp [Δ]; field_simp
  have ht' : b * t = ε * (n : ℝ) + b * u := by
    calc
      _ = b * Δ * (n : ℝ) + b * u := by dsimp [u]; ring
      _ = _ := by rw [hclock]
  change |ε * (n : ℝ) + ε * min 1 (u / d) - b * t| ≤ ε
  rw [ht', show ε * (n : ℝ) + ε * min 1 (u / d) - (ε * (n : ℝ) + b * u) =
    ε * min 1 (u / d) - b * u by ring]
  have hpu₀ : 0 ≤ ε * min 1 (u / d) := mul_nonneg hε.le (le_min zero_le_one (div_nonneg hu₀ hd.le))
  have hpu₁ : ε * min 1 (u / d) ≤ ε :=
    (mul_le_mul_of_nonneg_left (min_le_left _ _) hε.le).trans_eq (mul_one ε)
  have hcu₀ : 0 ≤ b * u := mul_nonneg hb.le hu₀
  have hcu₁ : b * u ≤ ε := (mul_le_mul_of_nonneg_left huΔ.le hb.le).trans_eq hclock
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Equal total input on a cell bounds the convolution error by the
cell's mass times the oscillation of the elapsed-time weight. -/
theorem equal_mass_cell_convolution_bound {S : Type*} [MeasurableSpace S]
    {ν : Measure S} {v f g : S → ℝ} {m a b : ℝ}
    (hfi : Integrable f ν) (hgi : Integrable g ν)
    (hf : ∀ᵐ x ∂ν, 0 ≤ f x) (hg : ∀ᵐ x ∂ν, 0 ≤ g x)
    (hfm : ∫ x, f x ∂ν = m) (hgm : ∫ x, g x ∂ν = m)
    (hfv : Integrable (fun x => v x * f x) ν)
    (hgv : Integrable (fun x => v x * g x) ν)
    (hvl : ∀ᵐ x ∂ν, a ≤ v x) (hvu : ∀ᵐ x ∂ν, v x ≤ b) :
    |(∫ x, v x * f x ∂ν) - ∫ x, v x * g x ∂ν| ≤ m * (b - a) := by
  have hl {h : S → ℝ} (hi : Integrable h ν) (hn : ∀ᵐ x ∂ν, 0 ≤ h x)
      (hm : ∫ x, h x ∂ν = m) (hv : Integrable (fun x => v x * h x) ν) :
      a * m ≤ ∫ x, v x * h x ∂ν := by
    rw [← hm, ← integral_const_mul]
    exact integral_mono_ae (hi.const_mul a) hv
      (hvl.mp (hn.mono fun _ hn' hb' => mul_le_mul_of_nonneg_right hb' hn'))
  have hu {h : S → ℝ} (hi : Integrable h ν) (hn : ∀ᵐ x ∂ν, 0 ≤ h x)
      (hm : ∫ x, h x ∂ν = m) (hv : Integrable (fun x => v x * h x) ν) :
      (∫ x, v x * h x ∂ν) ≤ b * m := by
    rw [← hm, ← integral_const_mul]
    exact integral_mono_ae hv (hi.const_mul b)
      (hvu.mp (hn.mono fun _ hn' hb' => mul_le_mul_of_nonneg_right hb' hn'))
  refine abs_le.mpr ⟨?_, ?_⟩ <;>
    nlinarith [hl hfi hf hfm hfv, hu hfi hf hfm hfv, hl hgi hg hgm hgv, hu hgi hg hgm hgv]

/-- The error from early full mesh cells telescopes for a decreasing
kernel. The last cells near the singularity are estimated separately. -/
theorem pulse_early_cells_telescope {n : ℕ} {m : ℝ} {A D : ℕ → ℝ}
    (hA : ∀ j < n, |A j| ≤ m * (D (j + 1) - D j)) :
    |∑ j ∈ Finset.range n, A j| ≤ m * (D n - D 0) := by
  calc
    _ ≤ ∑ j ∈ Finset.range n, |A j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range n, m * (D (j + 1) - D j) :=
      Finset.sum_le_sum fun j hj => hA j (Finset.mem_range.mp hj)
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      clear hA
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        ring

end RoughHeston

#print axioms RoughHeston.cumulativePulsedInput_error_le
#print axioms RoughHeston.equal_mass_cell_convolution_bound
#print axioms RoughHeston.pulse_early_cells_telescope
