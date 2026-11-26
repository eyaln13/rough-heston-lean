import PulsedImmigration
import RectangularPulseMeasure

/-! The actual rectangular cluster rates have the cumulative immigration
clock used in the deterministic mesh estimates. -/

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

set_option maxHeartbeats 1000000

noncomputable def fullPulseBirthCount (T b ε : ℝ) : ℕ := ⌊T/(ε/b)⌋₊+1

/-- All points `j ε/b` of the mesh up to the horizon, including zero. -/
noncomputable def explicitPulsedRate (T b ε d : ℝ) (s : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (fullPulseBirthCount T b ε),
    rectangularPulseRate ε d (s-(j:ℝ)*(ε/b))

private theorem intervalIntegrable_shifted_rectangularPulseRate (ε d τ a c : ℝ) :
    IntervalIntegrable (fun s : ℝ => rectangularPulseRate ε d (s-τ)) volume a c := by
  have hm : Measurable (fun s : ℝ => rectangularPulseRate ε d (s-τ)) :=
    (measurable_const.indicator measurableSet_Ioc).comp (measurable_id.sub measurable_const)
  rw [intervalIntegrable_iff]
  have h : IntervalIntegrable (fun _ : ℝ => ‖ε/d‖) volume a c := intervalIntegrable_const
  rw [intervalIntegrable_iff] at h
  apply h.mono' hm.aestronglyMeasurable
  apply Eventually.of_forall
  intro s
  by_cases hs : s-τ ∈ Ioc (0:ℝ) d <;> simp [rectangularPulseRate, hs] <;> positivity

theorem integral_shifted_rectangularPulseRate {ε d τ t : ℝ} (hτ : 0 ≤ τ) (ht : 0 ≤ t) :
    (∫ s in (0:ℝ)..t, rectangularPulseRate ε d (s-τ)) =
      (ε/d)*max (min d (t-τ)) 0 := by
  have hRate (s : ℝ) : rectangularPulseRate ε d (s-τ) =
      (Ioc τ (τ+d)).indicator (fun _ : ℝ => ε/d) s := by
    unfold rectangularPulseRate
    have h : s-τ ∈ Ioc (0:ℝ) d ↔ s ∈ Ioc τ (τ+d) := by
      simp only [mem_Ioc]
      exact and_congr (sub_pos) (sub_le_iff_le_add.trans (by rw [add_comm]))
    by_cases hs : s ∈ Ioc τ (τ+d) <;> simp [hs, h]
  rw [intervalIntegral.integral_of_le ht]
  simp_rw [hRate]
  rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    integral_const, Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter, Ioc_inter_Ioc,
    max_eq_left hτ, Real.volume_Ioc, ENNReal.toReal_ofReal' , smul_eq_mul]
  have hm : min (τ+d) t-τ = min d (t-τ) := by rw [← min_sub_sub_right, add_sub_cancel_left]
  rw [hm, mul_comm]

theorem explicitPulsedRate_integral_eq_clock {ε b d T t : ℝ}
    (hε : 0 < ε) (hb : 0 < b) (hd : 0 < d) (hdΔ : d ≤ ε/b)
    (ht : t ∈ Icc (0:ℝ) T) :
    (∫ s in (0:ℝ)..t, explicitPulsedRate T b ε d s) = cumulativePulsedInput ε b d t := by
  let Δ := ε/b
  let n := ⌊t/Δ⌋₊
  let N := fullPulseBirthCount T b ε
  let F (j : ℕ) := (ε/d)*max (min d (t-(j:ℝ)*Δ)) 0
  have hΔ : 0 < Δ := div_pos hε hb
  have hnt := (le_div_iff₀ hΔ).mp (Nat.floor_le (div_nonneg ht.1 hΔ.le))
  have htN := (div_lt_iff₀ hΔ).mp (Nat.lt_floor_add_one (t/Δ))
  have hnN : n+1 ≤ N := by
    unfold N n fullPulseBirthCount Δ
    exact Nat.succ_le_succ (Nat.floor_mono (div_le_div_of_nonneg_right ht.2 hΔ.le))
  have hCells (j : ℕ) (hj : j < n) : F j = ε := by
    have hjn : ((j:ℝ)+1) ≤ (n:ℝ) := by exact_mod_cast hj
    have h := mul_le_mul_of_nonneg_right hjn hΔ.le
    have hjd : d ≤ t-(j:ℝ)*Δ := by nlinarith [hnt, hdΔ]
    simp only [F, min_eq_left hjd, max_eq_left hd.le, div_mul_cancel₀ _ hd.ne']
  have hLater (j : ℕ) (hj : n+1 ≤ j) : F j = 0 := by
    have hnj : ((n:ℝ)+1) ≤ (j:ℝ) := by exact_mod_cast hj
    have h := mul_le_mul_of_nonneg_right hnj hΔ.le
    have hjt : t-(j:ℝ)*Δ ≤ 0 := by nlinarith
    simp only [F, max_eq_right ((min_le_right d _).trans hjt), mul_zero]
  have hAt : F n = ε*min 1 ((t-(n:ℝ)*Δ)/d) := by
    let u := t-(n:ℝ)*Δ
    have hu : 0 ≤ u := sub_nonneg.mpr hnt
    change ε/d*max (min d u) 0 = _
    rw [max_eq_left (le_min hd.le hu)]
    by_cases h : u ≤ d
    · rw [min_eq_right h, min_eq_right ((div_le_one₀ hd).2 h)]
      ring
    · rw [min_eq_left (le_of_not_ge h), min_eq_left ((one_le_div₀ hd).2 (le_of_not_ge h)),
        div_mul_cancel₀ _ hd.ne', mul_one]
  change (∫ s in (0:ℝ)..t, (∑ j ∈ Finset.range N, rectangularPulseRate ε d (s-(j:ℝ)*Δ))) = _
  rw [intervalIntegral.integral_finsetSum (s := Finset.range N)
    (f := fun (j : ℕ) s => rectangularPulseRate ε d (s-(j:ℝ)*Δ))
    (fun j _ => intervalIntegrable_shifted_rectangularPulseRate ε d ((j:ℝ)*Δ) 0 t)]
  have hSum : (∑ j ∈ Finset.range N, ∫ s in (0:ℝ)..t, rectangularPulseRate ε d (s-(j:ℝ)*Δ)) =
      ∑ j ∈ Finset.range N, F j := by
    apply Finset.sum_congr rfl
    intro j _
    exact integral_shifted_rectangularPulseRate (mul_nonneg (Nat.cast_nonneg _) hΔ.le) ht.1
  change (∑ j ∈ Finset.range N, ∫ s in (0:ℝ)..t, rectangularPulseRate ε d (s-(j:ℝ)*Δ)) = _
  rw [hSum, ← Finset.sum_subset (Finset.range_mono hnN) (fun j _ hj => hLater j (by
      simpa only [Finset.mem_range, not_lt] using hj)), Finset.sum_range_succ, hAt]
  have hEarly : (∑ j ∈ Finset.range n, F j) = (n:ℝ)*ε := by
    rw [show (∑ j ∈ Finset.range n, F j) = ∑ _j ∈ Finset.range n, ε from
      Finset.sum_congr rfl (fun j hj => hCells j (Finset.mem_range.mp hj)),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hEarly]
  change (n:ℝ)*ε + _ = ε*(n:ℝ) + _
  rw [mul_comm (n:ℝ) ε]

theorem explicitPulsedRate_clock_error_le {ε b d T t : ℝ}
    (hε : 0 < ε) (hb : 0 < b) (hd : 0 < d) (hdΔ : d ≤ ε/b)
    (ht : t ∈ Icc (0:ℝ) T) :
    |(∫ s in (0:ℝ)..t, explicitPulsedRate T b ε d s)-b*t| ≤ ε := by
  rw [explicitPulsedRate_integral_eq_clock hε hb hd hdΔ ht]
  exact cumulativePulsedInput_error_le hε hb hd ht.1

#print axioms RoughHeston.explicitPulsedRate_integral_eq_clock
#print axioms RoughHeston.explicitPulsedRate_clock_error_le

end RoughHeston
