import ExplicitPulsedKernelProfile

/-! Uniform deterministic convergence of the actual pulsed convolution.
Old cells are sandwiched by adjacent constant-rate cells. The final
one or two pulses are estimated directly at the singular endpoint. -/

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

set_option maxHeartbeats 1800000

theorem pulseKernelResponse_zero_of_nonpos (α ε d : ℝ) {a : ℝ} (ha : a ≤ 0) :
    pulseKernelResponse α ε d a = 0 := by
  rw [pulseKernelResponse, volterraConvolution, Ioc_eq_empty_of_le ha, setIntegral_empty]

theorem explicitPulsed_convolution_eq_sum {α T b ε d t : ℝ}
    (hα : 0 < α) (hε : 0 < ε) (hb : 0 < b) :
    volterraConvolution (hestonKernel α) (explicitPulsedRate T b ε d) t =
      ∑ j ∈ Finset.range (fullPulseBirthCount T b ε), pulseKernelResponse α ε d (t-(j:ℝ)*(ε/b)) := by
  have hInt (τ : ℝ) : IntegrableOn (fun s => hestonKernel α (t-s)*rectangularPulseRate ε d (s-τ))
      (Ioc 0 t) := by
    by_cases ht : 0 ≤ t
    · have hK : IntegrableOn (fun s => hestonKernel α (t-s)) (Ioc 0 t) := by
        apply (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).1
        have h := (hestonKernel_intervalIntegrable_nonneg hα le_rfl ht).comp_sub_left t
        simpa only [sub_zero, sub_self] using h.symm
      have hRate : Measurable (fun s : ℝ => rectangularPulseRate ε d (s-τ)) :=
        (measurable_const.indicator measurableSet_Ioc).comp (measurable_id.sub measurable_const)
      refine (hK.norm.mul_const ‖ε/d‖).mono' (hK.aestronglyMeasurable.mul hRate.aestronglyMeasurable) ?_
      apply Eventually.of_forall
      intro s
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      by_cases hs : s-τ ∈ Ioc (0:ℝ) d <;> simp [rectangularPulseRate, hs] <;> positivity
    · rw [Ioc_eq_empty_of_le (le_of_not_ge ht)]
      exact integrableOn_empty
  have hTranslate (τ : ℝ) (hτ : 0 ≤ τ) :
      (∫ s in Ioc (0:ℝ) t, hestonKernel α (t-s)*rectangularPulseRate ε d (s-τ)) =
        pulseKernelResponse α ε d (t-τ) := by
    by_cases hτt : τ ≤ t
    · rcases hτ.lt_or_eq with hτ₀ | hτ₀
      · exact volterra_shifted_kernel_integral (l := hestonKernel α) (k := rectangularPulseRate ε d)
          (fun u hu => indicator_of_notMem (fun (hx : u ∈ Ioc (0:ℝ) d) => not_lt_of_ge hu hx.1) _)
          ⟨hτ₀,hτt⟩
      · subst τ
        simp only [sub_zero, pulseKernelResponse, volterraConvolution]
    · rw [pulseKernelResponse_zero_of_nonpos _ _ _ (sub_nonpos.mpr (le_of_not_ge hτt))]
      calc
        _ = ∫ _ in Ioc (0:ℝ) t, (0:ℝ) := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro r hr
          have h : r-τ ∉ Ioc (0:ℝ) d := fun h => not_lt_of_ge
            (sub_nonpos.mpr (hr.2.trans (le_of_not_ge hτt))) h.1
          simp only [rectangularPulseRate, indicator_of_notMem h, mul_zero]
        _ = 0 := integral_zero _ _
  unfold volterraConvolution explicitPulsedRate
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum (Finset.range (fullPulseBirthCount T b ε))
    (fun j _ => hInt ((j:ℝ)*(ε/b)))]
  apply Finset.sum_congr rfl
  intro j _
  exact hTranslate ((j:ℝ)*(ε/b)) (mul_nonneg (Nat.cast_nonneg j) (div_nonneg hε.le hb.le))

theorem continuous_explicitPulsed_convolution {α T b ε d : ℝ}
    (hα : 0 < α) (hε : 0 < ε) (hb : 0 < b) (hd : 0 < d) :
    Continuous (volterraConvolution (hestonKernel α) (explicitPulsedRate T b ε d)) := by
  simp_rw [show volterraConvolution (hestonKernel α) (explicitPulsedRate T b ε d) = _ from
    funext fun _ => explicitPulsed_convolution_eq_sum hα hε hb]
  exact continuous_finsetSum _ fun j _ =>
    (continuous_pulseKernelResponse hα hε.le hd).comp (continuous_id.sub continuous_const)

private theorem sum_hestonKernel_adjacent_cells {α : ℝ} (hα : 0 < α) {age : ℕ → ℝ}
    (m : ℕ) (ha : ∀ j ≤ m, 0 ≤ age j) :
    (∑ j ∈ Finset.range m, ∫ s in age (j+1)..age j, hestonKernel α s) =
      ∫ s in age m..age 0, hestonKernel α s := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih (fun j hj => ha j (hj.trans (Nat.le_succ m))), add_comm]
    exact intervalIntegral.integral_add_adjacent_intervals
      (hestonKernel_intervalIntegrable_nonneg hα (ha _ le_rfl) (ha _ (Nat.le_succ m)))
      (hestonKernel_intervalIntegrable_nonneg hα (ha _ (Nat.le_succ m)) (ha _ (Nat.zero_le _)))

private theorem hestonKernel_interval_le_origin {α a c t : ℝ} (hα : 0 < α)
    (ha : 0 ≤ a) (hac : a ≤ c) (hct : c ≤ t) :
    (∫ s in a..c, hestonKernel α s) ≤ ∫ s in (0:ℝ)..t, hestonKernel α s := by
  have ht := ha.trans (hac.trans hct)
  rw [intervalIntegral.integral_of_le hac, intervalIntegral.integral_of_le ht]
  exact setIntegral_mono_set ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht).1
    (hestonKernel_intervalIntegrable_nonneg hα le_rfl ht))
    (ae_of_all _ (hestonKernel_nonneg_explicit hα)) (Ioc_subset_Ioc ha hct).eventuallyLE

/-- An explicit error bound for the aggregate convolution, uniform up
to the final mesh point and at all partially elapsed pulses. -/
theorem explicitPulsed_convolution_difference_bounds {α T b ε d t : ℝ}
    (hα : 0 < α) (hα' : α ≤ 1) (hε : 0 < ε) (hb : 0 < b) (hd : 0 < d)
    (hdΔ : d ≤ ε/b) (ht : t ∈ Icc (0:ℝ) T) :
    let Δ := ε/b
    let P := volterraConvolution (hestonKernel α) (explicitPulsedRate T b ε d) t
    let Q := b*(∫ s in (0:ℝ)..t, hestonKernel α s)
    Q - b*((2*Δ)^α/(Real.Gamma α*α)) ≤ P ∧
      P ≤ Q+2*((ε/d)*(d^α/(Real.Gamma α*α))) := by
  intro Δ P Q
  let n := ⌊t/Δ⌋₊
  let N := fullPulseBirthCount T b ε
  let a (j : ℕ) := t-(j:ℝ)*Δ
  let R (j : ℕ) := pulseKernelResponse α ε d (a j)
  let B := (ε/d)*(d^α/(Real.Gamma α*α))
  have hΔ : 0 < Δ := div_pos hε hb
  have hD : b*Δ = ε := by dsimp [Δ]; field_simp
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hQ : 0 ≤ Q := mul_nonneg hb.le
    (intervalIntegral.integral_nonneg_of_forall ht.1 (hestonKernel_nonneg_explicit hα))
  have hn : (n:ℝ)*Δ ≤ t := (le_div_iff₀ hΔ).mp (Nat.floor_le (div_nonneg ht.1 hΔ.le))
  have ht' : t < ((n:ℝ)+1)*Δ := (div_lt_iff₀ hΔ).mp (Nat.lt_floor_add_one _)
  have hnN : n+1 ≤ N := Nat.succ_le_succ (Nat.floor_mono (div_le_div_of_nonneg_right ht.2 hΔ.le))
  have ha (j : ℕ) (hj : j ≤ n) : 0 ≤ a j := sub_nonneg.mpr
    ((mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hΔ.le : (j:ℝ)*Δ ≤ (n:ℝ)*Δ).trans hn)
  have hR₀ (j : ℕ) : 0 ≤ R j := pulseKernelResponse_nonneg hα hε.le hd _
  have hR₁ (j : ℕ) : R j ≤ B := pulseKernelResponse_le_bound hα hα' hε.le hd _
  have hDrop (j : ℕ) (hj : n+1 ≤ j) : R j = 0 := by
    apply pulseKernelResponse_zero_of_nonpos
    have hc : ((n:ℝ)+1) ≤ (j:ℝ) := by exact_mod_cast hj
    exact sub_nonpos.mpr (ht'.le.trans (mul_le_mul_of_nonneg_right hc hΔ.le))
  have hP : P = ∑ j ∈ Finset.range (n+1), R j := by
    change volterraConvolution (hestonKernel α) (explicitPulsedRate T b ε d) t = _
    rw [explicitPulsed_convolution_eq_sum hα hε hb]
    exact (Finset.sum_subset (Finset.range_mono hnN) fun j _ hj => hDrop j (by
      simpa only [Finset.mem_range, not_lt] using hj)).symm
  have ha0 : a 0 = t := by simp [a]
  cases hn' : n with
  | zero =>
    have htΔ : t ≤ 2*Δ := by rw [hn'] at ht'; norm_num at ht'; linarith
    have hLo : Q ≤ b*((2*Δ)^α/(Real.Gamma α*α)) := by
      unfold Q
      rw [hestonKernel_integral hα ht.1]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
        (Real.rpow_le_rpow ht.1 htΔ hα.le) (by positivity)) hb.le
    rw [hP, hn']
    simp only [zero_add, Finset.sum_range_one]
    exact ⟨(sub_nonpos.mpr hLo).trans (hR₀ 0), (hR₁ 0).trans (by linarith)⟩
  | succ m =>
    have ha₀ (j : ℕ) (hj : j ≤ m+1) : 0 ≤ a j := ha j (by omega)
    have hstep (j : ℕ) : a (j+1) = a j-Δ := by simp [a, Nat.cast_add]; ring
    have hstep2 (j : ℕ) : a (j+2) = a j-2*Δ := by simp [a, Nat.cast_add]; ring
    have hUpper (j : ℕ) (hj : j ∈ Finset.range m) :
        R j ≤ b*(∫ s in a (j+2)..a (j+1), hestonKernel α s) := by
      have hz := ha₀ (j+2) (by have hj' := Finset.mem_range.mp hj; omega)
      rw [hstep j, hstep2 j]
      exact pulseKernelResponse_le_next_cell hα hα' hb.le hε.le hd hdΔ hD (by rw [hstep2] at hz; linarith)
    have hLower (j : ℕ) (hj : j ∈ Finset.range m) :
        b*(∫ s in a (j+1)..a j, hestonKernel α s) ≤ R (j+1) := by
      have hz := ha₀ (j+2) (by have hj' := Finset.mem_range.mp hj; omega)
      have haDelta : Δ ≤ a (j+1) := by rw [hstep (j+1)] at hz; linarith
      have hEnd : a (j+1)+Δ = a j := by rw [hstep]; ring
      simpa only [hEnd] using pulseKernelResponse_ge_previous_cell (Δ := Δ) hα hα' hb.le hε.le hd hdΔ hD haDelta
    constructor
    · have h := Finset.sum_le_sum hLower
      rw [← Finset.mul_sum, sum_hestonKernel_adjacent_cells hα m (fun j hj => ha₀ j (by omega)), ha0] at h
      have hSplit := intervalIntegral.integral_add_adjacent_intervals
        (hestonKernel_intervalIntegrable_nonneg hα le_rfl (ha₀ m (by omega)))
        (hestonKernel_intervalIntegrable_nonneg hα (ha₀ m (by omega)) ht.1)
      have ht₂ : a m ≤ 2*Δ := by
        rw [hn', Nat.cast_succ] at ht'
        dsimp [a]
        nlinarith
      have hNear := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
        (Real.rpow_le_rpow (ha₀ m (by omega)) ht₂ hα.le) (by positivity : 0 ≤ Real.Gamma α*α)) hb.le
      rw [← hestonKernel_integral hα (ha₀ m (by omega))] at hNear
      rw [hP, hn', Finset.sum_range_succ, Finset.sum_range_succ']
      dsimp [Q]
      nlinarith only [h, hSplit, hNear, hR₀ 0, hR₀ (m+1), show
          b*((∫ s in (0:ℝ)..a m,hestonKernel α s)+(∫ s in a m..t,hestonKernel α s))=
          b*(∫ s in (0:ℝ)..a m,hestonKernel α s)+b*(∫ s in a m..t,hestonKernel α s) from mul_add _ _ _,
        congrArg (fun x => b*x) hSplit]
    · have h := Finset.sum_le_sum hUpper
      rw [← Finset.mul_sum] at h
      have hCells := sum_hestonKernel_adjacent_cells hα (age := fun j => a (j+1)) m
        (fun j hj => ha₀ _ (by omega))
      have hCells' : (∑ j ∈ Finset.range m, ∫ s in a (j+2)..a (j+1), hestonKernel α s) =
          ∫ s in a (m+1)..a 1, hestonKernel α s := by
        simpa only [Nat.reduceAdd, Nat.add_assoc] using hCells
      rw [hCells'] at h
      have ha₁ : a 1 ≤ t := sub_le_self _ (mul_nonneg (Nat.cast_nonneg 1) hΔ.le)
      have hOrd : a (m+1) ≤ a 1 := by
        dsimp [a]
        apply sub_le_sub_left
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show 1 ≤ m+1 by omega)) hΔ.le
      have hSum := h.trans (mul_le_mul_of_nonneg_left
        (hestonKernel_interval_le_origin hα (ha₀ _ le_rfl) hOrd ha₁) hb.le)
      rw [hP, hn', Finset.sum_range_succ, Finset.sum_range_succ]
      exact add_le_add (add_le_add hSum (hR₁ m)) (hR₁ (m+1)) |>.trans_eq (by rw [two_mul]; ring)

#print axioms RoughHeston.explicitPulsed_convolution_eq_sum
#print axioms RoughHeston.continuous_explicitPulsed_convolution
#print axioms RoughHeston.explicitPulsed_convolution_difference_bounds

end RoughHeston
