import ExplicitPulsedInputClock
import PulsedImmigrationBounds
import ClusterPulseInverse

/-! A rectangular pulse has a continuous shifted kernel response. Old
pulses are bracketed by constant-rate responses from adjacent full cells. -/

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

set_option maxHeartbeats 1300000

theorem hestonKernel_eq_fractionalK_explicit (α : ℝ) : hestonKernel α = fractionalK α := by
  funext s
  by_cases hs : 0 < s <;> simp [hestonKernel, fractionalK, hs, le_of_not_gt]

theorem hestonKernel_intervalIntegrable_nonneg {α a b : ℝ} (hα : 0 < α)
    (ha : 0 ≤ a) (hb : 0 ≤ b) : IntervalIntegrable (hestonKernel α) volume a b := by
  have h (u : ℝ) (hu : 0 ≤ u) : IntervalIntegrable (hestonKernel α) volume 0 u := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hu,hestonKernel_eq_fractionalK_explicit]
    exact fractionalK_integrableOn_Ioc hα u
  exact (h a ha).symm.trans (h b hb)

theorem hestonKernel_nonneg_explicit {α : ℝ} (hα : 0 < α) (s : ℝ) : 0 ≤ hestonKernel α s := by
  unfold hestonKernel
  split_ifs <;> positivity

theorem hestonKernel_antitoneOn_explicit {α : ℝ} (hα : 0 < α) (hα' : α ≤ 1) :
    AntitoneOn (hestonKernel α) (Ioi (0:ℝ)) := by
  intro a ha b hb hab
  change 0 < a at ha
  change 0 < b at hb
  rw [hestonKernel, hestonKernel, if_pos ha, if_pos hb]
  exact div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_nonpos ha hab (sub_nonpos.mpr hα'))
    (Real.Gamma_pos_of_pos hα).le

noncomputable def pulseKernelResponse (α ε d : ℝ) : ℝ → ℝ :=
  volterraConvolution (hestonKernel α) (rectangularPulseRate ε d)

theorem continuous_pulseKernelResponse {α ε d : ℝ} (hα : 0 < α) (hε : 0 ≤ ε) (hd : 0 < d) :
    Continuous (pulseKernelResponse α ε d) := by
  unfold pulseKernelResponse
  rw [hestonKernel_eq_fractionalK_explicit]
  exact GirsanovPort.pulse_fractional_convolution_continuous hα hε hd

theorem pulseKernelResponse_eq_interval {α ε d a : ℝ} (hε : 0 ≤ ε) (hd : 0 < d) (ha : 0 ≤ a) :
    pulseKernelResponse α ε d a = (ε/d)*(∫ x in (a-min d a)..a, hestonKernel α x) := by
  rw [pulseKernelResponse, ← rectangularPulseMeasure_integral_eq_convolution hε hd,
    rectangularPulseMeasure, integral_smul_measure, ENNReal.toReal_ofReal (div_nonneg hε hd.le), smul_eq_mul,
    ← intervalIntegral.integral_of_le (le_min hd.le ha), intervalIntegral.integral_comp_sub_left, sub_zero]

theorem pulseKernelResponse_nonneg {α ε d : ℝ} (hα : 0 < α) (hε : 0 ≤ ε) (hd : 0 < d) (a : ℝ) :
    0 ≤ pulseKernelResponse α ε d a := by
  by_cases ha : 0 ≤ a
  · rw [pulseKernelResponse_eq_interval hε hd ha]
    exact mul_nonneg (div_nonneg hε hd.le) (intervalIntegral.integral_nonneg_of_forall
      (sub_le_self _ (le_min hd.le ha)) (hestonKernel_nonneg_explicit hα))
  · rw [pulseKernelResponse, volterraConvolution, Ioc_eq_empty_of_le (le_of_not_ge ha), setIntegral_empty]

theorem pulseKernelResponse_le_bound {α ε d : ℝ}
    (hα : 0 < α) (hα' : α ≤ 1) (hε : 0 ≤ ε) (hd : 0 < d) (a : ℝ) :
    pulseKernelResponse α ε d a ≤ (ε/d)*(d^α/(Real.Gamma α*α)) := by
  by_cases ha : 0 ≤ a
  · rw [pulseKernelResponse_eq_interval hε hd ha]
    let u := min d a
    have hu : 0 ≤ u := le_min hd.le ha
    have h := heston_pulse_convolution_le (k := hestonKernel α) (a := 0) (b := u) (t := a)
      hα hα' hε hd hu (min_le_right _ _) (by simpa only [sub_zero] using min_le_left d a)
      (hestonKernel_measurable α) (fun s _ => hestonKernel_nonneg_explicit hα s) (fun s _ => le_rfl)
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left, sub_zero] at h
    exact h
  · rw [pulseKernelResponse, volterraConvolution, Ioc_eq_empty_of_le (le_of_not_ge ha), setIntegral_empty]
    positivity

private theorem integral_hestonKernel_ge_endpoint {α a b : ℝ}
    (hα : 0 < α) (hα' : α ≤ 1) (ha : 0 ≤ a) (hab : a ≤ b) :
    (b-a)*hestonKernel α b ≤ ∫ r in a..b, hestonKernel α r := by
  have hb := ha.trans hab
  rw [← smul_eq_mul, ← intervalIntegral.integral_const (a := a) (b := b)]
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  apply setIntegral_mono_on (integrable_const _)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 (hestonKernel_intervalIntegrable_nonneg hα ha hb))
    measurableSet_Ioc
  exact fun r hr => hestonKernel_antitoneOn_explicit hα hα' (ha.trans_lt hr.1)
    ((ha.trans_lt hr.1).trans_le hr.2) hr.2

private theorem integral_hestonKernel_le_endpoint {α a b : ℝ}
    (hα : 0 < α) (hα' : α ≤ 1) (ha : 0 < a) (hab : a ≤ b) :
    (∫ r in a..b, hestonKernel α r) ≤ (b-a)*hestonKernel α a := by
  have hb := ha.le.trans hab
  rw [← smul_eq_mul, ← intervalIntegral.integral_const (a := a) (b := b)]
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  apply setIntegral_mono_on
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 (hestonKernel_intervalIntegrable_nonneg hα ha.le hb))
    (integrable_const _) measurableSet_Ioc
  exact fun r hr => hestonKernel_antitoneOn_explicit hα hα' ha (ha.trans hr.1) hr.1.le

/-- A full old pulse dominates the previous longer cell's contribution. -/
theorem pulseKernelResponse_ge_previous_cell {α ε d Δ b a : ℝ}
    (hα : 0 < α) (hα' : α ≤ 1) (hb : 0 ≤ b) (hε : 0 ≤ ε) (hd : 0 < d) (hdΔ : d ≤ Δ)
    (hmass : b*Δ = ε) (ha : Δ ≤ a) :
    b*(∫ r in a..(a+Δ), hestonKernel α r) ≤ pulseKernelResponse α ε d a := by
  have hΔ : 0 < Δ := hd.trans_le hdΔ
  have ha₀ := hΔ.trans_le ha
  have hpx := mul_le_mul_of_nonneg_left (integral_hestonKernel_ge_endpoint hα hα'
    (sub_nonneg.mpr (hdΔ.trans ha)) (sub_le_self a hd.le)) (div_nonneg hε hd.le)
  have hcx := mul_le_mul_of_nonneg_left (integral_hestonKernel_le_endpoint hα hα' ha₀
    (le_add_of_nonneg_right hΔ.le)) hb
  rw [pulseKernelResponse_eq_interval hε hd ha₀.le, min_eq_left (hdΔ.trans ha)]
  rw [show a-(a-d)=d by ring, ← mul_assoc, div_mul_cancel₀ _ hd.ne'] at hpx
  rw [show a+Δ-a=Δ by ring, ← mul_assoc, hmass] at hcx
  exact hcx.trans hpx

/-- An old pulse is bounded by the next full constant-rate cell. -/
theorem pulseKernelResponse_le_next_cell {α ε d Δ b a : ℝ}
    (hα : 0 < α) (hα' : α ≤ 1) (hb : 0 ≤ b) (hε : 0 ≤ ε) (hd : 0 < d) (hdΔ : d ≤ Δ)
    (hmass : b*Δ = ε) (ha : 2*Δ ≤ a) :
    pulseKernelResponse α ε d a ≤ b*(∫ r in (a-2*Δ)..(a-Δ), hestonKernel α r) := by
  have hΔ : 0 < Δ := hd.trans_le hdΔ
  have haΔ : 0 < a-Δ := by linarith
  have had : 0 < a-d := by linarith
  have had' : d ≤ a := by linarith
  have hpx := mul_le_mul_of_nonneg_left (integral_hestonKernel_le_endpoint hα hα' had
    (sub_le_self a hd.le)) (div_nonneg hε hd.le)
  have hcx := mul_le_mul_of_nonneg_left (integral_hestonKernel_ge_endpoint hα hα'
    (sub_nonneg.mpr ha) (show a-2*Δ ≤ a-Δ by linarith)) hb
  rw [pulseKernelResponse_eq_interval hε hd (by linarith), min_eq_left had']
  rw [show a-(a-d)=d by ring, ← mul_assoc, div_mul_cancel₀ _ hd.ne'] at hpx
  rw [show (a-Δ)-(a-2*Δ)=Δ by ring, ← mul_assoc, hmass] at hcx
  exact hpx.trans ((mul_le_mul_of_nonneg_left
    (hestonKernel_antitoneOn_explicit hα hα' haΔ had (by linarith)) hε).trans hcx)

#print axioms RoughHeston.pulseKernelResponse_le_bound
#print axioms RoughHeston.pulseKernelResponse_ge_previous_cell
#print axioms RoughHeston.pulseKernelResponse_le_next_cell

end RoughHeston
