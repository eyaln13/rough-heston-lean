import Verification
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RoughHeston

private theorem integrableOn_fractional_inverse_charge {α t : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1) (ht : 0 < t) :
    IntegrableOn (fun s => fractionalL α (t - s) * fractionalK α s) (Ioc 0 t) := by
  by_contra h
  have he := fractional_causal_kernel_inverse hα₀ hα₁ ht
  unfold volterraConvolution at he
  rw [integral_undef h] at he
  exact zero_ne_one he

private theorem integrableOn_fractional_inverse_drift {α t : ℝ} {f : ℝ → ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1) (hf : Measurable f)
    (hfi : IntegrableOn f (Ioc 0 t)) :
    IntegrableOn (fun s => fractionalL α (t - s) * volterraConvolution (fractionalK α) f s)
      (Ioc 0 t) := by
  have htri : IntegrableOn (fun s => ∫ u in Ioc (0 : ℝ) t,
      fractionalL α (t - s) * fractionalK α (s - u) * f u) (Ioc 0 t) :=
    (fractional_volterra_triangle_integrable hα₀ hα₁ hf hfi).integral_prod_left
  refine htri.congr_fun ?_ measurableSet_Ioc
  intro s hs
  change (∫ u in Ioc (0 : ℝ) t, fractionalL α (t - s) * fractionalK α (s - u) * f u) =
    fractionalL α (t - s) * volterraConvolution (fractionalK α) f s
  unfold volterraConvolution
  rw [← integral_const_mul]
  have hsub : Ioc (0 : ℝ) s ⊆ Ioc 0 t := Ioc_subset_Ioc_right hs.2
  have he := setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (μ := volume)
    (f := fun u => fractionalL α (t - s) * (fractionalK α (s - u) * f u))
    measurableSet_Ioc hsub (by
      intro u hu
      have hsu : s ≤ u := by
        by_contra! h
        exact hu.2 ⟨hu.1.1, h.le⟩
      simp [fractionalK, sub_nonpos.mpr hsu])
  simpa only [mul_assoc] using he

/-- Apply the inverse fractional kernel to a point charge and a Volterra
drift. The resulting primitive has an actual integrable defining kernel. -/
theorem fractional_rl_inverse_of_point_charge {α q t : ℝ} {w f : ℝ → ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1) (ht : 0 < t) (hf : Measurable f)
    (hfi : IntegrableOn f (Ioc 0 t))
    (hvol : ∀ s ∈ Ioc 0 t, w s = q * fractionalK α s +
      volterraConvolution (fractionalK α) f s) :
    IntegrableOn (fun s => fractionalL α (t - s) * w s) (Ioc 0 t) ∧
      volterraConvolution (fractionalL α) w t = q + ∫ s in Ioc (0 : ℝ) t, f s := by
  let F (s : ℝ) := fractionalL α (t - s) * fractionalK α s
  let G (s : ℝ) := fractionalL α (t - s) * volterraConvolution (fractionalK α) f s
  have hF : IntegrableOn F (Ioc 0 t) := integrableOn_fractional_inverse_charge hα₀ hα₁ ht
  have hG : IntegrableOn G (Ioc 0 t) := integrableOn_fractional_inverse_drift hα₀ hα₁ hf hfi
  have hab (s : ℝ) (hs : s ∈ Ioc 0 t) :
      q * F s + G s = fractionalL α (t - s) * w s := by
    dsimp only [F, G]
    rw [hvol s hs]
    ring
  have hh : IntegrableOn (fun s => q * F s + G s) (Ioc 0 t) := (hF.const_mul q).add hG
  refine ⟨hh.congr_fun hab measurableSet_Ioc, ?_⟩
  calc
    _ = ∫ s in Ioc (0 : ℝ) t, q * F s + G s :=
      (setIntegral_congr_fun measurableSet_Ioc hab).symm
    _ = q * (∫ s in Ioc (0 : ℝ) t, F s) + ∫ s in Ioc (0 : ℝ) t, G s := by
      rw [integral_add (hF.const_mul q) hG, integral_const_mul q F]
    _ = _ := by
      change q * volterraConvolution (fractionalL α) (fractionalK α) t +
        volterraConvolution (fractionalL α) (volterraConvolution (fractionalK α) f) t = _
      rw [fractional_causal_kernel_inverse hα₀ hα₁ ht, mul_one,
        fractional_volterra_inverts_drift hα₀ hα₁ hf hfi]

/-- The Riemann–Liouville primitive of a point-charge Riccati solution. -/
theorem fractional_riccati_rl_primitive {α q b c T t : ℝ} {w : ℝ → ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1) (ht : t ∈ Ioc 0 T)
    (hw : Measurable w) (hfi : IntegrableOn (fun s => b * w s + c * w s ^ 2) (Ioc 0 T))
    (hvol : ∀ s ∈ Ioc 0 T, w s = q * fractionalK α s +
      volterraConvolution (fractionalK α) (fun u => b * w u + c * w u ^ 2) s) :
    IntegrableOn (fun s => fractionalL α (t - s) * w s) (Ioc 0 t) ∧
    volterraConvolution (fractionalL α) w t = q + ∫ s in Ioc (0 : ℝ) t, b * w s + c * w s ^ 2 := by
  exact fractional_rl_inverse_of_point_charge hα₀ hα₁ ht.1
    ((hw.const_mul b).add ((hw.pow_const 2).const_mul c))
    (hfi.mono_set (Ioc_subset_Ioc_right ht.2))
    (fun s hs => hvol s (Ioc_subset_Ioc_right ht.2 hs))

/-- The Riemann–Liouville equation holds also as a derivative within the
positive solution interval at its right endpoint. -/
theorem fractional_riccati_rl_hasDerivWithinAt {α q b c T t : ℝ} {w : ℝ → ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1) (ht : t ∈ Ioc 0 T)
    (hw : Measurable w) (hcw : ContinuousOn w (Ioi 0))
    (hfi : IntegrableOn (fun s => b * w s + c * w s ^ 2) (Ioc 0 T))
    (hvol : ∀ s ∈ Ioc 0 T, w s = q * fractionalK α s +
      volterraConvolution (fractionalK α) (fun u => b * w u + c * w u ^ 2) s) :
    HasDerivWithinAt (volterraConvolution (fractionalL α) w) (b * w t + c * w t ^ 2) (Ioc 0 T) t := by
  let f (s : ℝ) := b * w s + c * w s ^ 2
  have hf : Measurable f := (hw.const_mul b).add ((hw.pow_const 2).const_mul c)
  have hfit : IntervalIntegrable f volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1.le).mpr
      (hfi.mono_set (Ioc_subset_Ioc_right ht.2))
  have hwct : ContinuousAt w t := hcw.continuousAt (Ioi_mem_nhds ht.1)
  have hfct : ContinuousAt f t :=
    (continuousAt_const.mul hwct).add (continuousAt_const.mul (hwct.pow 2))
  have hft := intervalIntegral.integral_hasDerivAt_right hfit
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hfct
  have h := (hft.const_add q).hasDerivWithinAt (s := Ioc (0 : ℝ) T)
  have he (s : ℝ) (hs : s ∈ Ioc 0 T) :
      volterraConvolution (fractionalL α) w s = q + ∫ u in (0 : ℝ)..s, f u := by
    rw [intervalIntegral.integral_of_le hs.1.le]
    exact (fractional_riccati_rl_primitive hα₀ hα₁ hs hw hfi hvol).2
  exact h.congr (fun s hs => he s hs) (he t ht)

/-- The Riemann–Liouville derivative on the interior of the solution horizon. -/
theorem fractional_riccati_rl_hasDerivAt {α q b c T t : ℝ} {w : ℝ → ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1) (ht : t ∈ Ioo 0 T)
    (hw : Measurable w) (hcw : ContinuousOn w (Ioi 0))
    (hfi : IntegrableOn (fun s => b * w s + c * w s ^ 2) (Ioc 0 T))
    (hvol : ∀ s ∈ Ioc 0 T, w s = q * fractionalK α s +
      volterraConvolution (fractionalK α) (fun u => b * w u + c * w u ^ 2) s) :
    HasDerivAt (volterraConvolution (fractionalL α) w) (b * w t + c * w t ^ 2) t :=
  HasDerivWithinAt.hasDerivAt
    (fractional_riccati_rl_hasDerivWithinAt hα₀ hα₁ ⟨ht.1, ht.2.le⟩ hw hcw hfi hvol)
    (mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Ioo_subset_Ioc_self)

/-- At a contact between the pure quadratic profile and the damped
Riccati solution, the quadratic contributions cancel exactly. -/
theorem fractional_riccati_rl_derivative_difference_at_contact {α κ a t : ℝ} {v w : ℝ → ℝ}
    (hv : HasDerivAt (volterraConvolution (fractionalL α) v) (-a * v t ^ 2) t)
    (hw : HasDerivAt (volterraConvolution (fractionalL α) w) (-κ * w t + -a * w t ^ 2) t)
    (heq : v t = w t) :
    HasDerivAt (fun s => volterraConvolution (fractionalL α) v s -
      volterraConvolution (fractionalL α) w s) (κ * w t) t := by
  convert hv.sub hw using 1
  rw [heq]
  ring

/-- The same cancellation for the derivative of the primitive of the gap. -/
theorem fractional_riccati_rl_gap_derivative_at_contact {α κ a t : ℝ} {v w : ℝ → ℝ}
    (hv : HasDerivAt (volterraConvolution (fractionalL α) v) (-a * v t ^ 2) t)
    (hw : HasDerivAt (volterraConvolution (fractionalL α) w) (-κ * w t + -a * w t ^ 2) t)
    (heq : v t = w t)
    (hL : ∀ᶠ s in 𝓝 t,
      IntegrableOn (fun u => fractionalL α (s - u) * v u) (Ioc 0 s) ∧
      IntegrableOn (fun u => fractionalL α (s - u) * w u) (Ioc 0 s)) :
    HasDerivAt (volterraConvolution (fractionalL α) (fun u => v u - w u)) (κ * w t) t := by
  apply (fractional_riccati_rl_derivative_difference_at_contact hv hw heq).congr_of_eventuallyEq
  filter_upwards [hL] with s hs
  unfold volterraConvolution
  simp_rw [mul_sub]
  exact integral_sub hs.1 hs.2

/-- Once the Riemann–Liouville memory formula is identified, a strictly
positive past is incompatible with a contact with the pure quadratic profile. -/
theorem fractional_riccati_no_contact_of_memory_identity {α κ a t : ℝ} {v w : ℝ → ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1) (ht : 0 < t) (hκ : 0 ≤ κ) (hwt : 0 ≤ w t)
    (hv : HasDerivAt (volterraConvolution (fractionalL α) v) (-a * v t ^ 2) t)
    (hw : HasDerivAt (volterraConvolution (fractionalL α) w) (-κ * w t + -a * w t ^ 2) t)
    (hL : ∀ᶠ s in 𝓝 t,
      IntegrableOn (fun u => fractionalL α (s - u) * v u) (Ioc 0 s) ∧
      IntegrableOn (fun u => fractionalL α (s - u) * w u) (Ioc 0 s))
    (hpast : ∀ s ∈ Ioo 0 t, 0 < v s - w s)
    (hint : IntervalIntegrable
      (fun u => (α * u ^ (-α - 1) / Real.Gamma (1 - α)) *
        ((v t - w t) - (v (t - u) - w (t - u)))) volume 0 t)
    (hidentity :
      deriv (volterraConvolution (fractionalL α) (fun u => v u - w u)) t =
        fractionalMemory α 0 (fun u => v u - w u) t) :
    v t ≠ w t := by
  intro heq
  have hneg := fractional_memory_negative_at_contact hα₀ hα₁
    (show (0 : ℝ) ≤ 0 from le_rfl) ht (g := fun u => v u - w u) (sub_eq_zero.mpr heq) hpast hint
  have hd := (fractional_riccati_rl_gap_derivative_at_contact hv hw heq hL).deriv
  rw [← hidentity, hd] at hneg
  exact (not_lt_of_ge (mul_nonneg hκ hwt)) hneg

/-- The causal fractional kernel is homogeneous under positive time dilation. -/
theorem fractionalK_time_scale (α : ℝ) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    fractionalK α (r * t) = r ^ (α - 1) * fractionalK α t := by
  unfold fractionalK
  by_cases ht : t ≤ 0
  · simp [ht, mul_nonpos_of_nonneg_of_nonpos hr.le ht]
  · rw [ite_eq_right ht, ite_eq_right (not_le.mpr (mul_pos hr (lt_of_not_ge ht))),
      Real.mul_rpow hr.le (lt_of_not_ge ht).le]
    ring

/-- Positive dilation scales the convolution by `r^α` after rescaling
its input. The identity is valid for the set-integral conventions. -/
theorem fractional_volterra_time_scale (α : ℝ) {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (f : ℝ → ℝ) :
    volterraConvolution (fractionalK α) f (r * t) =
      r ^ α * volterraConvolution (fractionalK α) (fun s => f (r * s)) t := by
  unfold volterraConvolution
  rw [← intervalIntegral.integral_of_le (mul_nonneg hr.le ht.le)]
  have he := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := t)
    (fun s => fractionalK α (r * t - s) * f s) r
  rw [smul_eq_mul, mul_zero, intervalIntegral.integral_of_le ht.le] at he
  rw [← he]
  have hEq : (∫ s in Ioc (0 : ℝ) t, fractionalK α (r * t - r * s) * f (r * s)) =
      ∫ s in Ioc (0 : ℝ) t, r ^ (α - 1) * (fractionalK α (t - s) * f (r * s)) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s _
    dsimp only
    rw [← mul_sub, fractionalK_time_scale α hr, mul_assoc]
  rw [hEq, integral_const_mul, ← mul_assoc]
  have hpow : r * r ^ (α - 1) = r ^ α := by
    calc
      _ = r ^ (1 : ℝ) * r ^ (α - 1) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hr, show 1 + (α - 1) = α by ring]
  rw [hpow]

/-- Rescaling a horizon by `r` multiplies the point charge by
`r^(2α−1)` and the linear coefficient by `r^α`. The quadratic coefficient
is invariant. -/
theorem fractional_riccati_rescale {α r q b c T : ℝ} {w : ℝ → ℝ}
    (hr : 0 < r)
    (hw : ∀ t ∈ Ioc 0 (r * T), w t = q * fractionalK α t +
      volterraConvolution (fractionalK α) (fun s => b * w s + c * w s ^ 2) t) :
    let W (t : ℝ) := r ^ α * w (r * t)
    ∀ t ∈ Ioc 0 T, W t = (q * r ^ (2 * α - 1)) * fractionalK α t +
      volterraConvolution (fractionalK α) (fun s => (r ^ α * b) * W s + c * W s ^ 2) t := by
  dsimp
  intro t ht
  rw [hw _ ⟨mul_pos hr ht.1, mul_le_mul_of_nonneg_left ht.2 hr.le⟩,
    fractionalK_time_scale α hr t, fractional_volterra_time_scale α hr ht.1, mul_add]
  have hpow : r ^ α * r ^ (α - 1) = r ^ (2 * α - 1) := by
    rw [← Real.rpow_add hr, show α + (α - 1) = 2 * α - 1 by ring]
  congr 1
  · rw [← hpow]
    ring
  · unfold volterraConvolution
    rw [← mul_assoc, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s _
    ring

/-- A positive time scale can make the rescaled damping arbitrarily small
while keeping the horizon within any prescribed positive bound. -/
theorem exists_small_fractional_riccati_scale {α κ T ε : ℝ}
    (hα : 0 < α) (hT : 0 < T) (hε : 0 < ε) :
    ∃ r ∈ Ioc 0 T, ‖κ‖ * r ^ α < ε := by
  have hcont : ContinuousAt (fun r : ℝ => ‖κ‖ * r ^ α) (0 : ℝ) :=
    (continuous_const.mul (Real.continuous_rpow_const hα.le)).continuousAt
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hcont ε hε
  let r := min T (δ / 2)
  have hr : 0 < r := lt_min hT (by positivity)
  have hrδ : r < δ := (min_le_right T (δ / 2)).trans_lt (by linarith)
  have hnear : dist r (0 : ℝ) < δ := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hr] using hrδ
  have hdist := hd hnear
  simp only [Real.dist_eq, Real.zero_rpow hα.ne', mul_zero, sub_zero] at hdist
  exact ⟨r, ⟨hr, min_le_left _ _⟩, (le_abs_self _).trans_lt hdist⟩

#print axioms fractional_rl_inverse_of_point_charge
#print axioms fractional_riccati_rl_primitive
#print axioms fractional_riccati_rl_hasDerivWithinAt
#print axioms fractional_riccati_rl_hasDerivAt
#print axioms fractional_riccati_rl_gap_derivative_at_contact
#print axioms fractional_riccati_no_contact_of_memory_identity
#print axioms fractional_riccati_rescale
#print axioms exists_small_fractional_riccati_scale

end RoughHeston
