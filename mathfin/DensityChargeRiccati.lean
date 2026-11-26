import RiccatiContinuation
import FractionalConvolutionRegularity

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RoughHeston

theorem density_fractionalK_mass {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t) :
    (∫ s in Ioc (0 : ℝ) t, fractionalK α (t-s)) = t^α / Real.Gamma (α+1) := by
  rcases eq_or_lt_of_le ht with he | hp
  · subst t
    simp [Real.zero_rpow hα.ne']
  have h := fractionalK_convolution_add hα (show (0 : ℝ) < 1 from zero_lt_one) hp
  have he (s : ℝ) (hs : s ∈ Ioc 0 t) : fractionalK α (t-s) =
      fractionalK α (t-s) * fractionalK 1 s := by
    have hu : fractionalK 1 s = 1 := by simp [fractionalK, not_le.mpr hs.1, Real.Gamma_one]
    rw [hu, mul_one]
  rw [setIntegral_congr_fun measurableSet_Ioc he]
  change volterraConvolution (fractionalK α) (fractionalK 1) t = _
  rw [h, fractionalK, ite_eq_right (not_le.mpr hp), add_sub_cancel_right]

private theorem density_fractionalK_integrable {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t) :
    IntegrableOn (fun s => fractionalK α (t-s)) (Ioc 0 t) := by
  have h := ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr
    (fractionalK_integrableOn_Ioc hα t)).symm.comp_sub_left t
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp (by
    simpa only [sub_zero, sub_self] using h)

private theorem integrable_density_drift_from_bound {α t : ℝ} {g : ℝ → ℝ}
    (hα : 0 < α) (ht : 0 ≤ t) (hm : Measurable g) {B : ℝ}
    (hb : ∀ s ∈ Ioc 0 t, ‖g s‖ ≤ B) :
    IntegrableOn (fun s => fractionalK α (t-s)*g s) (Ioc 0 t) := by
  have hi := (density_fractionalK_integrable hα ht).norm.mul_const B
  have hgm : Measurable (fun s => fractionalK α (t-s)*g s) :=
    ((fractionalK_measurable α).comp (measurable_const.sub measurable_id)).mul hm
  refine hi.mono' hgm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hb s hs) (norm_nonneg _)

theorem density_conv_integrable {α T t : ℝ} {g : ℝ → ℝ}
    (hα : 0 < α) (ht : t ∈ Icc 0 T) (hg : Continuous g) :
    IntegrableOn (fun s => fractionalK α (t-s)*g s) (Ioc 0 t) := by
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image (K := Icc (0 : ℝ) T) hg.norm.continuousOn
  exact integrable_density_drift_from_bound hα ht.1 hg.measurable
    (fun s hs => hB ⟨s, ⟨hs.1.le, hs.2.trans ht.2⟩, rfl⟩)

/-- A constant density charge and a constant initial value give the
usual continuous Volterra Riccati equation, at least on a positive interval. -/
theorem exists_local_density_riccati {α l d b c H : ℝ}
    (hα : 0 < α) (hH : 0 < H) :
    ∃ T ∈ Ioc (0 : ℝ) H, ∃ w : ℝ → ℝ, Continuous w ∧ w 0 = l ∧
      ∀ t ∈ Icc 0 T, w t = l +
        volterraConvolution (fractionalK α) (fun s => d+b*w s+c*w s^2) t := by
  let A (t : ℝ) := l + d * (t^α / Real.Gamma (α+1))
  have hA : Continuous A := continuous_const.add
    (continuous_const.mul ((Real.continuous_rpow_const hα.le).div_const _))
  obtain ⟨T, hT, w, hw, hV⟩ :=
    exists_local_forced_riccati (b := b) (c := c) hα hH hA.continuousOn
  refine ⟨T, hT, w, hw, ?_, ?_⟩
  · simpa [A, volterraConvolution, Real.zero_rpow hα.ne'] using hV 0 ⟨le_rfl, hT.1.le⟩
  · intro t ht
    have hPoly : Continuous (fun s => b*w s+c*w s^2) :=
      (continuous_const.mul hw).add (continuous_const.mul (hw.pow 2))
    unfold volterraConvolution
    have hK := density_fractionalK_integrable hα ht.1
    have hp := density_conv_integrable hα ht hPoly
    have he (s : ℝ) : fractionalK α (t-s)*(d+b*w s+c*w s^2) =
        fractionalK α (t-s)*d + fractionalK α (t-s)*(b*w s+c*w s^2) := by ring
    simp_rw [he]
    rw [integral_add (hK.mul_const d) hp, integral_mul_const, density_fractionalK_mass hα ht.1]
    rw [hV t ht]
    dsimp [A, volterraConvolution]
    ring

private theorem density_polynomial_increment {d b c x y B : ℝ}
    (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B) :
    ‖(d+b*y+c*y^2)-(d+b*x+c*x^2)‖ ≤ (‖b‖+2*‖c‖*B)*‖y-x‖ := by
  rw [show (d+b*y+c*y^2)-(d+b*x+c*x^2) = b*(y-x) + c*((y+x)*(y-x)) by ring]
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul]
  have hb : ‖y+x‖ ≤ 2*B := (norm_add_le _ _).trans
    ((add_le_add hy hx).trans_eq (by ring))
  calc
    _ ≤ ‖b‖*‖y-x‖+‖c‖*((2*B)*‖y-x‖) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hb (norm_nonneg _)) (norm_nonneg _))
    _ = _ := by ring

/-- An actual continuous density-charge solution satisfies its Caputo equation
on the open positive-time interval. -/
theorem density_riccati_caputo_of_volterra
    {α d b c T t : ℝ} {w : ℝ → ℝ}
    (hα : 1/2 < α) (hα' : α < 1) (ht : t ∈ Ioo 0 T) (hw : Continuous w)
    (hV : ∀ s ∈ Icc 0 T, w s = w 0 +
      volterraConvolution (fractionalK α) (fun u => d+b*w u+c*w u^2) s) :
    ContDiffAt ℝ 1 w t ∧
    IntervalIntegrable (fun u => (α*u^(-α-1)/Real.Gamma (1-α)) *
      (w t-w (t-u))) volume 0 t ∧
    fractionalMemory α (w 0) w t = d+b*w t+c*w t^2 := by
  have hα₀ : 0 < α := by linarith
  let F (s : ℝ) := d+b*w s+c*w s^2
  have hF : Continuous F := (continuous_const.add (continuous_const.mul hw)).add
    (continuous_const.mul (hw.pow 2))
  obtain ⟨B₀, hB₀⟩ := isCompact_Icc.bddAbove_image (K := Icc (0 : ℝ) T) hF.norm.continuousOn
  let B := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  let Q := B * (2/(Real.Gamma α*α))
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hHold (x : ℝ) (hx : x ∈ Icc 0 T) (y : ℝ) (hy : y ∈ Icc 0 T) (hxy : x ≤ y) :
      ‖w y-w x‖ ≤ Q*(y-x)^α := by
    have hb (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) (x+(y-x))) : ‖F s‖ ≤ B :=
      (hB₀ ⟨s, ⟨hs.1.le, by linarith [hs.2, hy.2]⟩, rfl⟩).trans (le_max_left _ _)
    have h := fractional_volterra_bounded_input_increment hα₀ hα'.le hx.1
      (sub_nonneg.mpr hxy) hF.measurable hB hb
    rw [show x+(y-x)=y by ring] at h
    rw [hV y hy, hV x hx, add_sub_add_left_eq_sub]
    exact h.trans_eq (by dsimp [Q]; ring)
  obtain ⟨D₀, hD₀⟩ := isCompact_Icc.bddAbove_image (K := Icc (0 : ℝ) T) hw.norm.continuousOn
  let D := max D₀ 0
  have hD : 0 ≤ D := le_max_right _ _
  have hDw (x : ℝ) (hx : x ∈ Icc 0 T) : ‖w x‖ ≤ D :=
    (hD₀ ⟨x, hx, rfl⟩).trans (le_max_left _ _)
  let C := ‖b‖+2*‖c‖*D
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hFH (x : ℝ) (hx : x ∈ Icc 0 T) (y : ℝ) (hy : y ∈ Icc 0 T) (hxy : x ≤ y) :
      ‖F y-F x‖ ≤ (C*Q)*(y-x)^α := by
    exact (density_polynomial_increment (d := d) (b := b) (c := c) (hDw x hx) (hDw y hy)).trans
      ((mul_le_mul_of_nonneg_left (hHold x hx y hy hxy) hC).trans_eq (by ring))
  have hVcd := fractionalVolterra_contDiffOn_of_holder hα₀ hα' (by linarith : 1 < α+α)
    hα₀.le (mul_nonneg hC hQ) hF.measurable hF.continuousOn hFH
  have hwcd : ContDiffAt ℝ 1 w t := by
    refine (contDiffAt_const.add (hVcd.contDiffAt (Ioo_mem_nhds ht.1 ht.2))
      (f := fun _ : ℝ => w 0)).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact hV s (Ioo_subset_Icc_self hs)
  let g (s : ℝ) := w s-w 0
  have hgc : Continuous g := hw.sub continuous_const
  have hgprim (s : ℝ) (hs : s ∈ Ioc 0 T) :
      volterraConvolution (fractionalL α) g s = ∫ u in Ioc (0 : ℝ) s, F u := by
    have he := (fractional_rl_inverse_of_point_charge (q := 0) hα₀ hα' hs.1 hF.measurable
      (hF.intervalIntegrable 0 s).1 (w := g) (fun u hu => by
        dsimp [g]
        rw [hV u ⟨hu.1.le, hu.2.trans hs.2⟩]
        simp [F])).2
    simpa only [zero_add] using he
  obtain ⟨hgM, hgD⟩ := fractional_rl_hasDerivAt_memory hα₀ hα' ht.1 hgc.measurable
    (hgc.intervalIntegrable 0 t).1 (hwcd.sub contDiffAt_const)
  have hDeriv : HasDerivAt (volterraConvolution (fractionalL α) g) (F t) t := by
    refine (intervalIntegral.integral_hasDerivAt_right (hF.intervalIntegrable 0 t)
      hF.measurable.aestronglyMeasurable.stronglyMeasurableAtFilter hF.continuousAt).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    rw [intervalIntegral.integral_of_le hs.1.le]
    exact hgprim s ⟨hs.1, hs.2.le⟩
  have hΔ (u : ℝ) : g t-g (t-u) = w t-w (t-u) := by dsimp [g]; ring
  have hMem : fractionalMemory α 0 g t = fractionalMemory α (w 0) w t := by
    unfold fractionalMemory
    simp_rw [hΔ]
    simp [g]
  exact ⟨hwcd, by simpa only [hΔ] using hgM, by rw [← hMem, ← hgD.deriv, hDeriv.deriv]⟩

/-- An actual density-charge solution with a positive forcing at zero
stays strictly positive, and below any constant supersolution starting
strictly above its initial value. -/
theorem density_riccati_pos_lt_constant
    {α d b c T B : ℝ} {w : ℝ → ℝ}
    (hα : 1/2 < α) (hα' : α < 1) (hT : 0 < T) (hd : 0 < d) (hw : Continuous w)
    (hw₀ : 0 ≤ w 0) (hBW : w 0 < B) (hB : d+b*B+c*B^2 ≤ 0)
    (hV : ∀ s ∈ Icc 0 T, w s = w 0 +
      volterraConvolution (fractionalK α) (fun u => d+b*w u+c*w u^2) s) :
    ∀ t ∈ Ioo 0 T, 0 < w t ∧ w t < B := by
  have hα₀ : 0 < α := by linarith
  let F (s : ℝ) := d+b*w s+c*w s^2
  have hF : Continuous F := (continuous_const.add (continuous_const.mul hw)).add
    (continuous_const.mul (hw.pow 2))
  have hPosStart : ∀ᶠ s in 𝓝 (0 : ℝ), s ∈ Ioi 0 → 0 < w s := by
    rcases eq_or_lt_of_le hw₀ with hzero | hpos
    · have hz : w 0 = 0 := hzero.symm
      have hF₀ : d/2 < F 0 := by simp [F, hz]; linarith
      have hFnear : ∀ᶠ s in 𝓝 (0 : ℝ), d/2 < F s :=
        continuousAt_const.eventually_lt hF.continuousAt hF₀
      obtain ⟨r, hr, hrF⟩ := Metric.eventually_nhds_iff.mp hFnear
      filter_upwards [Iio_mem_nhds (lt_min hr hT : (0:ℝ) < min r T)] with t ht ht₀
      have htpos : 0 < t := ht₀
      have htr : t < r := (show t < min r T from ht).trans_le (min_le_left _ _)
      have htT : t < T := (show t < min r T from ht).trans_le (min_le_right _ _)
      have hb (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) t) : d/2 ≤ F s := by
        apply (hrF ?_).le
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1.le]
        exact hs.2.trans_lt htr
      have hK (s : ℝ) : 0 ≤ fractionalK α (t-s) := by
        by_cases h : t-s ≤ 0
        · simp [fractionalK, h]
        · rw [fractionalK, ite_eq_right h]
          exact div_nonneg (Real.rpow_nonneg (le_of_lt (lt_of_not_ge h)) _)
            (Real.Gamma_pos_of_pos hα₀).le
      have hK₁ := density_fractionalK_integrable hα₀ htpos.le
      have hconv := density_conv_integrable hα₀ (T := T) ⟨htpos.le, htT.le⟩ hF
      have hInt := setIntegral_mono_on (hK₁.mul_const (d/2)) hconv measurableSet_Ioc
        (fun s hs => mul_le_mul_of_nonneg_left (hb s hs) (hK s))
      rw [integral_mul_const, density_fractionalK_mass hα₀ htpos.le] at hInt
      have hMass : 0 < (t^α/Real.Gamma (α+1))*(d/2) := by positivity
      rw [hV t ⟨htpos.le, htT.le⟩, hz, zero_add]
      exact hMass.trans_le hInt
    · exact (continuousAt_const.eventually_lt hw.continuousAt hpos).mono fun _ h _ => h
  have hUpperStart : ∀ᶠ s in 𝓝 (0 : ℝ), w s < B :=
    hw.continuousAt.eventually_lt continuousAt_const hBW
  obtain ⟨r, hr, hstart⟩ := Metric.eventually_nhds_iff.mp (hPosStart.and hUpperStart)
  let s₀ := min (r/2) (T/2)
  have hs₀ : 0 < s₀ := lt_min (by positivity) (by positivity)
  have hs₀r : s₀ < r := (min_le_left _ _).trans_lt (by linarith)
  have hpast (s : ℝ) (hs : s ∈ Ioc 0 s₀) : 0 < w s ∧ w s < B := by
    have hdist : dist s (0 : ℝ) < r := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1.le]
      exact hs.2.trans_lt hs₀r
    exact ⟨(hstart hdist).1 hs.1, (hstart hdist).2⟩
  intro t ht
  by_cases ht₀ : t ≤ s₀
  · exact hpast t ⟨ht.1, ht₀⟩
  have htarget : t ∈ Icc s₀ t := ⟨le_of_not_ge ht₀, le_rfl⟩
  have hInside (s : ℝ) (hs : s ∈ Icc s₀ t) : s ∈ Ioo 0 T :=
    ⟨hs₀.trans_le hs.1, hs.2.trans_lt ht.2⟩
  constructor
  · refine fractional_first_contact_comparison hα₀ hα' hw₀ hs₀ hw.continuousOn
      (fun s hs => (hpast s hs).1) ?_ t htarget
    intro s hs hz
    obtain ⟨_, hm, he⟩ := density_riccati_caputo_of_volterra hα hα' (hInside s hs) hw hV
    exact ⟨hm, by rw [he]; simpa [hz] using hd.le⟩
  · let g (s : ℝ) := B-w s
    have hg : Continuous g := continuous_const.sub hw
    have hpos : 0 < g t := by
      refine fractional_first_contact_comparison hα₀ hα' (sub_nonneg.mpr hBW.le) hs₀
        hg.continuousOn (fun s hs => sub_pos.mpr (hpast s hs).2) ?_ t htarget
      intro s hs hz
      have hEq : w s = B := (sub_eq_zero.mp hz).symm
      obtain ⟨_, hm, he⟩ := density_riccati_caputo_of_volterra hα hα' (hInside s hs) hw hV
      have hΔ (u : ℝ) : (α*u^(-α-1)/Real.Gamma (1-α))*(g s-g (s-u)) =
          -((α*u^(-α-1)/Real.Gamma (1-α))*(w s-w (s-u))) := by dsimp [g]; ring
      have hMem : fractionalMemory α (B-w 0) g s = -fractionalMemory α (w 0) w s := by
        unfold fractionalMemory
        simp_rw [hΔ]
        rw [intervalIntegral.integral_neg]
        dsimp [g]
        ring
      refine ⟨?_, ?_⟩
      · have hfun : (fun u : ℝ => (α*u^(-α-1)/Real.Gamma (1-α))*(g s-g (s-u))) =
            -(fun u : ℝ => (α*u^(-α-1)/Real.Gamma (1-α))*(w s-w (s-u))) := funext hΔ
        rw [hfun]
        exact hm.neg
      · rw [hMem, he, hEq]
        exact neg_nonneg.mpr hB
    exact sub_pos.mp hpos

#print axioms exists_local_density_riccati
#print axioms density_riccati_caputo_of_volterra
#print axioms density_riccati_pos_lt_constant

end RoughHeston
