import FractionalConvolutionRegularity

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RoughHeston

private theorem le_max_time_mul_rpow {α h U : ℝ}
    (hα : 0 < α) (hα' : α ≤ 1) (hh : 0 ≤ h) (hhU : h ≤ U) :
    h ≤ max 1 U * h^α := by
  have hp : 0 ≤ h^α := Real.rpow_nonneg hh _
  by_cases h₁ : h ≤ 1
  · have hsmall : h ≤ h^α := by
      rcases eq_or_lt_of_le hh with hz | hpos
      · rw [← hz]
        exact Real.rpow_nonneg le_rfl _
      · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hpos h₁ hα'
    exact hsmall.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (le_max_left 1 U) hp)
  · have hlarge : 1 ≤ h^α := by
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow (zero_le_one : (0 : ℝ) ≤ 1) (le_of_not_ge h₁) hα.le
    calc
      _ ≤ U := hhU
      _ ≤ max 1 U := le_max_right _ _
      _ ≤ _ := le_mul_of_one_le_right (le_trans zero_le_one (le_max_left _ _)) hlarge

private theorem caputo_coefficient_holder_on_compact {α a U T : ℝ} {k : ℝ → ℝ}
    (hα : 0 < α) (hα' : α ≤ 1) (ha : 0 ≤ a)
    (hsub : Icc a U ⊆ Ioo 0 T) (hk : ∀ s ∈ Ioo 0 T, ContDiffAt ℝ 1 k s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc a U, ∀ y ∈ Icc a U, x ≤ y →
      ‖k y-k x‖ ≤ C*(y-x)^α := by
  have hkOn : ContDiffOn ℝ 1 k (Ioo 0 T) :=
    fun s hs => (hk s hs).contDiffWithinAt
  have hderiv := (hkOn.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono hsub
  obtain ⟨B₀, hB₀⟩ := isCompact_Icc.bddAbove_image hderiv.norm
  let B := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hbd (s : ℝ) (hs : s ∈ Icc a U) : ‖deriv k s‖ ≤ B :=
    (hB₀ ⟨s, hs, rfl⟩).trans (le_max_left _ _)
  refine ⟨B*max 1 U, mul_nonneg hB (zero_le_one.trans (le_max_left _ _)), ?_⟩
  intro x hx y hy hxy
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun s hs => (hk s (hsub hs)).differentiableAt one_ne_zero)
    hbd (convex_Icc a U) hx hy
  rw [Real.norm_of_nonneg (sub_nonneg.mpr hxy)] at h
  have hb : y-x ≤ U := (sub_le_self y (ha.trans hx.1)).trans hy.2
  calc
    _ ≤ B*(y-x) := h
    _ ≤ B*(max 1 U*(y-x)^α) :=
      mul_le_mul_of_nonneg_left (le_max_time_mul_rpow hα hα' (sub_nonneg.mpr hxy) hb) hB
    _ = _ := by ring

/-- A continuous mean satisfying the Volterra equation has a genuine
Caputo equation at each positive preterminal time. The coefficient can
be singular at the excluded terminal time. -/
theorem caputo_mean_equation_of_volterra
    {α b T t : ℝ} {f k : ℝ → ℝ}
    (hα : 1/2 < α) (hα' : α < 1) (ht : t ∈ Ioo 0 T)
    (hf : ContinuousOn f (Ico 0 T)) (hk : ContinuousOn k (Ico 0 T))
    (hk₁ : ∀ s ∈ Ioo 0 T, ContDiffAt ℝ 1 k s)
    (hvol : ∀ s ∈ Ioo 0 T, f s = f 0 +
      volterraConvolution (fractionalK α) (fun u => b - k u*f u) s) :
    ContDiffAt ℝ 1 f t ∧
    IntervalIntegrable (fun u => (α*u^(-α-1)/Real.Gamma (1-α)) *
      (f t - f (t-u))) volume 0 t ∧
    fractionalMemory α (f 0) f t = b-k t*f t := by
  have hα₀ : 0 < α := by linarith
  let U := (t+T)/2
  have hUt : t < U := by dsimp [U]; linarith [ht.2]
  have hUT : U < T := by dsimp [U]; linarith [ht.2]
  have hU : 0 < U := ht.1.trans hUt
  let m (s : ℝ) := max 0 (min U s)
  have hmap (s : ℝ) : m s ∈ Icc 0 U := ⟨le_max_left _ _, max_le hU.le (min_le_left _ _)⟩
  have hms (s : ℝ) (hs : s ∈ Icc 0 U) : m s = s := by
    simp [m, min_eq_right hs.2, max_eq_right hs.1]
  have hmc : Continuous m := continuous_const.max (continuous_const.min continuous_id)
  have hsub : Icc (0 : ℝ) U ⊆ Ico 0 T := fun _ hs => ⟨hs.1, hs.2.trans_lt hUT⟩
  let F (s : ℝ) := b-k (m s)*f (m s)
  have hF : Continuous F :=
    continuous_const.sub (((hk.mono hsub).comp_continuous hmc hmap).mul
      ((hf.mono hsub).comp_continuous hmc hmap))
  have hFeq (s : ℝ) (hs : s ∈ Icc 0 U) : F s = b-k s*f s := by
    simp only [F, hms s hs]
  have hV (s : ℝ) (hs : s ∈ Icc 0 U) :
      f s = f 0 + volterraConvolution (fractionalK α) F s := by
    rcases eq_or_lt_of_le hs.1 with hsz | hs₀
    · subst s
      simp [volterraConvolution]
    · calc
        f s = f 0 + volterraConvolution (fractionalK α) (fun u => b-k u*f u) s :=
          hvol s ⟨hs₀, hs.2.trans_lt hUT⟩
        _ = _ := by
          congr 1
          unfold volterraConvolution
          apply setIntegral_congr_fun measurableSet_Ioc
          intro u hu
          simp only [hFeq u ⟨hu.1.le, hu.2.trans hs.2⟩]
  obtain ⟨B₀, hB₀⟩ := isCompact_Icc.bddAbove_image hF.continuousOn.norm
    (K := Icc (0 : ℝ) U)
  let B := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  let Q := B * (2/(Real.Gamma α*α))
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hfH (x : ℝ) (hx : x ∈ Icc 0 U) (y : ℝ) (hy : y ∈ Icc 0 U) (hxy : x ≤ y) :
      ‖f y-f x‖ ≤ Q*(y-x)^α := by
    have hb (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) (x+(y-x))) : ‖F s‖ ≤ B :=
      (hB₀ ⟨s, ⟨hs.1.le, by linarith [hs.2, hy.2]⟩, rfl⟩).trans (le_max_left _ _)
    have h := fractional_volterra_bounded_input_increment hα₀ hα'.le hx.1
      (sub_nonneg.mpr hxy) hF.measurable hB hb
    rw [show x+(y-x)=y by ring] at h
    rw [hV y hy, hV x hx, add_sub_add_left_eq_sub]
    exact h.trans_eq (by dsimp [Q]; ring)
  let d := t/2
  have hd : 0 < d := div_pos ht.1 (by norm_num)
  have hdt : d < t := by dsimp [d]; linarith [ht.1]
  have hsubD : Icc d U ⊆ Ioo 0 T := fun _ hs => ⟨hd.trans_le hs.1, hs.2.trans_lt hUT⟩
  obtain ⟨Hk, hHk, hkH⟩ := caputo_coefficient_holder_on_compact hα₀ hα'.le hd.le hsubD hk₁
  obtain ⟨Ck₀, hCk₀⟩ := isCompact_Icc.bddAbove_image (hk.mono hsub).norm
  obtain ⟨Cf₀, hCf₀⟩ := isCompact_Icc.bddAbove_image (hf.mono hsub).norm
  let Ck := max Ck₀ 0
  let Cf := max Cf₀ 0
  have hCk : 0 ≤ Ck := le_max_right _ _
  have hCf : 0 ≤ Cf := le_max_right _ _
  have hkb (s : ℝ) (hs : s ∈ Icc 0 U) : ‖k s‖ ≤ Ck :=
    (hCk₀ ⟨s, hs, rfl⟩).trans (le_max_left _ _)
  have hfb (s : ℝ) (hs : s ∈ Icc 0 U) : ‖f s‖ ≤ Cf :=
    (hCf₀ ⟨s, hs, rfl⟩).trans (le_max_left _ _)
  let H := Ck*Q+Hk*Cf
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hFH (x : ℝ) (hx : x ∈ Icc d U) (y : ℝ) (hy : y ∈ Icc d U) (hxy : x ≤ y) :
      ‖F y-F x‖ ≤ H*(y-x)^α := by
    have hx' : x ∈ Icc 0 U := ⟨hd.le.trans hx.1, hx.2⟩
    have hy' : y ∈ Icc 0 U := ⟨hd.le.trans hy.1, hy.2⟩
    rw [hFeq y hy', hFeq x hx',
      show (b-k y*f y)-(b-k x*f x) = -(k y*(f y-f x)+(k y-k x)*f x) by ring, norm_neg]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    calc
      _ ≤ Ck*(Q*(y-x)^α) + (Hk*(y-x)^α)*Cf :=
        add_le_add (mul_le_mul (hkb y hy') (hfH x hx' y hy' hxy) (norm_nonneg _) hCk)
          (mul_le_mul (hkH x hx y hy hxy) (hfb x hx') (norm_nonneg _) (by positivity))
      _ = _ := by dsimp [H]; ring
  have hFi : IntegrableOn F (Ioc 0 d) := (hF.intervalIntegrable 0 d).1
  have hVcd := fractionalVolterra_contDiffOn_of_local_holder hα₀ hα' (by linarith : 1 < α+α)
    hα₀.le hH hd.le hF.measurable hFi hF.continuousOn hFH
  have hfcd : ContDiffAt ℝ 1 f t := by
    have h := contDiffAt_const.add (hVcd.contDiffAt (Ioo_mem_nhds hdt hUt))
      (f := fun _ : ℝ => f 0)
    apply h.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ht.1 hUt] with s hs
    exact hV s (Ioo_subset_Icc_self hs)
  let g (s : ℝ) := f (m s)-f 0
  have hgc : Continuous g := ((hf.mono hsub).comp_continuous hmc hmap).sub continuous_const
  have hge (s : ℝ) (hs : s ∈ Icc 0 U) : g s = f s-f 0 := by simp [g, hms s hs]
  have hgcd : ContDiffAt ℝ 1 g t := by
    apply (hfcd.sub contDiffAt_const).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ht.1 hUt] with s hs
    exact hge s (Ioo_subset_Icc_self hs)
  have hgprim (s : ℝ) (hs : s ∈ Ioc 0 U) :
      volterraConvolution (fractionalL α) g s = ∫ u in Ioc (0 : ℝ) s, F u := by
    have he := (fractional_rl_inverse_of_point_charge (q := 0) hα₀ hα' hs.1 hF.measurable
      (hF.intervalIntegrable 0 s).1 (w := g) (fun u hu => by
        have huU : u ∈ Icc 0 U := ⟨hu.1.le, hu.2.trans hs.2⟩
        rw [hge u huU, hV u huU]
        simp)).2
    simpa only [zero_add] using he
  obtain ⟨hgM, hgD⟩ := fractional_rl_hasDerivAt_memory hα₀ hα' ht.1 hgc.measurable
    (hgc.intervalIntegrable 0 t).1 hgcd
  have hD : HasDerivAt (volterraConvolution (fractionalL α) g) (F t) t := by
    refine (intervalIntegral.integral_hasDerivAt_right (hF.intervalIntegrable 0 t)
      hF.measurable.aestronglyMeasurable.stronglyMeasurableAtFilter hF.continuousAt).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds ht.1 hUt] with s hs
    rw [intervalIntegral.integral_of_le hs.1.le]
    exact hgprim s ⟨hs.1, hs.2.le⟩
  have hΔ (u : ℝ) (hu : u ∈ Icc 0 t) : g t-g (t-u) = f t-f (t-u) := by
    rw [hge t ⟨ht.1.le, hUt.le⟩, hge (t-u) ⟨sub_nonneg.mpr hu.2,
      (sub_le_self t hu.1).trans hUt.le⟩]
    ring
  have hintegral : (∫ u in (0 : ℝ)..t, (α*u^(-α-1)/Real.Gamma (1-α)) * (g t-g (t-u))) =
      ∫ u in (0 : ℝ)..t, (α*u^(-α-1)/Real.Gamma (1-α)) * (f t-f (t-u)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht.1.le] at hu
    exact congrArg (fun z => (α*u^(-α-1)/Real.Gamma (1-α))*z) (hΔ u hu)
  have hMem : fractionalMemory α 0 g t = fractionalMemory α (f 0) f t := by
    unfold fractionalMemory
    rw [hintegral, sub_zero, hge t ⟨ht.1.le, hUt.le⟩]
  refine ⟨hfcd, ?_, ?_⟩
  · apply (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1.le).mpr
    apply hgM.1.congr_fun _ measurableSet_Ioc
    intro u hu
    exact congrArg (fun z => (α*u^(-α-1)/Real.Gamma (1-α))*z)
      (hΔ u (Ioc_subset_Icc_self hu))
  · rw [← hMem, ← hgD.deriv, hD.deriv, hFeq t ⟨ht.1.le, hUt.le⟩]

#print axioms caputo_mean_equation_of_volterra

end RoughHeston
