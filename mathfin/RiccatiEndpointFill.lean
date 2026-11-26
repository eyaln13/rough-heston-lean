import RiccatiEndpoint

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RoughHeston

private theorem continuousOn_fractionalVolterra_bounded_tail
    {α a d m B : ℝ} {f : ℝ → ℝ}
    (hα : 0 < α) (hα' : α ≤ 1) (hd : 0 ≤ d) (hdm : d < m) (hfm : Measurable f)
    (hi : IntegrableOn f (Ioc 0 d)) (hB : 0 ≤ B) (hbound : ∀ s ∈ Ioc d a, ‖f s‖ ≤ B) :
    ContinuousOn (volterraConvolution (fractionalK α) f) (Icc m a) := by
  let F := volterraConvolution (fractionalK α) f
  let C := (1-α)*(m-d)^(α-2)/Real.Gamma α * (∫ s in Ioc (0 : ℝ) d, ‖f s‖)
  let D := B * (2 / (Real.Gamma α * α))
  have hOrdered (x y : ℝ) (hx : x ∈ Icc m a) (hy : y ∈ Icc m a) (hxy : x ≤ y) :
      ‖F y - F x‖ ≤ C * (y-x) + D * (y-x)^α := by
    have h := fractional_volterra_local_input_increment hα hα' hd (sub_pos.mpr hdm)
      (show d + (m-d) ≤ x by linarith [hx.1]) (sub_nonneg.mpr hxy) hfm hi hB
      (show ∀ s ∈ Ioc d (x + (y-x)), ‖f s‖ ≤ B by
        rw [show x + (y-x) = y by ring]
        exact fun s hs => hbound s ⟨hs.1, hs.2.trans hy.2⟩)
    rw [show x + (y-x) = y by ring] at h
    convert h using 1
    dsimp [C, D, F]
    ring
  have hUnordered (x y : ℝ) (hx : x ∈ Icc m a) (hy : y ∈ Icc m a) :
      ‖F y - F x‖ ≤ C * ‖y-x‖ + D * ‖y-x‖^α := by
    rcases le_total x y with hxy | hyx
    · simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hxy)] using hOrdered x y hx hy hxy
    · have hnorm : ‖y-x‖ = x-y := by rw [norm_sub_rev, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hyx)]
      rw [hnorm, norm_sub_rev]
      exact hOrdered y x hy hx hyx
  intro x hx
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hCont : Continuous (fun y : ℝ => C*‖y-x‖+D*‖y-x‖^α) :=
    (continuous_const.mul (continuous_id.sub continuous_const).norm).add
      (continuous_const.mul ((Real.continuous_rpow_const hα.le).comp
        (continuous_id.sub continuous_const).norm))
  have hzero : Tendsto (fun y : ℝ => C*‖y-x‖+D*‖y-x‖^α) (𝓝[Icc m a] x) (𝓝 0) := by
    have hlim := hCont.continuousAt.continuousWithinAt (s := Icc m a) (x := x)
    rw [ContinuousWithinAt] at hlim
    simpa [Real.zero_rpow hα.ne'] using hlim
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hzero
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact hUnordered x y hx hy

/-- A continuous solution bounded near a finite right endpoint admits a
unique continuous value there, given by its Volterra formula. -/
theorem exists_point_charge_riccati_endpoint
    {α q b c a d B : ℝ} {w : ℝ → ℝ}
    (hα : 0 < α) (hα' : α < 1) (hd : 0 < d) (hda : d < a) (hm : Measurable w)
    (hc : ContinuousOn w (Ioo 0 a)) (hB : 0 ≤ B) (hbound : ∀ s ∈ Ioc d a, ‖w s‖ ≤ B)
    (hi : IntegrableOn (fun s => b*w s+c*w s^2) (Ioc 0 d))
    (hvol : ∀ s ∈ Ioo 0 a, w s = q*fractionalK α s +
      volterraConvolution (fractionalK α) (fun u => b*w u+c*w u^2) s) :
    ∃ W, Measurable W ∧ ContinuousOn W (Ioi 0) ∧ EqOn W w (Iio a) ∧
      ∀ s ∈ Ioc 0 a, W s = q*fractionalK α s +
        volterraConvolution (fractionalK α) (fun u => b*W u+c*W u^2) s := by
  let f (s : ℝ) := b*w s+c*w s^2
  let G (s : ℝ) := q*fractionalK α s + volterraConvolution (fractionalK α) f s
  let m := (a+d)/2
  let W (s : ℝ) := if s < a then w s else G a
  let mB := ‖b‖*B+‖c‖*B^2
  have hdm : d < m := by dsimp [m]; linarith
  have hma : m < a := by dsimp [m]; linarith
  have hm0 := hd.trans hdm
  have hfm : Measurable f := (hm.const_mul b).add ((hm.pow_const 2).const_mul c)
  have hiG : ContinuousOn G (Icc m a) := by
    have hK : ContinuousOn (fractionalK α) (Icc m a) := by
      have hp : ContinuousOn (fun s : ℝ => s^(α-1) / Real.Gamma α) (Icc m a) :=
        (continuousOn_id.rpow_const
          (fun (s : ℝ) (hs : s ∈ Icc m a) =>
            Or.inl (ne_of_gt (hm0.trans_le hs.1)))).div_const _
      refine hp.congr ?_
      intro s hs
      simp [fractionalK, not_le.mpr (hm0.trans_le hs.1)]
    refine (continuousOn_const.mul hK).add
      (continuousOn_fractionalVolterra_bounded_tail hα hα'.le hd.le hdm hfm hi
        (show 0 ≤ mB by dsimp [mB]; positivity) ?_)
    intro s hs
    calc
      ‖f s‖ ≤ ‖b‖*‖w s‖+‖c‖*‖w s‖^2 := by
        calc
          ‖f s‖ ≤ ‖b*w s‖ + ‖c*w s^2‖ := norm_add_le _ _
          _ = _ := by rw [norm_mul, norm_mul, norm_pow]
      _ ≤ mB := add_le_add (mul_le_mul_of_nonneg_left (hbound s hs) (norm_nonneg b))
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hbound s hs) 2) (norm_nonneg c))
  have hmatch : EqOn W w (Iio a) := fun s hs => ite_eq_left hs
  have hGa : EqOn W G (Icc m a) := by
    intro s hs
    rcases lt_or_eq_of_le hs.2 with hsa | hsa
    · rw [hmatch hsa]
      exact hvol s ⟨hm0.trans_le hs.1, hsa⟩
    · subst s
      exact ite_eq_right (lt_irrefl a)
  have hW : ContinuousOn W (Ioi 0) := by
    intro s hs
    apply ContinuousAt.continuousWithinAt
    rcases lt_trichotomy s a with hsa | hsa | has
    · refine (hc.continuousAt (Ioo_mem_nhds hs hsa)).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds hsa] with x hx
      exact hmatch hx
    · subst s
      have hnear : ∀ᶠ x in 𝓝 a, x ∈ Ioi m := Ioi_mem_nhds hma
      have hleft : ContinuousWithinAt W (Iic a) a := by
        have hmem : Icc m a ∈ 𝓝[Iic a] a := by
          filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hnear] with u hu hum
          exact ⟨hum.le, hu⟩
        have htendsto := (hiG a ⟨hma.le, le_rfl⟩).mono_of_mem_nhdsWithin hmem
        refine htendsto.congr_of_eventuallyEq ?_ (hGa ⟨hma.le, le_rfl⟩)
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hnear] with u hu hum
        exact hGa ⟨hum.le, hu⟩
      have hright : ContinuousWithinAt W (Ici a) a := by
        refine continuousWithinAt_const.congr (fun u hu => ite_eq_right (not_lt_of_ge hu))
          (ite_eq_right (lt_irrefl a))
      rw [← continuousWithinAt_univ, ← Iic_union_Ici]
      exact hleft.union hright
    · refine (continuousAt_const (y := G a)).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds has] with u hu
      exact ite_eq_right (not_lt_of_ge hu.le)
  refine ⟨W, hm.ite measurableSet_Iio measurable_const, hW, hmatch, ?_⟩
  intro s hs
  have hEq : volterraConvolution (fractionalK α) (fun u => b*W u+c*W u^2) s =
      volterraConvolution (fractionalK α) f s := by
    apply setIntegral_congr_ae measurableSet_Ioc
    filter_upwards [volume.ae_ne a] with u hua hu
    change fractionalK α (s-u)*(b*W u+c*W u^2) = fractionalK α (s-u)*(b*w u+c*w u^2)
    rw [hmatch (lt_of_le_of_ne (hu.2.trans hs.2) hua)]
  rw [hEq]
  rcases lt_or_eq_of_le hs.2 with hsa | hsa
  · rw [hmatch hsa]
    exact hvol s ⟨hs.1, hsa⟩
  · subst s
    exact ite_eq_right (lt_irrefl a)

#print axioms exists_point_charge_riccati_endpoint

end RoughHeston
