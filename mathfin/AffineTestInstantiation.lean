import AffinePathwiseTransform
import RiccatiGlobal
import RectangularPulseLowerTail
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace RoughHeston

/-- Positive point tests use the global point-charge Riccati solution. -/
theorem PointChargeRiccatiOn.affine_test
    {α q κ a T : ℝ} {w : ℝ → ℝ}
    (hα : 1/2 < α) (hT : 0 < T)
    (hw : PointChargeRiccatiOn α q (-κ) (-a) T w)
    (hn : ∀ t ∈ Ioo 0 T, 0 ≤ w t) :
    AffineRiccatiTestOn α κ a q T w (fun _ => 0) := by
  obtain ⟨h1,h2⟩ := integrableOn_riccati_powers_of_weighted_asymptotic
    hα hT hw.measurable hw.continuousOn_pos hw.asymptotic
  refine ⟨hw.measurable,hn,hw.contDiffAt_pos,h1,h2,measurable_const,fun _ _ => le_rfl,
    continuousOn_const,integrableOn_zero,?_⟩
  intro t ht
  rw [hw.volterra t ht]
  congr 1
  unfold volterraConvolution
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r _
  ring

theorem exists_affine_point_test
    {α q κ a T : ℝ} (hα : 1/2 < α) (hα' : α < 1) (hq : 0 < q)
    (hκ : 0 ≤ κ) (ha : 0 ≤ a) (hT : 0 < T) :
    ∃ w, AffineRiccatiTestOn α κ a q T w (fun _ => 0) ∧
      ∀ t > 0, 0 < w t ∧ w t ≤ q*fractionalK α t := by
  obtain ⟨w,hw,hB⟩ := exists_global_fractional_riccati_point_charge hα hα' hq
    (neg_nonpos.mpr hκ) (neg_nonpos.mpr ha)
  exact ⟨w,(hw T).affine_test hα hT (fun t ht => (hB t ht.1).1.le),hB⟩

private theorem affine_fractionalL_nonnegative {α x : ℝ} (hα : α < 1) (hx : 0 < x) :
    0 ≤ fractionalL α x := by
  rw [fractionalL,ite_eq_right (not_le.mpr hx)]
  exact div_nonneg (Real.rpow_nonneg hx.le _) (Real.Gamma_pos_of_pos (sub_pos.mpr hα)).le

private theorem affine_fractionalL_continuousOn (α : ℝ) :
    ContinuousOn (fractionalL α) (Ioi 0) := by
  refine (((continuousOn_id : ContinuousOn (fun x : ℝ => x) (Ioi 0)).rpow_const
    (p := -α) (fun _ hx => Or.inl (ne_of_gt hx))).div_const
    (Real.Gamma (1-α))).congr ?_
  intro x hx
  exact ite_eq_right (not_le.mpr hx)

theorem affine_input_on_of_initial_and_bounded_rate
    {α T v₀ C : ℝ} {r : ℝ → ℝ} (hα : 0 < α) (hα' : α < 1)
    (hT : 0 < T) (hv : 0 ≤ v₀) (hr : Measurable r)
    (hn : ∀ t ∈ Ioc 0 T, 0 ≤ r t) (hb : ∀ t ∈ Ioc 0 T, ‖r t‖ ≤ C) :
    AffineInputOn T (fun t => r t+v₀*fractionalL α t) := by
  have hi : IntegrableOn r (Ioc 0 T) := by
    refine (integrableOn_const (C := C) (by simp : volume (Ioc (0:ℝ) T) ≠ ∞)).mono'
      hr.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hb t ht
  refine ⟨hr.add ((fractionalL_measurable α).const_mul v₀),
    hi.add ((fractionalL_integrableOn_Ioc hα' T).const_mul v₀),
    fun t ht => add_nonneg (hn t ht) (mul_nonneg hv (affine_fractionalL_nonnegative hα' ht.1)),?_⟩
  exact ⟨_,affine_input_bounded_near_positive_terminal hα hα' hT
    (fun t ht => hb t ⟨(half_pos hT).trans_le ht.1,ht.2⟩) (fun _ _ => rfl)⟩

theorem affine_input_on_rectangular_pulse
    {α T ε d : ℝ} (hα : 0 < α) (hα' : α < 1) (hT : 0 < T) (hε : 0 ≤ ε) (hd : 0 < d) :
    AffineInputOn T (rectangularPulseRate ε d) := by
  have he : 0 ≤ ε/d := div_nonneg hε hd.le
  have hn (t : ℝ) : 0 ≤ rectangularPulseRate ε d t := by
    unfold rectangularPulseRate
    by_cases ht : t ∈ Ioc (0:ℝ) d
    · simpa only [indicator_of_mem ht] using he
    · simp only [indicator_of_notMem ht,le_refl]
  have hb (t : ℝ) : ‖rectangularPulseRate ε d t‖ ≤ ε/d := by
    rw [Real.norm_of_nonneg (hn t)]
    unfold rectangularPulseRate
    by_cases ht : t ∈ Ioc (0:ℝ) d
    · simp only [indicator_of_mem ht,le_refl]
    · simpa only [indicator_of_notMem ht] using he
  simpa only [zero_mul,add_zero] using affine_input_on_of_initial_and_bounded_rate
    (v₀ := 0) hα hα' hT le_rfl
    (by unfold rectangularPulseRate
        exact measurable_const.indicator measurableSet_Ioc)
    (fun t _ => hn t) (fun t _ => hb t)

private theorem affine_compact_continuous_extension {T : ℝ} (hT : 0 < T) {u : ℝ → ℝ}
    (hu : Continuous u) (huc : ∀ t ∈ Ioo 0 (T+3), ContDiffAt ℝ 1 u t) :
    ∃ w : ℝ → ℝ, Continuous w ∧ (∀ t > 0, ContDiffAt ℝ 1 w t) ∧ EqOn w u (Icc 0 T) := by
  let k : ContDiffBump (0:ℝ) := ⟨T+1,T+2,by linarith,by linarith⟩
  let w (t : ℝ) := k t*u t
  refine ⟨w,(k.contDiff (n := 1)).continuous.mul hu,?_,?_⟩
  · intro t ht
    by_cases ht' : t < T+3
    · exact k.contDiffAt.mul (huc t ⟨ht,ht'⟩)
    · refine (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds (show T+2<t by linarith [le_of_not_gt ht'])] with r hr
      have hr' : T+2 < r := hr
      have hz : k r = 0 := k.zero_of_le_dist (by
        change T+2 ≤ dist r (0:ℝ)
        rw [Real.dist_eq,sub_zero,abs_of_pos (by linarith)]
        exact hr'.le)
      simp [w,hz]
  · intro t ht
    have h1 : k t = 1 := k.one_of_mem_closedBall (by
      change dist t (0:ℝ) ≤ T+1
      rw [Real.dist_eq,sub_zero,abs_of_nonneg ht.1]
      linarith [ht.2])
    simp [w,h1]

/-- The two-parameter pulse density test q + l(L+κ) gives an actual
nonnegative, positive-time smooth affine test on each finite horizon. -/
theorem exists_affine_cluster_density_test
    {α κ a T q l : ℝ} (hα : 1/2 < α) (hα' : α < 1)
    (hκ : 0 ≤ κ) (ha : 0 < a) (hT : 0 < T) (hq : 0 < q) (hl : 0 ≤ l) :
    ∃ w : ℝ → ℝ, Continuous w ∧ w 0 = l ∧
      AffineRiccatiTestOn α κ a 0 T w (fun t => q+l*(fractionalL α t+κ)) ∧
      ∀ t ∈ Icc 0 T, w t = l +
        volterraConvolution (fractionalK α) (fun u => q+κ*l-κ*w u-a*(w u)^2) t := by
  have hα₀ : 0 < α := by linarith
  let z := q+κ*l
  let B := l+2+z/a
  have hz : 0 < z := add_pos_of_pos_of_nonneg hq (mul_nonneg hκ hl)
  have hza : 0 ≤ z/a := div_nonneg hz.le ha.le
  have hB₁ : 1 ≤ B := by dsimp [B]; linarith
  have hlB : l<B := by dsimp [B]; linarith
  have hB : z+(-κ)*B+(-a)*B^2 ≤ 0 := by
    have hBa : z ≤ a*B := by
      have h := (div_le_iff₀ ha).mp (show z/a ≤ B by dsimp [B]; linarith)
      simpa only [mul_comm a B] using h
    have hBA := mul_le_mul_of_nonneg_left hB₁ (show 0≤a*B by positivity)
    nlinarith [mul_nonneg hκ (show 0≤B by linarith)]
  obtain ⟨u,hu,hul,heq,hbound⟩ := exists_density_riccati_on_horizon
    hα hα' hz hl hlB hB (T+3)
  have huc (t : ℝ) (ht : t∈Ioo 0 (T+3)) : ContDiffAt ℝ 1 u t := by
    refine (density_riccati_caputo_of_volterra (d := z) (b := -κ) (c := -a) hα hα' ht hu (fun s hs => ?_)).1
    rw [hul]
    exact heq s hs
  obtain ⟨w,hw,hwcd,hwu⟩ := affine_compact_continuous_extension hT hu huc
  have hw0 : w 0=l := (hwu ⟨le_rfl,hT.le⟩).trans hul
  have hwEq (t : ℝ) (ht : t ∈ Icc 0 T) : w t = l +
      volterraConvolution (fractionalK α) (fun u => q+κ*l-κ*w u-a*(w u)^2) t := by
    rw [hwu ht,heq t ⟨ht.1,by linarith [ht.2]⟩]
    congr 1
    unfold volterraConvolution
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    dsimp only
    rw [hwu ⟨hr.1.le,hr.2.trans ht.2⟩]
    dsimp [z]
    ring
  have hfm : Measurable (fun t => q+l*(fractionalL α t+κ)) :=
    ((fractionalL_measurable α).add_const κ).const_mul l |>.const_add q
  have hfc : ContinuousOn (fun t => q+l*(fractionalL α t+κ)) (Ioi 0) :=
    continuousOn_const.add (continuousOn_const.mul ((affine_fractionalL_continuousOn α).add continuousOn_const))
  have hfi : IntegrableOn (fun t => q+l*(fractionalL α t+κ)) (Ioc 0 T) := by
    have hin (c : ℝ) : IntegrableOn (fun _ : ℝ => c) (Ioc 0 T) :=
      integrableOn_const (by simp)
    exact (hin q).add (((fractionalL_integrableOn_Ioc hα' T).add (hin κ)).const_mul l)
  refine ⟨w,hw,hw0,⟨hw.measurable,?_,hwcd,(hw.intervalIntegrable 0 T).1,
    ((hw.pow 2).intervalIntegrable 0 T).1,hfm,?_,hfc,hfi,?_⟩,hwEq⟩
  · intro t ht
    rw [hwu (Ioo_subset_Icc_self ht)]
    exact (hbound t ⟨ht.1.le,by linarith [ht.2]⟩).1
  · exact fun t ht => add_nonneg hq.le (mul_nonneg hl
      (add_nonneg (affine_fractionalL_nonnegative hα' ht.1) hκ))
  · intro t ht
    simpa only [zero_mul,zero_add] using density_riccati_affine_convolution hα₀ hα' ht hw hwEq

#print axioms exists_affine_point_test
#print axioms affine_input_on_of_initial_and_bounded_rate
#print axioms affine_input_on_rectangular_pulse
#print axioms exists_affine_cluster_density_test

end RoughHeston
