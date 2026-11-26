import RiccatiContinuation
import RiccatiDampingBound

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RoughHeston

/-- A continuous point-charge solution with its weighted initial value fixed.
The equation is required through the indicated horizon. -/
structure ContinuousPointChargeOn (α q b c T : ℝ) (w : ℝ → ℝ) : Prop where
  measurable : Measurable w
  continuousOn : ContinuousOn w (Ioi 0)
  volterra : ∀ t ∈ Ioc 0 T, w t = q * fractionalK α t +
    volterraConvolution (fractionalK α) (fun s => b * w s + c * w s^2) t
  asymptotic : Tendsto (fun s => s ^ (1-α) * w s) (𝓝[>] 0) (𝓝 (q / Real.Gamma α))

theorem ContinuousPointChargeOn.regular_restriction
    {α q b c S T : ℝ} {w : ℝ → ℝ}
    (hα : 1/2 < α) (hα' : α < 1) (hS : 0 < S) (hST : S < T)
    (hw : ContinuousPointChargeOn α q b c T w) :
    ∃ v, EqOn v w (Icc 0 S) ∧ PointChargeRiccatiOn α q b c S v := by
  let B : ContDiffBump (S/2) := ⟨S/2, T/2, by linarith, by linarith⟩
  let v (x : ℝ) := B x * w x
  have hB : ContDiff ℝ 1 (B : ℝ → ℝ) := B.contDiff
  have hvw : EqOn v w (Icc 0 S) := by
    intro x hx
    have hxB : x ∈ Metric.closedBall (S/2) B.rIn := by
      rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
      change -(S/2) ≤ x-S/2 ∧ x-S/2 ≤ S/2
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    simp [v, B.one_of_mem_closedBall hxB]
  refine ⟨v, hvw, hB.continuous.measurable.mul hw.measurable, ?_, ?_, ?_⟩
  · intro x hx
    by_cases hxT : x < T
    · exact hB.contDiffAt.mul (point_charge_riccati_contDiffAt_of_volterra hα hα'
        ⟨hx, hxT⟩ hw.measurable hw.continuousOn hw.asymptotic hw.volterra)
    · have hthin : B.rOut < dist x (S/2) := by
        rw [Real.dist_eq, abs_of_nonneg (by linarith [le_of_not_gt hxT])]
        change T/2 < x-S/2
        linarith [le_of_not_gt hxT]
      have hnear : ∀ᶠ y in 𝓝 x, B.rOut < dist y (S/2) :=
        continuousAt_const.eventually_lt (continuousAt_id.dist continuousAt_const) hthin
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hnear] with y hy
      simp [v, B.zero_of_le_dist hy.le]
  · intro x hx
    have hs : Ioc (0 : ℝ) x ⊆ Icc 0 S := fun z hz =>
      ⟨hz.1.le, hz.2.trans hx.2⟩
    rw [hvw (hs ⟨hx.1, le_rfl⟩), hw.volterra x ⟨hx.1, hx.2.trans hST.le⟩]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioc
    intro z hz
    change fractionalK α (x-z) * (b*w z+c*w z^2) =
      fractionalK α (x-z) * (b*v z+c*v z^2)
    rw [hvw (hs hz)]
  · have hnear : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Icc 0 S := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hS)] with x hx hxS
      exact ⟨(show 0 < x from hx).le, (show x < S from hxS).le⟩
    refine hw.asymptotic.congr' ?_
    filter_upwards [hnear] with x hx
    rw [hvw hx]

theorem ContinuousPointChargeOn.pos_le_charge_kernel
    {α q b c T t : ℝ} {w : ℝ → ℝ}
    (hα : 1/2 < α) (hα' : α < 1) (hq : 0 < q) (hb : b ≤ 0) (hc : c ≤ 0)
    (hw : ContinuousPointChargeOn α q b c T w) (ht : t ∈ Ioo 0 T) :
    0 < w t ∧ w t ≤ q * fractionalK α t := by
  obtain ⟨v, hvw, hv⟩ := hw.regular_restriction hα hα' ht.1 ht.2
  rw [← hvw (show t ∈ Icc 0 t from ⟨ht.1.le, le_rfl⟩)]
  exact ⟨point_charge_riccati_pos hα hα' ht.1 hq hv t ⟨ht.1, le_rfl⟩,
    point_charge_riccati_le_charge_kernel hα hα' ht.1 hq hb hc hv t ⟨ht.1, le_rfl⟩⟩

theorem ContinuousPointChargeOn.eq_of_lt_horizons
    {α q b c S T t : ℝ} {v w : ℝ → ℝ}
    (hα : 1/2 < α) (hα' : α < 1) (hq : 0 < q) (hb : b ≤ 0) (hc : c ≤ 0)
    (hv : ContinuousPointChargeOn α q b c S v)
    (hw : ContinuousPointChargeOn α q b c T w)
    (ht : 0 < t) (htS : t < S) (htT : t < T) : v t = w t := by
  obtain ⟨v', hvv, hv'⟩ := hv.regular_restriction hα hα' ht htS
  obtain ⟨w', hww, hw'⟩ := hw.regular_restriction hα hα' ht htT
  have ht' : t ∈ Icc 0 t := ⟨ht.le, le_rfl⟩
  rw [← hvv ht', ← hww ht']
  exact point_charge_riccati_eqOn_of_nonpositive_drift hα hα' ht hq hb hc hv' hw' ⟨ht, le_rfl⟩

#print axioms ContinuousPointChargeOn.regular_restriction
#print axioms ContinuousPointChargeOn.pos_le_charge_kernel
#print axioms ContinuousPointChargeOn.eq_of_lt_horizons

end RoughHeston
