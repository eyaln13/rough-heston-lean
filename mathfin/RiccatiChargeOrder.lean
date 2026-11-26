import FractionalConvolutionRegularity

open MeasureTheory Set Filter
open scoped Topology Interval NNReal

namespace RoughHeston

/-- A regular point-charge solution on a finite horizon, with its
weighted initial value fixed by the charge. -/
structure PointChargeRiccatiOn (α q b c T : ℝ) (w : ℝ → ℝ) : Prop where
  measurable : Measurable w
  contDiffAt_pos : ∀ t, 0 < t → ContDiffAt ℝ 1 w t
  volterra : ∀ t ∈ Ioc 0 T, w t = q * fractionalK α t +
    volterraConvolution (fractionalK α) (fun s => b * w s + c * w s^2) t
  asymptotic : Tendsto (fun s => s ^ (1-α) * w s) (𝓝[>] 0) (𝓝 (q / Real.Gamma α))

theorem PointChargeRiccatiOn.continuousOn_pos {α q b c T : ℝ} {w : ℝ → ℝ}
    (hw : PointChargeRiccatiOn α q b c T w) : ContinuousOn w (Ioi 0) :=
  fun t ht => (hw.contDiffAt_pos t ht).continuousAt.continuousWithinAt

theorem PointChargeRiccatiOn.of_global_volterra {α q b c T : ℝ} {w : ℝ → ℝ}
    (hα : 1 / 2 < α) (hα' : α < 1) (hm : Measurable w) (hc : ContinuousOn w (Ioi 0))
    (hvol : ∀ t > 0, w t = q * fractionalK α t +
      volterraConvolution (fractionalK α) (fun s => b * w s + c * w s^2) t)
    (hlim : Tendsto (fun s => s ^ (1-α) * w s) (𝓝[>] 0) (𝓝 (q / Real.Gamma α))) :
    PointChargeRiccatiOn α q b c T w :=
  ⟨hm, fun t ht => point_charge_riccati_contDiffAt_of_volterra hα hα'
    (T := t+1) ⟨ht, by linarith⟩ hm hc hlim (fun s hs => hvol s hs.1),
    fun t ht => hvol t ht.1, hlim⟩

private theorem point_charge_kernel_contDiffAt {α t : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ 1 (fractionalK α) t := by
  have hp : ContDiffAt ℝ 1 (fun s : ℝ => s^(α-1)) t :=
    Real.contDiffAt_rpow_const_of_ne ht.ne'
  have hK : ContDiffAt ℝ 1 (fun s : ℝ => s^(α-1) / Real.Gamma α) t := by
    simpa only [div_eq_mul_inv] using
      hp.mul (show ContDiffAt ℝ 1 (fun _ : ℝ => (Real.Gamma α)⁻¹) t from contDiffAt_const)
  refine hK.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact ite_eq_right (not_le.mpr (show 0 < s from hs))

private theorem point_charge_kernel_pos {α t : ℝ} (hα : 0 < α) (ht : 0 < t) :
    0 < fractionalK α t := by
  rw [fractionalK, ite_eq_right (not_le.mpr ht)]
  exact div_pos (Real.rpow_pos_of_pos ht _) (Real.Gamma_pos_of_pos hα)

private theorem tendsto_weighted_fractionalK (α : ℝ) :
    Tendsto (fun s : ℝ => s ^ (1-α) * fractionalK α s) (𝓝[>] 0) (𝓝 ((Real.Gamma α)⁻¹)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hpos : 0 < s := hs
  rw [fractionalK, ite_eq_right (not_le.mpr hpos), ← mul_div_assoc,
    ← Real.rpow_add hpos, show 1-α+(α-1)=0 by ring, Real.rpow_zero, one_div]

private theorem strict_positive_of_fractional_weighted_start {α A T : ℝ} {g : ℝ → ℝ}
    (hα : 0 < α) (hα' : α < 1) (hA : 0 < A)
    (hc : ContinuousOn g (Ioi 0))
    (hlim : Tendsto (fun t => t^(1-α) * g t) (𝓝[>] 0) (𝓝 A))
    (hcontact : ∀ t ∈ Ioc 0 T, g t = 0 →
      IntervalIntegrable (fun u => (α*u^(-α-1)/Real.Gamma (1-α)) * (g t-g (t-u))) volume 0 t ∧
      0 ≤ fractionalMemory α 0 g t) :
    ∀ t ∈ Ioc 0 T, 0 < g t := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp (hlim.eventually (Ioi_mem_nhds hA)))
  let d := r/2
  have hd : 0 < d := by dsimp [d]; positivity
  have hstart (t : ℝ) (ht : t ∈ Ioc 0 d) : 0 < g t := by
    have hdist : dist t (0 : ℝ) < r := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
      have hh : t ≤ r/2 := ht.2
      linarith
    have hprod : 0 < t^(1-α) * g t := hball hdist ht.1
    exact (mul_pos_iff_of_pos_left (Real.rpow_pos_of_pos ht.1 _)).mp hprod
  intro t ht
  by_cases htd : t ≤ d
  · exact hstart t ⟨ht.1, htd⟩
  · exact fractional_first_contact_comparison hα hα' le_rfl hd
      (hc.mono (fun _ hs => hd.trans_le hs.1)) hstart
      (fun s hs => hcontact s ⟨hd.trans_le hs.1, hs.2⟩) t ⟨le_of_not_ge htd, ht.2⟩

private theorem fractionalMemory_eq_of_primitive {α p T t : ℝ} {g F : ℝ → ℝ}
    (hα : 0 < α) (hα' : α < 1) (ht : t ∈ Ioc 0 T)
    (hgm : Measurable g) (hgi : IntegrableOn g (Ioc 0 t))
    (hgc : ContDiffAt ℝ 1 g t)
    (hFm : Measurable F) (hFi : IntegrableOn F (Ioc 0 t))
    (hFc : ContinuousAt F t)
    (hprim : ∀ s ∈ Ioc 0 T,
      volterraConvolution (fractionalL α) g s = p + ∫ u in Ioc (0 : ℝ) s, F u) :
    IntervalIntegrable (fun u => (α*u^(-α-1)/Real.Gamma (1-α)) * (g t-g (t-u))) volume 0 t ∧
      fractionalMemory α 0 g t = F t := by
  obtain ⟨hi, hG⟩ := fractional_rl_hasDerivAt_memory hα hα' ht.1 hgm hgi hgc
  have hI := (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1.le).mpr hFi
  have hD := (intervalIntegral.integral_hasDerivAt_right hI
    hFm.aestronglyMeasurable.stronglyMeasurableAtFilter hFc).const_add p
  have he (s : ℝ) (hs : s ∈ Ioc 0 T) :
      volterraConvolution (fractionalL α) g s = p + ∫ u in (0 : ℝ)..s, F u := by
    rw [intervalIntegral.integral_of_le hs.1.le]
    exact hprim s hs
  have hD' := hD.hasDerivWithinAt.congr he (he t ht)
  have hU := uniqueDiffOn_Ioc (0 : ℝ) T t ht
  exact ⟨hi, (hG.hasDerivWithinAt.derivWithin hU).symm.trans (hD'.derivWithin hU)⟩

private theorem point_charge_fractionalL_mul_kernel_integrable {α t : ℝ}
    (hα : 0 < α) (hα' : α < 1) (ht : 0 < t) :
    IntegrableOn (fun s => fractionalL α (t-s) * fractionalK α s) (Ioc 0 t) := by
  by_contra hi
  have h := fractional_causal_kernel_inverse hα hα' ht
  unfold volterraConvolution at h
  rw [integral_undef hi] at h
  exact zero_ne_one h

/-- A strictly positive effective charge gap rules out contact whenever
the drift difference is nonnegative at contact. Adding a positive
multiple of the point kernel is allowed because its inverse primitive
is constant. -/
theorem point_charge_riccati_strict_perturbed_order
    {α qv qw bv cv bw cw T ε : ℝ} {v w : ℝ → ℝ}
    (hα : 1 / 2 < α) (hα' : α < 1) (hT : 0 < T) (hq : 0 < qv-qw+ε)
    (hv : PointChargeRiccatiOn α qv bv cv T v) (hw : PointChargeRiccatiOn α qw bw cw T w)
    (hcontact : ∀ t ∈ Ioc 0 T, v t-w t+ε*fractionalK α t = 0 →
      0 ≤ (bv*v t+cv*v t^2)-(bw*w t+cw*w t^2)) :
    ∀ t ∈ Ioc 0 T, 0 < v t - w t + ε * fractionalK α t := by
  have hα₀ : 0 < α := by linarith
  let g (t : ℝ) := v t - w t + ε * fractionalK α t
  let Fv (s : ℝ) := bv*v s+cv*v s^2
  let Fw (s : ℝ) := bw*w s+cw*w s^2
  let F (s : ℝ) := Fv s-Fw s
  have hgm : Measurable g :=
    (hv.measurable.sub hw.measurable).add ((fractionalK_measurable α).const_mul ε)
  have hgc (t : ℝ) (ht : 0 < t) : ContDiffAt ℝ 1 g t :=
    ((hv.contDiffAt_pos t ht).sub (hw.contDiffAt_pos t ht)).add
      (contDiffAt_const.mul (point_charge_kernel_contDiffAt ht))
  have hFvm : Measurable Fv := (hv.measurable.const_mul bv).add ((hv.measurable.pow_const 2).const_mul cv)
  have hFwm : Measurable Fw := (hw.measurable.const_mul bw).add ((hw.measurable.pow_const 2).const_mul cw)
  have hFm : Measurable F := hFvm.sub hFwm
  have hFc (t : ℝ) (ht : 0 < t) : ContinuousAt F t := by
    have hc₁ := (hv.contDiffAt_pos t ht).continuousAt
    have hc₂ := (hw.contDiffAt_pos t ht).continuousAt
    exact ((continuousAt_const.mul hc₁).add (continuousAt_const.mul (hc₁.pow 2))).sub
      ((continuousAt_const.mul hc₂).add (continuousAt_const.mul (hc₂.pow 2)))
  obtain ⟨hvi, hvi₂⟩ := integrableOn_riccati_powers_of_weighted_asymptotic hα hT
    hv.measurable hv.continuousOn_pos hv.asymptotic
  obtain ⟨hwi, hwi₂⟩ := integrableOn_riccati_powers_of_weighted_asymptotic hα hT
    hw.measurable hw.continuousOn_pos hw.asymptotic
  have hFv : IntegrableOn Fv (Ioc 0 T) := (hvi.const_mul bv).add (hvi₂.const_mul cv)
  have hFw : IntegrableOn Fw (Ioc 0 T) := (hwi.const_mul bw).add (hwi₂.const_mul cw)
  have hFi : IntegrableOn F (Ioc 0 T) := hFv.sub hFw
  have hgi : IntegrableOn g (Ioc 0 T) :=
    (hvi.sub hwi).add ((fractionalK_integrableOn_Ioc hα₀ T).const_mul ε)
  have hlim : Tendsto (fun t => t^(1-α)*g t) (𝓝[>] 0) (𝓝 ((qv-qw+ε)/Real.Gamma α)) := by
    have hh := (hv.asymptotic.sub hw.asymptotic).add ((tendsto_weighted_fractionalK α).const_mul ε)
    rw [show qv/Real.Gamma α-qw/Real.Gamma α+ε*(Real.Gamma α)⁻¹ =
      (qv-qw+ε)/Real.Gamma α by ring] at hh
    apply hh.congr'
    exact Eventually.of_forall fun t => by dsimp [g]; ring
  have hprim (t : ℝ) (ht : t ∈ Ioc 0 T) :
      volterraConvolution (fractionalL α) g t = (qv-qw+ε) + ∫ u in Ioc (0 : ℝ) t, F u := by
    obtain ⟨hLv, hvP⟩ := fractional_riccati_rl_primitive hα₀ hα' ht hv.measurable hFv hv.volterra
    obtain ⟨hLw, hwP⟩ := fractional_riccati_rl_primitive hα₀ hα' ht hw.measurable hFw hw.volterra
    have hLK := point_charge_fractionalL_mul_kernel_integrable (α := α) hα₀ hα' ht.1
    have hDiff : IntegrableOn (fun s => fractionalL α (t-s) * v s - fractionalL α (t-s) * w s)
        (Ioc 0 t) := hLv.sub hLw
    have hLift : volterraConvolution (fractionalL α) g t =
        volterraConvolution (fractionalL α) v t - volterraConvolution (fractionalL α) w t +
          ε * volterraConvolution (fractionalL α) (fractionalK α) t := by
      unfold volterraConvolution
      calc
        _ = ∫ s in Ioc (0 : ℝ) t, (fractionalL α (t-s) * v s - fractionalL α (t-s) * w s) +
            ε * (fractionalL α (t-s) * fractionalK α s) :=
          setIntegral_congr_fun measurableSet_Ioc (fun s _ => by dsimp [g]; ring)
        _ = _ := by
          rw [integral_add hDiff (hLK.const_mul ε), integral_sub hLv hLw, integral_const_mul]
    rw [hLift, hvP, hwP, fractional_causal_kernel_inverse hα₀ hα' ht.1]
    change (qv + ∫ s in Ioc (0 : ℝ) t, Fv s) -
        (qw + ∫ s in Ioc (0 : ℝ) t, Fw s) + ε*1 =
        qv-qw+ε + ∫ s in Ioc (0 : ℝ) t, Fv s-Fw s
    rw [integral_sub (hFv.mono_set (Ioc_subset_Ioc_right ht.2))
      (hFw.mono_set (Ioc_subset_Ioc_right ht.2))]
    ring
  apply strict_positive_of_fractional_weighted_start hα₀ hα'
    (div_pos hq (Real.Gamma_pos_of_pos hα₀)) (fun t ht => (hgc t ht).continuousAt.continuousWithinAt) hlim
  intro t ht hz
  obtain ⟨hi, hM⟩ := fractionalMemory_eq_of_primitive hα₀ hα' ht hgm
    (hgi.mono_set (Ioc_subset_Ioc_right ht.2)) (hgc t ht.1) hFm
    (hFi.mono_set (Ioc_subset_Ioc_right ht.2)) (hFc t ht.1) hprim
  refine ⟨hi, ?_⟩
  rw [hM]
  exact hcontact t ht hz

/-- Larger charge gives a strictly larger solution with the same drift. -/
theorem point_charge_riccati_strictMono_charge
    {α qv qw b c T : ℝ} {v w : ℝ → ℝ}
    (hα : 1 / 2 < α) (hα' : α < 1) (hT : 0 < T) (hq : qw<qv)
    (hv : PointChargeRiccatiOn α qv b c T v) (hw : PointChargeRiccatiOn α qw b c T w) :
    ∀ t ∈ Ioc 0 T, w t < v t := by
  have hcontact (t : ℝ) (_ : t ∈ Ioc 0 T)
      (hz : v t-w t+0*fractionalK α t = 0) :
      0 ≤ (b*v t+c*v t^2)-(b*w t+c*w t^2) := by
    have he : v t = w t := sub_eq_zero.mp (by simpa only [zero_mul, add_zero] using hz)
    simp [he]
  have h := point_charge_riccati_strict_perturbed_order hα hα' hT
    (show 0 < qv-qw+0 by linarith) hv hw hcontact
  exact fun t ht => sub_pos.mp (by simpa only [zero_mul, add_zero] using h t ht)

theorem zero_pointChargeRiccatiOn (α b c T : ℝ) :
    PointChargeRiccatiOn α 0 b c T (fun _ => 0) := by
  refine ⟨measurable_const, fun _ _ => contDiffAt_const, ?_, ?_⟩
  · intro t _
    simp [volterraConvolution]
  · simpa only [mul_zero, zero_div] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0))

/-- Every positive point charge stays strictly positive. -/
theorem point_charge_riccati_pos
    {α q b c T : ℝ} {w : ℝ → ℝ}
    (hα : 1 / 2 < α) (hα' : α < 1) (hT : 0 < T) (hq : 0<q)
    (hw : PointChargeRiccatiOn α q b c T w) : ∀ t ∈ Ioc 0 T, 0 < w t :=
  point_charge_riccati_strictMono_charge hα hα' hT hq hw (zero_pointChargeRiccatiOn α b c T)

/-- For a family of nonnegative charges, the values at each fixed
positive time are monotone in the charge. -/
theorem point_charge_riccati_mono_charge_family
    {α b c T t : ℝ} {w : ℝ≥0 → ℝ → ℝ}
    (hα : 1 / 2 < α) (hα' : α < 1) (ht : t ∈ Ioc 0 T)
    (hw : ∀ q : ℝ≥0, PointChargeRiccatiOn α (q : ℝ) b c T (w q)) :
    Monotone (fun q => w q t) := by
  intro q r hqr
  rcases eq_or_lt_of_le hqr with rfl | h
  · exact le_rfl
  · exact (point_charge_riccati_strictMono_charge hα hα' (ht.1.trans_le ht.2)
      (show (q : ℝ) < (r : ℝ) from h) (hw r) (hw q) t ht).le

/-- Increasing the charge or weakening the negative drift coefficients
increases the solution. For equal charges, perturbing the gap by a small
point kernel supplies a strict initial gap. -/
theorem point_charge_riccati_le_of_drift_coefficients
    {α qv qw bv cv bw cw T : ℝ} {v w : ℝ → ℝ}
    (hα : 1 / 2 < α) (hα' : α < 1) (hT : 0 < T)
    (hqw : 0 < qw) (hq : qw≤qv)
    (hb : bw≤bv) (hc : cw≤cv) (hb₀ : bw≤0) (hc₀ : cw≤0)
    (hv : PointChargeRiccatiOn α qv bv cv T v) (hw : PointChargeRiccatiOn α qw bw cw T w) :
    ∀ t ∈ Ioc 0 T, w t ≤ v t := by
  have hα₀ : 0 < α := by linarith
  have hvpos := point_charge_riccati_pos hα hα' hT (hqw.trans_le hq) hv
  intro t ht
  by_contra! hbad
  let K := fractionalK α t
  have hK : 0 < K := point_charge_kernel_pos hα₀ ht.1
  let ε := (w t-v t)/(2*K)
  have hε : 0 < ε := div_pos (sub_pos.mpr hbad) (mul_pos (by norm_num) hK)
  have hεK : ε*K = (w t-v t)/2 := by
    dsimp [ε]
    field_simp [hK.ne']
  have hg (s : ℝ) (hs : s ∈ Ioc 0 T) (hz : v s-w s+ε*fractionalK α s = 0) :
      0 ≤ (bv*v s+cv*v s^2)-(bw*w s+cw*w s^2) := by
    have hvw : v s ≤ w s := by
      linarith only [hz, mul_nonneg hε.le (point_charge_kernel_pos hα₀ hs.1).le]
    have hvs := (hvpos s hs).le
    have hb₁ := (mul_le_mul_of_nonpos_left hvw hb₀).trans (mul_le_mul_of_nonneg_right hb hvs)
    have hc₁ := (mul_le_mul_of_nonpos_left (pow_le_pow_left₀ hvs hvw 2) hc₀).trans
      (mul_le_mul_of_nonneg_right hc (sq_nonneg (v s)))
    exact sub_nonneg.mpr (add_le_add hb₁ hc₁)
  have hpos := point_charge_riccati_strict_perturbed_order hα hα' hT
    (add_pos_of_nonneg_of_pos (sub_nonneg.mpr hq) hε) hv hw hg t ht
  change 0 < v t-w t+ε*K at hpos
  rw [hεK] at hpos
  linarith

/-- At a fixed positive charge, the damped solution lies below the
undamped solution. -/
theorem point_charge_riccati_damped_le_undamped
    {α q κ a T : ℝ} {v w : ℝ → ℝ}
    (hα : 1 / 2 < α) (hα' : α < 1) (hT : 0 < T)
    (hq : 0 < q) (hκ : 0 ≤ κ) (ha : 0 ≤ a)
    (hv : PointChargeRiccatiOn α q 0 (-a) T v)
    (hw : PointChargeRiccatiOn α q (-κ) (-a) T w) :
    ∀ t ∈ Ioc 0 T, w t ≤ v t :=
  point_charge_riccati_le_of_drift_coefficients hα hα' hT hq le_rfl
    (neg_nonpos.mpr hκ) le_rfl (neg_nonpos.mpr hκ) (neg_nonpos.mpr ha) hv hw

/-- Positive-charge solutions are unique for nonpositive coefficients
within the regular weighted class. -/
theorem point_charge_riccati_eqOn_of_nonpositive_drift
    {α q b c T : ℝ} {v w : ℝ → ℝ}
    (hα : 1 / 2 < α) (hα' : α < 1) (hT : 0 < T)
    (hq : 0 < q) (hb : b ≤ 0) (hc : c ≤ 0)
    (hv : PointChargeRiccatiOn α q b c T v)
    (hw : PointChargeRiccatiOn α q b c T w) :
    EqOn v w (Ioc 0 T) := by
  intro t ht
  exact le_antisymm
    (point_charge_riccati_le_of_drift_coefficients hα hα' hT hq le_rfl le_rfl le_rfl hb hc hw hv t ht)
    (point_charge_riccati_le_of_drift_coefficients hα hα' hT hq le_rfl le_rfl le_rfl hb hc hv hw t ht)

#print axioms point_charge_riccati_strict_perturbed_order
#print axioms point_charge_riccati_strictMono_charge
#print axioms point_charge_riccati_pos
#print axioms point_charge_riccati_mono_charge_family
#print axioms point_charge_riccati_damped_le_undamped
#print axioms point_charge_riccati_eqOn_of_nonpositive_drift

end RoughHeston
