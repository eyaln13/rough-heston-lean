import RiccatiChargeOrder
import SingularRiccatiLimit
import FractionalKernelSemigroup
import Mathlib.Topology.UniformSpace.Dini

open MeasureTheory Set Filter
open scoped Topology

namespace RoughHeston

private theorem fractionalK_nonnegative_for_damping {α : ℝ} (hα : 0 < α) (x : ℝ) :
    0 ≤ fractionalK α x := by
  by_cases hx : x ≤ 0
  · simp [fractionalK, hx]
  · rw [fractionalK, ite_eq_right hx]
    exact div_nonneg (Real.rpow_nonneg (lt_of_not_ge hx).le _) (Real.Gamma_pos_of_pos hα).le

private theorem fractionalK_mul_rpow_integrable {α p t : ℝ}
    (hα : 0 < α) (hp : -1 < p) (ht : 0 < t) :
    IntegrableOn (fun s => fractionalK α (t-s) * s^p) (Ioc 0 t) := by
  have ha : 0 < p+1 := by linarith
  obtain ⟨hi, _⟩ := real_beta_weight_scaled ha hα ht
  simp only [show p+1-1=p by ring] at hi
  have hβ : IntegrableOn (fun s => (Real.Gamma α)⁻¹ * (s^p * (t-s)^(α-1))) (Ioo 0 t) :=
    (hi.mono_set Ioo_subset_Ioc_self).const_mul _
  rw [integrableOn_Ioc_iff_integrableOn_Ioo]
  refine hβ.congr_fun ?_ measurableSet_Ioo
  intro s hs
  change (Real.Gamma α)⁻¹ * (s^p * (t-s)^(α-1)) = fractionalK α (t-s) * s^p
  rw [fractionalK, ite_eq_right (not_le.mpr (sub_pos.mpr hs.2))]
  ring

/-- Exact convolution of two fractional point kernels. -/
theorem fractionalK_self_convolution {α t : ℝ} (hα : 0 < α) (ht : 0 < t) :
    volterraConvolution (fractionalK α) (fractionalK α) t =
      t^(2*α-1)/Real.Gamma (2*α) := by
  rw [fractionalK_convolution_add hα hα ht, fractionalK, ite_eq_right (not_le.mpr ht),
    show α + α = 2 * α by ring]

/-- The nonpositive Riccati drift bounds a positive solution by its
uncompensated point-charge term. -/
theorem point_charge_riccati_le_charge_kernel {α q b c T : ℝ} {w : ℝ → ℝ}
    (hα : 1/2 < α) (hα' : α < 1) (hT : 0 < T) (hq : 0 < q)
    (hb : b ≤ 0) (hc : c ≤ 0) (hw : PointChargeRiccatiOn α q b c T w) :
    ∀ t ∈ Ioc 0 T, w t ≤ q * fractionalK α t := by
  have hα₀ : 0 < α := by linarith
  have hwpos := point_charge_riccati_pos hα hα' hT hq hw
  intro t ht
  have hInt : volterraConvolution (fractionalK α) (fun s => b*w s+c*w s^2) t ≤ 0 := by
    unfold volterraConvolution
    apply integral_nonpos_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hws := (hwpos s (Ioc_subset_Ioc_right ht.2 hs)).le
    exact mul_nonpos_of_nonneg_of_nonpos (fractionalK_nonnegative_for_damping hα₀ _)
      (add_nonpos (mul_nonpos_of_nonpos_of_nonneg hb hws)
        (mul_nonpos_of_nonpos_of_nonneg hc (sq_nonneg _)))
  rw [hw.volterra t ht]
  linarith

private theorem point_charge_kernel_drift_integrable {α q b c T t : ℝ} {w : ℝ → ℝ}
    (hα : 1/2 < α) (hα' : α < 1) (hq : 0 < q)
    (hb : b ≤ 0) (hc : c ≤ 0) (ht : t ∈ Ioc 0 T)
    (hw : PointChargeRiccatiOn α q b c T w) :
    IntegrableOn (fun s => fractionalK α (t-s) * (b*w s+c*w s^2)) (Ioc 0 t) := by
  have hα₀ : 0 < α := by linarith
  have hT := ht.1.trans_le ht.2
  have hwpos := point_charge_riccati_pos hα hα' hT hq hw
  have hk := point_charge_riccati_le_charge_kernel hα hα' hT hq hb hc hw
  let D := q/Real.Gamma α
  have hD : 0 ≤ D := div_nonneg hq.le (Real.Gamma_pos_of_pos hα₀).le
  have hW (s : ℝ) (hs : s ∈ Ioc 0 t) : 0 ≤ w s ∧ w s ≤ D * s^(α-1) := by
    have hsT := Ioc_subset_Ioc_right ht.2 hs
    refine ⟨(hwpos s hsT).le, (hk s hsT).trans_eq ?_⟩
    rw [fractionalK, ite_eq_right (not_le.mpr hs.1)]
    dsimp [D]
    ring
  have hK : Measurable (fun s => fractionalK α (t-s)) :=
    (fractionalK_measurable α).comp (measurable_const.sub measurable_id)
  have hIw : IntegrableOn (fun s => fractionalK α (t-s) * w s) (Ioc 0 t) := by
    have hi := (fractionalK_mul_rpow_integrable hα₀ (by linarith : -1 < α-1) ht.1).mul_const D
    refine hi.mono' (hK.mul hw.measurable).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hn := fractionalK_nonnegative_for_damping hα₀ (t-s)
    rw [Real.norm_of_nonneg (mul_nonneg hn (hW s hs).1)]
    exact (mul_le_mul_of_nonneg_left (hW s hs).2 hn).trans_eq (by ring)
  have hIw₂ : IntegrableOn (fun s => fractionalK α (t-s) * w s^2) (Ioc 0 t) := by
    have hi := (fractionalK_mul_rpow_integrable hα₀ (by linarith : -1 < (α-1)+(α-1))
      ht.1).mul_const (D^2)
    refine hi.mono' (hK.mul (hw.measurable.pow_const 2)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hn := fractionalK_nonnegative_for_damping hα₀ (t-s)
    rw [Real.norm_of_nonneg (mul_nonneg hn (sq_nonneg _))]
    refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hW s hs).1 (hW s hs).2 2) hn).trans_eq ?_
    rw [mul_pow, pow_two (s^(α-1)), ← Real.rpow_add hs.1]
    ring
  have hi : IntegrableOn (fun s => b * (fractionalK α (t-s) * w s) +
      c * (fractionalK α (t-s) * w s^2)) (Ioc 0 t) := (hIw.const_mul b).add (hIw₂.const_mul c)
  refine hi.congr_fun ?_ measurableSet_Ioc
  intro s _
  ring

private theorem fractionalK_self_integrable_for_damping {α t : ℝ} (hα : 0 < α) (ht : 0 < t) :
    IntegrableOn (fun s => fractionalK α (t-s)*fractionalK α s) (Ioc 0 t) := by
  have hi : IntegrableOn (fun s => (fractionalK α (t-s)*s^(α-1)) * (Real.Gamma α)⁻¹) (Ioc 0 t) :=
    (fractionalK_mul_rpow_integrable hα (by linarith : -1 < α-1) ht).mul_const _
  refine hi.congr_fun ?_ measurableSet_Ioc
  intro s hs
  change fractionalK α (t-s)*s^(α-1)*(Real.Gamma α)⁻¹ = fractionalK α (t-s)*fractionalK α s
  rw [show fractionalK α s = s^(α-1)/Real.Gamma α from ite_eq_right (not_le.mpr hs.1),
    div_eq_mul_inv, mul_assoc]

/-- Nonnegative damping changes a finite positive-charge solution by at
most `κ q (Kα*Kα)(t)` on the common solution horizon. -/
theorem point_charge_riccati_damping_error
    {α q κ a T : ℝ} {v w : ℝ → ℝ}
    (hα : 1/2 < α) (hα' : α < 1) (hT : 0 < T)
    (hq : 0 < q) (hκ : 0 ≤ κ) (ha : 0 ≤ a)
    (hv : PointChargeRiccatiOn α q 0 (-a) T v)
    (hw : PointChargeRiccatiOn α q (-κ) (-a) T w) :
    ∀ t ∈ Ioc 0 T, 0 ≤ v t-w t ∧
      v t-w t ≤ κ*q*volterraConvolution (fractionalK α) (fractionalK α) t := by
  have hα₀ : 0 < α := by linarith
  have horder := point_charge_riccati_damped_le_undamped hα hα' hT hq hκ ha hv hw
  have hwpos := point_charge_riccati_pos hα hα' hT hq hw
  have hupper := point_charge_riccati_le_charge_kernel hα hα' hT hq (neg_nonpos.mpr hκ)
    (neg_nonpos.mpr ha) hw
  intro t ht
  let Fv (s : ℝ) := fractionalK α (t-s)*(0*v s+(-a)*v s^2)
  let Fw (s : ℝ) := fractionalK α (t-s)*((-κ)*w s+(-a)*w s^2)
  let Q (s : ℝ) := κ*q*(fractionalK α (t-s)*fractionalK α s)
  have hFv : IntegrableOn Fv (Ioc 0 t) :=
    point_charge_kernel_drift_integrable hα hα' hq le_rfl (neg_nonpos.mpr ha) ht hv
  have hFw : IntegrableOn Fw (Ioc 0 t) :=
    point_charge_kernel_drift_integrable hα hα' hq (neg_nonpos.mpr hκ) (neg_nonpos.mpr ha) ht hw
  have hQ : IntegrableOn Q (Ioc 0 t) :=
    (fractionalK_self_integrable_for_damping hα₀ ht.1).const_mul _
  refine ⟨sub_nonneg.mpr (horder t ht), ?_⟩
  have hP (s : ℝ) (hs : s ∈ Ioc 0 t) : Fv s-Fw s ≤ Q s := by
    have hsT := Ioc_subset_Ioc_right ht.2 hs
    have hsq : w s^2 ≤ v s^2 := pow_le_pow_left₀ (hwpos s hsT).le (horder s hsT) 2
    have hb := mul_le_mul_of_nonneg_left (hupper s hsT) hκ
    have hc := mul_le_mul_of_nonneg_left hsq ha
    have h : (0*v s+(-a)*v s^2)-((-κ)*w s+(-a)*w s^2) ≤ κ*q*fractionalK α s := by
      linarith only [hb, hc]
    calc
      _ = fractionalK α (t-s)*((0*v s+(-a)*v s^2)-((-κ)*w s+(-a)*w s^2)) := by
        dsimp [Fv, Fw]; ring
      _ ≤ fractionalK α (t-s)*(κ*q*fractionalK α s) :=
        mul_le_mul_of_nonneg_left h (fractionalK_nonnegative_for_damping hα₀ _)
      _ = _ := by dsimp [Q]; ring
  have he : v t-w t = (∫ s in Ioc (0 : ℝ) t, Fv s) - ∫ s in Ioc (0 : ℝ) t, Fw s := by
    rw [hv.volterra t ht, hw.volterra t ht, volterraConvolution, volterraConvolution]
    change (q*fractionalK α t+∫ s in Ioc (0 : ℝ) t, Fv s) -
      (q*fractionalK α t+∫ s in Ioc (0 : ℝ) t, Fw s) = _
    ring
  rw [he, ← integral_sub hFv hFw]
  calc
    _ ≤ ∫ s in Ioc (0 : ℝ) t, Q s := setIntegral_mono_on (hFv.sub hFw) hQ measurableSet_Ioc hP
    _ = _ := by unfold Q volterraConvolution; rw [integral_const_mul]

/-- Monotone undamped charge convergence is uniform for the weighted
solution on compact intervals bounded away from the charged endpoint. -/
theorem finite_undamped_charge_weighted_lower
    {α a δ T η : ℝ} {v : ℕ → ℝ → ℝ}
    (hα : 1/2 < α) (hα' : α < 1) (hδ : 0 < δ) (hδT : δ ≤ T) (hη : 0 < η)
    (hv : ∀ n : ℕ, PointChargeRiccatiOn α (n : ℝ) 0 (-a) T (v n))
    (hlim : ∀ t ∈ Icc δ T, Tendsto (fun n => v n t) atTop
      (𝓝 (singularRiccatiProfile α (singularRiccatiCoefficient α a) t))) :
    ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N, ∀ t ∈ Icc δ T,
      singularRiccatiCoefficient α a - η ≤ t^α * v n t := by
  have hα₀ : 0 < α := by linarith
  have hT := hδ.trans_le hδT
  let c := singularRiccatiCoefficient α a
  let V (n : ℕ) (t : ℝ) := t^α * v n t
  have hVc (n : ℕ) : ContinuousOn (V n) (Icc δ T) :=
    (Real.continuous_rpow_const hα₀.le).continuousOn.mul
      ((hv n).continuousOn_pos.mono (fun _ ht => hδ.trans_le ht.1))
  have hmono (t : ℝ) (ht : t ∈ Icc δ T) : Monotone (fun n => V n t) := by
    intro n m hnm
    rcases eq_or_lt_of_le hnm with rfl | hlt
    · exact le_rfl
    · apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (hδ.le.trans ht.1) _)
      exact (point_charge_riccati_strictMono_charge hα hα' hT
        (Nat.cast_lt.mpr hlt) (hv m) (hv n) t ⟨hδ.trans_le ht.1, ht.2⟩).le
  have hpt (t : ℝ) (ht : t ∈ Icc δ T) : Tendsto (fun n => V n t) atTop (𝓝 c) := by
    have ht₀ := hδ.trans_le ht.1
    have h := (hlim t ht).const_mul (t^α)
    have he : t^α * singularRiccatiProfile α c t = c := by
      rw [singularRiccatiProfile, ite_eq_left ht₀, mul_left_comm, ← Real.rpow_add ht₀,
        add_neg_cancel, Real.rpow_zero, mul_one]
    change Tendsto (fun n => V n t) atTop (𝓝 (t^α * singularRiccatiProfile α c t)) at h
    rwa [he] at h
  have hU := Monotone.tendstoUniformlyOn_of_forall_tendsto isCompact_Icc hVc hmono
    (continuousOn_const : ContinuousOn (fun _ : ℝ => c) (Icc δ T)) hpt
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((Metric.tendstoUniformlyOn_iff.mp hU) η hη)
  refine ⟨max N 1, lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _), ?_⟩
  intro n hn t ht
  have h := hN n ((le_max_left _ _).trans hn) t ht
  change dist c (V n t) < η at h
  rw [Real.dist_eq] at h
  linarith only [(abs_lt.mp h).2]

/-- For sufficiently small damping, a single finite positive charge
uniformly attains any strictly smaller singular coefficient on a fixed
compact positive-time interval. -/
theorem exists_finite_charge_damped_lower_bound
    {α a δ T η : ℝ} {v : ℕ → ℝ → ℝ}
    (hα : 1/2 < α) (hα' : α < 1) (ha : 0 ≤ a)
    (hδ : 0 < δ) (hδT : δ ≤ T) (hη : 0 < η)
    (hv : ∀ n : ℕ, PointChargeRiccatiOn α (n : ℝ) 0 (-a) T (v n))
    (hlim : ∀ t ∈ Icc δ T, Tendsto (fun n => v n t) atTop
      (𝓝 (singularRiccatiProfile α (singularRiccatiCoefficient α a) t))) :
    ∃ N : ℕ, 0 < N ∧ ∃ κ₀ : ℝ, 0 < κ₀ ∧
      ∀ κ ∈ Icc 0 κ₀, ∀ {w : ℝ → ℝ},
        PointChargeRiccatiOn α (N : ℝ) (-κ) (-a) T w →
        ∀ t ∈ Icc δ T, (singularRiccatiCoefficient α a - η)*t^(-α) ≤ w t := by
  obtain ⟨N, hN, hvl⟩ := finite_undamped_charge_weighted_lower hα hα' hδ hδT
    (show 0 < η/2 by positivity) hv hlim
  have hα₀ : 0 < α := by linarith
  have hq : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hT := hδ.trans_le hδT
  have hΓ : 0 < Real.Gamma (2*α) := Real.Gamma_pos_of_pos (by positivity)
  have hpow : 0 ≤ 3*α-1 := by linarith
  let D := (N : ℝ)*T^(3*α-1)/Real.Gamma (2*α)
  have hD : 0 < D := div_pos (mul_pos hq (Real.rpow_pos_of_pos hT _)) hΓ
  let κ₀ := η/(2*D)
  have hκ₀ : 0 < κ₀ := div_pos hη (mul_pos (by norm_num) hD)
  refine ⟨N, hN, κ₀, hκ₀, ?_⟩
  intro κ hκ w hw t ht
  have ht₀ := hδ.trans_le ht.1
  have htT : t ∈ Ioc 0 T := ⟨ht₀, ht.2⟩
  have hl := hvl N le_rfl t ht
  have hdiff := (point_charge_riccati_damping_error hα hα' hT hq hκ.1 ha (hv N) hw t htT).2
  rw [fractionalK_self_convolution hα₀ ht₀] at hdiff
  have herr : t^α*(v N t-w t) ≤ η/2 := by
    calc
      _ ≤ t^α * (κ*(N : ℝ)*(t^(2*α-1)/Real.Gamma (2*α))) :=
        mul_le_mul_of_nonneg_left hdiff (Real.rpow_nonneg ht₀.le _)
      _ = κ*((N : ℝ)*t^(3*α-1)/Real.Gamma (2*α)) := by
        have he : t^α*t^(2*α-1)=t^(3*α-1) := by
          rw [← Real.rpow_add ht₀, show α+(2*α-1)=3*α-1 by ring]
        rw [← he]
        ring
      _ ≤ κ*D := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht₀.le ht.2 hpow) hq.le) hΓ.le) hκ.1
      _ ≤ κ₀*D := mul_le_mul_of_nonneg_right hκ.2 hD.le
      _ = η/2 := by dsimp [κ₀]; field_simp [hD.ne']
  have hl' : singularRiccatiCoefficient α a-η ≤ t^α*w t := by
    rw [mul_sub] at herr
    linarith only [hl, herr]
  apply (mul_le_mul_iff_of_pos_left (Real.rpow_pos_of_pos ht₀ α)).mp
  rw [mul_left_comm, ← Real.rpow_add ht₀, add_neg_cancel, Real.rpow_zero, mul_one]
  exact hl'

/-- The coefficient in the singular Riccati profile supplies the
fractional boundary comparison coefficient. -/
theorem two_mul_singularRiccatiCoefficient
    {α a : ℝ} (hα' : α < 1) (ha : 0 < a) :
    2*a*singularRiccatiCoefficient α a = boundaryCoefficient α := by
  have hΓ : 0 < Real.Gamma (2-2*α) := Real.Gamma_pos_of_pos (by linarith)
  unfold singularRiccatiCoefficient boundaryCoefficient
  field_simp [ha.ne', hΓ.ne']

/-- Finite-charge damped solutions attain a strict Caputo comparison
margin on every prescribed compact positive-time interval. -/
theorem exists_finite_charge_strict_caputo_lower
    {α a p δ T : ℝ} {v : ℕ → ℝ → ℝ}
    (hα : 1/2 < α) (hα' : α < 1) (ha : 0 < a)
    (hδ : 0 < δ) (hδT : δ ≤ T)
    (hp : caputoCoefficient α p < boundaryCoefficient α)
    (hv : ∀ n : ℕ, PointChargeRiccatiOn α (n : ℝ) 0 (-a) T (v n))
    (hlim : ∀ t ∈ Icc δ T, Tendsto (fun n => v n t) atTop
      (𝓝 (singularRiccatiProfile α (singularRiccatiCoefficient α a) t))) :
    ∃ N : ℕ, 0 < N ∧ ∃ κ₀ : ℝ, 0 < κ₀ ∧
      ∀ κ ∈ Icc 0 κ₀, ∀ {w : ℝ → ℝ},
        PointChargeRiccatiOn α (N : ℝ) (-κ) (-a) T w →
        ∀ t ∈ Icc δ T, caputoCoefficient α p * t^(-α) < 2*a*w t := by
  let η := (boundaryCoefficient α-caputoCoefficient α p)/(4*a)
  have hη : 0 < η := div_pos (sub_pos.mpr hp) (mul_pos (by norm_num) ha)
  obtain ⟨N, hN, κ₀, hκ₀, hbound⟩ := exists_finite_charge_damped_lower_bound hα hα' ha.le
    hδ hδT hη hv hlim
  have he : 2*a*η = (boundaryCoefficient α-caputoCoefficient α p)/2 := by
    dsimp [η]
    field_simp [ha.ne']
    ring
  have hc : caputoCoefficient α p < 2*a*(singularRiccatiCoefficient α a-η) := by
    rw [mul_sub, two_mul_singularRiccatiCoefficient hα' ha, he]
    linarith only [hp]
  refine ⟨N, hN, κ₀, hκ₀, ?_⟩
  intro κ hκ w hw t ht
  have hl := hbound κ hκ hw t ht
  calc
    _ < (2*a*(singularRiccatiCoefficient α a-η))*t^(-α) :=
      mul_lt_mul_of_pos_right hc (Real.rpow_pos_of_pos (hδ.trans_le ht.1) _)
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hl (mul_nonneg (by norm_num) ha.le)

#print axioms fractionalK_self_convolution
#print axioms point_charge_riccati_damping_error
#print axioms finite_undamped_charge_weighted_lower
#print axioms exists_finite_charge_damped_lower_bound
#print axioms exists_finite_charge_strict_caputo_lower

end RoughHeston
