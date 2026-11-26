import FractionalPowerTriangle
import FractionalKernelSemigroup
import HestonWeightedFubini

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

private theorem fractionalK_unit_positive {t : ℝ} (ht : 0<t) : fractionalK 1 t=1 := by
  simp [fractionalK,not_le.mpr ht,Real.Gamma_one]

private theorem convolution_primitive (g : ℝ→ℝ) (t : ℝ) :
    volterraConvolution (fractionalK 1) g t = ∫ r in Ioc (0:ℝ) t,g r := by
  unfold volterraConvolution
  rw [← restrict_Ioo_eq_restrict_Ioc]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r hr
  change fractionalK 1 (t-r)*g r=g r
  rw [fractionalK_unit_positive (sub_pos.mpr hr.2),one_mul]

private theorem volterra_bounded_assoc {f g : ℝ→ℝ} {a β t C B : ℝ}
    (ha : 0<a) (hβ : 0<β) (ht : 0<t) (hf : Measurable f) (hg : Measurable g)
    (hfb : ∀ r∈Ioc (0:ℝ) t, |f r|≤C*fractionalK a r)
    (hgb : ∀ r∈Ioc (0:ℝ) t, ‖g r‖≤B) :
    volterraConvolution f (volterraConvolution (fractionalK β) g) t =
      volterraConvolution (volterraConvolution f (fractionalK β)) g t := by
  have he := volterra_fractional_smul_assoc_of_power_bounds hβ ht hf hg.stronglyMeasurable
    ({()} : Finset Unit) ({()} : Finset Unit) (fun _ => a) (fun _ => C) (fun _ => 1) (fun _ => B)
    (fun _ _ => ha) (fun _ _ => zero_lt_one)
    (fun r hr => by simpa using hfb r hr)
    (fun r hr => by simpa [fractionalK_unit_positive hr.1] using hgb r hr)
  simpa only [volterraSmulConvolution,volterraConvolution,smul_eq_mul] using he

/-- Applying the causal kernel to the inverse history recovers the ordinary
primitive. The forcing can then be substituted on the entire past interval. -/
theorem fractional_inverse_recovers_primitive {α t : ℝ} {V d : ℝ→ℝ}
    (hα : 0<α) (hα' : α<1) (ht : 0<t)
    (hV : Continuous V)
    (hInv : EqOn (volterraConvolution (fractionalL α) V) d (Ioc (0:ℝ) t)) :
    (∫ r in Ioc (0:ℝ) t,V r)=volterraConvolution (fractionalK α) d t := by
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (hV.continuousOn (s := Icc (0:ℝ) t))
  have hK (r : ℝ) (hr : r∈Ioc (0:ℝ) t) :
      |fractionalK α r|≤1*fractionalK α r := by
    have hnon : 0≤fractionalK α r := by
      rw [fractionalK,ite_eq_right (not_le.mpr hr.1)]
      exact div_nonneg (Real.rpow_nonneg hr.1.le _) (Real.Gamma_pos_of_pos hα).le
    simp [abs_of_nonneg hnon]
  have ha := volterra_bounded_assoc hα (sub_pos.mpr hα') ht (fractionalK_measurable α)
    hV.measurable hK (fun r hr => hB r (Ioc_subset_Icc_self hr))
  have hL : fractionalK (1-α)=fractionalL α := by
    funext r
    simp only [fractionalK,fractionalL,show 1-α-1= -α by ring]
  have hKL : EqOn (volterraConvolution (fractionalK α) (fractionalK (1-α))) (fractionalK 1)
      (Icc (0:ℝ) t) := by
    intro r hr
    rcases eq_or_lt_of_le hr.1 with hr0|hr0
    · subst r
      simp [volterraConvolution,fractionalK]
    · rw [fractionalK_convolution_add hα (sub_pos.mpr hα') hr0,show α+(1-α)=1 by ring]
  have hconv : volterraConvolution (volterraConvolution (fractionalK α) (fractionalK (1-α))) V t =
      volterraConvolution (fractionalK 1) V t := by
    unfold volterraConvolution
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    change volterraConvolution (fractionalK α) (fractionalK (1-α)) (t-r)*V r=
      fractionalK 1 (t-r)*V r
    rw [hKL (show t-r∈Icc 0 t from ⟨sub_nonneg.mpr hr.2,sub_le_self _ hr.1.le⟩)]
  calc
    _ = volterraConvolution (fractionalK 1) V t := (convolution_primitive V t).symm
    _ = volterraConvolution (fractionalK α) (volterraConvolution (fractionalL α) V) t := by
      rw [← hL,ha,hconv]
    _ = _ := by
      unfold volterraConvolution
      apply setIntegral_congr_fun measurableSet_Ioc
      intro r hr
      change fractionalK α (t-r)*volterraConvolution (fractionalL α) V r = fractionalK α (t-r)*d r
      rw [hInv hr]

private theorem bounded_weighted_convolution_integrable {R g : ℝ→ℝ} {t B : ℝ}
    (hR : Measurable R) (hg : Measurable g) (ht : 0≤t)
    (hi : IntegrableOn R (Ioc (0:ℝ) t)) (hb : ∀ r∈Ioc (0:ℝ) t, ‖g r‖≤B) :
    IntegrableOn (fun r => R (t-r)*g r) (Ioc (0:ℝ) t) := by
  have hI := (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).2 hi
  have hI' : IntervalIntegrable (fun r => R (t-r)) volume 0 t :=
    by simpa only [sub_zero,sub_self] using (hI.comp_sub_left t).symm
  refine (hI'.1.norm.mul_const B).mono'
    (((hR.comp (measurable_const.sub measurable_id)).mul hg).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hb r hr) (norm_nonneg _)

/-- Resolve the deterministic integrated Volterra equation for a continuous
drive and primitive. The two paths can be fixed on one sample point. -/
theorem resolve_integrated_fractional_equation {α κ t : ℝ} {R A D : ℝ→ℝ}
    (hα : 0<α) (ht : 0<t) (hR : Measurable R) (hA : Continuous A) (hD : Continuous D)
    {Rbound : ℝ} (hRb : ∀ r∈Ioc (0:ℝ) t, |R r|≤Rbound*fractionalK α r)
    (hRes : ∀ r∈Ioc (0:ℝ) t,R r=fractionalK α r-κ*volterraConvolution (fractionalK α) R r)
    (hEq : EqOn A (volterraConvolution (fractionalK α) (fun r => D r-κ*A r)) (Ioc (0:ℝ) t)) :
    A t=volterraConvolution R D t := by
  let K := fractionalK α
  let g (r : ℝ) := D r-κ*A r
  have hgc : Continuous g := hD.sub (continuous_const.mul hA)
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (hgc.continuousOn (s := Icc (0:ℝ) t))
  obtain ⟨BA,hBA⟩ := isCompact_Icc.exists_bound_of_continuousOn (hA.continuousOn (s := Icc (0:ℝ) t))
  have hI (f : ℝ→ℝ) (hfm : Measurable f)
      (hfb : ∀ r∈Ioc (0:ℝ) t, ‖f r‖≤Rbound*fractionalK α r) : IntegrableOn f (Ioc 0 t) := by
    refine ((fractionalK_integrableOn_Ioc hα t).const_mul Rbound).mono' hfm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr using hfb r hr
  have hRi := hI R hR (fun r hr => by simpa only [Real.norm_eq_abs] using hRb r hr)
  have hKi := fractionalK_integrableOn_Ioc hα t
  have hRg := bounded_weighted_convolution_integrable hR hgc.measurable ht.le hRi
    (fun r hr => hB r (Ioc_subset_Icc_self hr))
  have hKg := bounded_weighted_convolution_integrable (fractionalK_measurable α)
    hgc.measurable ht.le hKi (fun r hr => hB r (Ioc_subset_Icc_self hr))
  have hRA := bounded_weighted_convolution_integrable hR hA.measurable ht.le hRi
    (fun r hr => hBA r (Ioc_subset_Icc_self hr))
  have hass := volterra_bounded_assoc hα hα ht hR hgc.measurable hRb
    (fun r hr => hB r (Ioc_subset_Icc_self hr))
  have ha : volterraConvolution R A t=volterraConvolution (volterraConvolution R K) g t := by
    rw [← hass]
    unfold volterraConvolution
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    change R (t-r)*A r=R (t-r)*volterraConvolution K g r
    rw [hEq hr]
  have he (r : ℝ) (hr : r ∈ Ioo (0:ℝ) t) :
      κ*(volterraConvolution R K (t-r)*g r) = K (t-r)*g r-R (t-r)*g r := by
    have hb := hRes (t-r) ⟨sub_pos.mpr hr.2,sub_le_self _ hr.1.le⟩
    rw [← volterraConvolution_comm_at (sub_nonneg.mpr hr.2.le)] at hb
    rw [← mul_assoc]
    linarith only [congrArg (fun x : ℝ => x*g r) hb]
  have hlinear : κ*volterraConvolution (volterraConvolution R K) g t =
      volterraConvolution K g t-volterraConvolution R g t := by
    unfold volterraConvolution
    rw [← integral_const_mul,← integral_sub hKg hRg,← restrict_Ioo_eq_restrict_Ioc]
    apply setIntegral_congr_fun measurableSet_Ioo
    exact he
  have hDsplit : volterraConvolution R D t=volterraConvolution R g t+κ*volterraConvolution R A t := by
    unfold volterraConvolution
    rw [← integral_const_mul,← integral_add hRg (hRA.const_mul κ)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r _
    dsimp [g]
    ring
  rw [hDsplit,ha,hlinear,hEq ⟨ht,le_rfl⟩]
  change volterraConvolution K g t = _
  ring

#print axioms fractional_inverse_recovers_primitive
#print axioms resolve_integrated_fractional_equation

end RoughHeston
