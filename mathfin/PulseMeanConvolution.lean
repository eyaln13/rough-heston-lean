import IntegratedFractionalResolvent
import CanonicalFractionalPulseAge

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

private theorem unitKernel_eq_one {x : ℝ} (hx : 0<x) : fractionalK 1 x=1 := by
  simp [fractionalK,not_le.mpr hx,Real.Gamma_one]

private theorem unit_conv_primitive (f : ℝ→ℝ) {t : ℝ} (ht : 0≤t) :
    volterraConvolution (fractionalK 1) f t=∫ r in (0:ℝ)..t,f r := by
  unfold volterraConvolution
  rw [intervalIntegral.integral_of_le ht,← restrict_Ioo_eq_restrict_Ioc]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r hr
  change fractionalK 1 (t-r)*f r=f r
  rw [unitKernel_eq_one (sub_pos.mpr hr.2),one_mul]

/-- The time primitive commutes with a causal resolvent acting on any
bounded measurable deterministic immigration. -/
theorem primitive_commutes_causal_resolvent {α t D B : ℝ} {R j : ℝ→ℝ}
    (hα : 0<α) (ht : 0<t) (hD : 0≤D)
    (hR : Measurable R) (hR₀ : ∀ r≤0,R r=0)
    (hRb : ∀ r∈Ioc (0:ℝ) t, |R r|≤D*fractionalK α r)
    (hj : Measurable j) (hjB : ∀ r∈Ioc (0:ℝ) t,‖j r‖≤B) :
    volterraConvolution R (fun s => ∫ r in (0:ℝ)..s,j r) t =
      ∫ s in (0:ℝ)..t,volterraConvolution R j s := by
  let K := fractionalK 1
  have hk : Measurable K := fractionalK_measurable _
  have hL := volterra_fractional_smul_assoc_of_power_bounds (β := 1)
    zero_lt_one ht hR hj.stronglyMeasurable
    ({()} : Finset Unit) ({()} : Finset Unit) (fun _ => α) (fun _ => D) (fun _ => 1) (fun _ => B)
    (fun _ _ => hα) (fun _ _ => zero_lt_one)
    (fun r hr => by simpa using hRb r hr)
    (fun r hr => by simpa [unitKernel_eq_one hr.1] using hjB r hr)
  let ν := volume.restrict (Ioc (0:ℝ) t)
  have htri : Integrable (fun z : ℝ×ℝ => (K (t-z.1)*fractionalK α (z.1-z.2))*j z.2) (ν.prod ν) := by
    have htri := fractional_power_triangle_smul_integrable hα ht hk hj.stronglyMeasurable
      ({()} : Finset Unit) ({()} : Finset Unit) (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => B)
      (fun _ _ => zero_lt_one) (fun _ _ => zero_lt_one)
      (fun r hr => by simp [K,unitKernel_eq_one hr.1])
      (fun r hr => by simpa [unitKernel_eq_one hr.1] using hjB r hr)
    simpa only [ν,smul_eq_mul] using htri
  have htriR : Integrable (fun z : ℝ×ℝ => (K (t-z.1)*R (z.1-z.2)) • j z.2) (ν.prod ν) := by
    refine (htri.norm.const_mul D).mono' ?_ ?_
    · exact (((hk.comp (measurable_const.sub measurable_fst)).mul
        (hR.comp (measurable_fst.sub measurable_snd))).mul (hj.comp measurable_snd)).aestronglyMeasurable
    have hfst : ∀ᵐ z ∂ν.prod ν,z.1∈Ioc (0:ℝ) t :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
    have hsnd : ∀ᵐ z ∂ν.prod ν,z.2∈Ioc (0:ℝ) t :=
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hfst,hsnd] with z hz₁ hz₂
    by_cases hp : 0<z.1-z.2
    · have hh := hRb (z.1-z.2) ⟨hp,(sub_le_self _ hz₂.1.le).trans hz₁.2⟩
      have hK : 0≤fractionalK α (z.1-z.2) := by
        rw [fractionalK,ite_eq_right (not_le.mpr hp)]
        exact div_nonneg (Real.rpow_nonneg hp.le _) (Real.Gamma_pos_of_pos hα).le
      simp only [smul_eq_mul,norm_mul,Real.norm_eq_abs (R (z.1-z.2)),Real.norm_of_nonneg hK]
      have hmul := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hh (norm_nonneg (K (t-z.1)))) (norm_nonneg (j z.2))
      exact hmul.trans_eq (by ring)
    · simp only [smul_eq_mul,hR₀ _ (le_of_not_gt hp),mul_zero,zero_mul,norm_zero]
      exact mul_nonneg hD (norm_nonneg (K (t-z.1)*fractionalK α (z.1-z.2)*j z.2))
  have hAssocL : volterraConvolution R (volterraConvolution K j) t =
      volterraConvolution (volterraConvolution R K) j t := by
    simpa only [volterraSmulConvolution,K,volterraConvolution,smul_eq_mul] using hL
  have hAssocR : volterraConvolution K (volterraConvolution R j) t =
      volterraConvolution (volterraConvolution K R) j t := by
    simpa only [volterraSmulConvolution,volterraConvolution,smul_eq_mul] using
      volterra_smul_convolution_assoc hR₀ htriR
  calc
    _ = volterraConvolution R (volterraConvolution K j) t := by
      unfold volterraConvolution
      apply setIntegral_congr_fun measurableSet_Ioc
      intro r hr
      change R (t-r)*(∫ x in (0:ℝ)..r,j x)=R (t-r)*volterraConvolution K j r
      rw [unit_conv_primitive j hr.1.le]
    _ = volterraConvolution (volterraConvolution R K) j t := hAssocL
    _ = volterraConvolution (volterraConvolution K R) j t := by
      unfold volterraConvolution
      apply setIntegral_congr_fun measurableSet_Ioc
      intro r hr
      change volterraConvolution R K (t-r)*j r=volterraConvolution K R (t-r)*j r
      rw [volterraConvolution_comm_at (sub_nonneg.mpr hr.2)]
    _ = volterraConvolution K (volterraConvolution R j) t := hAssocR.symm
    _ = _ := unit_conv_primitive _ ht.le

/-- The affine profile of a translated rectangular pulse is the resolvent
integral over the translated pulse interval, with a fixed horizon cutoff
on the resolvent. -/
theorem translatedPulse_resolvent_value {T s ε d : ℝ} {τ : ℝ≥0} {R : ℝ→ℝ}
    (hd : 0<d) (hs : s∈Icc (0:ℝ) T) (hR₀ : ∀ r≤0,R r=0) :
    volterraConvolution R (fun u => translatedPulseRate τ ε d u.toNNReal) s =
      (ε/d)*∫ u in (s-(τ:ℝ)-d)..(s-(τ:ℝ)), (Ioc (0:ℝ) T).indicator R u := by
  let k := (Ioc (0:ℝ) T).indicator R
  let S := Ioc (τ:ℝ) ((τ:ℝ)+d)
  have he : EqOn (fun u => R (s-u)*translatedPulseRate τ ε d u.toNNReal)
      (S.indicator (fun u => (ε/d)*k (s-u))) (Ioc 0 s) := by
    intro u hu
    have he : u-(τ:ℝ)∈Ioc (0:ℝ) d ↔ u∈S := by
      change (0<u-(τ:ℝ) ∧ u-(τ:ℝ)≤d) ↔ ((τ:ℝ)<u ∧ u≤(τ:ℝ)+d)
      constructor <;> intro hh <;> constructor <;> linarith [hh.1,hh.2]
    have hk : k (s-u)=R (s-u) := by
      by_cases hp : 0<s-u
      · exact Set.indicator_of_mem (show s-u∈Ioc (0:ℝ) T from ⟨hp,(sub_le_self _ hu.1.le).trans hs.2⟩) R
      · rw [hR₀ _ (le_of_not_gt hp)]
        exact Set.indicator_of_notMem (show s-u∉Ioc (0:ℝ) T from fun h => hp h.1) R
    change R (s-u)*translatedPulseRate τ ε d u.toNNReal =
      S.indicator (fun u => (ε/d)*k (s-u)) u
    unfold translatedPulseRate rectangularPulseRate
    rw [Real.coe_toNNReal u hu.1.le]
    by_cases h : u∈S
    · rw [Set.indicator_of_mem h,Set.indicator_of_mem (he.mpr h),hk,mul_comm]
    · simp only [Set.indicator_of_notMem h,Set.indicator_of_notMem (fun h' => h (he.mp h')),mul_zero]
  unfold volterraConvolution
  rw [setIntegral_congr_fun measurableSet_Ioc he,setIntegral_indicator
    (show MeasurableSet S from measurableSet_Ioc)]
  have hExt : (∫ u in (Ioc (0:ℝ) s ∩ S),(ε/d)*k (s-u)) = ∫ u in S,(ε/d)*k (s-u) := by
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (show MeasurableSet S from measurableSet_Ioc) inter_subset_right
    intro u hu
    have hus : s<u := by
      by_contra! h
      exact hu.2 ⟨⟨(NNReal.coe_nonneg τ).trans_lt hu.1.1,h⟩,hu.1⟩
    change (ε/d)*k (s-u)=0
    rw [show k (s-u)=0 from Set.indicator_of_notMem (show s-u∉Ioc (0:ℝ) T from fun h => (not_lt_of_ge (sub_nonpos.mpr hus.le)) h.1) R,mul_zero]
  rw [hExt,integral_const_mul]
  congr 1
  rw [show S=Ioc (τ:ℝ) ((τ:ℝ)+d) from rfl,← intervalIntegral.integral_of_le
    (le_add_of_nonneg_right hd.le),intervalIntegral.integral_comp_sub_left,sub_add_eq_sub_sub]

/-- The deterministic rectangular-pulse mean is continuous through the
birth and the end of the pulse. -/
theorem translatedPulse_resolvent_continuous_extension {T ε d : ℝ} {τ : ℝ≥0} {R : ℝ→ℝ}
    (hd : 0<d) (hR₀ : ∀ r≤0,R r=0) (hRi : IntegrableOn R (Ioc (0:ℝ) T)) :
    ∃ g : ℝ→ℝ,Continuous g ∧ EqOn
      (volterraConvolution R (fun u => translatedPulseRate τ ε d u.toNNReal)) g (Icc (0:ℝ) T) := by
  let k := (Ioc (0:ℝ) T).indicator R
  have hi : Integrable k := (integrable_indicator_iff measurableSet_Ioc).2 hRi
  let A (s : ℝ) := ∫ u in (0:ℝ)..s,k u
  have hA : Continuous A := intervalIntegral.continuous_primitive (fun a b => hi.intervalIntegrable) 0
  have hdiff (a b : ℝ) : (∫ u in a..b,k u)=A b-A a := by
    have h := intervalIntegral.integral_add_adjacent_intervals (hi.intervalIntegrable (a := 0) (b := a))
      (hi.intervalIntegrable (a := a) (b := b))
    change A a+(∫ u in a..b,k u)=A b at h
    linarith
  let g (s : ℝ) := (ε/d)*(A (s-(τ:ℝ))-A (s-(τ:ℝ)-d))
  have hg : Continuous g := continuous_const.mul
    ((hA.comp (continuous_id.sub continuous_const)).sub
      (hA.comp ((continuous_id.sub continuous_const).sub continuous_const)))
  refine ⟨g,hg,?_⟩
  intro s hs
  rw [translatedPulse_resolvent_value hd hs hR₀,hdiff]

#print axioms primitive_commutes_causal_resolvent
#print axioms translatedPulse_resolvent_value
#print axioms translatedPulse_resolvent_continuous_extension

end RoughHeston
