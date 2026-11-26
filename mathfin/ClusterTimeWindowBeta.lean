import ClusterKernelBetaBound

open MeasureTheory Set Filter
open scoped NNReal ENNReal Interval

namespace RoughHeston

theorem cluster_beta_window {a b p q : ℝ} (hab : a<b) (hp : 0<p) (hq : 0<q) :
    let f (u : ℝ) := (u-a)^(p-1)*(b-u)^(q-1)
    IntegrableOn f (Ioc a b) ∧
      (∫ u in Ioc a b, f u) = (b-a)^(p+q-1)*(Real.Gamma p*Real.Gamma q/Real.Gamma (p+q)) := by
  let L := b-a
  have hL : 0<L := sub_pos.mpr hab
  let g (x : ℝ) := x^(p-1)*(L-x)^(q-1)
  have ⟨hgi,hg⟩ := real_beta_weight_scaled hp hq hL
  have hi : IntervalIntegrable g volume 0 L :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le).2 hgi
  have hshift : IntervalIntegrable (fun u => g (u + -a)) volume a b := by
    simpa only [sub_neg_eq_add,zero_add, L,sub_add_cancel] using hi.comp_add_right (-a)
  have he : (fun u => (u-a)^(p-1)*(b-u)^(q-1))=fun u => g (u + -a) := by
    funext u; dsimp [g,L]; rw [show b-a-(u + -a)=b-u by ring,sub_eq_add_neg u a]
  dsimp only
  rw [he]
  constructor
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).1 hshift
  · rw [←intervalIntegral.integral_of_le hab.le,intervalIntegral.integral_comp_add_right,
      add_neg_cancel, ←sub_eq_add_neg,intervalIntegral.integral_of_le hL.le]
    exact hg

/-- Integrating a physical row supported on a subinterval of the
horizon gives exactly the beta estimate in the length of the subinterval. -/
theorem heston_time_window_beta_bound {T a b : ℝ≥0} (hab : a<b) (hbT : b≤T)
    {p q C : ℝ} (hp : 0<p) (hq : 0<q) (hC : 0≤C) {g : ℝ≥0 → ℝ}
    (hg : Measurable g) (hzero : ∀ t, t∉Ioc a b → g t=0)
    (hdom : ∀ t∈Ioo a b, 0 ≤ g t ∧ g t ≤
      C*(((t:ℝ)-(a:ℝ))^(p-1)*((b:ℝ)-(t:ℝ))^(q-1))) :
    Integrable g (hestonTimeMeasure T) ∧
    (∫ t,g t ∂hestonTimeMeasure T) ≤
      C*(((b:ℝ)-(a:ℝ))^(p+q-1)*(Real.Gamma p*Real.Gamma q/Real.Gamma (p+q))) := by
  let S := Ioc (a:ℝ) (b:ℝ)
  let ν := volume.restrict (Ioc (0:ℝ) (T:ℝ))
  let f (u : ℝ) := (u-(a:ℝ))^(p-1)*((b:ℝ)-u)^(q-1)
  have hab' : (a:ℝ)<(b:ℝ) := hab
  obtain ⟨hfi,hf⟩ := cluster_beta_window hab' hp hq
  have hS : MeasurableSet S := measurableSet_Ioc
  have hν : ν.restrict S = volume.restrict S := by
    rw [Measure.restrict_restrict hS, inter_eq_left.mpr
      (Ioc_subset_Ioc a.coe_nonneg (show (b:ℝ)≤(T:ℝ) from hbT))]
  have hcomp : ∀ᵐ u ∂volume.restrict S, 0 ≤ g u.toNNReal ∧ g u.toNNReal ≤ C*f u := by
    filter_upwards [ae_restrict_mem hS,ae_restrict_of_ae (volume.ae_ne (b:ℝ))] with u hu hne
    have hu0 := a.coe_nonneg.trans hu.1.le
    have huc : (u.toNNReal:ℝ)=u := Real.coe_toNNReal _ hu0
    have hl : a<u.toNNReal := by change (a:ℝ)<(u.toNNReal:ℝ); rw [huc]; exact hu.1
    have hr : u.toNNReal<b := by change (u.toNNReal:ℝ)<(b:ℝ); rw [huc]; exact lt_of_le_of_ne hu.2 hne
    simpa only [huc,f] using hdom u.toNNReal ⟨hl,hr⟩
  let G (u : ℝ) := g u.toNNReal
  have hG : Measurable G := hg.comp continuous_real_toNNReal.measurable
  have hi : Integrable G (volume.restrict S) := by
    apply (hfi.const_mul C).mono' hG.aestronglyMeasurable
    filter_upwards [hcomp] with u hu
    change ‖g u.toNNReal‖ ≤ C*f u
    rw [Real.norm_of_nonneg hu.1]; exact hu.2
  have he : G =ᵐ[ν] S.indicator G := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    by_cases hs : u∈S
    · rw [indicator_of_mem hs]
    · rw [indicator_of_notMem hs]
      apply hzero
      intro hz
      apply hs
      change (a:ℝ)<u ∧ u≤(b:ℝ)
      have h' : (a:ℝ)<(u.toNNReal:ℝ) ∧ (u.toNNReal:ℝ)≤(b:ℝ) := ⟨hz.1,hz.2⟩
      simpa only [Real.coe_toNNReal _ hu.1.le] using h'
  have hiν : Integrable G ν := by
    apply Integrable.congr _ he.symm
    apply (integrable_indicator_iff hS).2
    change Integrable G (ν.restrict S)
    rwa [hν]
  have hbound := integral_mono_ae hi (hfi.const_mul C) (hcomp.mono fun _ h => h.2)
  rw [integral_const_mul,hf] at hbound
  unfold hestonTimeMeasure
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  refine ⟨(integrable_map_measure hg.aestronglyMeasurable continuous_real_toNNReal.measurable.aemeasurable).2 hiν,?_⟩
  rw [integral_map continuous_real_toNNReal.measurable.aemeasurable hg.aestronglyMeasurable]
  change ∫ u,G u ∂ν ≤ _
  rw [integral_congr_ae he,integral_indicator hS,hν]
  exact hbound

#print axioms cluster_beta_window
#print axioms heston_time_window_beta_bound

end RoughHeston
