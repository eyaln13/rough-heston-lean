import AffineFutureTerminalLimit
import AffineDeterministicIntegrability
import AffineTestPrimitive
import Mathlib.Analysis.Calculus.FDeriv.Measurable

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RoughHeston

/-- Deterministic data used by the point and density affine tests. -/
structure AffineRiccatiTestOn (α κ a q T : ℝ) (w f : ℝ → ℝ) : Prop where
  solution_measurable : Measurable w
  solution_nonnegative : ∀ t ∈ Ioo 0 T, 0 ≤ w t
  solution_smooth : ∀ t > 0, ContDiffAt ℝ 1 w t
  solution_integrable : IntegrableOn w (Ioc 0 T)
  solution_sq_integrable : IntegrableOn (fun s => (w s)^2) (Ioc 0 T)
  rate_measurable : Measurable f
  rate_nonnegative : ∀ t ∈ Ioo 0 T, 0 ≤ f t
  rate_continuous : ContinuousOn f (Ioi 0)
  rate_integrable : IntegrableOn f (Ioc 0 T)
  volterra : ∀ t ∈ Ioc 0 T, w t = q*fractionalK α t+
    volterraConvolution (fractionalK α) (fun r => f r-κ*w r-a*(w r)^2) t

/-- Nonnegative deterministic input with integrable initial history and
a bounded rate near the positive terminal time. -/
structure AffineInputOn (T : ℝ) (j : ℝ → ℝ) : Prop where
  measurable : Measurable j
  integrable : IntegrableOn j (Ioc 0 T)
  nonnegative : ∀ s ∈ Ioc 0 T, 0 ≤ j s
  terminal_bound : ∃ C : ℝ, ∀ s ∈ Icc (T/2) T, ‖j s‖ ≤ C

noncomputable def affinePastPayoff (f V : ℝ → ℝ) (T t : ℝ) : ℝ :=
  ∫ r in Ioc (0:ℝ) t, f (T-r)*V r

noncomputable def affineFuturePayoff (α : ℝ) (w j V : ℝ → ℝ) (T t : ℝ) : ℝ :=
  ∫ y in Ioc (0:ℝ) (T-t), w (T-t-y)*affineFutureInput α t j V y

private theorem integrableOn_mul_of_right_bound
    {f g : ℝ → ℝ} {S : Set ℝ} {C : ℝ}
    (hS : MeasurableSet S) (hf : IntegrableOn f S) (hg : Measurable g)
    (hB : ∀ x ∈ S, ‖g x‖ ≤ C) :
    IntegrableOn (fun x => f x*g x) S := by
  refine (hf.norm.mul_const C).mono' (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem hS] with x hx
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hB x hx) (norm_nonneg _)

private theorem affine_reflected_integrableOn {T : ℝ} {f : ℝ → ℝ}
    (hT : 0 ≤ T) (hi : IntegrableOn f (Ioc 0 T)) :
    IntegrableOn (fun r => f (T-r)) (Ioc 0 T) := by
  have h := ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr hi).symm.comp_sub_left T
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp (by
    simpa only [sub_self,sub_zero] using h)

theorem affine_test_integrable_past_payoff
    {T : ℝ} {f V : ℝ → ℝ} (hT : 0 ≤ T)
    (hf : IntegrableOn f (Ioc 0 T)) (hV : Continuous V) :
    IntegrableOn (fun r => f (T-r)*V r) (Ioc 0 T) := by
  obtain ⟨C,hC⟩ := isCompact_Icc.bddAbove_image (K := Icc (0:ℝ) T) hV.norm.continuousOn
  exact integrableOn_mul_of_right_bound measurableSet_Ioc (affine_reflected_integrableOn hT hf)
    hV.measurable (fun r hr => hC ⟨r,Ioc_subset_Icc_self hr,rfl⟩)

theorem AffineRiccatiTestOn.solution_continuous
    {α κ a q T : ℝ} {w f : ℝ → ℝ} (h : AffineRiccatiTestOn α κ a q T w f) :
    ContinuousOn w (Ioi 0) :=
  fun t ht => (h.solution_smooth t ht).continuousAt.continuousWithinAt

theorem AffineRiccatiTestOn.primitive
    {α κ a q T : ℝ} {w f : ℝ → ℝ} (h : AffineRiccatiTestOn α κ a q T w f)
    (hα : 0 < α) (hα' : α < 1) (hT : 0 < T) :
    (∀ t ∈ Ioc 0 T, IntegrableOn (fun r => fractionalL α (t-r)*w r) (Ioc 0 t)) ∧
      (∀ t ∈ Ioo 0 T, HasDerivAt (volterraConvolution (fractionalL α) w)
        (f t-κ*w t-a*(w t)^2) t) ∧
      Tendsto (volterraConvolution (fractionalL α) w) (𝓝[>] (0:ℝ)) (𝓝 q) :=
  affine_test_primitive_and_derivative hα hα' hT
    ((h.rate_measurable.sub (h.solution_measurable.const_mul κ)).sub
      ((h.solution_measurable.pow_const 2).const_mul a))
    ((h.rate_integrable.sub (h.solution_integrable.const_mul κ)).sub
      (h.solution_sq_integrable.const_mul a))
    ((h.rate_continuous.sub (continuousOn_const.mul h.solution_continuous)).sub
      (continuousOn_const.mul (h.solution_continuous.pow 2))) h.volterra

theorem affine_terminal_input_pairing_integrable
    {T : ℝ} {w j : ℝ → ℝ} (hT : 0 < T)
    (hwM : Measurable w) (hwc : ContinuousOn w (Ioi 0)) (hwi : IntegrableOn w (Ioc 0 T))
    (hj : AffineInputOn T j) :
    IntegrableOn (fun r => w (T-r)*j r) (Ioc 0 T) := by
  obtain ⟨C,hC⟩ := hj.terminal_bound
  let m := T/2
  have hm : 0 < m := half_pos hT
  have hmT : m ≤ T := by dsimp [m]; linarith
  have hwOn : ContinuousOn w (Icc m T) := hwc.mono (fun _ hs => hm.trans_le hs.1)
  obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image hwOn.norm
  have hLeft' : IntegrableOn (fun r => j r*w (T-r)) (Ioc 0 m) :=
    integrableOn_mul_of_right_bound measurableSet_Ioc
      (hj.integrable.mono_set (Ioc_subset_Ioc_right hmT))
      (hwM.comp (measurable_const.sub measurable_id)) (fun r hr =>
        hB ⟨T-r,⟨by dsimp [m] at *; linarith [hr.2],sub_le_self _ hr.1.le⟩,rfl⟩)
  have hLeft : IntegrableOn (fun r => w (T-r)*j r) (Ioc 0 m) := by
    simpa only [mul_comm] using hLeft'
  have hRight : IntegrableOn (fun r => w (T-r)*j r) (Ioc m T) :=
    integrableOn_mul_of_right_bound measurableSet_Ioc
      ((affine_reflected_integrableOn hT.le hwi).mono_set (Ioc_subset_Ioc_left hm.le))
      hj.measurable (fun r hr => hC r ⟨hr.1.le,hr.2⟩)
  rw [← Ioc_union_Ioc_eq_Ioc hm.le hmT]
  exact hLeft.union hRight

/-- The deterministic pathwise verification of the preterminal split
from the actual inverse variance equation. -/
theorem affine_pathwise_exponent_split
    {α κ a q T t : ℝ} {w f j V M : ℝ → ℝ}
    (hα : 0 < α) (hα' : α < 1) (ht : t ∈ Ioo 0 T)
    (hw : AffineRiccatiTestOn α κ a q T w f)
    (hj : AffineInputOn T j) (hV : Continuous V)
    (hInv : ∀ s ∈ Ioc 0 t, M s = volterraConvolution (fractionalL α) V s +
      ∫ r in Ioc (0:ℝ) s,κ*V r-j r) :
    w (T-t)*M t +
      (∫ r in Ioc (0:ℝ) t,deriv w (T-r)*M r) +
      a*(∫ r in Ioc (0:ℝ) t,(w (T-r))^2*V r) =
        affinePastPayoff f V T t-volterraConvolution w j T+affineFuturePayoff α w j V T t := by
  have hT := ht.1.trans ht.2
  let d := T-t
  have hd : 0 < d := sub_pos.mpr ht.2
  have hdT : d ≤ T := sub_le_self _ ht.1.le
  have hdt : d+t = T := by dsimp [d]; ring
  have hPrim := (hw.primitive hα hα' hT).2.1
  have hDerivative (r : ℝ) (hr : r∈Ioo d (d+t)) :
      HasDerivAt (volterraConvolution (fractionalL α) w) (f r-κ*w r-a*(w r)^2) r :=
    hPrim r ⟨hd.trans hr.1,hr.2.trans_eq hdt⟩
  let g (r : ℝ) := deriv w (d+r)
  have hg : Measurable g := (measurable_deriv w).comp (measurable_const.add measurable_id)
  have hgc : ContinuousOn g (Icc 0 t) := by
    have he : ContDiffOn ℝ 1 w (Ioi 0) := fun r hr => (hw.solution_smooth r hr).contDiffWithinAt
    exact (he.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).comp
      (continuous_const.add continuous_id).continuousOn (fun r hr => add_pos_of_pos_of_nonneg hd hr.1)
  obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image hgc.norm
  let C := max B 0
  have hC : 0 ≤ C := le_max_right _ _
  have hCbound (r : ℝ) (hr : r∈Icc 0 t) : ‖g r‖ ≤ C :=
    (hB ⟨r,hr,rfl⟩).trans (le_max_left _ _)
  have hVint : IntegrableOn V (Ioc 0 t) := (hV.intervalIntegrable 0 t).1
  have hLint : IntegrableOn (fun r => fractionalL α (t-r)*V r) (Ioc 0 t) := by
    obtain ⟨Vmax,hVm⟩ := isCompact_Icc.bddAbove_image (K := Icc (0:ℝ) t) hV.norm.continuousOn
    exact integrableOn_mul_of_right_bound measurableSet_Ioc
      (fractionalL_reflected_integrableOn_Ioc hα' ht.1.le) hV.measurable
      (fun r hr => hVm ⟨r,Ioc_subset_Icc_self hr,rfl⟩)
  have hD : IntegrableOn (fun r => κ*V r-j r) (Ioc 0 t) :=
    (hVint.const_mul κ).sub (hj.integrable.mono_set (Ioc_subset_Ioc_right ht.2.le))
  have hTF := affine_volterra_triangle_integrable ht.1.le hC hg (fractionalL_measurable α)
    hV.measurable (fun r hr => ite_eq_left hr) (fractionalL_integrableOn_Ioc hα' t)
    hVint hCbound
  have hTD := affine_volterra_triangle_integrable ht.1.le hC hg (fractionalK_measurable 1)
    ((hV.measurable.const_mul κ).sub hj.measurable)
    (fun r hr => ite_eq_left hr) (fractionalK_integrableOn_Ioc zero_lt_one t) hD hCbound
  have hTH := affine_history_triangle_integrable hα hα' hd ht.1.le hw.solution_measurable
    (hw.solution_integrable.mono_set (Ioc_subset_Ioc_right hdT))
    (hw.solution_continuous.mono (fun _ hr => (half_pos hd).trans_le hr.1))
    hV.measurable hV.continuousOn
  have hWC : ContinuousOn (fun r : ℝ => w (T-r)) (Icc 0 t) :=
    hw.solution_continuous.comp (continuous_const.sub continuous_id).continuousOn
      (fun r hr => sub_pos.mpr (hr.2.trans_lt ht.2))
  have hWV : IntegrableOn (fun r => (w (T-r))^2*V r) (Ioc 0 t) :=
    ((hWC.pow 2).mul hV.continuousOn).intervalIntegrable_of_Icc ht.1.le |>.1
  have hWj := affine_terminal_input_pairing_integrable hT hw.solution_measurable
    hw.solution_continuous hw.solution_integrable hj
  have hFv := (affine_test_integrable_past_payoff hT.le hw.rate_integrable hV).mono_set
    (Ioc_subset_Ioc_right ht.2.le)
  have he := affine_preterminal_inverse_exponent_split hα hα' hd ht.1
    hw.solution_measurable (hw.solution_integrable.mono_set (Ioc_subset_Ioc_right hdT))
    hw.solution_smooth hDerivative hInv hLint hD
    (by simpa only [hdt] using hWj) (by simpa only [hdt] using hFv)
    (by simpa only [hdt] using hWV) hTF hTD hTH
  unfold volterraConvolution affinePastPayoff affineFuturePayoff affineFutureInput at *
  have hEq (r : ℝ) : d+(t-r)=T-r := by linarith
  simp_rw [hEq,hdt] at he
  exact he

/-- The nonnegative future payoff contributes to the uniform bound
on the preterminal stochastic exponential. -/
theorem affine_future_payoff_nonnegative
    {α κ a q T t : ℝ} {w f j V : ℝ → ℝ} (hα : 0 ≤ α) (hα' : α < 1)
    (ht : t∈Icc 0 T) (hw : AffineRiccatiTestOn α κ a q T w f)
    (hj : AffineInputOn T j) (hV : ∀ r ∈ Ioc 0 T,0≤V r) :
    0 ≤ affineFuturePayoff α w j V T t := by
  unfold affineFuturePayoff
  apply integral_nonneg_of_ae
  rw [← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  have hw₀ : 0 ≤ w (T-t-y) := hw.solution_nonnegative _ ⟨by linarith [hy.2],
    by linarith [ht.1,hy.1]⟩
  refine mul_nonneg hw₀ (add_nonneg (hj.nonnegative _ ⟨by linarith [ht.1,hy.1],
    by linarith [hy.2]⟩) ?_)
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  exact mul_nonneg (fractionalHistoryDensity_nonneg hα hα' (by linarith [hy.1,hr.2]))
    (hV r ⟨hr.1,hr.2.trans ht.2⟩)

/-- The known past and the future exponent approach the full terminal
payoff, including its possible point mass. -/
theorem affine_pathwise_payoffs_left_limit
    {α κ a q T : ℝ} {w f j V : ℝ → ℝ}
    (hα : 0 < α) (hα' : α < 1) (hT : 0 < T)
    (hw : AffineRiccatiTestOn α κ a q T w f)
    (hj : AffineInputOn T j) (hV : Continuous V) :
    Tendsto (fun t => affinePastPayoff f V T t+affineFuturePayoff α w j V T t)
      (𝓝[<] T) (𝓝 (q*V T+affinePastPayoff f V T T)) := by
  have hI := affine_test_integrable_past_payoff hT.le hw.rate_integrable hV
  have hPast := continuousOn_affine_ordinary_primitive hI
  have hNH : 𝓝[<] T ≤ 𝓝[Icc (0:ℝ) T] T := by
    refine le_inf nhdsWithin_le_nhds (le_principal_iff.mpr ?_)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hT)] with t ht h0
    exact ⟨(show 0<t from h0).le,(show t<T from ht).le⟩
  have hp := hPast T ⟨hT.le,le_rfl⟩
  change Tendsto (affinePastPayoff f V T) (𝓝[Icc 0 T] T) (𝓝 (affinePastPayoff f V T T)) at hp
  have hDil : Tendsto (fun t : ℝ => T-t) (𝓝[<] T) (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hc : Continuous (fun t : ℝ => T-t) := continuous_const.sub continuous_id
      have ht : Tendsto (fun t : ℝ => T-t) (𝓝 T) (𝓝 (T-T)) := hc.continuousAt
      simpa only [sub_self] using ht.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact sub_pos.mpr (show t<T from ht)
  obtain ⟨J,hJ⟩ := hj.terminal_bound
  have hh := hw.primitive hα hα' hT
  have hF := (affine_future_exponent_tendsto_terminal hα hα' hT hw.solution_measurable
    hw.solution_integrable hw.solution_nonnegative hh.1 hh.2.2 hj.measurable hJ hV).comp hDil
  have hF' : Tendsto (affineFuturePayoff α w j V T) (𝓝[<] T) (𝓝 (q*V T)) := by
    refine hF.congr (fun t => ?_)
    change (∫ y in Ioc (0:ℝ) (T-t),w (T-t-y)*affineFutureInput α (T-(T-t)) j V y) = _
    rw [show T-(T-t)=t by ring]
    rfl
  simpa only [add_comm (affinePastPayoff f V T T) (q*V T)] using (hp.mono_left hNH).add hF'

theorem affine_initial_exponent_nonnegative
    {α κ a q T : ℝ} {w f j : ℝ → ℝ}
    (hw : AffineRiccatiTestOn α κ a q T w f) (hj : AffineInputOn T j) :
    0 ≤ volterraConvolution w j T := by
  unfold volterraConvolution
  apply integral_nonneg_of_ae
  rw [← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  exact mul_nonneg (hw.solution_nonnegative _ ⟨sub_pos.mpr hr.2,by linarith [hr.1]⟩)
    (hj.nonnegative r (Ioo_subset_Ioc_self hr))

theorem affine_past_payoff_nonnegative
    {α κ a q T t : ℝ} {w f V : ℝ → ℝ}
    (ht : t < T) (hw : AffineRiccatiTestOn α κ a q T w f)
    (hV : ∀ r ∈ Ioc 0 t,0≤V r) :
    0 ≤ affinePastPayoff f V T t := by
  unfold affinePastPayoff
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  exact mul_nonneg (hw.rate_nonnegative _ ⟨sub_pos.mpr (hr.2.trans_lt ht),by linarith [hr.1]⟩)
    (hV r hr)

@[simp] theorem affine_past_payoff_zero (f V : ℝ → ℝ) (T : ℝ) :
    affinePastPayoff f V T 0 = 0 := by simp [affinePastPayoff]

@[simp] theorem affine_future_payoff_zero (α : ℝ) (w j V : ℝ → ℝ) (T : ℝ) :
    affineFuturePayoff α w j V T 0 = volterraConvolution w j T := by
  simp [affineFuturePayoff,affineFutureInput,volterraConvolution]

#print axioms affine_pathwise_exponent_split
#print axioms affine_future_payoff_nonnegative
#print axioms affine_pathwise_payoffs_left_limit

end RoughHeston
