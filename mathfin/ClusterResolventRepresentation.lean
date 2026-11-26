import HestonAffineTransformIdentity
import FractionalPowerTriangle
import VolterraMomentBound

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Interval Topology

namespace RoughHeston
namespace GirsanovPort

private theorem fractionalK_nonneg_at {α : ℝ} (hα : 0 < α) (s : ℝ) :
    0 ≤ fractionalK α s := by
  unfold fractionalK
  split
  · exact le_rfl
  · rename_i hs
    exact div_nonneg (Real.rpow_nonneg (le_of_lt (lt_of_not_ge hs)) _) (Real.Gamma_pos_of_pos hα).le

private theorem reflected_weight_on_bounded [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℝ} (hT : 0 ≤ T) {k : ℝ → ℝ} {g : ℝ → E}
    (hk : Measurable k) (hI : IntegrableOn k (Ioc 0 T))
    (hg : StronglyMeasurable g) {c : ℝ} (hc : ∀ u ∈ Icc 0 T, ‖g u‖ ≤ c) :
    IntegrableOn (fun u => k (T-u) • g u) (Ioc (0 : ℝ) T) := by
  have hki := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 hI
  have hcomp : IntervalIntegrable (fun u => k (T-u)) volume 0 T := by
    simpa only [sub_zero, sub_self] using (hki.comp_sub_left T).symm
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 hcomp
  have hmk : Measurable (fun u => k (T-u)) := hk.comp (measurable_const.sub measurable_id)
  have hm : AEStronglyMeasurable (fun u => k (T-u) • g u) (volume.restrict (Ioc 0 T)) :=
    (hmk.stronglyMeasurable.smul hg).aestronglyMeasurable
  refine (hi.norm.mul_const c).mono' hm ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hc u (Ioc_subset_Icc_self hu)) (norm_nonneg _)

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 m} {B U : ℝ≥0 → Ω → ℝ}

/-- The second-kind resolvent representation follows from the original
fixed-horizon cluster equation in L². The weighting identity is the
linear specialization of the checked affine stochastic Fubini identity. -/
theorem cluster_resolvent_representation_of_fractional_equation
    {α κ σ : ℝ} (hα : 1/2 < α) (hα' : α ≤ 1) (t : ℝ≥0) (ht : 0 < t)
    (hB₂ : ∀ r, MemLp (B r) 2 P)
    (hU : IsStronglyPredictable F U) (hU₀ : ∀ s ω, 0 ≤ U s ω)
    (hUi : ∀ s, Integrable (U s) P) {C : ℝ} (hMean : ∀ s, (∫ ω, U s ω ∂P) ≤ C)
    {R : ℝ → ℝ} (hR : Measurable R)
    (hLoc : ∀ s ∈ Ioc 0 (t : ℝ), |R s| ≤ 2 * fractionalK α s)
    (hRes : ∀ s ∈ Ioc 0 (t : ℝ), R s =
      fractionalK α s - κ * volterraConvolution (fractionalK α) R s)
    (v j : ℝ → Lp ℝ 2 P)
    (hvM : StronglyMeasurable v) (hvC : ContinuousOn v (Icc 0 (t : ℝ)))
    (hjM : StronglyMeasurable j) {J : ℝ} (hjB : ∀ s ∈ Icc 0 (t : ℝ), ‖j s‖ ≤ J)
    (hEq : ∀ s ∈ Icc 0 (t : ℝ), v s =
      volterraSmulConvolution (fractionalK α) (fun u => j u - κ • v u) s +
        σ • fixedHestonConvolutionLp (T := t) hα hB₂ hU hU₀ hUi hMean s) :
    ∃ W : Lp ℝ 2 (jointPredictableMeasure F P t),
      (⇑W =ᵐ[jointPredictableMeasure F P t] fun p =>
        R ((t : ℝ) - (p.1 : ℝ)) * Real.sqrt (U p.1 p.2)) ∧
      v (t : ℝ) = volterraSmulConvolution R j (t : ℝ) + σ • jointItoIntegralCLM t hB₂ W := by
  let T := (t : ℝ)
  let ν := volume.restrict (Ioc (0 : ℝ) T)
  let K := fractionalK α
  let f (u : ℝ) := -κ * R u
  let d (u : ℝ) := j u - κ • v u
  let D := volterraSmulConvolution K d
  let S := fixedHestonConvolutionLp (T := t) hα hB₂ hU hU₀ hUi hMean
  have hT : 0 ≤ T := NNReal.coe_nonneg _
  have hTpos : 0 < T := by exact_mod_cast ht
  have hαp : 0 < α := by linarith
  have hKmeas : Measurable K := fractionalK_measurable _
  have hKi : IntegrableOn K (Ioc 0 T) := fractionalK_integrableOn_Ioc hαp _
  have hRi : IntegrableOn R (Ioc 0 T) := by
    refine (hKi.const_mul 2).mono' hR.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    simpa only [Real.norm_eq_abs] using hLoc s hs
  have hKsq : IntegrableOn (fun s => K s ^ 2) (Ioc 0 T) := by
    have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1
      (intervalIntegrable_fractionalK_add_sq hα hT)
    refine hi.mono' (hKmeas.pow_const 2).aestronglyMeasurable ?_
    exact ae_of_all _ fun s => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact le_add_of_nonneg_left (fractionalK_nonneg_at hαp _)
  have hRsqI : IntegrableOn (fun s => R s ^ 2) (Ioc 0 T) := by
    refine (hKsq.const_mul 4).mono' (hR.pow_const 2).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
    have h := pow_le_pow_left₀ (abs_nonneg _) (hLoc s hs) 2
    nlinarith
  have hfi : IntegrableOn f (Ioc 0 T) := hRi.const_mul _
  have hfm : Measurable f := hR.const_mul _
  have hfB (s : ℝ) (hs : s ∈ Ioc 0 T) : |f s| ≤ (2 * |κ|) * K s := by
    dsimp [f]
    rw [abs_mul, abs_neg]
    exact (mul_le_mul_of_nonneg_left (hLoc s hs) (abs_nonneg _)).trans_eq (by ring)
  have hvB : ∃ L, ∀ s ∈ Icc (0 : ℝ) T, ‖v s‖ ≤ L := by
    obtain ⟨L, hL⟩ := isCompact_Icc.bddAbove_image hvC.norm
    exact ⟨L, fun s hs => hL ⟨s, hs, rfl⟩⟩
  obtain ⟨L, hL⟩ := hvB
  have hdM : StronglyMeasurable d := by
    change StronglyMeasurable (j - κ • v)
    exact hjM.sub (hvM.const_smul _)
  have hdB (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) : ‖d s‖ ≤ J + |κ| * L := by
    exact (norm_sub_le _ _).trans (add_le_add (hjB s hs)
      (by rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hL s hs) (abs_nonneg _)))
  have hSc : Continuous S := fixedHestonConvolutionLp_continuous hα hα' hB₂ hU hU₀ hUi hMean
  obtain ⟨J', hJ'⟩ := isCompact_Icc.bddAbove_image hSc.norm.continuousOn
  have hSB (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) : ‖S s‖ ≤ J' := hJ' ⟨s, hs, rfl⟩
  have hFbound (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) : ‖v s - σ • S s‖ ≤ L + |σ| * J' := by
    exact (norm_sub_le _ _).trans (add_le_add (hL s hs)
      (by rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hSB s hs) (abs_nonneg _)))
  have hw (s : ℝ) (hs : s ∈ Ioc 0 T) : R s =
      (1 : ℝ) * K s + volterraConvolution K f s := by
    rw [one_mul, hRes s hs]
    have he : volterraConvolution K f s = -κ * volterraConvolution K R s := by
      unfold volterraConvolution
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ fun u => by dsimp [f]; ring
    rw [he]
    ring
  have hRot (s : ℝ) (hs : s ∈ Ioc 0 T) : volterraConvolution f K s = R s - K s := by
    rw [volterraConvolution_comm_at hs.1.le]
    linarith [hw s hs]
  have htri : Integrable (fun z : ℝ × ℝ => (f (T-z.1) * K (z.1-z.2)) • d z.2) (ν.prod ν) := by
    refine fractional_power_triangle_smul_integrable hαp hTpos hfm hdM
      ({()} : Finset Unit) ({()} : Finset Unit) (fun _ => α) (fun _ => 2 * |κ|)
      (fun _ => 1) (fun _ => J + |κ| * L)
      (fun _ _ => hαp) (fun _ _ => by norm_num) ?_ ?_
    · intro s hs
      simpa only [Finset.sum_singleton] using hfB s hs
    · intro s hs
      have hK1 : fractionalK 1 s = 1 := by simp [fractionalK, not_le_of_gt hs.1, Real.Gamma_one]
      simpa only [Finset.sum_singleton, hK1, mul_one] using hdB s (Ioc_subset_Icc_self hs)
  have hKd : Integrable (fun s => K (T-s) • d s) ν :=
    reflected_weight_on_bounded hT hKmeas hKi hdM hdB
  have hrd : Integrable (fun s => volterraConvolution f K (T-s) • d s) ν := by
    refine (reflected_weight_on_bounded hT (hR.sub hKmeas) (hRi.sub hKi) hdM hdB).congr ?_
    have hae : ∀ᵐ s ∂ν, s ∈ Ioo 0 T := by
      rw [show ν = volume.restrict (Ioo (0 : ℝ) T) from Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm]
      exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [hae] with s hs
    have hmem : T-s ∈ Ioc (0 : ℝ) T := ⟨sub_pos.mpr hs.2, sub_le_self _ hs.1.le⟩
    change (R (T-s)-K (T-s)) • d s = _
    rw [hRot _ hmem]
  have hfd : Integrable (fun s => f (T-s) • D s) ν := by
    have hm : StronglyMeasurable (fun s => v s - σ • S s) := by
      change StronglyMeasurable (v - σ • S)
      exact hvM.sub (hSc.stronglyMeasurable.const_smul _)
    refine (reflected_weight_on_bounded hT hfm hfi hm hFbound).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have he : v s - σ • S s = D s := by rw [hEq s (Ioc_subset_Icc_self hs), add_sub_cancel_right]
    rw [he]
  have hfS : Integrable (fun s => f (T-s) • S s) ν :=
    reflected_weight_on_bounded hT hfm hfi hSc.stronglyMeasurable hSB
  have hwj : Integrable (fun s => R (T-s) • j s) ν :=
    reflected_weight_on_bounded hT hR hRi hjM hjB
  have hwv : Integrable (fun s => R (T-s) • v s) ν :=
    reflected_weight_on_bounded hT hR hRi hvM hL
  have hwwv : Integrable (fun s => R (T-s) ^ 2 • v s) ν :=
    reflected_weight_on_bounded hT (hR.pow_const 2) hRsqI hvM hL
  have hgv : Integrable (fun s => (0 : ℝ) • v s) ν := by simp
  obtain ⟨W, hW, h⟩ := heston_affineTransform_identity (σ := σ) (κ := κ) (a := 0) (q := 1)
    hα hα' t ht hB₂ hU hU₀ hUi hMean (fun _ => 0) R v j
    (by simpa only [f, neg_mul, zero_sub, zero_mul, sub_zero] using hfm)
    (by simpa only [f, neg_mul, zero_sub, zero_mul, sub_zero] using hfi)
    (by simpa only [f, zero_sub, zero_mul, sub_zero, neg_mul] using hw)
    (fun s hs => hEq s (Ioc_subset_Icc_self hs))
    (by simpa only [f, zero_sub, zero_mul, sub_zero, neg_mul] using htri)
    hKd
    (by simpa only [f, zero_sub, zero_mul, sub_zero, neg_mul] using hrd)
    (by simpa only [f, zero_sub, zero_mul, sub_zero, neg_mul] using hfd)
    (by simpa only [f, zero_sub, zero_mul, sub_zero, neg_mul] using hfS)
    hwj hwv hwwv hgv
  refine ⟨W, hW, ?_⟩
  simpa only [one_smul, zero_smul, add_zero, volterraSmulConvolution, integral_zero] using h

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.cluster_resolvent_representation_of_fractional_equation
