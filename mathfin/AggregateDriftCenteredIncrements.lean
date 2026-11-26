import HestonKernelShiftWeights
import AggregateFixedMeshForward
import WeightedDriftPowerMoment

/-! Mean-reversion increments of the actual fractional aggregate law
are controlled by the L¹ shift of the kernel and uniform variance moments. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston.GirsanovPort

set_option maxHeartbeats 1400000

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {T : ℝ≥0} {B U : ℝ≥0 → Ω → ℝ}

private theorem integrable_shifted_hestonKernel_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {T t α : ℝ} (hα : 0 < α) (ht : 0 ≤ t) (htT : t ≤ T)
    {g : ℝ → E} (hg : StronglyMeasurable g) (hgc : ContinuousOn g (Icc 0 T)) :
    IntegrableOn (fun r => hestonKernel α (t-r) • g r) (Ioc 0 T) := by
  have hK : IntegrableOn (fun r => hestonKernel α (t-r)) (Ioc 0 T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (ht.trans htT)).1
      (intervalIntegrable_causal_hestonKernel_translate ht htT (f := id) rfl
        (hestonKernel_intervalIntegrable_nonneg hα le_rfl ht))
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hgc
  refine (hK.norm.mul_const D).mono' (hK.aestronglyMeasurable.smul hg.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hD r (Ioc_subset_Icc_self hr)) (norm_nonneg _)

/-- The L² drift increment is represented by a single time integral
using the true weight difference on the full interval. -/
theorem forward_drift_increment_representative
    {α κ σ : ℝ} (hα : 1/2 < α) (hB₂ : ∀ t, MemLp (B t) 2 P) {D : ℝ → ℝ}
    (L : CenteredHestonRowData P F T α κ σ hα B U hB₂ D)
    {s t : ℝ} (hs : s ∈ Icc 0 (T:ℝ)) (ht : t ∈ Icc 0 (T:ℝ)) :
    let g := fun r => (-κ:ℝ) • L.pathLp r
    let G := volterraSmulConvolution (hestonKernel α) g
    let k := fun r => hestonKernel α (t-r)-hestonKernel α (s-r)
    ⇑(G t-G s) =ᵐ[P] fun ω => ∫ r in Ioc (0:ℝ) (T:ℝ), k r*((-κ)*U r.toNNReal ω) := by
  intro g G k
  have hα₀ : 0 < α := by linarith
  have hg : StronglyMeasurable g := by
    change StronglyMeasurable ((-κ:ℝ) • L.pathLp)
    exact L.continuous_pathLp.stronglyMeasurable.const_smul (-κ)
  have hgc : ContinuousOn g (Icc 0 (T:ℝ)) := by
    change ContinuousOn ((-κ:ℝ) • L.pathLp) _
    exact L.continuous_pathLp.continuousOn.const_smul (-κ)
  have hΓ (u : ℝ) (hu : u ∈ Icc 0 (T:ℝ)) :
      G u = ∫ r in Ioc (0:ℝ) (T:ℝ), hestonKernel α (u-r) • g r := by
    unfold G volterraSmulConvolution
    exact (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (μ := volume) measurableSet_Ioc
      (Ioc_subset_Ioc_right hu.2) (fun r hr => by
        have hr' : u ≤ r := by by_contra! h; exact hr.2 ⟨hr.1.1,h.le⟩
        rw [hestonKernel, if_neg (not_lt_of_ge (sub_nonpos.mpr hr')), zero_smul])).symm
  have hi (u : ℝ) (hu : u ∈ Icc 0 (T:ℝ)) :
      IntegrableOn (fun r => hestonKernel α (u-r) • g r) (Ioc 0 (T:ℝ)) :=
    integrable_shifted_hestonKernel_smul hα₀ hu.1 hu.2 hg hgc
  have hki : IntegrableOn (fun r => k r • g r) (Ioc 0 (T:ℝ)) := by
    have hdiff : (fun r => k r • g r) =
        (fun r => hestonKernel α (t-r) • g r)-(fun r => hestonKernel α (s-r) • g r) := by
      funext r
      exact sub_smul _ _ _
    rw [hdiff]
    exact (hi t ht).sub (hi s hs)
  have hEq : G t-G s = ∫ r in Ioc (0:ℝ) (T:ℝ), k r • g r := by
    simp only [k, sub_smul, hΓ _ hs, hΓ _ ht]
    exact (integral_sub (hi t ht) (hi s hs)).symm
  have hkm : Measurable k := ((hestonKernel_measurable α).comp (measurable_const.sub measurable_id)).sub
    ((hestonKernel_measurable α).comp (measurable_const.sub measurable_id))
  let Ureal := fun (r : ℝ) ω => U r.toNNReal ω
  have hUm : Measurable (Function.uncurry Ureal) :=
    (L.predictable.mono F.predictable_le_prod).measurable.comp
      (continuous_real_toNNReal.measurable.prodMap (measurable_id : Measurable (@id Ω)))
  have hRep (r : ℝ) : ⇑(g r) =ᵐ[P] fun ω => (-κ)*Ureal r ω := by
    filter_upwards [Lp.coeFn_smul (-κ) (L.pathLp r), L.rep r] with ω ha hb
    change ((-κ:ℝ) • L.pathLp r) ω = _
    rw [ha, Pi.smul_apply, smul_eq_mul, hb]
  rw [hEq]
  exact coeFn_integral_weighted_L2_path_ae hkm (hUm.const_mul (-κ)) hki hRep

/-- A uniform q-th moment of the variance controls its mean-reversion
increment with the stronger time power αq. -/
theorem forward_drift_increment_lintegral_bound
    {α κ σ : ℝ} (hα : 1/2 < α) (hα' : α ≤ 1) (hB₂ : ∀ t, MemLp (B t) 2 P) {D : ℝ → ℝ}
    (L : CenteredHestonRowData P F T α κ σ hα B U hB₂ D)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ (T:ℝ))
    (q : ℕ) (hq : 1 ≤ q) {C : ℝ} (hC : 0 ≤ C)
    (hMom : ∀ r ≤ T, Integrable (fun ω => U r ω^q) P ∧ (∫ ω, U r ω^q ∂P) ≤ C) :
    let G := volterraSmulConvolution (hestonKernel α) (fun r => (-κ:ℝ) • L.pathLp r)
    (∫⁻ ω, ‖(G t-G s) ω‖ₑ^q ∂P) ≤
      ENNReal.ofReal ((2/(Real.Gamma α*α))*(t-s)^α)^q * ENNReal.ofReal (‖κ‖^q*C) := by
  intro G
  let k (r : ℝ) := hestonKernel α (t-r)-hestonKernel α (s-r)
  let V (r : ℝ) (ω : Ω) := (-κ)*U r.toNNReal ω
  let ν := volume.restrict (Ioc (0:ℝ) (T:ℝ))
  have hkm : Measurable k := ((hestonKernel_measurable α).comp (measurable_const.sub measurable_id)).sub
    ((hestonKernel_measurable α).comp (measurable_const.sub measurable_id))
  have hki : Integrable k ν := by
    have h := (intervalIntegrable_hestonKernelDifference hα hs (hs.trans hst) (hst.trans ht) ht).2
    exact ((integrable_norm_iff hkm.aestronglyMeasurable).mp ((intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).1 h))
  have hVm : Measurable (Function.uncurry V) := ((L.predictable.mono F.predictable_le_prod).measurable.comp
      (continuous_real_toNNReal.measurable.prodMap (measurable_id : Measurable (@id Ω)))).const_mul (-κ)
  have hVi : ∀ᵐ ω ∂P, Integrable (fun r => k r*V r ω) ν := by
    apply Eventually.of_forall
    intro ω
    have hc : Continuous (fun r => V r ω) := continuous_const.mul
      ((L.continuous_paths ω).comp continuous_real_toNNReal)
    obtain ⟨A,hA⟩ := (isCompact_Icc (a := (0:ℝ)) (b := (T:ℝ))).exists_bound_of_continuousOn hc.continuousOn
    refine (hki.norm.mul_const A).mono' (hki.aestronglyMeasurable.mul hc.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc (μ := volume) (s := Ioc (0:ℝ) (T:ℝ))] with r hr
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hA r (Ioc_subset_Icc_self hr)) (norm_nonneg _)
  have hVq : ∀ᵐ r ∂ν, (∫⁻ ω, ‖V r ω‖ₑ^q ∂P) ≤ ENNReal.ofReal (‖κ‖^q*C) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc (μ := volume) (s := Ioc (0:ℝ) (T:ℝ))] with r hr
    have hrT : r.toNNReal ≤ T := NNReal.coe_le_coe.mp ((Real.coe_toNNReal r hr.1.le).trans_le hr.2)
    obtain ⟨hi,hp⟩ := hMom r.toNNReal hrT
    have hNorm (ω : Ω) : ‖V r ω‖^q = ‖κ‖^q*(U r.toNNReal ω)^q := by
      simp only [V,norm_mul,norm_neg,Real.norm_of_nonneg (L.nonnegative _ _),mul_pow]
    have hInt : Integrable (fun ω => ‖V r ω‖^q) P := (hi.const_mul _).congr (ae_of_all _ fun ω => (hNorm ω).symm)
    have hEq : (∫⁻ ω, ‖V r ω‖ₑ^q ∂P) = ENNReal.ofReal (‖κ‖^q*∫ ω, U r.toNNReal ω^q ∂P) := by
      rw [← integral_const_mul]
      calc
        _ = ∫⁻ ω, ENNReal.ofReal (‖V r ω‖^q) ∂P := lintegral_congr fun ω => by
          rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
        _ = ENNReal.ofReal (∫ ω, ‖V r ω‖^q ∂P) :=
          (ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ fun ω => pow_nonneg (norm_nonneg _) _)).symm
        _ = _ := congrArg ENNReal.ofReal (integral_congr_ae (ae_of_all _ hNorm))
    rw [hEq]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hp (by positivity))
  have hRep := forward_drift_increment_representative hα hB₂ L ⟨hs,hst.trans ht⟩ ⟨hs.trans hst,ht⟩
  have hEq : (∫⁻ ω, ‖(G t-G s) ω‖ₑ^q ∂P) = ∫⁻ ω, ‖∫ r, k r*V r ω ∂ν‖ₑ^q ∂P := by
    apply lintegral_congr_ae
    filter_upwards [hRep] with ω hω
    change (G t-G s) ω = _ at hω
    rw [hω]
  rw [hEq]
  have hBound := lintegral_weighted_drift_power_le hkm hki hVm hVi q hq hVq
  have hmass : (∫ r, ‖k r‖ ∂ν) ≤ (2/(Real.Gamma α*α))*(t-s)^α := by
    rw [← intervalIntegral.integral_of_le T.coe_nonneg]
    exact (hestonKernel_lower_shift_energy_mass hα hα' hs hst ht).2
  exact hBound.trans (mul_left_mono (pow_le_pow_left' (ENNReal.ofReal_le_ofReal hmass) q))

#print axioms RoughHeston.GirsanovPort.forward_drift_increment_representative
#print axioms RoughHeston.GirsanovPort.forward_drift_increment_lintegral_bound

end RoughHeston.GirsanovPort
