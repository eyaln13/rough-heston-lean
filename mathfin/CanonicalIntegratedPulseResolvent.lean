import IntegratedFractionalResolvent
import CanonicalClusterMixed
import FractionalFixedMeshLaw

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
local notation "Path" => CanonicalPath T (CoupledPhysicalState ι)

noncomputable def canonicalVariancePrimitive (T : ℝ≥0) (i : Option ι) (s : ℝ)
    (p : CanonicalPath T (CoupledPhysicalState ι)) : ℝ :=
  ∫ r in (0:ℝ)..s,canonicalPhysicalVariance T i r.toNNReal p

noncomputable def physicalImmigrationPrimitive (β : ℝ≥0→ℝ) (s : ℝ) : ℝ :=
  ∫ r in (0:ℝ)..s,β r.toNNReal

theorem continuous_physicalImmigrationPrimitive {β : ℝ≥0→ℝ} {B : ℝ}
    (hβ : Measurable β) (hB : ∀ t,‖β t‖≤B) :
    Continuous (physicalImmigrationPrimitive β) := by
  have hI (a b : ℝ) : IntegrableOn (fun r => β r.toNNReal) (Ioc a b) := by
    refine (integrableOn_const (C := B)
      (by simp [Real.volume_Ioc] : volume (Ioc a b)≠∞)).mono'
        (hβ.comp continuous_real_toNNReal.measurable).aestronglyMeasurable ?_
    exact ae_of_all _ fun r => hB r.toNNReal
  exact intervalIntegral.continuous_primitive (fun a b => ⟨hI a b,hI b a⟩) 0

/-- The integrated pulse solves the second-kind resolvent representation on
the physical time line. The only random drive is its original residual. -/
theorem FractionalFixedMeshLaw.canonicalPulse_integrated_resolvent
    {α κ σ : ℝ} {v : Option ι→ℝ} {β : Option ι→ℝ≥0→ℝ}
    (L : FractionalFixedMeshLaw T α κ σ v β) {i : ι} (hv : v (some i)=0)
    (hα : 0<α) (hα' : α<1) {R : ℝ→ℝ} (hR : Measurable R)
    {Rbound : ℝ} (hRb : ∀ r∈Ioc (0:ℝ) (T:ℝ), |R r|≤Rbound*fractionalK α r)
    (hRes : ∀ r∈Ioc (0:ℝ) (T:ℝ),R r=fractionalK α r-κ*volterraConvolution (fractionalK α) R r)
    {B : ℝ} (hβ : Measurable (β (some i))) (hB : ∀ t,‖β (some i) t‖≤B) :
    ∀ᵐ p ∂(L.law:Measure Path),∀ s∈Icc (0:ℝ) (T:ℝ),
      canonicalVariancePrimitive T (some i) s p =
        volterraConvolution R (physicalImmigrationPrimitive (β (some i))) s +
        volterraConvolution R (fun r => canonicalPhysicalResidual T (some i) r.toNNReal p) s := by
  filter_upwards [L.inverse (some i)] with p hp s hs
  rcases eq_or_lt_of_le hs.1 with hs0|hs0
  · subst s
    simp [canonicalVariancePrimitive,volterraConvolution]
  let A (r : ℝ) := canonicalVariancePrimitive T (some i) r p
  let M (r : ℝ) := canonicalPhysicalResidual T (some i) r.toNNReal p
  let H := physicalImmigrationPrimitive (β (some i))
  let U (r : ℝ) := canonicalPhysicalVariance T (some i) r.toNNReal p
  have hU : Continuous U := (canonicalPhysicalVariance_time_continuous (some i) p).comp continuous_real_toNNReal
  have hA : Continuous A :=
    intervalIntegral.continuous_primitive (fun a b => hU.intervalIntegrable a b) 0
  have hM : Continuous M := (canonicalPhysicalResidual_time_continuous (some i) p).comp continuous_real_toNNReal
  have hH : Continuous H := continuous_physicalImmigrationPrimitive hβ hB
  have hD (r : ℝ) (hr : r∈Ioc (0:ℝ) s) :
      volterraConvolution (fractionalL α) U r=M r+H r-κ*A r := by
    have ht := hp r.toNNReal (Real.toNNReal_le_iff_le_coe.mpr (hr.2.trans hs.2))
    rw [Real.coe_toNNReal _ hr.1.le] at ht
    have hb : IntervalIntegrable (fun u => β (some i) u.toNNReal) volume 0 r := by
      refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hr.1.le).2 ?_
      refine (integrableOn_const (C := B)
        (by simp [Real.volume_Ioc] : volume (Ioc (0:ℝ) r)≠∞)).mono'
          (hβ.comp continuous_real_toNNReal.measurable).aestronglyMeasurable ?_
      exact ae_of_all _ fun u => hB u.toNNReal
    simp only [hv,sub_zero] at ht
    rw [intervalIntegral.integral_sub hb ((hU.intervalIntegrable 0 r).const_mul κ),
      intervalIntegral.integral_const_mul] at ht
    change volterraConvolution (fractionalL α) U r = M r+(H r-κ*A r) at ht
    linarith only [ht]
  have hEq : EqOn A (volterraConvolution (fractionalK α) (fun r => (M r+H r)-κ*A r)) (Ioc 0 s) := by
    intro t ht
    change (∫ r in (0:ℝ)..t,U r)=_
    rw [intervalIntegral.integral_of_le ht.1.le]
    exact fractional_inverse_recovers_primitive hα hα' ht.1 hU
      (fun r hr => hD r ⟨hr.1,hr.2.trans ht.2⟩)
  have hsol := resolve_integrated_fractional_equation hα hs0 hR hA (hM.add hH)
    (fun r hr => hRb r ⟨hr.1,hr.2.trans hs.2⟩) (fun r hr => hRes r ⟨hr.1,hr.2.trans hs.2⟩) hEq
  change A s = volterraConvolution R H s+volterraConvolution R M s
  rw [hsol]
  have hRi : IntegrableOn (fun u => R (s-u)) (Ioc 0 s) := by
    have hi : IntegrableOn R (Ioc 0 s) := by
      refine ((fractionalK_integrableOn_Ioc hα s).const_mul Rbound).mono'
        hR.aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      simpa only [Real.norm_eq_abs] using hRb r ⟨hr.1,hr.2.trans hs.2⟩
    have hj := ((intervalIntegrable_iff_integrableOn_Ioc_of_le hs.1).2 hi).comp_sub_left s
    simpa only [sub_zero,sub_self] using hj.2
  have hW (f : ℝ→ℝ) (hf : Continuous f) :
      IntegrableOn (fun u => R (s-u)*f u) (Ioc 0 s) := by
    obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hf.continuousOn (s := Icc (0:ℝ) s))
    refine (hRi.norm.mul_const C).mono'
      (((hR.comp (measurable_const.sub measurable_id)).mul hf.measurable).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC r (Ioc_subset_Icc_self hr)) (norm_nonneg _)
  unfold volterraConvolution
  simp only [Pi.add_apply]
  simp_rw [mul_add]
  rw [integral_add (hW M hM) (hW H hH),add_comm]

#print axioms FractionalFixedMeshLaw.canonicalPulse_integrated_resolvent

end RoughHeston
