import CanonicalMixedPulseMoments

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

namespace FractionalFixedMeshLaw

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
  {α κ σ : ℝ} {v : Option ι→ℝ} {β : Option ι→ℝ≥0→ℝ}
  (L : FractionalFixedMeshLaw T α κ σ v β)
local notation "Path" => CanonicalPath T (CoupledPhysicalState ι)

omit [Fintype ι] [DecidableEq ι] in
private theorem canonical_real_pulse_joint (i : Option ι) :
    Measurable (fun z : ℝ × Path => canonicalPhysicalVariance T i z.1.toNNReal z.2) := by
  have ht : Continuous (fun r : ℝ => canonicalEvalTime T r.toNNReal) :=
    (continuous_real_toNNReal.min continuous_const).subtype_mk _
  have he : Continuous (fun z : ℝ × Path => canonicalPathEval T z.1.toNNReal z.2) :=
    continuous_eval.comp (continuous_snd.prodMk (ht.comp continuous_fst))
  exact (((continuous_apply i).comp continuous_fst).comp he).measurable

omit [Fintype ι] [DecidableEq ι] in
private theorem canonicalVariance_min (i : Option ι) (t : ℝ≥0) :
    canonicalPhysicalVariance T i t=canonicalPhysicalVariance T i (min t T) := by
  have he : canonicalEvalTime T t = canonicalEvalTime T (min t T) :=
    Subtype.ext (min_eq_left (min_le_right t T)).symm
  funext p
  change (p (canonicalEvalTime T t)).1 i=(p (canonicalEvalTime T (min t T))).1 i
  rw [he]

private theorem physicalTime_variance_fourth_eLpNorm :
    ∃ C : ℝ≥0∞,C≠∞ ∧ ∀ i t,eLpNorm (canonicalPhysicalVariance T i t) 4 (L.law:Measure Path)≤C := by
  obtain ⟨C,hC,hq⟩ := L.varianceMoments 2
  refine ⟨C^(1/4:ℝ),ENNReal.rpow_ne_top_of_nonneg (by norm_num) hC,?_⟩
  intro i t
  rw [canonicalVariance_min i t]
  have hz : 0 ≤ᵐ[(L.law:Measure Path)] canonicalPhysicalVariance T i (min t T) := by
    filter_upwards [L.nonnegative] with p hp
    exact hp i (canonicalEvalTime T (min t T))
  have hs : (fun p => ‖canonicalPhysicalVariance T i (min t T) p‖ₑ ^ (4:ℕ)) =ᵐ[(L.law:Measure Path)]
      fun p => ENNReal.ofReal (max (canonicalPhysicalVariance T i (min t T) p) 0)^(4:ℕ) := by
    filter_upwards [hz] with p hp
    have hp' : 0≤canonicalPhysicalVariance T i (min t T) p := hp
    rw [← ofReal_norm,Real.norm_of_nonneg hp',max_eq_left hp']
  have hm : AEStronglyMeasurable (canonicalPhysicalVariance T i (min t T)) (L.law:Measure Path) :=
    (((continuous_apply i).comp continuous_fst).comp (continuous_canonicalPathEval T (min t T))).stronglyMeasurable.aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (4:ℝ≥0∞) ≠ 0)
    (by simp : (4:ℝ≥0∞) ≠ ∞) hm]
  norm_num only [ENNReal.toReal_ofNat,ENNReal.rpow_natCast,ENNReal.rpow_ofNat,one_div]
  rw [lintegral_congr_ae hs]
  exact ENNReal.rpow_le_rpow (by simpa using hq i (min t T) (min_le_right _ _)) (by positivity)

/-- The physical row has a globally continuous L² trajectory after
constant extension of the canonical process across its horizon. -/
theorem variance_real_lp2_trajectory (i : Option ι) :
    ∃ U : ℝ→Lp ℝ 2 (L.law:Measure Path), Continuous U ∧
      ∀ r,⇑(U r) =ᵐ[(L.law:Measure Path)] canonicalPhysicalVariance T i r.toNNReal := by
  let x (r : ℝ) := canonicalPhysicalVariance T i r.toNNReal
  obtain ⟨C,hC⟩ := L.variance_uniform_memLp 1
  norm_num at hC
  have h₂ (r : ℝ) : MemLp (x r) 2 (L.law:Measure Path) := by
    change MemLp (canonicalPhysicalVariance T i r.toNNReal) 2 (L.law:Measure Path)
    rw [canonicalVariance_min]
    exact (hC i _ (min_le_right _ _)).1
  obtain ⟨C₄,hC₄,h₄⟩ := L.physicalTime_variance_fourth_eLpNorm
  exact ⟨fun r => (h₂ r).toLp (x r),continuous_toLp_two_of_continuous_paths_uniform_fourth h₂
    (ae_of_all _ fun p => (canonicalPhysicalVariance_time_continuous i p).comp continuous_real_toNNReal)
    hC₄ (fun r => h₄ i r.toNNReal),fun r => (h₂ r).coeFn_toLp⟩

/-- Two distinct pulse variances have zero covariance at different
interior physical observation times. The compensated residual bracket,
ordinary deterministic resolvent and L² differentiation all use the joint
fixed-mesh law itself. -/
theorem pulse_mixed_covariance {i j : ι} (hij : i≠j)
    (hi : v (some i)=0) (hj : v (some j)=0)
    (hα : 1/2<α) (hα' : α<1) {R : ℝ→ℝ} (hR : Measurable R)
    {Rbound : ℝ} (hRb : ∀ r∈Ioc (0:ℝ) (T:ℝ),|R r|≤Rbound*fractionalK α r)
    (hRes : ∀ r∈Ioc (0:ℝ) (T:ℝ),R r=fractionalK α r-κ*volterraConvolution (fractionalK α) R r)
    {B : ℝ} (hβ : ∀ i,Measurable (β i)) (hB : ∀ i t,‖β i t‖≤B)
    {s t : ℝ≥0} (hs : 0<s) (hsT : s<T) (ht : 0<t) (htT : t<T) :
    (∫ p,canonicalPhysicalVariance T (some i) s p*canonicalPhysicalVariance T (some j) t p ∂(L.law:Measure Path)) =
      (∫ p,canonicalPhysicalVariance T (some i) s p ∂(L.law:Measure Path))*
        (∫ p,canonicalPhysicalVariance T (some j) t p ∂(L.law:Measure Path)) := by
  let μ := (L.law:Measure Path)
  let x (i : Option ι) (r : ℝ) := canonicalPhysicalVariance T i r.toNNReal
  obtain ⟨C,hC⟩ := L.variance_uniform_memLp 1
  norm_num at hC
  have hC₀ : 0≤C := (integral_nonneg fun _ => sq_nonneg _).trans (hC (some i) 0 zero_le).2
  have h₂ (i : Option ι) (r : ℝ) : MemLp (x i r) 2 μ := by
    change MemLp (canonicalPhysicalVariance T i r.toNNReal) 2 μ
    rw [canonicalVariance_min]
    exact (hC i _ (min_le_right _ _)).1
  have hbound (i : Option ι) (r : ℝ) (hr : r∈Icc (0:ℝ) (T:ℝ)) :
      (∫ p,(x i r p)^2 ∂μ)≤C :=
    (hC i _ (Real.toNNReal_le_iff_le_coe.mpr hr.2)).2
  obtain ⟨C₄,hC₄,h₄⟩ := L.physicalTime_variance_fourth_eLpNorm
  have hx (i : Option ι) : Continuous (fun r => (h₂ i r).toLp (x i r)) :=
    continuous_toLp_two_of_continuous_paths_uniform_fourth (h₂ i)
      (ae_of_all _ fun p => (canonicalPhysicalVariance_time_continuous i p).comp continuous_real_toNNReal)
      hC₄ (fun r => h₄ i r.toNNReal)
  have hprim (a b : ℝ) (ha : a∈Ioo (0:ℝ) (T:ℝ)) (hb : b∈Ioo (0:ℝ) (T:ℝ)) :=
    L.integrated_pulse_mixed_covariance hij hi hj hα hα' hR hRb hRes hβ hB
      (Ioo_subset_Icc_self ha) (Ioo_subset_Icc_self hb)
  have hs' : (s:ℝ)∈Ioo (0:ℝ) (T:ℝ) := ⟨NNReal.coe_pos.mpr hs,NNReal.coe_lt_coe.mpr hsT⟩
  have ht' : (t:ℝ)∈Ioo (0:ℝ) (T:ℝ) := ⟨NNReal.coe_pos.mpr ht,NNReal.coe_lt_coe.mpr htT⟩
  have he := zero_mixed_covariance_of_orthogonal_primitives (U := x (some i)) (V := x (some j))
    (canonical_real_pulse_joint _) (canonical_real_pulse_joint _) (h₂ _) (h₂ _)
    hC₀ hC₀ (hbound _) (hbound _) (fun r => (h₂ _ r).toLp (x _ r))
    (fun r => (h₂ _ r).toLp (x _ r)) (hx _).continuousOn (hx _).continuousOn
    (fun r _ => (h₂ _ r).coeFn_toLp) (fun r _ => (h₂ _ r).coeFn_toLp)
    (fun a ha => (hprim a t ha ht').1) (fun b hb => (hprim s b hs' hb).2.1)
    (fun a ha b hb => (hprim a b ha hb).2.2) hs' ht'
  simpa only [x,Real.toNNReal_coe] using he

end FractionalFixedMeshLaw

#print axioms FractionalFixedMeshLaw.pulse_mixed_covariance
#print axioms FractionalFixedMeshLaw.variance_real_lp2_trajectory

end RoughHeston
