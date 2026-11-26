import ClusterLpPath
import PathLpContinuityFromFourthMoments

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace RoughHeston.GirsanovPort

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {U : ℝ≥0 → Ω → ℝ}

/-- The analytic input to the inverse equation. Fixed-mesh laws supply it
through slice fourth moments, including after conditioning at a birth. -/
structure FocalPulseRegularity (P : Measure Ω) (U : ℝ≥0 → Ω → ℝ) : Prop where
  integrable : ∀ t, Integrable (U t) P
  mean_bounded : ∃ A : ℝ, ∀ t, (∫ ω,U t ω ∂P)≤A
  trajectory : ∃ v : ℝ → Lp ℝ 2 P, Continuous v ∧ ∀ s, ⇑(v s)=ᵐ[P] U s.toNNReal

theorem FocalPulseRegularity.of_dominated {D : Ω → ℝ} (hD : MemLp D 2 P)
    (hU : ∀ t, Measurable (U t)) (hc : ∀ᵐ ω ∂P,Continuous (fun t => U t ω))
    (hDU : ∀ᵐ ω ∂P, ∀ t, ‖U t ω‖≤‖D ω‖) : FocalPulseRegularity P U := by
  obtain ⟨hi,hM,hv⟩ := cluster_continuous_L2_path_of_dominated hD hU hc hDU
  exact ⟨hi,⟨_,hM⟩,hv⟩

theorem FocalPulseRegularity.mean_continuous (h : FocalPulseRegularity P U) :
    Continuous fun t => ∫ ω,U t ω ∂P := by
  obtain ⟨v,hv,hRep⟩ := h.trajectory
  let e : Lp ℝ 2 P := (memLp_const (1:ℝ)).toLp (fun _ : Ω => (1:ℝ))
  have he : ⇑e =ᵐ[P] fun _ => (1:ℝ) := (memLp_const (1:ℝ)).coeFn_toLp
  have hh : Continuous (fun t : ℝ≥0 => inner ℝ e (v (t:ℝ))) := continuous_const.inner (hv.comp continuous_subtype_val)
  refine hh.congr fun t => ?_
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [he,hRep (t:ℝ)] with ω h₁ h₂
  simp only [Real.toNNReal_coe] at h₂
  rw [h₁,h₂];simp [RCLike.inner_apply]

theorem FocalPulseRegularity.of_uniform_fourth
    (hm : ∀ t, Measurable (U t)) (hpath : ∀ᵐ ω ∂P, Continuous (fun t => U t ω))
    {C : ℝ≥0∞} (hC : C ≠ ⊤) (hbound : ∀ t, eLpNorm (U t) 4 P ≤ C) :
    FocalPulseRegularity P U := by
  have h₄ (t : ℝ≥0) : MemLp (U t) 4 P := (hbound t).trans_lt (lt_top_iff_ne_top.mpr hC)
  have h₂ (t : ℝ≥0) : MemLp (U t) 2 P := (h₄ t).mono_exponent (by norm_num)
  have hInt (t : ℝ≥0) := (h₂ t).integrable one_le_two
  refine ⟨hInt,⟨C.toReal,fun t => ?_⟩,?_⟩
  · have hg := (eLpNorm_le_eLpNorm_of_exponent_le (μ:=P) (f:=U t) (by norm_num : (1:ℝ≥0∞)≤4)).trans (hbound t)
    rw [eLpNorm_one_eq_lintegral_enorm (hm t).aestronglyMeasurable] at hg
    exact (le_abs_self _).trans ((norm_integral_le_lintegral_norm (μ:=P) (U t)).trans (ENNReal.toReal_mono hC (by simpa only [ofReal_norm] using hg)))
  · let v (s : ℝ) := (h₂ s.toNNReal).toLp (U s.toNNReal)
    exact ⟨v,(continuous_toLp_two_of_continuous_paths_uniform_fourth h₂ hpath hC hbound).comp continuous_real_toNNReal,
      fun s => (h₂ s.toNNReal).coeFn_toLp⟩

#print axioms FocalPulseRegularity.of_dominated
#print axioms FocalPulseRegularity.mean_continuous
#print axioms FocalPulseRegularity.of_uniform_fourth

end RoughHeston.GirsanovPort
