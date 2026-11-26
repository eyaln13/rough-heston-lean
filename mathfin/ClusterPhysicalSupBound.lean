import ClusterCanonicalSupBound
import CanonicalMartingalePushforward
import FractionalSmoothJointTightnessInput

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston

/-- A measurable supremum on the physical time block. The constant is
chosen before the law, the horizon and the coefficient of the increments. -/
theorem physical_sup_power_of_increments {n : ℕ} (hn : 0<n) {γ : ℝ} (hγ : 1<γ)
    : ∃ K : ℝ, 0≤K ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {T : ℝ≥0} (_ : 0<T) (μ : Measure Ω)
      (N : ℝ≥0 → Ω → ℝ) (_ : ∀ t, Measurable (N t))
      (_ : ∀ ω, ContinuousOn (fun t => N t ω) (Icc 0 T))
      (_ : ∀ᵐ ω ∂μ, N 0 ω=0) (C : ℝ) (_ : 0≤C),
      (∀ a b : ℝ≥0, a<b → b≤T →
        Integrable (fun ω => ‖N b ω-N a ω‖^n) μ ∧
        (∫ ω, ‖N b ω-N a ω‖^n ∂μ) ≤ C*((b:ℝ)-(a:ℝ))^γ) →
      ∃ W : Ω → ℝ, Measurable W ∧
        (∀ G : MeasurableSpace Ω, (∀ t≤T, Measurable[G] (N t)) → Measurable[G] W) ∧
        (∀ ω, 0≤W ω) ∧
        (∀ t≤T, ∀ ω, ‖N t ω‖≤W ω) ∧
        Integrable (fun ω => W ω^n) μ ∧ (∫ ω, W ω^n ∂μ) ≤ K*C*(T:ℝ)^γ := by
  obtain ⟨K,hK,hsup⟩ := canonical_sup_power_of_increments hn hγ
  refine ⟨K,hK,?_⟩
  intro Ω m T hT μ N hNm hNc hN0 C hC hinc
  let φ (ω : Ω) : CanonicalPath T (ℝ × ℝ) :=
    ⟨fun t => (N t.val ω,0),(continuousOn_iff_continuous_domRestrict.mp (hNc ω)).prodMk continuous_const⟩
  have hm : Measurable φ := measurable_canonicalPath_of_evaluations
    fun t => (hNm t.val).prodMk measurable_const
  let ν := Measure.map φ μ
  have hzero : ∀ᵐ f ∂ν, f (canonicalEvalTime T 0)=0 := by
    apply (ae_map_iff hm.aemeasurable (measurableSet_eq_fun (continuous_canonicalPathEval (E := ℝ × ℝ) T 0).measurable measurable_const)).mpr
    filter_upwards [hN0] with ω h
    change (N (min 0 T) ω, (0:ℝ)) = 0
    simp [h]
  have horder (s t : CanonicalPathTime T) (hle : s.val≤t.val) :
      (∫⁻ f, edist (f s) (f t)^(n:ℝ) ∂ν) ≤ ENNReal.ofReal C*edist s t^γ := by
    rcases eq_or_lt_of_le hle with he|hlt
    · have he' : s=t := Subtype.ext he
      simp [he', ENNReal.zero_rpow_of_pos (show 0<(n:ℝ) by exact_mod_cast hn),
        ENNReal.zero_rpow_of_pos (show 0<γ by linarith)]
    obtain ⟨hi,hE⟩ := hinc s.val t.val hlt t.property.2
    change (∫⁻ f : CanonicalPath T (ℝ × ℝ), edist (f s) (f t)^(n:ℝ) ∂μ.map φ) ≤ _
    rw [lintegral_map (by fun_prop) hm]
    have heq (ω : Ω) : edist (φ ω s) (φ ω t)^(n:ℝ) =
        ENNReal.ofReal (‖N t.val ω-N s.val ω‖^n) := by
      change edist (N s.val ω,(0:ℝ)) (N t.val ω,0)^(n:ℝ) = _
      rw [edist_dist,Prod.dist_eq]
      simp only [dist_self,max_eq_left dist_nonneg,ENNReal.rpow_natCast]
      rw [dist_comm,dist_eq_norm,ENNReal.ofReal_pow (norm_nonneg _)]
    simp_rw [heq]
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun ω => pow_nonneg (norm_nonneg _) _),
      edist_canonicalPathTime_eq_ofReal hle,ENNReal.ofReal_rpow_of_nonneg
        (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hle)) (by linarith),
      ← ENNReal.ofReal_mul hC]
    exact ENNReal.ofReal_le_ofReal hE
  have hall (s t : CanonicalPathTime T) :
      (∫⁻ f, edist (f s) (f t)^(n:ℝ) ∂ν) ≤ ENNReal.ofReal C*edist s t^γ := by
    rcases le_total s.val t.val with h|h
    · exact horder s t h
    · simpa only [edist_comm] using horder t s h
  obtain ⟨hi,he⟩ := hsup T hT ν _ ENNReal.ofReal_ne_top hzero hall
  refine ⟨fun ω => ‖φ ω‖,hm.norm,?_,fun ω => norm_nonneg _,?_,?_,?_⟩
  · intro G hG
    exact (measurable_canonicalPath_of_evaluations (m := G) (φ := φ) fun t =>
      (hG t.val t.property.2).prodMk measurable_const).norm
  · intro t ht ω
    have h := (φ ω).norm_coe_le_norm (⟨t,zero_le,ht⟩ : CanonicalPathTime T)
    change ‖(N t ω,(0:ℝ))‖ ≤ ‖φ ω‖ at h
    simpa only [Prod.norm_def,norm_zero,max_eq_left (norm_nonneg _)] using h
  · exact (integrable_map_measure (by fun_prop) hm.aemeasurable).mp hi
  · change (∫ ω, (fun f : CanonicalPath T (ℝ × ℝ) => ‖f‖^n) (φ ω) ∂μ) ≤ _
    have hc : Continuous (fun f : CanonicalPath T (ℝ × ℝ) => ‖f‖^n) := continuous_norm.pow n
    rw [← integral_map (μ := μ) hm.aemeasurable hc.aestronglyMeasurable]
    simpa [ν,ENNReal.toReal_ofReal hC] using he

#print axioms physical_sup_power_of_increments

end RoughHeston
