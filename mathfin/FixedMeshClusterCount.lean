import LebesguePulseMesh
import OrthogonalClusterMoments
import UniformClusterSeparation

open MeasureTheory Set
open scoped NNReal ENNReal Topology

namespace RoughHeston

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The off-diagonal part of the count uses a mixed moment at the two
observation times. Nonnegativity and the marginal bounds give the mesh scale. -/
theorem mesh_cluster_event_bounds {ι : Type*} {F : Finset ι}
    {E : ι → Set Ω} {A : ι → Ω → ℝ} {m : ι → ℝ} {K ε ℓ : ℝ}
    (hK : 0 ≤ K) (hε : 0 ≤ ε) (hℓ : 0 < ℓ)
    (hA : ∀ i ∈ F, MemLp (A i) 2 μ)
    (hAn : ∀ i ∈ F, 0 ≤ᵐ[μ] A i)
    (hmean : ∀ i ∈ F, (∫ ω, A i ω ∂μ) = m i)
    (hm : ∀ i ∈ F, m i ≤ K * ε)
    (hc : ∀ i ∈ F, ∀ j ∈ F, i ≠ j →
      (∫ ω, A i ω * A j ω ∂μ) = m i * m j)
    (hE : ∀ i ∈ F, E i ⊆ {ω | ℓ ≤ A i ω}) :
    (∀ i ∈ F, μ.real (E i) ≤ (K / ℓ) * ε) ∧
      (∀ i ∈ F, ∀ j ∈ F, i ≠ j →
        μ.real (E i ∩ E j) ≤ (K / ℓ)^2 * ε^2) := by
  have hmn : ∀ i ∈ F, 0 ≤ m i := fun i hi =>
    (hmean i hi) ▸ integral_nonneg_of_ae (hAn i hi)
  constructor
  · intro i hi
    have hb := (measureReal_mono (μ := μ) (hE i hi)).trans
      (show μ.real {ω | ℓ ≤ A i ω} ≤ (K * ε) / ℓ from
        (le_div_iff₀ hℓ).2 (by
          rw [mul_comm]
          exact (mul_meas_ge_le_integral_of_nonneg (hAn i hi)
            ((hA i hi).integrable (by norm_num)) ℓ).trans (by rw [hmean i hi]; exact hm i hi)))
    convert hb using 1
    ring
  · intro i hi j hj hij
    have hs : E i ∩ E j ⊆ {ω | ℓ ≤ A i ω ∧ ℓ ≤ A j ω} :=
      fun _ hω => ⟨hE i hi hω.1,hE j hj hω.2⟩
    calc
      _ ≤ (∫ ω, A i ω * A j ω ∂μ) / (ℓ * ℓ) :=
        (measureReal_mono hs).trans
          (joint_exceedance_le_product_moment (hAn i hi) (hAn j hj)
            ((hA i hi).integrable_mul (hA j hj)) hℓ hℓ)
      _ ≤ (K * ε * (K * ε)) / (ℓ * ℓ) := by
        rw [hc i hi j hj hij]
        exact div_le_div_of_nonneg_right
          (mul_le_mul (hm i hi) (hm j hj) (hmn j hj) (mul_nonneg hK hε)) (by positivity)
      _ = _ := by ring

/-- Evaluation of the difference at a single time gives a lower bound
on the canonical sup norm. -/
theorem canonicalPairGap_ge_abs_eval {T : ℝ≥0} (p : CanonicalPath T (ℝ × ℝ))
    (t : ℝ≥0) :
    |(canonicalPathEval T t p).1 - (canonicalPathEval T t p).2| ≤ canonicalPairGap T p := by
  rw [canonicalPairGap_eq_iSup]
  let f : C(ℝ × ℝ,ℝ) := ⟨fun x => x.1-x.2,continuous_fst.sub continuous_snd⟩
  exact le_ciSup (f := fun s : CanonicalPathTime T => |(p s).1 - (p s).2|) (by
    refine ⟨‖f.comp p‖,?_⟩
    rintro a ⟨s,rfl⟩
    simpa [f,Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm (f.comp p) s) (canonicalEvalTime T t)

/-- A mixed-time product-moment identity suffices for a uniform
separation estimate on the physical mesh. The linear single-event lower
bound is supplied in the original probability measure. -/
theorem interior_pulse_mesh_uniform_separation {T : ℝ≥0} {b ε c K ℓ : ℝ}
    (hT : 0 < T) (hb : 0 < b) (hε : 0 < ε) (hmesh : ε ≤ b * (T:ℝ) / 12)
    (hc : 0 < c) (hK : 0 ≤ K) (hℓ : 0 < ℓ)
    (path : Ω → CanonicalPath T (ℝ × ℝ)) (mpath : Measurable path)
    (obs : ℕ → ℝ≥0) (A : ℕ → Ω → ℝ) (m : ℕ → ℝ)
    (hAm : ∀ i ∈ interiorPulseBirths T b ε, Measurable (A i))
    (hA : ∀ i ∈ interiorPulseBirths T b ε, MemLp (A i) 2 μ)
    (hAn : ∀ i ∈ interiorPulseBirths T b ε, 0 ≤ᵐ[μ] A i)
    (hmean : ∀ i ∈ interiorPulseBirths T b ε, (∫ ω, A i ω ∂μ) = m i)
    (hm : ∀ i ∈ interiorPulseBirths T b ε, m i ≤ K * ε)
    (hmix : ∀ i ∈ interiorPulseBirths T b ε, ∀ j ∈ interiorPulseBirths T b ε, i ≠ j →
      (∫ ω, A i ω * A j ω ∂μ) = m i * m j)
    (hdom : ∀ i ∈ interiorPulseBirths T b ε, ∀ᵐ ω ∂μ,
      A i ω ≤ (canonicalPathEval T (obs i) (path ω)).1)
    (hlower : ∀ i ∈ interiorPulseBirths T b ε, c * ε ≤ μ.real
      {ω | ℓ ≤ A i ω ∧ (canonicalPathEval T (obs i) (path ω)).2 = 0}) :
    ENNReal.ofReal ((c * (b * (T:ℝ) / 4))^2 / (1 + 2 * (K / ℓ)^2 * (b * (T:ℝ))^2)) ≤
      μ {ω | ℓ ≤ canonicalPairGap T (path ω)} := by
  let F := interiorPulseBirths T b ε
  let E (i : ℕ) := {ω | ℓ ≤ A i ω ∧ (canonicalPathEval T (obs i) (path ω)).2 = 0 ∧
    A i ω ≤ (canonicalPathEval T (obs i) (path ω)).1}
  have hprojs (i : ℕ) : Measurable (fun ω => canonicalPathEval T (obs i) (path ω)) :=
    (ContinuousMap.measurable_eval (canonicalEvalTime T (obs i))).comp mpath
  have hmE (i : ℕ) (hi : i ∈ F) : MeasurableSet (E i) :=
    (measurableSet_le measurable_const (hAm i hi)).inter
      ((measurableSet_eq_fun (hprojs i).snd measurable_const).inter
        (measurableSet_le (hAm i hi) (hprojs i).fst))
  have hlower' (i : ℕ) (hi : i ∈ F) : c * ε ≤ μ.real (E i) := by
    have he : E i =ᵐ[μ] {ω | ℓ ≤ A i ω ∧ (canonicalPathEval T (obs i) (path ω)).2=0} := by
      filter_upwards [hdom i hi] with ω hd
      simp only [E,Set.mem_ofPred_eq,hd,and_true]
    rw [Measure.real,measure_congr he]
    exact hlower i hi
  have hp := (mesh_cluster_event_bounds (μ := μ) (E := E) hK hε.le hℓ hA hAn
    hmean hm hmix (fun _ _ _ hω => hω.1)).2
  obtain ⟨hs₁,hs₂⟩ := interiorPulseBirths_card_mass (NNReal.coe_pos.mpr hT) hb hε hmesh
  exact (clusterEventUnion_uniform_probability_bound F E hmE hε.le hc (sq_nonneg (K/ℓ))
    (by positivity) (by positivity) hs₁ hs₂ hlower' hp).trans (measure_mono (by
      rintro ω ⟨i,_,ha,hy,hd⟩
      change ℓ ≤ canonicalPairGap T (path ω)
      refine le_trans ?_ (canonicalPairGap_ge_abs_eval (path ω) (obs i))
      apply le_abs.mpr
      left
      rw [hy,sub_zero]
      exact ha.trans hd))

#print axioms mesh_cluster_event_bounds
#print axioms interior_pulse_mesh_uniform_separation

end RoughHeston
