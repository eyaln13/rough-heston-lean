import ClusterResolventIncrementRow
import ClusterRealMomentTransfer

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston.GirsanovPort

noncomputable def pastResolventDifference (R : ℝ → ℝ) (a b : ℝ≥0) (s : ℝ≥0) : ℝ :=
  (Ioc 0 a).indicator (fun z : ℝ≥0 => R ((b:ℝ)-(z:ℝ))-R ((a:ℝ)-(z:ℝ))) s

noncomputable def newResolventWeight (R : ℝ → ℝ) (a b : ℝ≥0) (s : ℝ≥0) : ℝ :=
  (Ioc a b).indicator (fun z : ℝ≥0 => R ((b:ℝ)-(z:ℝ))) s

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 m} {T : ℝ≥0} {U : ℝ≥0 → Ω → ℝ}

/-- Split an increment of the noise into its two actual predictable
rows before applying separate time-weighted moment estimates. -/
theorem cluster_split_increment_row {a b : ℝ≥0} (hab : a≤b)
    {R : ℝ → ℝ} (hz : ∀ x≤0, R x=0) {σ : ℝ}
    (f : Lp ℝ 2 (jointPredictableMeasure F P T))
    (hf : f =ᵐ[jointPredictableMeasure F P T] fun z =>
      σ*(R ((b:ℝ)-(z.1:ℝ))-R ((a:ℝ)-(z.1:ℝ)))*Real.sqrt (U z.1 z.2)) :
    ∃ θ ψ : Lp ℝ 2 (jointPredictableMeasure F P T), f=θ+ψ ∧
      (θ =ᵐ[jointPredictableMeasure F P T] fun z => σ*pastResolventDifference R a b z.1*Real.sqrt (U z.1 z.2)) ∧
      (ψ =ᵐ[jointPredictableMeasure F P T] fun z => σ*newResolventWeight R a b z.1*Real.sqrt (U z.1 z.2)) := by
  let S := Ioc (0:ℝ≥0) a ×ˢ (univ : Set Ω)
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hθ := (Lp.memLp f).indicator (measurableSet_joint_timeBand F a).nullMeasurableSet
  let θ := hθ.toLp (S.indicator ⇑f)
  have he : ⇑θ =ᵐ[jointPredictableMeasure F P T] S.indicator ⇑f := hθ.coeFn_toLp
  refine ⟨θ,f-θ,by abel,?_,?_⟩
  · filter_upwards [he,hf] with z hθ' h
    by_cases hs : z.1∈Ioc 0 a
    · simpa only [S, indicator_of_mem (show z∈S from ⟨hs,mem_univ _⟩),h,
        pastResolventDifference,indicator_of_mem hs] using hθ'
    · simpa only [S,indicator_of_notMem (show z∉S from fun hz => hs hz.1),
        pastResolventDifference,indicator_of_notMem hs,mul_zero,zero_mul] using hθ'
  · filter_upwards [Lp.coeFn_sub f θ,he,hf,ae_mem_joint_timeBand F P T] with z hd hθ' h hmem
    change (f-θ) z=f z-θ z at hd
    rw [hd,hθ']
    by_cases hp : z.1≤a
    · have hs : z∈S := ⟨⟨hmem.1.1,hp⟩,mem_univ _⟩
      have hn : z.1∉Ioc a b := fun h => (not_lt_of_ge hp) h.1
      simp only [indicator_of_mem hs,newResolventWeight,indicator_of_notMem hn,
        mul_zero,zero_mul,sub_self]
    · have ha : a<z.1 := lt_of_not_ge hp
      have hs : z∉S := fun hh => hp hh.1.2
      have hza := hz _ (sub_nonpos.mpr (show (a:ℝ)≤(z.1:ℝ) from ha.le))
      rw [indicator_of_notMem hs,sub_zero,h,hza,sub_zero]
      by_cases hzb : z.1≤b
      · rw [newResolventWeight,indicator_of_mem (show z.1∈Ioc a b from ⟨ha,hzb⟩)]
      · have hn : z.1∉Ioc a b := fun h => hzb h.2
        rw [newResolventWeight,indicator_of_notMem hn,
          hz _ (sub_nonpos.mpr (show (b:ℝ)≤(z.1:ℝ) from (le_of_not_ge hzb)))]

/-- Add the bounds on the signed terminal integrals in the two windows. -/
theorem cluster_integral_sum_moment {μ : Measure Ω} {X Y Z : Ω → ℝ} {p : ℕ}
    (hX : MemLp X (p:ℝ≥0∞) μ) (hY : MemLp Y (p:ℝ≥0∞) μ) [IsProbabilityMeasure μ]
    (he : Z=ᵐ[μ] X+Y) {A D : ℝ}
    (ha : (∫ ω, ‖X ω‖^p ∂μ)≤A) (hd : (∫ ω, ‖Y ω‖^p ∂μ)≤D) :
    MemLp Z (p:ℝ≥0∞) μ ∧ (∫ ω, ‖Z ω‖^p ∂μ)≤(2:ℝ)^(p-1)*(A+D) := by
  have hZ := (hX.add hY).ae_eq he.symm
  have hx := hX.integrable_norm_pow'
  have hy := hY.integrable_norm_pow'
  have hh : (fun ω => ‖Z ω‖^p)≤ᵐ[μ] fun ω =>
      (2:ℝ)^(p-1)*(‖X ω‖^p+‖Y ω‖^p) := by
    filter_upwards [he] with ω hω
    rw [hω]
    exact (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) p).trans
      (add_pow_le (norm_nonneg _) (norm_nonneg _) p)
  have h := integral_mono_ae hZ.integrable_norm_pow' ((hx.add hy).const_mul _) hh
  rw [integral_const_mul] at h
  simp only [Pi.add_apply] at h
  rw [integral_add hx hy] at h
  exact ⟨hZ,h.trans (mul_le_mul_of_nonneg_left (add_le_add ha hd) (by positivity))⟩

#print axioms cluster_split_increment_row
#print axioms cluster_integral_sum_moment

end RoughHeston.GirsanovPort
