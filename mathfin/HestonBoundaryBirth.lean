import HestonZeroBoundary
import AffineBirthExpectation

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace RoughHeston

/-- Boundary persistence for an arbitrary compact subset of the
positive-time interior of the supplied horizon. -/
theorem heston_zero_boundary_on_compact
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} {M V C : ℝ≥0 → Ω → ℝ}
    {α κ a b v₀ : ℝ} {U : ℝ≥0} {I : Set ℝ}
    (hα : 1/2<α) (hα' : α<1) (hκ : 0≤κ) (ha : 0<a) (hb : 0≤b) (hv₀ : 0≤v₀)
    (hI : IsCompact I) (hIU : I ⊆ Ioo (0:ℝ) (U:ℝ))
    (hP : HestonBoundaryProcess μ 𝒢 U α κ a b v₀ M V C) :
    ∃ c C₁ η h₀ : ℝ, 0<c ∧ 0<C₁ ∧ 0<η ∧ 0<h₀ ∧
      ∀ t∈I,
        c≤μ.real {ω | V t.toNNReal ω=0} ∧
        ∀ h∈Ioc (0:ℝ) h₀,
          (@boundaryConditionedMeasure Ω m μ {ω | V t.toNNReal ω=0}).real
            {ω | 0<V (t+h).toNNReal ω}≤C₁*h^η := by
  rcases I.eq_empty_or_nonempty with he|hn
  · subst I
    exact ⟨1,1,1,1,zero_lt_one,zero_lt_one,zero_lt_one,zero_lt_one,fun t ht => ht.elim⟩
  obtain ⟨lo,hlo⟩ := hI.exists_isLeast hn
  obtain ⟨hi,hhi⟩ := hI.exists_isGreatest hn
  obtain ⟨c,C₁,η,h₀,hc,hC₁,hη,hh₀,hB⟩ := heston_zero_boundary_proposition
    hα hα' hκ ha hb hv₀ (hIU hlo.1).1 (hIU hhi.1).2 hP
  exact ⟨c,C₁,η,h₀,hc,hC₁,hη,hh₀,fun t ht => hB t ⟨hlo.2 ht,hhi.2 ht⟩⟩

/-- The birth value used in the stopped occupation comparison has
exactly its original zero-conditioned Laplace-complement expectation. -/
theorem heston_boundary_birth_expectation
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} {M V C : ℝ≥0 → Ω → ℝ}
    {α κ a b v₀ : ℝ} {U T s : ℝ≥0} {w : ℝ → ℝ} {n : ℕ}
    (hα : 1/2<α) (hα' : α<1) (ha : 0≤a) (hb : 0≤b) (hv₀ : 0≤v₀)
    (hT : T≤U) (hs : s<T) (hP : HestonBoundaryProcess μ 𝒢 U α κ a b v₀ M V C)
    (hw : PointChargeRiccatiOn α (n:ℝ) (-κ) (-a) (T:ℝ) w) (hwn : ∀ t>0,0≤w t)
    (hZ : 0<μ {ω | V s ω=0}) :
    let Q := @boundaryConditionedMeasure Ω m μ {ω | V s ω=0}
    let Ψ (ω : Ω) := affineFuturePayoff α w (fun r => b+v₀*fractionalL α r)
      (fun r => V r.toNNReal ω) T s
    (∫ ω,1-Real.exp (-Ψ ω) ∂Q)=(∫ ω,1-laplaceBoundaryWeight (V T) n ω ∂Q) ∧
      (∫ ω,1-Real.exp (-Ψ ω) ∂Q)≤Q.real {ω | 0<V T ω} := by
  let _ : MeasurableSpace Ω := m
  have hA : MeasurableSet[𝒢 s] {ω | V s ω=0} :=
    measurableSet_eq_fun (hP.variance_adapted s).measurable measurable_const
  have hVm : Measurable (V T) := ((hP.variance_adapted T).mono (𝒢.le T)).measurable
  have he := heston_boundary_conditional_point_test hα hα' ha hb hv₀ hT hs hP hw hwn
  have hEq : laplaceBoundaryWeight (V T) n=fun ω => Real.exp (-((n:ℝ)*V T ω)) := by
    funext ω
    simp only [laplaceBoundaryWeight,neg_mul]
  exact affine_birth_laplace_complement_expectation (𝒢.le s) hA hZ hVm
    (hP.variance_nonnegative T) n (by rw [hEq]; exact he)

#print axioms heston_zero_boundary_on_compact
#print axioms heston_boundary_birth_expectation

end RoughHeston
