import CanonicalUsualModels
import ExplicitLebesgueCompanionMoment
import UniformAcrossMeshLaws

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston

open GirsanovPort

/-- The actual companion has a second-moment bound chosen uniformly
over every admissible mesh, both on the physical law and its completion. -/
theorem uniform_explicitLebesgueCompanion_second
    {T : ℝ≥0} {α κ σ b v₀ : ℝ}
    (hT : 0<T) (hα : 1/2<α) (hα' : α<1) (hκ : 0≤κ) (hσ : 0≤σ) (hb : 0<b) (hv₀ : 0≤v₀) :
    ∃ B₂ : ℝ,0≤B₂ ∧ ∀ {ε : ℝ},0<ε →
      ∀ (L : FractionalFixedMeshLaw T α κ σ (lebesgueMeshInitial T b ε v₀) (lebesgueMeshInput T α b ε)),
      ∀ t≤T,
        let P := (L.law:Measure (CanonicalPath T (CoupledPhysicalState (FixedMeshClusterIndex (T:ℝ) b ε))))
        ((∫ p,(canonicalPhysicalVariance T none t p)^2 ∂P)≤B₂) ∧
          (∫ p,(canonicalRegularVariance T none v₀ t p)^2 ∂physicalCompletedMeasure P)≤B₂ := by
  let C := v₀+constantImmigrationConvolution α b T
  let D := fractionalAggregateMomentCap σ α T C 1
  let B := max D 0
  refine ⟨B,le_max_right _ _,?_⟩
  intro ε hε L t ht
  let I := FixedMeshClusterIndex (T:ℝ) b ε
  let P := (L.law:Measure (CanonicalPath T (CoupledPhysicalState I)))
  let V := canonicalRegularVariance T (none : Option I) v₀ t
  let G := canonicalPhysicalVariance T (none : Option I) t
  have hG : (∫ p,(G p)^2 ∂P)≤D := by
    simpa only [G,P,pow_one] using
      (explicitLebesguePulseLaw_companion_dyadic_bound L hT hα hα' hκ hσ hb hε hv₀ 1 t ht).2
  refine ⟨hG.trans (le_max_left _ _),?_⟩
  have hV : StronglyMeasurable V :=
    ((canonicalRegularVariance_adapted (T := T) (none : Option I) v₀ t).mono
      ((canonicalPathNaturalFiltration (E := CoupledPhysicalState I) T).le t))
  have hVeq : (fun p => (V p)^2) =ᵐ[P] fun p => (G p)^2 := by
    filter_upwards [canonicalRegularVariance_ae_paths L.starts L.nonnegative none] with p hp
    have he : V p=G p := hp t
    rw [he]
  change (∫ p,(V p)^2 ∂physicalCompletedMeasure P)≤B
  calc
    _ = ∫ p,(V p)^2 ∂P := physical_completion_integral P (hV.pow 2)
    _ = ∫ p,(G p)^2 ∂P := integral_congr_ae hVeq
    _ ≤ _ := hG.trans (le_max_left _ _)

/-- The boundary atom and occupation constants for the actual competitor
are fixed before the mesh and its birth time. -/
theorem uniform_explicitLebesgueCompanion_zero_boundary
    {T : ℝ≥0} {α κ σ b v₀ : ℝ}
    (hT : 0<T) (hα : 1/2<α) (hα' : α<1) (hκ : 0≤κ)
    (hσ : 0<σ) (hb : 0<b) (hv₀ : 0≤v₀) :
    ∃ c C η h₀ : ℝ,0<c ∧ 0<C ∧ 0<η ∧ 0<h₀ ∧
      ∀ {ε : ℝ},0<ε →
      ∀ (L : FractionalFixedMeshLaw T α κ σ (lebesgueMeshInitial T b ε v₀) (lebesgueMeshInput T α b ε)),
      ∀ t∈Icc ((T:ℝ)/3) (2*(T:ℝ)/3),
        let P := physicalCompletedMeasure
          (L.law:Measure (CanonicalPath T (CoupledPhysicalState (FixedMeshClusterIndex (T:ℝ) b ε))))
        let A := {p | canonicalRegularVariance T none v₀ t.toNNReal p=0}
        c≤P.real A ∧ ∀ h∈Ioc (0:ℝ) h₀,
          (boundaryConditionedMeasure P A).real {p | 0<canonicalRegularVariance T none v₀ (t+h).toNNReal p}≤C*h^η := by
  obtain ⟨B₂,hB₂,hB⟩ := uniform_explicitLebesgueCompanion_second hT hα hα' hκ hσ.le hb hv₀
  have hTr : 0<(T:ℝ) := NNReal.coe_pos.mpr hT
  obtain ⟨c,C,η,h₀,hc,hC,hη,hh₀,hBound⟩ :=
    uniform_heston_zero_boundary_over_laws_over_sample_spaces (U := T)
      (lo := (T:ℝ)/3) (hi := 2*(T:ℝ)/3) (v₀ := v₀) (a := σ^2/2)
      hα hα' hκ (by positivity) hb.le hv₀ (by positivity) (by linarith) hB₂
  refine ⟨c,C,η,h₀,hc,hC,hη,hh₀,?_⟩
  intro ε hε L t ht
  exact hBound _ _ (L.usualCompanionBoundary hα' hv₀ (show lebesgueMeshInput T α b ε none=(fun _ => b) from rfl))
    (fun r hr => (hB hε L r hr).2) t ht

#print axioms uniform_explicitLebesgueCompanion_second
#print axioms uniform_explicitLebesgueCompanion_zero_boundary

end RoughHeston
