import ExplicitLebesgueUniformGapEndpoint
import UniformExplicitMeshSeparation

/-! The single-birth lower bound supplies the last model-specific input. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston

/-- A uniform positive lower bound, of order one pulse mass, for a
focal birth at fixed observation age and a zero companion variance. -/
def ExplicitLebesgueBirthLowerBound : Prop :=
  ∀ (T : ℝ≥0) (α v₀ κ θ σ : ℝ)
    (_ : 0 < T) (_ : 1/2 < α) (_ : α < 1) (_ : 0 < v₀) (hκ : 0 < κ) (hθ : 0 < θ) (_ : 0 < σ),
    let b := κ*θ
    ∃ (r : ℝ≥0) (c ℓ εbar : ℝ),
      0 < r ∧ (r:ℝ) < (T:ℝ)/3 ∧ 0 < c ∧ 0 < ℓ ∧ 0 < εbar ∧
      ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 → ε ≤ εbar → lebesguePulseDuration α ε ≤ ε/b →
      ∃ L : FractionalFixedMeshLaw T α κ σ (lebesgueMeshInitial T b ε v₀)
        (lebesgueMeshInput T α b ε),
      ∀ i : {i : ℕ // i ∈ interiorPulseBirths T b ε},
        c*ε ≤ (L.law : Measure _).real
          {p | ℓ ≤ canonicalPhysicalVariance T
            (some (interiorLebesguePulseIndex (NNReal.coe_nonneg T) (mul_pos hκ hθ) hε i))
            (lebesguePulseBirthTime b ε i.val+r) p ∧
            canonicalPhysicalVariance T none (lebesguePulseBirthTime b ε i.val+r) p = 0}

/-- Assemble the complete argument after supplying the actual single-birth
lower bound on the literal fixed mesh. -/
theorem explicitLebesgueUniformGap_of_birthLowerBound (hBirth : ExplicitLebesgueBirthLowerBound) : ExplicitLebesgueUniformGap := by
  intro T α v₀ κ θ σ hT hα hα' hv₀ hκ hθ hσ
  let b := κ*θ
  have hb : 0 < b := mul_pos hκ hθ
  obtain ⟨r,c,ℓ,εbar,hr,hrT,hc,hℓ,hεbar,hLower⟩ := hBirth T α v₀ κ θ σ hT hα hα' hv₀ hκ hθ hσ
  obtain ⟨p,hp,hSep⟩ := uniform_explicitLebesgueMesh_separation (κ := κ) (σ := σ) (v₀ := v₀)
    hT hα hα' hb hr hrT hc hℓ
  let E := min εbar (min (b*(T:ℝ)/12) (b*(r:ℝ)/2))
  have hE : 0 < E := lt_min hεbar (lt_min (by positivity) (by positivity))
  refine ⟨E,ℓ,p,hE,hℓ,hp,?_⟩
  intro ε hε hε₁ hEs hwidth
  have hE₁ : ε ≤ εbar := hEs.trans (min_le_left _ _)
  have hMesh : ε ≤ b*(T:ℝ)/12 := hEs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hWidth : lebesguePulseDuration α ε ≤ (r:ℝ)/2 := hwidth.trans <| (div_le_iff₀ hb).2 <|
    (hEs.trans ((min_le_right _ _).trans (min_le_right _ _))).trans_eq (by ring)
  obtain ⟨L,hL⟩ := hLower ε hε hε₁ hE₁ hwidth
  exact ⟨L,hSep ε hε hMesh hWidth L hL⟩

theorem theorem1_1_of_explicitLebesgueBirthLowerBound (hBirth : ExplicitLebesgueBirthLowerBound) : Theorem1_1 :=
  theorem1_1_of_explicitLebesgueUniformGap (explicitLebesgueUniformGap_of_birthLowerBound hBirth)

#print axioms RoughHeston.explicitLebesgueUniformGap_of_birthLowerBound

#print axioms RoughHeston.theorem1_1_of_explicitLebesgueBirthLowerBound

end RoughHeston
