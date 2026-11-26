import ExplicitLebesgueMeshLimit
import LebesgueMeshScaleSequence

/-! Exact endpoint of the deterministic and stochastic approximation
argument. The gap hypothesis names the actual fixed-mesh focal law. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston

/-- The uniform separation assertion on the literal rectangular-pulse
laws used in the proof, at every sufficiently small admissible mass. -/
def ExplicitLebesgueUniformGap : Prop :=
  ∀ (T : ℝ≥0) (α v₀ κ θ σ : ℝ),
    0 < T → 1/2 < α → α < 1 → 0 < v₀ → 0 < κ → 0 < θ → 0 < σ →
    let b := κ*θ
    ∃ (εbar ℓ : ℝ) (p : ℝ≥0∞), 0 < εbar ∧ 0 < ℓ ∧ 0 < p ∧
      ∀ ε, 0 < ε → ε ≤ 1 → ε ≤ εbar → lebesguePulseDuration α ε ≤ ε/b →
      ∃ L : FractionalFixedMeshLaw T α κ σ (lebesgueMeshInitial T b ε v₀)
        (lebesgueMeshInput T α b ε),
        p ≤ (L.pairLaw : Measure (CanonicalPath T (ℝ × ℝ))) {z | ℓ ≤ canonicalPairGap T z}

/-- The exact direct rough-Heston theorem follows from the uniform
separation estimate on the actual discrete-immigration laws. -/
theorem regularHestonPair_of_explicitLebesgueUniformGap (hGap : ExplicitLebesgueUniformGap) : 
    ∀ (T : ℝ≥0) (α v₀ κ θ σ : ℝ), 0<T → 1/2<α → α<1 → 0<v₀ → 0<κ → 0<θ → 0<σ →
      RegularHestonPair T α v₀ κ θ σ := by
  intro T α v₀ κ θ σ hT hα hα' hv₀ hκ hθ hσ
  let b := κ*θ
  have hb : 0 < b := mul_pos hκ hθ
  obtain ⟨εbar, ℓ, p, hεbar,hℓ,hp,h⟩ := hGap T α v₀ κ θ σ hT hα hα' hv₀ hκ hθ hσ
  obtain ⟨ε,hε,hε₁,hsmall,hε0,hd⟩ := exists_lebesgueMesh_mass_sequence (by linarith : 0 < α) hα' hb hεbar
  have hLaw (n : ℕ) := h (ε n) (hε n) (hε₁ n) (hsmall n) (hd n)
  let L (n : ℕ) := Classical.choose (hLaw n)
  exact regular_heston_of_explicitLebesguePulseLaws hT hα hα' hκ.le hσ hb
    rfl hv₀.le hε hε₁ hε0 hd L hℓ hp (fun n => Classical.choose_spec (hLaw n))

theorem theorem1_1_of_explicitLebesgueUniformGap (hGap : ExplicitLebesgueUniformGap) : Theorem1_1 := by
  intro T α v₀ κ θ σ hT hα hα' hv₀ hκ hθ hσ
  exact (regularHestonPair_of_explicitLebesgueUniformGap hGap T α v₀ κ θ σ hT hα hα' hv₀ hκ hθ hσ).variance

#print axioms RoughHeston.regularHestonPair_of_explicitLebesgueUniformGap

#print axioms RoughHeston.theorem1_1_of_explicitLebesgueUniformGap

end RoughHeston
