import TheoremStatement

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace RoughHeston

/-- Properties of the limiting variance paths used to construct the
price integrals on a correlated Brownian extension. -/
structure HestonPriceVarianceData {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) (V : ℝ≥0 → Ω → ℝ) : Prop where
  continuous : ∀ ω, Continuous (fun t => V t ω)
  nonnegative : ∀ t ω, 0≤V t ω
  integrable : ∀ t, Integrable (V t) P
  mean_bound : ∃ C : ℝ, ∀ t, (∫ ω,V t ω ∂P)≤C

def RegularHestonPair (T : ℝ≥0) (α v₀ κ θ σ : ℝ) : Prop :=
  ∃ (Ω : Type) (m : MeasurableSpace Ω) (P : @Measure Ω m)
    (F : Filtration ℝ≥0 m) (B X Y : ℝ≥0→Ω→ℝ),
    IsProbabilityMeasure P ∧ IsBrownianOn P F T B ∧
    IsHestonVarianceSolution P F T α v₀ κ θ σ B X ∧
    IsHestonVarianceSolution P F T α v₀ κ θ σ B Y ∧
    0<P {ω | ∃ t≤T,X t ω≠Y t ω} ∧ HestonPriceVarianceData P X ∧ HestonPriceVarianceData P Y

theorem RegularHestonPair.variance {T : ℝ≥0} {α v₀ κ θ σ : ℝ} (h : RegularHestonPair T α v₀ κ θ σ) :
    ∃ (Ω : Type) (m : MeasurableSpace Ω) (P : @Measure Ω m)
      (F : Filtration ℝ≥0 m) (B X Y : ℝ≥0→Ω→ℝ),
      IsProbabilityMeasure P ∧ IsBrownianOn P F T B ∧
      IsHestonVarianceSolution P F T α v₀ κ θ σ B X ∧
      IsHestonVarianceSolution P F T α v₀ κ θ σ B Y ∧ 0<P {ω | ∃ t≤T,X t ω≠Y t ω} := by
  obtain ⟨Ω,m,P,F,B,X,Y,hp,hB,hX,hY,hsep,_,_⟩ := h
  exact ⟨Ω,m,P,F,B,X,Y,hp,hB,hX,hY,hsep⟩

#print axioms RegularHestonPair.variance

end RoughHeston
