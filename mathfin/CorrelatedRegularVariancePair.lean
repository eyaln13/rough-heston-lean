import RegularHestonPair
import CorrelatedHestonVariancePair
import JointBrownianIncrements

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston

open MathFin.ItoLocalMartingale (nullAugmentation)

/-- The two stock and variance drivers form a Brownian pair with
respect to the joint filtration, with correlation measured by their
quadratic covariation. The endpoints allow a degenerate Gaussian law. -/
structure HestonCorrelatedDrivers {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) (F : Filtration ℝ≥0 m) (T : ℝ≥0) (ρ : ℝ) (B W : ℝ≥0 → Ω → ℝ) : Prop where
  variance_driver : MathFinBridge.BrownianOn P F T B
  price_driver : MathFinBridge.BrownianOn P F T W
  correlation : Martingale (fun t ω => B t ω*W t ω-ρ*((min t T:ℝ≥0):ℝ)) F P
  jointly_gaussian : ∀ s t, s≤t → t≤T →
    let D := fun ω => (B t ω-B s ω,W t ω-W s ω)
    IsGaussian (P.map D) ∧ Indep ((inferInstance : MeasurableSpace (ℝ×ℝ)).comap D) (F s) P

/-- On the usual correlated extension the original two variances remain
separated, and their moment bounds still apply to the price integrals. -/
theorem RegularHestonPair.correlated {T : ℝ≥0} {α v₀ κ θ σ : ℝ} (h : RegularHestonPair T α v₀ κ θ σ)
    (ρ : ℝ) (hρ : |ρ|≤1) :
    ∃ (Ω : Type) (m : MeasurableSpace Ω) (P : @Measure Ω m)
      (F : Filtration ℝ≥0 m) (B W X Y : ℝ≥0→Ω→ℝ),
      IsProbabilityMeasure P ∧ F.IsComplete P ∧ F.IsRightContinuous ∧ HestonCorrelatedDrivers P F T ρ B W ∧
      IsHestonVarianceSolution P F T α v₀ κ θ σ B X ∧ IsHestonVarianceSolution P F T α v₀ κ θ σ B Y ∧
      0<P {ω | ∃ t≤T,X t ω≠Y t ω} ∧ HestonPriceVarianceData P X ∧ HestonPriceVarianceData P Y := by
  obtain ⟨Ω,m,μ,G,B,X,Y,hμ,hB,hX,hY,hsep,dx,dy⟩ := h
  let _ : MeasurableSpace Ω := m
  let _ : IsProbabilityMeasure μ := hμ
  let Ω' := Ω × (ℝ≥0→ℝ)
  let P₀ := μ.prod gaussianLimit
  let P := physicalCompletedMeasure P₀
  let F := physicalUsualFiltration P₀ (nullAugmentation (prodFiltration G canonicalAuxiliaryFiltration) P₀)
  let B' (t : ℝ≥0) (z : Ω') := B (min t T) z.1
  let C (t : ℝ≥0) (z : Ω') := brownian (min t T) z.2
  let W (t : ℝ≥0) (z : Ω') := ρ*B' t z+Real.sqrt (1-ρ^2)*C t z
  have hExt := separated_hestonVariancePair_on_correlated_product hB hX hY hsep ρ hρ
  obtain ⟨hB',hW,hcross,hProj,hX',hY',hgap⟩ := hExt
  have hp := correlated_product_fst_measurePreserving (μ:=μ)
  let _ : MeasurableSpace Ω' := physicalCompletedSpace P₀
  have hCad : StronglyAdapted F C := by
    simpa only [zero_mul,one_mul,zero_add] using (hProj 0 1 (by norm_num)).adapted
  have hD : HestonCorrelatedDrivers P F T ρ B' W :=
    ⟨hB',hW,hcross,fun _ _ hst ht =>
      jointly_gaussian_independent_increments_of_correlated_projections hB'.adapted hCad hProj ρ hst ht⟩
  have lift {V : ℝ≥0→Ω→ℝ} (hV : HestonPriceVarianceData μ V) :
      HestonPriceVarianceData P (fun t (z : Ω') => V t z.1) := by
    obtain ⟨K,hK⟩ := hV.mean_bound
    refine ⟨fun z => hV.continuous z.1,fun t z => hV.nonnegative t z.1,
      fun t => hp.integrable_comp_of_integrable (hV.integrable t),⟨K,?_⟩⟩
    intro t
    have hmeas := (hV.integrable t).aestronglyMeasurable
    rw [← hp.map_eq] at hmeas
    have hEq := integral_map hp.measurable.aemeasurable hmeas
    rw [hp.map_eq] at hEq
    exact hEq.symm.le.trans (hK t)
  exact ⟨Ω',_,P,F,B',W,_,_,inferInstance,inferInstance,inferInstance,hD,hX',hY',hgap,lift dx,lift dy⟩

#print axioms RegularHestonPair.correlated

end RoughHeston
