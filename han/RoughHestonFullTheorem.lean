import RoughHestonVarianceTheorem
import CorrelatedRegularVariancePair
import HestonPriceSDE
import HestonBrownianItoEquivalence

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston

open GirsanovPort

/-- The risk-neutral price equation on [0,T]. The driver is the named
price Brownian, held constant after T for the finite-horizon integral.
The local integral is obtained from ordinary square-integrable stopped
integrands on a single increasing sequence of stopping times. -/
def IsHestonPriceSolution {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 m) (T : ℝ≥0) (s₀ : ℝ)
    (W V S : ℝ≥0→Ω→ℝ) : Prop :=
  IsStronglyPredictable F S ∧ (∀ ω, Continuous (fun t => S t ω)) ∧
    (∀ ω, S 0 ω=s₀) ∧ (∀ t ω,0<S t ω) ∧
    ∃ hW₂ : ∀ t, MemLp (W (min t T)) 2 P,
      HasLocalizedJointBrownianIntegral T F P (B:=fun t => W (min t T)) hW₂ (fun t ω => S t ω*Real.sqrt (V t ω))
        (fun t ω => S t ω-s₀)

/-- A version of the actual predictable Brownian integral at each
observation time satisfies the direct equation on one event of probability one. -/
def HasHestonBrownianItoEquation {Ω : Type*} {m : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {F : Filtration ℝ≥0 m} {T : ℝ≥0}
    {B : ℝ≥0→Ω→ℝ} {α : ℝ} (hB : MathFinBridge.BrownianOn P F T B) (hα : 1/2<α)
    (v₀ κ θ σ : ℝ) (V : ℝ≥0→Ω→ℝ) : Prop :=
  ∃ (hp : IsStronglyPredictable F V) (hn : ∀ t ω,0≤V t ω) (hi : ∀ t,Integrable (V t) P)
    (C : ℝ) (hm : ∀ t,(∫ ω,V t ω ∂P)≤C) (Z : ℝ≥0→Ω→ℝ),
    (∀ u : Icc (0:ℝ≥0) T,Z u=ᵐ[P] hestonBrownianItoConvolution hB hα hp hn hi hm u) ∧
      ∀ᵐ ω ∂P, ∀ t≤T,V t ω=v₀+hestonVarianceDrift α κ θ V t ω+σ*Z t ω

private theorem ito_equation_for_regular_variance {Ω : Type*} {m : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {F : Filtration ℝ≥0 m} {T : ℝ≥0}
    {B V : ℝ≥0→Ω→ℝ} {α v₀ κ θ σ : ℝ} (hB : MathFinBridge.BrownianOn P F T B)
    (hα : 1/2<α) (hα' : α<1) (h : IsHestonVarianceSolution P F T α v₀ κ θ σ B V)
    (d : HestonPriceVarianceData P V) : HasHestonBrownianItoEquation hB hα v₀ κ θ σ V := by
  obtain ⟨C,hm⟩ := d.mean_bound
  have hp := h.1.isStronglyPredictable_of_leftContinuous (fun ω _ => (d.continuous ω).continuousAt.continuousWithinAt)
  exact ⟨hp,d.nonnegative,d.integrable,C,hm,(isHestonVarianceSolution_iff_brownianIto
    hB hα hα'.le hp h.1 h.2.1 d.nonnegative d.integrable hm).mp h⟩

/-- Both solutions of the price–variance system use the same Brownian
pair, shared initial data and one joint filtration. The terminal
separation event concerns the paths on the entire time interval. -/
def FullRoughHestonTheorem : Prop :=
  ∀ (T : ℝ≥0) (α v₀ κ θ σ ρ s₀ : ℝ),
    0<T → ∀ hα : 1/2<α, α<1 → 0<v₀ → 0<κ → 0<θ → 0<σ → |ρ|≤1 → 0<s₀ →
    ∃ (Ω : Type) (m : MeasurableSpace Ω) (P : @Measure Ω m)
      (F : Filtration ℝ≥0 m) (B W X Y Sx Sy : ℝ≥0→Ω→ℝ) (hP : IsProbabilityMeasure P),
      let _ : IsProbabilityMeasure P := hP
      F.IsComplete P ∧ F.IsRightContinuous ∧ ∃ drivers : HestonCorrelatedDrivers P F T ρ B W,
      HasHestonBrownianItoEquation drivers.variance_driver hα v₀ κ θ σ X ∧
      HasHestonBrownianItoEquation drivers.variance_driver hα v₀ κ θ σ Y ∧
      IsHestonVarianceSolution P F T α v₀ κ θ σ B X ∧ IsHestonVarianceSolution P F T α v₀ κ θ σ B Y ∧
      IsHestonPriceSolution P F T s₀ W X Sx ∧ IsHestonPriceSolution P F T s₀ W Y Sy ∧
      0<P {ω | ∃ t≤T, X t ω≠Y t ω}

private theorem price_for_regular_variance {Ω : Type*} {m : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {F : Filtration ℝ≥0 m} [F.IsComplete P] [F.IsRightContinuous]
    {T : ℝ≥0} {s₀ : ℝ} {W V : ℝ≥0→Ω→ℝ} (hs : 0<s₀)
    (hW : MathFinBridge.BrownianOn P F T W) (hV : StronglyAdapted F V) (d : HestonPriceVarianceData P V) :
    ∃ S, IsHestonPriceSolution P F T s₀ W V S := by
  obtain ⟨K,hK⟩ := d.mean_bound
  obtain ⟨_,_,S,_,_,_,_,_,_,hSp,hSc,hS₀,hSpos,hS⟩ :=
    exists_heston_price_sde hW hV d.continuous d.nonnegative d.integrable hK hs
  exact ⟨S,hSp,hSc,hS₀,hSpos,_,hS⟩

/-- Theorem 1.1 including its price consequence for every admissible
correlation, with a single pair of noises for both price equations. -/
theorem theorem1_1_full : FullRoughHestonTheorem := by
  intro T α v₀ κ θ σ ρ s₀ hT hα hα' hv hκ hθ hσ hρ hs
  have h := regularHestonPair_of_explicitLebesgueUniformGap
    (explicitLebesgueUniformGap_of_birthLowerBound explicitLebesgueBirthLowerBound_proved)
    T α v₀ κ θ σ hT hα hα' hv hκ hθ hσ
  obtain ⟨Ω,m,P,F,B,W,X,Y,hP,hFc,hFr,hD,hX,hY,hsep,dx,dy⟩ := h.correlated ρ hρ
  let _ : MeasurableSpace Ω := m
  let _ : IsProbabilityMeasure P := hP
  let _ : F.IsComplete P := hFc
  let _ : F.IsRightContinuous := hFr
  obtain ⟨Sx,hSx⟩ := price_for_regular_variance hs hD.price_driver hX.1 dx
  obtain ⟨Sy,hSy⟩ := price_for_regular_variance hs hD.price_driver hY.1 dy
  exact ⟨Ω,m,P,F,B,W,X,Y,Sx,Sy,hP,hFc,hFr,hD,ito_equation_for_regular_variance hD.variance_driver hα hα' hX dx,
    ito_equation_for_regular_variance hD.variance_driver hα hα' hY dy,hX,hY,hSx,hSy,hsep⟩

#print axioms theorem1_1_full

end RoughHeston
