import CorrelatedBrownianProduct
import FixedHestonHorizon

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

open MathFin.ItoLocalMartingale (nullAugmentation)

section MeasurePreserving

variable {Ω Ω' : Type*} {m : MeasurableSpace Ω} {m' : MeasurableSpace Ω'}
  {μ : Measure Ω} {μ' : Measure Ω'} {φ : Ω' → Ω}
  {F : Filtration ℝ≥0 m} {F' : Filtration ℝ≥0 m'}
  {B V : ℝ≥0 → Ω → ℝ} {α v₀ κ θ σ : ℝ} {t T : ℝ≥0}

/-- A measure-preserving pullback preserves the stochastic convolution
defined by the two dyadic limits, including its L² representatives. -/
theorem IsHestonConvolutionAt.comp_measurePreserving {z : Ω → ℝ}
    (h : IsHestonConvolutionAt μ α t B V z) (hφ : MeasurePreserving φ μ' μ)
    (hB : ∀ s, Measurable (B s)) (hV : ∀ s, Measurable (V s)) :
    IsHestonConvolutionAt μ' α t (fun s => B s ∘ φ) (fun s => V s ∘ φ) (z ∘ φ) := by
  obtain ⟨hz, J, hJ, hlim⟩ := h
  let G := uniformDyadicGrids t
  let R (n j : ℕ) := dyadicTerminal G j (fun k => hestonCutoffWeight α t V n (G.grid j k)) B
  have hR (n j : ℕ) : Measurable (R n j) := by
    change Measurable (fun ω => R n j ω)
    simp only [R, dyadicTerminal, gridIntegral, runningSum, Finset.sum_apply, Pi.mul_apply, Pi.sub_apply]
    apply Finset.measurable_fun_sum
    intro k _
    exact (((hV _).sqrt.min measurable_const).const_mul _).mul ((hB _).sub (hB _))
  have hcomp (n j : ℕ) : dyadicTerminal G j
      (fun k => hestonCutoffWeight α t (fun s => V s ∘ φ) n (G.grid j k))
      (fun s => B s ∘ φ) = R n j ∘ φ := by
    funext ω
    simp only [R, dyadicTerminal, gridIntegral, runningSum, Finset.sum_apply, Pi.mul_apply,
      Pi.sub_apply, hestonCutoffWeight, Function.comp_apply]
  refine ⟨hz.comp_measurePreserving hφ, fun n => J n ∘ φ, fun n => ?_, ?_⟩
  · refine ⟨(hJ n).1.comp_measurePreserving hφ, (hJ n).2.congr (fun j => ?_)⟩
    rw [hcomp n j]
    change eLpNorm (R n j - J n) 2 μ = eLpNorm ((R n j - J n) ∘ φ) 2 μ'
    exact (eLpNorm_comp_measurePreserving ((hR n j).aestronglyMeasurable.sub
      (hJ n).1.aestronglyMeasurable) hφ).symm
  · refine hlim.congr fun n => ?_
    change eLpNorm (J n - z) 2 μ = eLpNorm ((J n - z) ∘ φ) 2 μ'
    exact (eLpNorm_comp_measurePreserving ((hJ n).1.aestronglyMeasurable.sub
      hz.aestronglyMeasurable) hφ).symm

/-- A pullback by a measure-preserving projection gives the same rough
Heston equation, adapted to the new past. -/
theorem IsHestonVarianceSolution.comp_measurePreserving
    (h : IsHestonVarianceSolution μ F T α v₀ κ θ σ B V)
    (hφ : MeasurePreserving φ μ' μ) (hB : StronglyAdapted F B)
    (hVa : StronglyAdapted F' (fun s => V s ∘ φ)) :
    IsHestonVarianceSolution μ' F' T α v₀ κ θ σ (fun s => B s ∘ φ) (fun s => V s ∘ φ) := by
  obtain ⟨hV, hc, hn, Z, hZ, he⟩ := h
  exact ⟨hVa, hφ.quasiMeasurePreserving.ae hc, hφ.quasiMeasurePreserving.ae hn, fun s => Z s ∘ φ,
    fun t ht => (hZ t ht).comp_measurePreserving hφ (fun s => ((hB s).mono (F.le s)).measurable)
      (fun s => ((hV s).mono (F.le s)).measurable), hφ.quasiMeasurePreserving.ae he⟩

/-- Stopping only the driver at the observation horizon leaves a variance
solution unchanged throughout that horizon. -/
theorem IsHestonVarianceSolution.freeze_driver
    (h : IsHestonVarianceSolution μ F T α v₀ κ θ σ B V) :
    IsHestonVarianceSolution μ F T α v₀ κ θ σ (fun t => B (min t T)) V := by
  obtain ⟨ha, hc, hn, Z, hZ, he⟩ := h
  refine ⟨ha, hc, hn, Z, fun t ht => (hZ t ht).congr_driver_on (fun s hs => ?_), he⟩
  rw [min_eq_left (hs.trans ht)]

end MeasurePreserving

section Extension

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℝ≥0 m} {T : ℝ≥0} {α v₀ κ θ σ : ℝ} {B V : ℝ≥0 → Ω → ℝ}

local notation "Paths" => (ℝ≥0 → ℝ)
local notation "P₀" => (μ.prod gaussianLimit)
local notation "Q" => (physicalCompletedMeasure P₀)
local notation "F" =>
  (physicalUsualFiltration P₀ (nullAugmentation (prodFiltration 𝒢 canonicalAuxiliaryFiltration) P₀))

theorem IsHestonVarianceSolution.on_correlated_product [IsProbabilityMeasure μ]
    (hB : StronglyAdapted 𝒢 B) (hV : IsHestonVarianceSolution μ 𝒢 T α v₀ κ θ σ B V) :
    IsHestonVarianceSolution Q F T α v₀ κ θ σ
      (fun t (z : Ω × Paths) => B (min t T) z.1) (fun t z => V t z.1) := by
  let : MeasurableSpace (Ω × Paths) := physicalCompletedSpace P₀
  have hBa : StronglyAdapted 𝒢 (fun t => B (min t T)) :=
    fun t => (hB _).mono (𝒢.mono (min_le_left _ _))
  apply hV.freeze_driver.comp_measurePreserving (correlated_product_fst_measurePreserving (μ := μ)) hBa
  apply StronglyAdapted.physicalUsual (P := P₀)
  intro t
  exact ((hV.1 t).comp_measurable (@measurable_fst Ω Paths (𝒢 t) (canonicalAuxiliaryFiltration t))).mono le_sup_left

/-- Both original variance processes and their positive separation event
survive the same extension that supplies the correlated Brownian pair. -/
theorem separated_hestonVariancePair_on_correlated_product [IsProbabilityMeasure μ]
    {X Y : ℝ≥0 → Ω → ℝ} (hB : IsBrownianOn μ 𝒢 T B)
    (hX : IsHestonVarianceSolution μ 𝒢 T α v₀ κ θ σ B X)
    (hY : IsHestonVarianceSolution μ 𝒢 T α v₀ κ θ σ B Y)
    (hsep : 0 < μ {ω | ∃ t ≤ T, X t ω ≠ Y t ω})
    (ρ : ℝ) (hρ : |ρ| ≤ 1) :
    let B' (t : ℝ≥0) (z : Ω × Paths) := B (min t T) z.1
    let C (t : ℝ≥0) (z : Ω × Paths) := brownian (min t T) z.2
    let W (t : ℝ≥0) (z : Ω × Paths) := ρ * B' t z + Real.sqrt (1 - ρ ^ 2) * C t z
    let X' (t : ℝ≥0) (z : Ω × Paths) := X t z.1
    let Y' (t : ℝ≥0) (z : Ω × Paths) := Y t z.1
    MathFinBridge.BrownianOn Q F T B' ∧ MathFinBridge.BrownianOn Q F T W ∧
    Martingale (fun t z => B' t z * W t z - ρ * ((min t T : ℝ≥0) : ℝ)) F Q ∧
    (∀ x y : ℝ, x ^ 2 + y ^ 2 = 1 → MathFinBridge.BrownianOn Q F T (fun t z => x * B' t z + y * C t z)) ∧
    IsHestonVarianceSolution Q F T α v₀ κ θ σ B' X' ∧
    IsHestonVarianceSolution Q F T α v₀ κ θ σ B' Y' ∧
    0 < Q {z | ∃ t ≤ T, X' t z ≠ Y' t z} := by
  intro B' C W X' Y'
  have hBm : MathFinBridge.BrownianOn μ 𝒢 T B :=
    ⟨hB.adapted, hB.zero_at_start, hB.continuous_paths, hB.normal_increment, hB.independent_of_past⟩
  obtain ⟨hb, _, hw, hcross, hp⟩ := brownianOn_correlated_product hBm ρ hρ
  refine ⟨hb, hw, hcross, hp, hX.on_correlated_product hB.adapted, hY.on_correlated_product hB.adapted, ?_⟩
  let A : Set Ω := {ω | ∃ t ≤ T, X t ω ≠ Y t ω}
  have he : {z : Ω × Paths | ∃ t ≤ T, X' t z ≠ Y' t z} = A ×ˢ (univ : Set Paths) := by
    ext z
    simp [A, X', Y']
  rw [he]
  change 0 < P₀ (A ×ˢ (univ : Set Paths))
  rw [Measure.prod_prod, measure_univ, mul_one]
  exact hsep

end Extension

#print axioms IsHestonConvolutionAt.comp_measurePreserving
#print axioms IsHestonVarianceSolution.on_correlated_product
#print axioms separated_hestonVariancePair_on_correlated_product

end RoughHeston
