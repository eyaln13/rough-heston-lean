import RegularHestonPair
import CanonicalInverseMartingaleData
import CanonicalSeparation

open MeasureTheory ProbabilityTheory Filter Set
open scoped MeasureTheory Topology NNReal ENNReal

namespace RoughHeston

/-- Continuous nonnegative extension of the first variance coordinate. -/
def canonicalFirstVariance : C(ℝ × ℝ, ℝ) :=
  ⟨fun x => max 0 x.1, continuous_const.max continuous_fst⟩

/-- Continuous nonnegative extension of the second variance coordinate. -/
def canonicalSecondVariance : C(ℝ × ℝ, ℝ) :=
  ⟨fun x => max 0 x.2, continuous_const.max continuous_snd⟩

private theorem norm_max_zero_le_norm (x : ℝ) : ‖max 0 x‖ ≤ ‖x‖ := by
  rw [Real.norm_of_nonneg (le_max_left _ _), Real.norm_eq_abs]
  exact max_le (abs_nonneg _) (le_abs_self _)

/-- The continuous density of the quadratic covariation of the two
variance martingales on the canonical pair path. -/
noncomputable def canonicalVarianceCovariance (σ : ℝ) (f k : C(ℝ × ℝ, ℝ)) :
    C(ℝ × ℝ, ℝ) :=
  ⟨fun x => (σ * Real.sqrt (f x)) * (σ * Real.sqrt (k x)),
    (continuous_const.mul (Real.continuous_sqrt.comp f.continuous)).mul
      (continuous_const.mul (Real.continuous_sqrt.comp k.continuous))⟩

variable {T : ℝ≥0} {α v₀ κ θ σ : ℝ}
  {μ : Measure (CanonicalPath T (ℝ × ℝ))} [IsProbabilityMeasure μ]

/-- The canonical invariance martingales and their compensated products
give the witnesses for the exact pathwise nonuniqueness statement on
the prescribed horizon. -/
theorem regular_heston_of_canonical_martingales
    (hT : 0 < T) (hα : 1 / 2 < α) (hα' : α < 1) (hσ : 0 < σ)
    (hpath : MemLp (fun p : CanonicalPath T (ℝ × ℝ) => ‖p‖) 2 μ)
    (hnonneg : ∀ᵐ p ∂μ, ∀ t ≤ T,
      0 ≤ (canonicalPathEval T t p).1 ∧ 0 ≤ (canonicalPathEval T t p).2)
    (hsep : 0 < μ {p | ∃ t ≤ T, (canonicalPathEval T t p).1 ≠ (canonicalPathEval T t p).2}) :
    let 𝒢 := canonicalPathNaturalFiltration (E := ℝ × ℝ) T
    let f := canonicalFirstVariance
    let k := canonicalSecondVariance
    let M := canonicalVarianceMartingale T α v₀ κ θ f
    let N := canonicalVarianceMartingale T α v₀ κ θ k
    let Cmm := canonicalVarianceCompensator T (canonicalVarianceCovariance σ f f)
    let Cmn := canonicalVarianceCompensator T (canonicalVarianceCovariance σ f k)
    let Cnn := canonicalVarianceCompensator T (canonicalVarianceCovariance σ k k)
    Martingale M 𝒢 μ → Martingale N 𝒢 μ →
    (∀ t, MemLp (M t) 2 μ) → (∀ t, MemLp (N t) 2 μ) →
    Martingale (fun t => M t * M t - Cmm t) 𝒢 μ →
    Martingale (fun t => M t * N t - Cmn t) 𝒢 μ →
    Martingale (fun t => N t * N t - Cnn t) 𝒢 μ →
    RegularHestonPair T α v₀ κ θ σ := by
  intro 𝒢 f k M N Cmm Cmn Cnn hM hN hM₂ hN₂ hmm hmn hnn
  let X := canonicalVarianceCoordinate T f
  let Y := canonicalVarianceCoordinate T k
  have hf (x : ℝ × ℝ) : ‖f x‖ ≤ ‖x‖ := (norm_max_zero_le_norm x.1).trans (le_max_left _ _)
  have hk (x : ℝ × ℝ) : ‖k x‖ ≤ ‖x‖ := (norm_max_zero_le_norm x.2).trans (le_max_right _ _)
  have dx := canonicalVarianceInverseMartingaleData hα'
    (fun x => le_max_left 0 x.1) hf hpath hM hM₂
  have dy := canonicalVarianceInverseMartingaleData hα'
    (fun x => le_max_left 0 x.2) hk hpath hN hN₂
  have hcomp (a b : C(ℝ × ℝ, ℝ)) :
      ∀ᵐ p ∂μ, ∀ t ≤ T,
      canonicalVarianceCompensator T (canonicalVarianceCovariance σ a b) t p =
        ∫ s in (0 : ℝ)..(t : ℝ),
          (σ * Real.sqrt (canonicalVarianceCoordinate T a s.toNNReal p)) *
            (σ * Real.sqrt (canonicalVarianceCoordinate T b s.toNNReal p)) := by
    refine ae_of_all μ fun p t ht => ?_
    unfold canonicalVarianceCompensator
    rw [min_eq_left ht]
    exact (intervalIntegral.integral_of_le (NNReal.coe_nonneg t)).symm
  have hsep' : 0 < μ {p | ∃ t ≤ T, X t p ≠ Y t p} := by
    apply hsep.trans_le
    apply measure_mono_ae
    filter_upwards [hnonneg] with p hp h
    obtain ⟨t, ht, hneq⟩ := h
    refine ⟨t, ht, ?_⟩
    have hp₁ := (hp t ht).1
    have hp₂ := (hp t ht).2
    simpa only [X, Y, canonicalVarianceCoordinate, f, k, canonicalFirstVariance, canonicalSecondVariance,
      ContinuousMap.coe_mk, max_eq_right hp₁, max_eq_right hp₂] using hneq
  obtain ⟨B, hB, hX, hY, hXY⟩ :=
    separated_heston_of_inverse_martingales hT hα hα' hσ dx dy hmm hmn hnn
      (by simpa only [pow_two] using hcomp f f) (hcomp f k) (by simpa only [pow_two] using hcomp k k) hsep'
  have reg {V U : ℝ≥0 → CanonicalPath T (ℝ × ℝ) → ℝ}
      (d : VarianceInverseMartingaleData μ (canonicalPathNaturalFiltration T) T α v₀ κ θ V U) :
      HestonPriceVarianceData (μ.prod gaussianLimit)
        (fun t (z : CanonicalPath T (ℝ × ℝ) × (ℝ≥0→ℝ)) => V t z.1) := by
    obtain ⟨A,hA⟩ := d.mean_bound
    exact ⟨fun z => d.path_continuous z.1,fun t z => d.nonnegative t z.1,
      fun t => (measurePreserving_fst (μ:=μ) (ν:=gaussianLimit)).integrable_comp_of_integrable (d.integrable t),
      ⟨A,fun t => by simpa only [integral_fun_fst,probReal_univ,one_smul] using hA t⟩⟩
  exact ⟨_, _, _, _, B, _, _, inferInstance, hB, hX, hY, hXY,reg dx,reg dy⟩

theorem separated_heston_of_canonical_martingales
    (hT : 0 < T) (hα : 1 / 2 < α) (hα' : α < 1) (hσ : 0 < σ)
    (hpath : MemLp (fun p : CanonicalPath T (ℝ × ℝ) => ‖p‖) 2 μ)
    (hnonneg : ∀ᵐ p ∂μ, ∀ t ≤ T,
      0 ≤ (canonicalPathEval T t p).1 ∧ 0 ≤ (canonicalPathEval T t p).2)
    (hsep : 0 < μ {p | ∃ t ≤ T, (canonicalPathEval T t p).1 ≠ (canonicalPathEval T t p).2}) :
    let 𝒢 := canonicalPathNaturalFiltration (E := ℝ × ℝ) T
    let f := canonicalFirstVariance
    let k := canonicalSecondVariance
    let M := canonicalVarianceMartingale T α v₀ κ θ f
    let N := canonicalVarianceMartingale T α v₀ κ θ k
    let Cmm := canonicalVarianceCompensator T (canonicalVarianceCovariance σ f f)
    let Cmn := canonicalVarianceCompensator T (canonicalVarianceCovariance σ f k)
    let Cnn := canonicalVarianceCompensator T (canonicalVarianceCovariance σ k k)
    Martingale M 𝒢 μ → Martingale N 𝒢 μ →
    (∀ t, MemLp (M t) 2 μ) → (∀ t, MemLp (N t) 2 μ) →
    Martingale (fun t => M t * M t - Cmm t) 𝒢 μ →
    Martingale (fun t => M t * N t - Cmn t) 𝒢 μ →
    Martingale (fun t => N t * N t - Cnn t) 𝒢 μ →
    ∃ (Ω : Type) (m : MeasurableSpace Ω) (P : @Measure Ω m)
      (F : Filtration ℝ≥0 m) (B X Y : ℝ≥0 → Ω → ℝ),
      IsProbabilityMeasure P ∧ IsBrownianOn P F T B ∧
        IsHestonVarianceSolution P F T α v₀ κ θ σ B X ∧
        IsHestonVarianceSolution P F T α v₀ κ θ σ B Y ∧
        0 < P {p | ∃ t ≤ T, X t p ≠ Y t p} := by
  intro 𝒢 f k M N Cmm Cmn Cnn hM hN hM₂ hN₂ hmm hmn hnn
  exact (regular_heston_of_canonical_martingales hT hα hα' hσ hpath hnonneg hsep hM hN hM₂ hN₂ hmm hmn hnn).variance

end RoughHeston

#print axioms RoughHeston.regular_heston_of_canonical_martingales
#print axioms RoughHeston.separated_heston_of_canonical_martingales
