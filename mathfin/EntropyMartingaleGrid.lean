import EntropyBregman
import GridQuadraticClock
import Mathlib.Probability.Martingale.Basic

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace RoughHeston
namespace GirsanovPort

variable {Ω ι : Type*} [m : MeasurableSpace Ω] [Preorder ι] {μ : Measure Ω} [IsFiniteMeasure μ]
  {F : Filtration ι m} {Z : ι → Ω → ℝ}

noncomputable def regularizedEntropy (η x : ℝ) : ℝ := (x + η) * Real.log (x + η)

private theorem abs_log_add_one_le {x η : ℝ} (hη : 0 < η) (hx : 0 ≤ x) :
    |Real.log (x + η) + 1| ≤ |x| + (η + η⁻¹ + 1) := by
  have hp : 0 < x + η := by positivity
  have hUpper := Real.log_le_self hp.le
  have hLower := Real.log_le_self (inv_nonneg.mpr hp.le)
  rw [Real.log_inv] at hLower
  have hInv : (x + η)⁻¹ ≤ η⁻¹ := inv_anti₀ hη (le_add_of_nonneg_left hx)
  rw [abs_of_nonneg hx]
  refine abs_le.mpr ⟨?_, ?_⟩
  · linarith
  · linarith [inv_nonneg.mpr hη.le]

private theorem regularizedEntropyTangent_memLp {X : Ω → ℝ}
    (hX : MemLp X 2 μ) (hX₀ : ∀ᵐ ω ∂μ, 0 ≤ X ω) {η : ℝ} (hη : 0 < η) :
    MemLp (fun ω => Real.log (X ω + η) + 1) 2 μ := by
  have hb : MemLp (fun ω => |X ω| + (η + η⁻¹ + 1)) 2 μ :=
    hX.abs.add (memLp_const _)
  refine hb.mono' ((hX.aemeasurable.add_const η).log.add_const 1).aestronglyMeasurable ?_
  exact hX₀.mono fun ω hω => by
    simpa only [Real.norm_eq_abs] using abs_log_add_one_le hη hω

/-- For an L² nonnegative martingale, each conditional entropy increment
bounds the squared increment averaged with the maximum endpoint denominator. -/
theorem integral_entropyWeightedIncrement_le (hZ : Martingale Z F μ)
    (hZ₂ : ∀ t, MemLp (Z t) 2 μ) (hZ₀ : ∀ t, ∀ᵐ ω ∂μ, 0 ≤ Z t ω)
    {s t : ι} (hst : s ≤ t) {η : ℝ} (hη : 0 < η) :
    (∫ ω, (Z t ω - Z s ω) ^ 2 / (2 * (max (Z s ω) (Z t ω) + η)) ∂μ) ≤
      (∫ ω, regularizedEntropy η (Z t ω) ∂μ) -
        ∫ ω, regularizedEntropy η (Z s ω) ∂μ := by
  let A (ω : Ω) := Real.log (Z s ω + η) + 1
  let Δ (ω : Ω) := Z t ω - Z s ω
  have hA₂ : MemLp A 2 μ := regularizedEntropyTangent_memLp (hZ₂ s) (hZ₀ s) hη
  have hΔ₂ : MemLp Δ 2 μ := (hZ₂ t).sub (hZ₂ s)
  have hΔ₁ : Integrable Δ μ := hΔ₂.integrable one_le_two
  have hAΔ : Integrable (fun ω => A ω * Δ ω) μ := hA₂.integrable_mul hΔ₂
  have hAadapted : StronglyMeasurable[F s] A := by
    let : MeasurableSpace Ω := F s
    exact (((hZ.stronglyAdapted s).measurable.add_const η).log.add_const 1).stronglyMeasurable
  have hMean : (∫ ω, A ω * Δ ω ∂μ) = 0 := by
    rw [← integral_condExp (F.le s)]
    have h := condExp_mul_of_stronglyMeasurable_left hAadapted hAΔ hΔ₁
    apply integral_eq_zero_of_ae
    filter_upwards [h, conditional_mean_martingale_increment hZ hst] with ω hw hd
    change μ[A * Δ | F s] ω = 0
    rw [hw, Pi.mul_apply, show μ[Δ | F s] ω = 0 from hd, mul_zero]
  have hEnt (r : ι) : Integrable (fun ω => regularizedEntropy η (Z r ω)) μ :=
    integrable_mulLog_of_nonnegative_L2 ((hZ₂ r).add (memLp_const η))
      ((hZ₀ r).mono fun _ hw => add_nonneg hw hη.le)
  let E (ω : Ω) := Δ ω ^ 2 / (2 * (max (Z s ω) (Z t ω) + η))
  have hm : AEStronglyMeasurable E μ := by
    dsimp [E]
    exact ((hΔ₂.aemeasurable.pow_const 2).div
      (aemeasurable_const.mul (((hZ₂ s).aemeasurable.max (hZ₂ t).aemeasurable).add_const η))).aestronglyMeasurable
  have hi : Integrable E μ := by
    refine (hΔ₂.integrable_sq.div_const (2 * η)).mono' hm ?_
    filter_upwards [hZ₀ s] with ω hs
    have hd : 2 * η ≤ 2 * (max (Z s ω) (Z t ω) + η) := by
      linarith [hs.trans (le_max_left (Z s ω) (Z t ω))]
    have hp := (show 0 < 2 * η by positivity).trans_le hd
    have hE₀ : 0 ≤ E ω := div_nonneg (sq_nonneg _) hp.le
    rw [Real.norm_eq_abs, abs_of_nonneg hE₀]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hd
  have hpt : ∀ᵐ ω ∂μ, E ω ≤ regularizedEntropy η (Z t ω) -
      regularizedEntropy η (Z s ω) - A ω * Δ ω := by
    filter_upwards [hZ₀ s, hZ₀ t] with ω hs ht
    have h := entropy_bregman_lower (show 0 < Z s ω + η by positivity)
      (show 0 < Z t ω + η by positivity)
      (add_le_add_left (le_max_left (Z s ω) (Z t ω)) η)
      (add_le_add_left (le_max_right (Z s ω) (Z t ω)) η)
    simpa only [E, regularizedEntropy, A, Δ, add_sub_add_right_eq_sub] using h
  have hf : Integrable (fun ω => regularizedEntropy η (Z t ω) -
      regularizedEntropy η (Z s ω) - A ω * Δ ω) μ := ((hEnt t).sub (hEnt s)).sub hAΔ
  have h := integral_mono_ae hi hf hpt
  have he1 : Integrable (fun ω => regularizedEntropy η (Z t ω) - regularizedEntropy η (Z s ω)) μ :=
    (hEnt t).sub (hEnt s)
  rw [integral_sub he1 hAΔ, integral_sub (hEnt t) (hEnt s), hMean, sub_zero] at h
  exact h

/-- The discrete entropy budget telescopes on any deterministic grid. -/
theorem sum_integral_entropyWeightedIncrement_le (hZ : Martingale Z F μ)
    (hZ₂ : ∀ t, MemLp (Z t) 2 μ) (hZ₀ : ∀ t, ∀ᵐ ω ∂μ, 0 ≤ Z t ω)
    (grid : ℕ →o ι) (n : ℕ) {η : ℝ} (hη : 0 < η) :
    (∑ k ∈ Finset.range n, ∫ ω, (Z (grid (k + 1)) ω - Z (grid k) ω) ^ 2 /
      (2 * (max (Z (grid k) ω) (Z (grid (k + 1)) ω) + η)) ∂μ) ≤
      (∫ ω, regularizedEntropy η (Z (grid n) ω) ∂μ) -
        ∫ ω, regularizedEntropy η (Z (grid 0) ω) ∂μ := by
  refine le_trans (Finset.sum_le_sum fun k _ =>
    integral_entropyWeightedIncrement_le hZ hZ₂ hZ₀ (grid.monotone (Nat.le_succ k)) hη) ?_
  exact (Finset.sum_range_sub (fun k => ∫ ω, regularizedEntropy η (Z (grid k) ω) ∂μ) n).le

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.sum_integral_entropyWeightedIncrement_le
