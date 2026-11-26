import FiniteHorizonBrownianSampling
import GridQuadraticClock
import MathFin.Probability.Brownian.QuadraticVariationL2
import MathFin.Probability.Analysis.FiniteMeasureCauchySchwarz
import SizeBiasedBurst

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} {H : ℝ≥0} {B : ℝ≥0 → Ω → ℝ}

private def gridIndex (n k : ℕ) : Fin (n + 1) :=
  ⟨k % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩

private noncomputable def gridErrorSquare (n : ℕ) (v : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  ((∑ k ∈ Finset.range n, (x (gridIndex n (k + 1)) - x (gridIndex n k)) ^ 2) - v) ^ 2

private theorem gridErrorSquare_of_path (grid : ℕ →o ℝ≥0) (n : ℕ) (v : ℝ) (x : ℝ≥0 → ℝ) :
    gridErrorSquare n v (WithLp.toLp 2 (fun i : Fin (n + 1) => x (grid i.val))) =
      ((∑ k ∈ Finset.range n, (x (grid (k + 1)) - x (grid k)) ^ 2) - v) ^ 2 := by
  unfold gridErrorSquare
  congr 2
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  have hk₀ : k < n + 1 := hk'.trans n.lt_succ_self
  have hk₁ : k + 1 < n + 1 := Nat.succ_lt_succ hk'
  change (x (grid ((k + 1) % (n + 1))) - x (grid (k % (n + 1)))) ^ 2 = _
  rw [Nat.mod_eq_of_lt hk₀, Nat.mod_eq_of_lt hk₁]

/-- The exact Brownian grid-error variance holds on the supplied finite
horizon and over any starting time, via its sampled Gaussian law. -/
theorem finiteBrownian_gridQuadraticSum_L2_rate (hB : MathFinBridge.BrownianOn μ F H B)
    (grid : ℕ →o ℝ≥0) (n : ℕ) (hn : grid n ≤ H) :
    (∫ ω, (gridQuadraticSum grid B n ω - ((grid n : ℝ) - (grid 0 : ℝ))) ^ 2 ∂μ) =
      ∑ k ∈ Finset.range n, 2 * ((grid (k + 1) : ℝ) - (grid k : ℝ)) ^ 2 := by
  let v : ℝ := (grid n : ℝ) - (grid 0 : ℝ)
  let times (i : Fin (n + 1)) := grid i.val
  have ht (i : Fin (n + 1)) : times i ≤ H :=
    (grid.monotone (Nat.le_of_lt_succ i.isLt)).trans hn
  have hψ : Measurable (gridErrorSquare n v) := by
    unfold gridErrorSquare
    fun_prop
  have hX := hasLaw_sampled_brownianOn hB times ht
  have hRef := hasLaw_sampled_preBrownian isBrownianReal_brownian.toIsPreBrownianReal times
  have hEv := (hX.integral_comp hψ.aestronglyMeasurable).trans
    (hRef.integral_comp hψ.aestronglyMeasurable).symm
  simp only [Function.comp_def, times] at hEv
  have hEv' : (∫ ω, (gridQuadraticSum grid B n ω - v) ^ 2 ∂μ) =
      ∫ ω, (gridQuadraticSum grid brownian n ω - v) ^ 2 ∂gaussianLimit := by
    calc
      _ = ∫ ω, gridErrorSquare n v (WithLp.toLp 2 (fun i => B (grid i.val) ω)) ∂μ :=
        integral_congr_ae (ae_of_all _ fun ω => (gridErrorSquare_of_path grid n v (fun t => B t ω)).symm)
      _ = ∫ ω, gridErrorSquare n v (WithLp.toLp 2 (fun i => brownian (grid i.val) ω)) ∂gaussianLimit := hEv
      _ = _ := integral_congr_ae (ae_of_all _ fun ω => gridErrorSquare_of_path grid n v (fun t => brownian t ω))
  change (∫ ω, (gridQuadraticSum grid B n ω - v) ^ 2 ∂μ) = _
  rw [hEv']
  let shiftGrid (k : ℕ) := grid k - grid 0
  have hfirst (k : ℕ) : grid 0 ≤ grid k := grid.monotone (Nat.zero_le k)
  have harith (k : ℕ) : grid 0 + shiftGrid k = grid k := add_tsub_cancel_of_le (hfirst k)
  have hsReal (k : ℕ) : (shiftGrid k : ℝ) = (grid k : ℝ) - (grid 0 : ℝ) :=
    NNReal.coe_sub (hfirst k)
  have hmono : Monotone shiftGrid := fun _ _ hij => tsub_le_tsub_right (grid.monotone hij) _
  have hzero : shiftGrid 0 = 0 := tsub_self _
  have hmeas (t : ℝ≥0) : Measurable (fun ω => brownian (grid 0 + t) ω - brownian (grid 0) ω) :=
    (measurable_brownian _).sub (measurable_brownian _)
  have hR := MathFin.QuadraticVariationL2.sum_increment_sq_sub_sq_integral
    (isBrownianReal_brownian.toIsPreBrownianReal.shift (grid 0)) hmeas hmono hzero n
  simpa only [gridQuadraticSum, harith, hsReal, sub_sub_sub_cancel_right, v] using hR

private theorem finiteBrownian_gridQuadraticSum_memLp (hB : MathFinBridge.BrownianOn μ F H B)
    (grid : ℕ →o ℝ≥0) (n : ℕ) (hn : grid n ≤ H) :
    MemLp (gridQuadraticSum grid B n) 2 μ := by
  haveI : ENNReal.HolderTriple 4 4 2 := ⟨by
    have htwo : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have htop : (2 : ℝ≥0∞) ≠ ∞ := ENNReal.ofNat_ne_top
    rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num,
      ENNReal.mul_inv (Or.inl htwo) (Or.inl htop), ← two_mul, ← mul_assoc,
      ENNReal.mul_inv_cancel htwo htop, one_mul]⟩
  unfold gridQuadraticSum
  refine memLp_finsetSum _ fun k hk => ?_
  have hst : grid k ≤ grid (k + 1) := grid.monotone (Nat.le_succ k)
  have ht : grid (k + 1) ≤ H :=
    (grid.monotone (Nat.succ_le_of_lt (Finset.mem_range.mp hk))).trans hn
  have hmeas (r : ℝ≥0) : Measurable (B r) := ((hB.adapted r).mono (F.le r)).measurable
  have h : HasLaw (B (grid (k + 1)) - B (grid k))
      (gaussianReal 0 (grid (k + 1) - grid k)) μ :=
    ⟨((hmeas _).sub (hmeas _)).aemeasurable, hB.normal_increment _ _ hst ht⟩
  have h₄ : MemLp (B (grid (k + 1)) - B (grid k)) 4 μ := h.memLp (memLp_id_gaussianReal 4)
  have hprod : MemLp (fun ω => (B (grid (k + 1)) ω - B (grid k) ω) *
      (B (grid (k + 1)) ω - B (grid k) ω)) 2 μ := h₄.mul h₄
  simpa only [← pow_two] using hprod

omit [IsProbabilityMeasure μ] in
private theorem integral_abs_sizeBias_le {Z f : Ω → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hZ : Measurable Z) (hZ₀ : ∀ᵐ ω ∂μ, 0 ≤ Z ω) (hZ₂ : MemLp Z 2 μ) (hf₂ : MemLp f 2 μ) :
    (∫ ω, |f ω| ∂sizeBiasedLaw μ Z ε) ≤
      (Real.sqrt (∫ ω, Z ω ^ 2 ∂μ) * Real.sqrt (∫ ω, f ω ^ 2 ∂μ)) / ε := by
  rw [integral_sizeBiasedLaw_eq hε hZ hZ₀]
  apply div_le_div_of_nonneg_right _ hε.le
  have he : (∫ ω, Z ω * |f ω| ∂μ) = ∫ ω, |Z ω * f ω| ∂μ := by
    apply integral_congr_ae
    filter_upwards [hZ₀] with ω hω
    rw [abs_mul, abs_of_nonneg hω]
  rw [he]
  exact MathFin.integral_abs_mul_le_sqrt_mul_sqrt hZ₂ hf₂

/-- A terminal mass density in L² transfers the old Brownian quadratic
variation estimate to an L¹ bound under the actual size-biased law. -/
theorem sizeBiased_oldBrownian_gridQuadraticSum_L1_bound (hB : MathFinBridge.BrownianOn μ F H B)
    (grid : ℕ →o ℝ≥0) (n : ℕ) (hn : grid n ≤ H) {Z : Ω → ℝ} {ε : ℝ}
    (hε : 0 < ε) (hZ : Measurable Z) (hZ₀ : ∀ᵐ ω ∂μ, 0 ≤ Z ω) (hZ₂ : MemLp Z 2 μ) :
    (∫ ω, |gridQuadraticSum grid B n ω - ((grid n : ℝ) - (grid 0 : ℝ))| ∂sizeBiasedLaw μ Z ε) ≤
      (Real.sqrt (∫ ω, Z ω ^ 2 ∂μ) *
        Real.sqrt (∑ k ∈ Finset.range n, 2 * ((grid (k + 1) : ℝ) - (grid k : ℝ)) ^ 2)) / ε := by
  let f (ω : Ω) := gridQuadraticSum grid B n ω - ((grid n : ℝ) - (grid 0 : ℝ))
  have hf : MemLp f 2 μ := (finiteBrownian_gridQuadraticSum_memLp hB grid n hn).sub (memLp_const _)
  have h := integral_abs_sizeBias_le hε hZ hZ₀ hZ₂ hf
  rw [show (∫ ω, f ω ^ 2 ∂μ) = _ from finiteBrownian_gridQuadraticSum_L2_rate hB grid n hn] at h
  exact h

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.finiteBrownian_gridQuadraticSum_L2_rate
#print axioms RoughHeston.GirsanovPort.sizeBiased_oldBrownian_gridQuadraticSum_L1_bound
