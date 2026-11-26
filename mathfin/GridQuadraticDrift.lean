import GridQuadraticClock
import MathFin.Probability.Analysis.FiniteMeasureCauchySchwarz

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
theorem integrable_gridQuadraticSum_of_memLp {X : ℝ≥0 → Ω → ℝ}
    (hX : ∀ t, MemLp (X t) 2 μ) (grid : ℕ →o ℝ≥0) (n : ℕ) :
    Integrable (gridQuadraticSum grid X n) μ :=
  integrable_finsetSum _ fun k _ => ((hX (grid (k + 1))).sub (hX (grid k))).integrable_sq

omit [IsFiniteMeasure μ] in
/-- Cauchy–Schwarz bounds the L¹ effect of subtracting a drift
from a squared-increment sum. -/
theorem integral_abs_gridQuadraticSum_sub_le {B D : ℝ≥0 → Ω → ℝ}
    (hB : ∀ t, MemLp (B t) 2 μ) (hD : ∀ t, MemLp (D t) 2 μ)
    (grid : ℕ →o ℝ≥0) (n : ℕ) :
    let qB := gridQuadraticSum grid B n
    let qD := gridQuadraticSum grid D n
    let qN := gridQuadraticSum grid (fun t ω => B t ω - D t ω) n
    (∫ ω, |qN ω - qB ω| ∂μ) ≤ (∫ ω, qD ω ∂μ) +
      2 * Real.sqrt (∫ ω, qB ω ∂μ) * Real.sqrt (∫ ω, qD ω ∂μ) := by
  let qB := gridQuadraticSum grid B n
  let qD := gridQuadraticSum grid D n
  let qN := gridQuadraticSum grid (fun t ω => B t ω - D t ω) n
  let b (ω : Ω) (k : ℕ) := B (grid (k + 1)) ω - B (grid k) ω
  let d (ω : Ω) (k : ℕ) := D (grid (k + 1)) ω - D (grid k) ω
  have hB₀ (ω : Ω) : 0 ≤ qB ω := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hD₀ (ω : Ω) : 0 ≤ qD ω := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hBi : Integrable qB μ := integrable_gridQuadraticSum_of_memLp hB grid n
  have hDi : Integrable qD μ := integrable_gridQuadraticSum_of_memLp hD grid n
  have hNi : Integrable qN μ := integrable_gridQuadraticSum_of_memLp (fun t => (hB t).sub (hD t)) grid n
  have hsqrtB : MemLp (fun ω => Real.sqrt (qB ω)) 2 μ := by
    apply (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hBi.aestronglyMeasurable)).2
    exact hBi.congr (ae_of_all _ fun ω => (Real.sq_sqrt (hB₀ ω)).symm)
  have hsqrtD : MemLp (fun ω => Real.sqrt (qD ω)) 2 μ := by
    apply (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hDi.aestronglyMeasurable)).2
    exact hDi.congr (ae_of_all _ fun ω => (Real.sq_sqrt (hD₀ ω)).symm)
  have hCSint : Integrable (fun ω => Real.sqrt (qB ω) * Real.sqrt (qD ω)) μ :=
    hsqrtB.integrable_mul hsqrtD
  have hint : (∫ ω, Real.sqrt (qB ω) * Real.sqrt (qD ω) ∂μ) ≤
      Real.sqrt (∫ ω, qB ω ∂μ) * Real.sqrt (∫ ω, qD ω ∂μ) := by
    have h := MathFin.integral_abs_mul_le_sqrt_mul_sqrt hsqrtB hsqrtD
    simp_rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),
      Real.sq_sqrt (hB₀ _), Real.sq_sqrt (hD₀ _)] at h
    exact h
  have hpoint (ω : Ω) : |qN ω - qB ω| ≤
      qD ω + 2 * (Real.sqrt (qB ω) * Real.sqrt (qD ω)) := by
    have he : qN ω = qB ω + qD ω - 2 * ∑ k ∈ Finset.range n, b ω k * d ω k := by
      change (∑ k ∈ Finset.range n,
        ((B (grid (k + 1)) ω - D (grid (k + 1)) ω) - (B (grid k) ω - D (grid k) ω)) ^ 2) = _
      calc
        _ = ∑ k ∈ Finset.range n, (b ω k ^ 2 + d ω k ^ 2 - 2 * (b ω k * d ω k)) := by
          apply Finset.sum_congr rfl
          intro k _
          dsimp [b, d]
          ring
        _ = _ := by simp only [qB, qD, b, d, gridQuadraticSum,
          Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    have hsum := Real.sum_mul_le_sqrt_mul_sqrt (Finset.range n) (fun k => |b ω k|) (fun k => |d ω k|)
    simp only [← abs_mul, sq_abs] at hsum
    have habs : |∑ k ∈ Finset.range n, b ω k * d ω k| ≤ Real.sqrt (qB ω) * Real.sqrt (qD ω) :=
      (Finset.abs_sum_le_sum_abs _ _).trans hsum
    rw [show qN ω - qB ω = qD ω - 2 * ∑ k ∈ Finset.range n, b ω k * d ω k by rw [he]; ring]
    have htri := abs_add_le (qD ω) (-(2 * ∑ k ∈ Finset.range n, b ω k * d ω k))
    simp only [abs_neg, abs_mul, abs_of_nonneg (hD₀ ω), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at htri
    exact htri.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left habs (show (0 : ℝ) ≤ 2 from by norm_num)))
  change (∫ ω, |qN ω - qB ω| ∂μ) ≤ _
  calc
    _ ≤ ∫ ω, qD ω + 2 * (Real.sqrt (qB ω) * Real.sqrt (qD ω)) ∂μ :=
      integral_mono ((hNi.sub hBi).abs) (hDi.add (hCSint.const_mul 2)) hpoint
    _ = (∫ ω, qD ω ∂μ) + 2 * ∫ ω, Real.sqrt (qB ω) * Real.sqrt (qD ω) ∂μ := by
      rw [integral_add hDi (hCSint.const_mul 2), integral_const_mul]
    _ ≤ _ := by
      rw [mul_assoc 2]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hint (show (0 : ℝ) ≤ 2 from by norm_num))

/-- Subtracting a process with vanishing expected squared increments
preserves an L¹ quadratic variation limit. -/
theorem gridQuadraticSum_sub_L1_tendsto {B D : ℝ≥0 → Ω → ℝ} [IsProbabilityMeasure μ]
    (hB : ∀ t, MemLp (B t) 2 μ) (hD : ∀ t, MemLp (D t) 2 μ)
    (grid : ℕ → (ℕ →o ℝ≥0)) (n : ℕ → ℕ) (v : ℝ)
    (hOld : Tendsto (fun j => ∫ ω, |gridQuadraticSum (grid j) B (n j) ω - v| ∂μ) atTop (𝓝 0))
    (hDrift : Tendsto (fun j => ∫ ω, gridQuadraticSum (grid j) D (n j) ω ∂μ) atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm (gridQuadraticSum (grid j) (fun t ω => B t ω - D t ω) (n j) -
      fun _ => v) 1 μ) atTop (𝓝 0) := by
  let qB j := gridQuadraticSum (grid j) B (n j)
  let qD j := gridQuadraticSum (grid j) D (n j)
  let qN j := gridQuadraticSum (grid j) (fun t ω => B t ω - D t ω) (n j)
  let e j : ℝ := ∫ ω, |qB j ω - v| ∂μ
  let d j : ℝ := ∫ ω, qD j ω ∂μ
  have hIntB (j : ℕ) : Integrable (qB j) μ := integrable_gridQuadraticSum_of_memLp hB (grid j) (n j)
  have hIntN (j : ℕ) : Integrable (qN j) μ :=
    integrable_gridQuadraticSum_of_memLp (fun t => (hB t).sub (hD t)) (grid j) (n j)
  have hBmean (j : ℕ) : (∫ ω, qB j ω ∂μ) ≤ v + e j := by
    have he : (∫ ω, qB j ω ∂μ) - v = ∫ ω, qB j ω - v ∂μ := by
      rw [integral_sub (hIntB j) (integrable_const _), integral_const]
      simp
    have h := (le_abs_self (∫ ω, qB j ω - v ∂μ)).trans abs_integral_le_integral_abs
    rw [← he] at h
    exact (sub_le_iff_le_add.mp h).trans_eq (add_comm _ _)
  have hBound (j : ℕ) : (∫ ω, |qN j ω - v| ∂μ) ≤
      e j + d j + 2 * Real.sqrt (v + e j) * Real.sqrt (d j) := by
    have hshift := integral_abs_gridQuadraticSum_sub_le hB hD (grid j) (n j)
    have hTri : (∫ ω, |qN j ω - v| ∂μ) ≤ (∫ ω, |qN j ω - qB j ω| ∂μ) + e j := by
      have hdiff : Integrable (fun ω => |qN j ω - qB j ω|) μ := ((hIntN j).sub (hIntB j)).abs
      have hbi : Integrable (fun ω => |qB j ω - v|) μ := ((hIntB j).sub (integrable_const v)).abs
      have hni : Integrable (fun ω => |qN j ω - v|) μ := ((hIntN j).sub (integrable_const v)).abs
      have hsum := integral_mono hni (hdiff.add hbi) (fun ω => abs_sub_le (qN j ω) (qB j ω) v)
      change (∫ ω, |qN j ω - v| ∂μ) ≤ ∫ ω, |qN j ω - qB j ω| + |qB j ω - v| ∂μ at hsum
      rwa [integral_add hdiff hbi] at hsum
    have hnonneg : 0 ≤ (2 : ℝ) := by norm_num
    have hM := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hBmean j)) hnonneg) (Real.sqrt_nonneg (d j))
    linarith
  have hPhase : Tendsto (fun j => Real.sqrt (v + e j)) atTop (𝓝 (Real.sqrt v)) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp (hOld.const_add v)
    simpa only [Function.comp_def, add_zero] using h
  have hD0 : Tendsto (fun j => Real.sqrt (d j)) atTop (𝓝 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hDrift
    simpa only [Function.comp_def, Real.sqrt_zero] using h
  have hR : Tendsto (fun j => e j + d j + 2 * Real.sqrt (v + e j) * Real.sqrt (d j)) atTop (𝓝 0) := by
    have h := (hOld.add hDrift).add ((hPhase.const_mul 2).mul hD0)
    simpa only [mul_zero, add_zero] using h
  have hReal : Tendsto (fun j => ∫ ω, |qN j ω - v| ∂μ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hR
      (fun _ => integral_nonneg fun _ => abs_nonneg _) hBound
  have hNN := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hReal
  simp only [Function.comp_def, ENNReal.ofReal_zero] at hNN
  refine hNN.congr ?_
  intro j
  have hi := (hIntN j).sub (integrable_const v)
  have hi' : Integrable (fun ω => |qN j ω - v|) μ := hi.abs
  rw [eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable,
    ofReal_integral_eq_lintegral_ofReal hi' (ae_of_all _ fun _ => abs_nonneg _)]
  exact lintegral_congr fun ω => by
    change ENNReal.ofReal |qN j ω - v| = ‖qN j ω - v‖ₑ
    rw [← Real.norm_eq_abs, ofReal_norm]

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.integral_abs_gridQuadraticSum_sub_le
#print axioms RoughHeston.GirsanovPort.gridQuadraticSum_sub_L1_tendsto
