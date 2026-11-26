import CanonicalPathSupMoment

/-! Keeping the same power in the dyadic supremum estimate preserves
the factor of the rescaled immigration mass. -/

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston

/-- A random initial value and the dyadic increments may both have small
moments. The supremum bound retains their full order, with no additive
constant independent of those moments. -/
theorem canonical_sup_same_power_of_dyadic_moments {T : ℝ≥0} (hT : 0 < T)
    {n : ℕ} (hn : 0 < n) {ρ : ℝ≥0} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {μ : Measure (CanonicalPath T (ℝ × ℝ))} {C q : ℝ≥0∞}
    (hC : C ≠ ⊤) (hq : 2*q < 1)
    (hstart : Integrable (fun f : CanonicalPath T (ℝ × ℝ) => ‖f (canonicalEvalTime T 0)‖^n) μ)
    (hinc : ∀ j (k : Fin (2^j)),
      (∫⁻ f, weightedDyadicIncrement T n (dyadicMomentWeight n ρ) j k f ∂μ) ≤ C*q^j) :
    let G := 1+2*(ρ:ℝ)/(1-ρ)
    let B := C*(1-2*q)⁻¹
    Integrable (fun f => ‖f‖^n) μ ∧ (∫ f, ‖f‖^n ∂μ) ≤
      2^(n-1)*((∫ f, ‖f (canonicalEvalTime T 0)‖^n ∂μ)+G^n*B.toReal) := by
  dsimp only
  let J := dyadicIncrementPowerSum T n ρ
  let B := C*(1-2*q)⁻¹
  let G := 1+2*(ρ:ℝ)/(1-ρ)
  have hG : 0 ≤ G := by dsimp [G]; have : (ρ:ℝ) < 1 := hρ1; positivity
  have hB : B ≠ ⊤ := ENNReal.mul_ne_top hC (ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hq).ne')
  have hjm : Measurable J := measurable_dyadicIncrementPowerSum T n ρ
  have hj : (∫⁻ f,J f ∂μ) ≤ B := lintegral_dyadicIncrementPowerSum_le hinc
  have hjf := ne_top_of_le_ne_top hB hj
  have hae : ∀ᵐ f ∂μ, J f < ⊤ := ae_lt_top hjm hjf
  have hi := integrable_toReal_of_lintegral_ne_top hjm.aemeasurable hjf
  let A (f : CanonicalPath T (ℝ × ℝ)) := ‖f (canonicalEvalTime T 0)‖^n
  let F (f : CanonicalPath T (ℝ × ℝ)) := 2^(n-1)*(A f+G^n*(J f).toReal)
  have hFi : Integrable F μ := (hstart.add (hi.const_mul (G^n))).const_mul _
  have hpath : (fun f => ‖f‖^n) ≤ᵐ[μ] F := by
    filter_upwards [hae] with f hf
    have h := norm_canonicalPath_le_of_dyadicIncrementPowerSum hT
      (show 0 < (n:ℝ) by exact_mod_cast hn) hρ hρ1 f hf.ne
    let L := (J f).toNNReal
    have hn' := (pow_le_pow_left₀ (norm_nonneg f) h n).trans
      (add_pow_le (norm_nonneg _) (mul_nonneg hG (NNReal.coe_nonneg _)) n)
    have hr : ((L^((n:ℝ)⁻¹) : ℝ≥0):ℝ)^n = (J f).toReal := by
      rw [← NNReal.coe_pow,NNReal.rpow_inv_natCast_pow _ hn.ne']; rfl
    change ‖f‖^n ≤ 2^(n-1)*(A f + G^n*(J f).toReal)
    simpa only [A, mul_pow, ← show L = (dyadicIncrementPowerSum T n ρ f).toNNReal from rfl, hr]
      using hn'
  have hs : Integrable (fun f : CanonicalPath T (ℝ × ℝ) => ‖f‖^n) μ :=
    hFi.mono' (continuous_norm.pow n).aestronglyMeasurable
      (hpath.mono fun f h => by rwa [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)])
  have hmean := ENNReal.toReal_mono hB hj
  rw [← integral_toReal hjm.aemeasurable hae] at hmean
  refine ⟨hs, (integral_mono_ae hs hFi hpath).trans ?_⟩
  change (∫ f, 2^(n-1)*(A f+G^n*(J f).toReal) ∂μ) ≤ _
  rw [integral_const_mul,integral_add hstart (hi.const_mul _),integral_const_mul]
  gcongr

#print axioms canonical_sup_same_power_of_dyadic_moments

end RoughHeston
