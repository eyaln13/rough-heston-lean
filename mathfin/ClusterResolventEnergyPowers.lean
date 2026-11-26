import ClusterKernelBetaBound

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace RoughHeston

/-- Physical kernel energy, and kernel energy weighted by the
time-dependent lower-order moment, on the actual horizon T. -/
theorem cluster_resolvent_energy_power_bounds {T : ℝ≥0} (hT : 0 < T)
    {α σ D : ℝ} (hα : 1/2 < α) (hD : 0 ≤ D)
    {R : ℝ → ℝ} (hR : Measurable R)
    (hdom : ∀ x ∈ Ioc 0 (T:ℝ), |R x| ≤ 2*fractionalK α x) :
    let β := 2*α-1
    let A := (2*|σ|/Real.Gamma α)^2
    let w (s : ℝ≥0) := (σ*R ((T:ℝ)-(s:ℝ)))^2
    let c (s : ℝ≥0) := D*(s:ℝ)^(α-1)
    Integrable w (hestonTimeMeasure T) ∧
    (∫ s,w s ∂hestonTimeMeasure T) ≤ A*((T:ℝ)^β*(Real.Gamma 1*Real.Gamma β/Real.Gamma (1+β))) ∧
    Integrable (fun s => w s*c s) (hestonTimeMeasure T) ∧
    (∫ s,w s*c s ∂hestonTimeMeasure T) ≤ (A*D)*
      ((T:ℝ)^(α+β-1)*(Real.Gamma α*Real.Gamma β/Real.Gamma (α+β))) := by
  dsimp only
  let β := 2*α-1
  let A := (2*|σ|/Real.Gamma α)^2
  let w (s : ℝ≥0) := (σ*R ((T:ℝ)-(s:ℝ)))^2
  let c (s : ℝ≥0) := D*(s:ℝ)^(α-1)
  have hb : 0 < β := by dsimp [β]; linarith
  have ha : 0 < α := by linarith
  have hA : 0 ≤ A := sq_nonneg _
  have hw : Measurable w := by dsimp [w]; fun_prop
  have hc : Measurable c := by dsimp [c]; fun_prop
  have hpt (s : ℝ≥0) (hs : s < T) : w s ≤ A*((T:ℝ)-(s:ℝ))^(β-1) := by
    have hx : 0 < (T:ℝ)-(s:ℝ) := sub_pos.mpr (show (s:ℝ)<T from hs)
    exact fractional_square_noise_weight ha hx (hdom _ ⟨hx,sub_le_self _ s.coe_nonneg⟩)
  have hb1 := heston_time_integral_beta_bound hT (a:=1) (by norm_num) hb hA hw
    (fun s _ hs => ⟨sq_nonneg _, by simpa only [sub_self, Real.rpow_zero,one_mul] using hpt s hs⟩)
  have hbw := heston_time_integral_beta_bound hT ha hb (mul_nonneg hA hD) (hw.mul hc)
    (fun s _ hs => by
      have hn : 0 ≤ c s := mul_nonneg hD (Real.rpow_nonneg s.coe_nonneg _)
      refine ⟨mul_nonneg (sq_nonneg _) hn, (mul_le_mul_of_nonneg_right (hpt s hs) hn).trans_eq ?_⟩
      dsimp [c]; ring)
  exact ⟨hb1.1, by simpa only [show 1+β-1=β by ring] using hb1.2, hbw.1, hbw.2⟩

#print axioms cluster_resolvent_energy_power_bounds

end RoughHeston
