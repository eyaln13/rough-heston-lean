import LaplaceBoundary
import Verification

open MeasureTheory Filter Set
open scoped MeasureTheory Topology

namespace RoughHeston

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- A nonnegative stopped transform bounds the probability of being
positive before the stopping time. At terminal observations inside
the event S, its value agrees with the Laplace complement. -/
theorem stopped_positive_le_of_laplace_test
    {S : Set Ω} (hS : MeasurableSet S) {Y : Ω → ℝ} (hY : Measurable Y)
    (hY₀ : ∀ ω, 0 ≤ Y ω) {Z : ℕ → Ω → ℝ} {C : ℝ}
    (hZi : ∀ n, Integrable (Z n) μ) (hZ₀ : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ Z n ω)
    (hterminal : ∀ n, ∀ ω ∈ S, Z n ω = 1 - Real.exp (-(n : ℝ) * Y ω))
    (hmean : ∀ n, (∫ ω, Z n ω ∂μ) ≤ C) :
    μ.real (S ∩ {ω | 0 < Y ω}) ≤ C := by
  have hp : (μ.restrict S).real {ω | 0 < Y ω} ≤ C := by
    apply positive_probability_of_laplace_bounds hY hY₀
    intro n
    rw [setIntegral_congr_fun hS (fun ω hω => (hterminal n ω hω).symm)]
    exact (setIntegral_le_integral (hZi n) (hZ₀ n)).trans (hmean n)
  rw [measureReal_restrict_apply (measurableSet_lt measurable_const hY), inter_comm] at hp
  exact hp

noncomputable def occupationEnvelope (r γ s : ℝ) : ℝ :=
  s⁻¹ * (r / s) ^ (3 * γ)

private theorem occupationEnvelope_nonneg {r γ s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    0 ≤ occupationEnvelope r γ s :=
  mul_nonneg (inv_nonneg.mpr hs.le) (Real.rpow_nonneg (div_nonneg hr.le hs.le) _)

private theorem occupationEnvelope_mul_power_eq {r γ η s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    occupationEnvelope r γ s * s ^ η =
      r ^ (3 * γ) * s ^ (η - 3 * γ - 1) := by
  unfold occupationEnvelope
  rw [Real.div_rpow hr.le hs.le, div_eq_mul_inv, ← Real.rpow_neg hs.le]
  have h := Real.rpow_add hs (-(3 * γ)) η
  have h' := Real.rpow_add hs (-1) (-(3 * γ) + η)
  have hneg : s⁻¹ = s ^ (-1 : ℝ) := (Real.rpow_neg_one s).symm
  calc
    _ = r ^ (3 * γ) * (s⁻¹ * (s ^ (-(3 * γ)) * s ^ η)) := by ring
    _ = _ := by rw [hneg, ← h, ← h']; congr 2; ring

/-- The stopped occupation bound and the envelope give the integrable
quadratic drift cost. The singularity of the envelope is compensated by
the power decay of the active-event probability. -/
theorem stopped_occupation_cost_bound {r η γ C D : ℝ}
    (hr : 0 < r) (hgap : 3 * γ < η) (hC : 0 ≤ C) (_hD : 0 ≤ D)
    {J : Set (ℝ × Ω)} (hJ : MeasurableSet J) {cost : ℝ → Ω → ℝ}
    (hcost : Measurable (Function.uncurry cost))
    (hc₀ : ∀ s ∈ Ioc (0 : ℝ) r, ∀ ω, 0 ≤ cost s ω)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) r, ∀ ω,
      cost s ω ≤ {ω' | (s, ω') ∈ J}.indicator
        (fun _ => C * occupationEnvelope r γ s) ω)
    (hocc : ∀ s ∈ Ioc (0 : ℝ) r, μ.real {ω | (s, ω) ∈ J} ≤ D * s ^ η) :
    let ν := volume.restrict (Ioc (0 : ℝ) r)
    Integrable (Function.uncurry cost) (ν.prod μ) ∧
      (∫ ω, (∫ s in Ioc (0 : ℝ) r, cost s ω) ∂μ) ≤ C * D * r ^ η / (η - 3 * γ) := by
  dsimp only
  let ν := volume.restrict (Ioc (0 : ℝ) r)
  let w (s : ℝ) := C * D * (r ^ (3 * γ) * s ^ (η - 3 * γ - 1))
  have hw : Integrable w ν := by
    have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le hr.le).mp
      (intervalIntegral.intervalIntegrable_rpow' (r := η - 3 * γ - 1) (by linarith))
    exact (hi.const_mul (r ^ (3 * γ))).const_mul (C * D)
  have hcostI (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) r) :
      Integrable (cost s) μ ∧ (∫ ω, cost s ω ∂μ) ≤ w s := by
    let A := {ω | (s, ω) ∈ J}
    have hA : MeasurableSet A := hJ.preimage (measurable_const.prodMk measurable_id)
    let d := C * occupationEnvelope r γ s
    have hd : 0 ≤ d := mul_nonneg hC (occupationEnvelope_nonneg hr hs.1)
    have hdI : Integrable (A.indicator (fun _ => d)) μ := (integrable_const d).indicator hA
    have hsm : AEStronglyMeasurable (cost s) μ :=
      (hcost.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    have hci : Integrable (cost s) μ := hdI.mono' hsm (ae_of_all μ fun ω => by
      rw [Real.norm_of_nonneg (hc₀ s hs ω)]
      exact hbound s hs ω)
    refine ⟨hci, ?_⟩
    calc
      _ ≤ ∫ ω, A.indicator (fun _ => d) ω ∂μ :=
        integral_mono hci hdI (hbound s hs)
      _ = d * μ.real A := by rw [integral_indicator hA, setIntegral_const, smul_eq_mul, mul_comm]
      _ ≤ d * (D * s ^ η) := mul_le_mul_of_nonneg_left (hocc s hs) hd
      _ = w s := by
        dsimp only [d, w]
        rw [show C * occupationEnvelope r γ s * (D * s ^ η) =
          C * D * (occupationEnvelope r γ s * s ^ η) by ring,
          occupationEnvelope_mul_power_eq hr hs.1]
  have hcostNorm : Integrable (fun s => ∫ ω, ‖cost s ω‖ ∂μ) ν := by
    refine hw.mono_nonneg hcost.aestronglyMeasurable.norm.integral_prod_right'
      (ae_of_all ν fun _ => integral_nonneg fun _ => norm_nonneg _) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have he : (∫ ω, ‖cost s ω‖ ∂μ) = ∫ ω, cost s ω ∂μ := integral_congr_ae
      (ae_of_all μ fun ω => Real.norm_of_nonneg (hc₀ s hs ω))
    rw [he]
    exact (hcostI s hs).2
  have hprod : Integrable (Function.uncurry cost) (ν.prod μ) :=
    (integrable_prod_iff hcost.aestronglyMeasurable).2
      ⟨(ae_restrict_mem measurableSet_Ioc).mono fun s hs => (hcostI s hs).1, hcostNorm⟩
  refine ⟨hprod, ?_⟩
  rw [← integral_integral_swap hprod]
  calc
    _ ≤ ∫ s, w s ∂ν := integral_mono_ae hprod.integral_prod_left hw
      ((ae_restrict_mem measurableSet_Ioc).mono fun s hs => (hcostI s hs).2)
    _ = _ := by
      dsimp only [w, ν]
      rw [integral_const_mul, integral_const_mul, ← intervalIntegral.integral_of_le hr.le,
        integral_rpow (Or.inl (by linarith : -1 < η - 3 * γ - 1))]
      have hpos : 0 < η - 3 * γ := sub_pos.mpr hgap
      rw [show η - 3 * γ - 1 + 1 = η - 3 * γ by ring, Real.zero_rpow hpos.ne', sub_zero,
        ← mul_div_assoc, ← Real.rpow_add hr, show 3 * γ + (η - 3 * γ) = η by ring, mul_div_assoc]

end RoughHeston

#print axioms RoughHeston.stopped_positive_le_of_laplace_test
#print axioms RoughHeston.stopped_occupation_cost_bound
