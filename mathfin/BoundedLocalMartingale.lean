import BrownianMotion.StochasticIntegral.LocalMartingale
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace RoughHeston

/-- A uniform almost-sure bound on the paths upgrades a local
martingale to a martingale on the same filtration. -/
theorem martingale_of_bounded_localMartingale {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝒢 : Filtration ℝ≥0 m} {X : ℝ≥0 → Ω → ℝ}
    (had : StronglyAdapted 𝒢 X) (hX : IsLocalMartingale X 𝒢 μ)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ ω ∂μ, ∀ t, ‖X t ω‖ ≤ C) :
    Martingale X 𝒢 μ := by
  obtain ⟨τ, hτ, hloc⟩ := hX
  let Y (n : ℕ) := stoppedProcess (fun i => {ω | ⊥ < τ n ω}.indicator (X i)) (τ n)
  have hY (n : ℕ) : Martingale (Y n) 𝒢 μ := (hloc n).1
  have hYi (n : ℕ) (t : ℝ≥0) : ∀ᵐ ω ∂μ, ‖Y n t ω‖ ≤ C := by
    filter_upwards [hbound] with ω hω
    change ‖{ξ | ⊥ < τ n ξ}.indicator (X (min (t : WithTop ℝ≥0) (τ n ω)).untopA) ω‖ ≤ C
    by_cases hω' : ω ∈ {ξ | ⊥ < τ n ξ}
    · rw [indicator_of_mem hω']
      exact hω _
    · rw [indicator_of_notMem hω', norm_zero]
      exact hC
  have hlim (t : ℝ≥0) : ∀ᵐ ω ∂μ, Tendsto (fun n => Y n t ω) atTop (𝓝 (X t ω)) := by
    filter_upwards [hτ.tendsto_top] with ω hω
    have he : ∀ᶠ n in atTop, (t : WithTop ℝ≥0) < τ n ω :=
      hω.eventually (Ioi_mem_nhds (WithTop.coe_lt_top t))
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with n hn
    have hb : ⊥ < τ n ω := lt_of_le_of_lt bot_le hn
    change X t ω = stoppedProcess (fun i => {ξ | ⊥ < τ n ξ}.indicator (X i)) (τ n) t ω
    rw [stoppedProcess_eq_of_le hn.le, indicator_of_mem hb]
  have hi (t : ℝ≥0) : Integrable (X t) μ :=
    (integrable_const C).mono' ((had t).mono (𝒢.le t)).aestronglyMeasurable
      (hbound.mono fun _ h => h t)
  have htest (s t : ℝ≥0) (hst : s ≤ t) (A : Set Ω) (hA : MeasurableSet[𝒢 s] A) :
      (∫ ω in A, X s ω ∂μ) = ∫ ω in A, X t ω ∂μ := by
    have hYlim (u : ℝ≥0) : Tendsto (fun n => ∫ ω in A, Y n u ω ∂μ) atTop
        (𝓝 (∫ ω in A, X u ω ∂μ)) := by
      apply tendsto_integral_of_dominated_convergence (fun _ => C)
        (fun n => ((hY n).integrable u).aestronglyMeasurable.mono_measure Measure.restrict_le_self)
        (integrable_const C)
      · intro n
        exact ae_restrict_of_ae (hYi n u)
      · exact ae_restrict_of_ae (hlim u)
    exact tendsto_nhds_unique (hYlim s) ((hYlim t).congr fun n => (hY n).setIntegral_eq hst hA |>.symm)
  have hSub : Submartingale X 𝒢 μ :=
    submartingale_of_setIntegral_le had hi fun s t hst A hA => (htest s t hst A hA).le
  have hNeg : Submartingale (-X) 𝒢 μ :=
    submartingale_of_setIntegral_le had.neg (fun t => (hi t).neg) (fun s t hst A hA => by
      simpa only [Pi.neg_apply, integral_neg, neg_le_neg_iff] using (htest s t hst A hA).ge)
  exact martingale_iff.2 ⟨by simpa only [neg_neg] using hNeg.neg, hSub⟩

end RoughHeston

#print axioms RoughHeston.martingale_of_bounded_localMartingale
