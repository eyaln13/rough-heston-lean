import JointDyadicIntegral
import ClippedDyadicGrid

open MeasureTheory ProbabilityTheory Filter Set
open scoped MeasureTheory ProbabilityTheory Topology NNReal ENNReal

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}

/-- Dyadic sums stopped at the observation time give the same Itô
integral as the one constructed on the shorter horizon. -/
theorem jointItoIntegralCLM_stopped_dyadic [IsFiniteMeasure μ] {T t : ℝ≥0} (htT : t ≤ T)
    (hM : Martingale M 𝒢 μ) (hM₂ : ∀ s, MemLp (M s) 2 μ)
    (hclock : Martingale (fun s ω => M s ω ^ 2 - ((min s t : ℝ≥0) : ℝ)) 𝒢 μ)
    {H : ℝ≥0 → Ω → ℝ} {C : ℝ}
    (hHa : StronglyAdapted 𝒢 H)
    (hHsm : StronglyMeasurable[𝒢.predictable] (Function.uncurry H))
    (hHcts : ∀ᵐ ω ∂μ, ContinuousOn (fun s => H s ω) (Icc 0 t))
    (hHB : ∀ s ω, ‖H s ω‖ ≤ C)
    (hH₂ : MemLp (Function.uncurry H) 2 (jointPredictableMeasure 𝒢 μ t)) :
    Tendsto (fun j => eLpNorm
      (gridIntegralProcess ((uniformDyadicGrids T).grid j)
        (fun k => H ((uniformDyadicGrids T).grid j k)) M (2 ^ j) t -
        (jointItoIntegralCLM t hM₂ (hH₂.toLp (Function.uncurry H)) : Ω → ℝ))
      2 μ) atTop (𝓝 0) := by
  let ν := (MathFin.ItoIntegralCLM.timeMeasureHorizon t).prod μ
  let G := clippedDyadicGrid T t
  let S (j : ℕ) : JointTBoundedSP t 𝒢 :=
    jointGridSP (G j) (n := 2 ^ j) (clippedDyadicGrid_terminal_vertex htT j).le
      (fun k => (hHa (G j k)).measurable) (fun k ω => hHB (G j k) ω)
  let U (j : ℕ) := Function.uncurry ⇑(S j).val
  have htime : ∀ᵐ z : ℝ≥0 × Ω ∂ν, z.1 ∈ Ioc 0 t :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
  have hcont : ∀ᵐ z : ℝ≥0 × Ω ∂ν, ContinuousOn (fun s => H s z.2) (Icc 0 t) :=
    Measure.quasiMeasurePreserving_snd.ae hHcts
  have he (j : ℕ) (z : ℝ≥0 × Ω) :
      U j z = ∑ k ∈ Finset.range (2 ^ j),
        (Ioc (G j k) (G j (k + 1))).indicator (fun _ => H (G j k) z.2) z.1 :=
    congrFun (jointGridSP_uncurry (G j) (n := 2 ^ j)
      (clippedDyadicGrid_terminal_vertex htT j).le
      (fun k => (hHa (G j k)).measurable) (fun k ω => hHB (G j k) ω)) z
  have hbd (j : ℕ) : ∀ᵐ z ∂ν, ‖U j z - H z.1 z.2‖ ≤ 2 * C := by
    filter_upwards [htime] with z hz
    have hzT : z.1 ∈ Ioc 0 T := ⟨hz.1, hz.2.trans htT⟩
    obtain ⟨k, _, _, hk⟩ := uniformDyadicStep_eq_coeff (fun s => H (min s t) z.2) hzT j
    rw [he j z, clippedDyadicGrid_step_eq hz.2 j (fun s => H s z.2), hk]
    have hsum := add_le_add (hHB (min ((uniformDyadicGrids T).grid j k) t) z.2) (hHB z.1 z.2)
    simpa only [two_mul] using (norm_sub_le _ _).trans hsum
  have hpoint : ∀ᵐ z ∂ν, Tendsto (fun j => U j z - H z.1 z.2) atTop (𝓝 0) := by
    filter_upwards [htime, hcont] with z hz hzc
    have huv : Tendsto (fun j => U j z) atTop (𝓝 (H z.1 z.2)) :=
      (tendsto_clippedDyadicGrid_step htT hz hzc).congr (fun j => (he j z).symm)
    simpa only [Pi.sub_def, sub_self] using huv.sub (tendsto_const_nhds (x := H z.1 z.2))
  refine (jointItoIntegralCLM_of_bounded_simple_limits t hM hM₂ hclock
    S hHsm hH₂ hbd hpoint).congr (fun j => ?_)
  rw [show jointItoSimple M (S j).val = gridIntegral (G j) (fun k => H (G j k)) M (2 ^ j) from
    jointItoSimple_jointGridSP M (G j) (n := 2 ^ j) (clippedDyadicGrid_terminal_vertex htT j).le
      (fun k => (hHa (G j k)).measurable) (fun k ω => hHB (G j k) ω)]
  rw [gridIntegral_clippedDyadicGrid_eq_stopped]

end RoughHeston

#print axioms RoughHeston.jointItoIntegralCLM_stopped_dyadic
