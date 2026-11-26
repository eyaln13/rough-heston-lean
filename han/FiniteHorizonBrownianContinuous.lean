import FiniteHorizonLevy

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace RoughHeston
namespace GirsanovPort

open MathFinBridge (BrownianOn)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {H : ℝ≥0} {X : ℝ≥0 → Ω → ℝ}

/-- Extend a finite-horizon Brownian version constantly beyond its
horizon and choose a globally continuous path on each sample. The
fixed-time agreements preserve the Brownian law on the original horizon. -/
theorem exists_continuous_modification_of_brownianOn (hX : BrownianOn μ F H X)
    (hnull : ∀ N : Set Ω, MeasurableSet N → μ N = 0 → MeasurableSet[F 0] N) :
    ∃ B : ℝ≥0 → Ω → ℝ, BrownianOn μ F H B ∧
      (∀ ω, Continuous (fun t => B t ω)) ∧ ∀ t ≤ H, B t =ᵐ[μ] X t := by
  classical
  obtain ⟨N, hcover, hNm, hNnull⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hX.continuous_paths)
  let good : Set Ω := Nᶜ
  have hgood₀ : MeasurableSet[F 0] good := (hnull N hNm hNnull).compl
  have hgood : ∀ᵐ ω ∂μ, ω ∈ good := ae_iff.mpr (by simpa [good] using hNnull)
  have hgood_cts (ω : Ω) (hω : ω ∈ good) : ContinuousOn (fun t => X t ω) (Icc 0 H) := by
    by_contra hbad
    exact hω (hcover hbad)
  let B (t : ℝ≥0) : Ω → ℝ := good.indicator (X (min t H))
  have hBa (t : ℝ≥0) (ht : t ≤ H) : B t =ᵐ[μ] X t := hgood.mono fun ω hω => by
    simp only [B, indicator_of_mem hω, min_eq_left ht]
  have hBcts (ω : Ω) : Continuous (fun t => B t ω) := by
    by_cases hω : ω ∈ good
    · simpa only [B, indicator_of_mem hω, Function.comp_def, id_eq] using
        (hgood_cts ω hω).comp_continuous (continuous_id.min continuous_const)
          (fun t => ⟨zero_le, min_le_right t H⟩)
    · simpa only [B, indicator_of_notMem hω] using
        (continuous_const : Continuous (fun _ : ℝ≥0 => (0 : ℝ)))
  have hBinc (s t : ℝ≥0) (hs : s ≤ H) (ht : t ≤ H) :
      (fun ω => X t ω - X s ω) =ᵐ[μ] (fun ω => B t ω - B s ω) := by
    filter_upwards [hBa s hs, hBa t ht] with ω hωs hωt
    rw [hωs, hωt]
  refine ⟨B, ⟨?_, (hBa 0 zero_le).trans hX.zero_at_start,
    ae_of_all μ (fun ω => (hBcts ω).continuousOn), ?_, ?_⟩, hBcts, hBa⟩
  · intro t
    exact ((hX.adapted (min t H)).mono (F.mono (min_le_left t H))).indicator
      (F.mono (show 0 ≤ t from zero_le) good hgood₀)
  · intro s t hst ht
    rw [← Measure.map_congr (hBinc s t (hst.trans ht) ht)]
    exact hX.normal_increment s t hst ht
  · intro s t hst ht
    have hold : @IndepFun Ω ℝ Ω mΩ (borel ℝ) (F s) (fun ω => X t ω - X s ω) id μ := by
      change Indep (MeasurableSpace.comap (fun ω => X t ω - X s ω) (borel ℝ))
        (MeasurableSpace.comap id (F s)) μ
      simpa only [MeasurableSpace.comap_id] using hX.independent_of_past s t hst ht
    have hnew := hold.congr (hBinc s t (hst.trans ht) ht) Filter.EventuallyEq.rfl
    change Indep (MeasurableSpace.comap (fun ω => B t ω - B s ω) (borel ℝ))
      (MeasurableSpace.comap id (F s)) μ at hnew
    simpa only [MeasurableSpace.comap_id] using hnew

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.exists_continuous_modification_of_brownianOn
