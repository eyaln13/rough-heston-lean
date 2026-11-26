import JointDyadicIntegral

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A continuous process with a square-integrable uniform path bound
has a continuous Bochner L² representative and uniformly integrable slices. -/
theorem cluster_continuous_L2_path_of_dominated {U : ℝ≥0 → Ω → ℝ} {D : Ω → ℝ}
    [IsFiniteMeasure P] (hD : MemLp D 2 P)
    (hU : ∀ t, Measurable (U t))
    (hUc : ∀ᵐ ω ∂P, Continuous (fun t => U t ω))
    (hBound : ∀ᵐ ω ∂P, ∀ t, ‖U t ω‖ ≤ ‖D ω‖) :
    (∀ t, Integrable (U t) P) ∧ (∀ t, (∫ ω, U t ω ∂P) ≤ ∫ ω, ‖D ω‖ ∂P) ∧
      ∃ v : ℝ → Lp ℝ 2 P, Continuous v ∧ ∀ s, ⇑(v s) =ᵐ[P] U s.toNNReal := by
  have hU₂ (t : ℝ≥0) : MemLp (U t) 2 P :=
    hD.mono (hU t).aestronglyMeasurable (hBound.mono fun _ h => h t)
  have hUi (t : ℝ≥0) : Integrable (U t) P := (hU₂ t).integrable one_le_two
  refine ⟨hUi, fun t => ?_, ?_⟩
  · exact integral_mono_ae (hUi t) (hD.norm.integrable one_le_two)
      (hBound.mono fun ω hω => (le_abs_self _).trans (hω t))
  · let v (t : ℝ≥0) := (hU₂ t).toLp (U t)
    have hvc : Continuous v := by
      rw [continuous_iff_continuousAt]
      intro t
      apply tendsto_nhds_iff_seq_tendsto.2
      intro u hu
      apply tendsto_iff_edist_tendsto_0.mpr
      simp only [v, Function.comp_apply, Lp.edist_toLp_toLp]
      apply tendsto_eLpNorm_two_dominated (hD.const_mul 2)
      · exact fun n => ((hU (u n)).sub (hU t)).aestronglyMeasurable
      · intro n
        filter_upwards [hBound] with ω hω
        change ‖U (u n) ω - U t ω‖ ≤ ‖(2 : ℝ) * D ω‖
        calc
          _ ≤ ‖U (u n) ω‖ + ‖U t ω‖ := norm_sub_le _ _
          _ ≤ ‖D ω‖ + ‖D ω‖ := add_le_add (hω _) (hω _)
          _ = _ := by rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), two_mul]
      · filter_upwards [hUc] with ω hω
        have hp := (hω.tendsto t).comp hu
        simpa only [Function.comp_apply, Pi.sub_apply, sub_self] using hp.sub (tendsto_const_nhds (x := U t ω))
    exact ⟨v ∘ Real.toNNReal, hvc.comp continuous_real_toNNReal, fun _ => (hU₂ _).coeFn_toLp⟩

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.cluster_continuous_L2_path_of_dominated
