import PhysicalBirthStopCertificate
import PhysicalMeshProductModels

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace RoughHeston

open GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 m} {T S : ℝ≥0} {α κ σ b v₀ : ℝ} {B M Y C : ℝ≥0 → Ω → ℝ}

/-- The actual companion inverse includes the singular contribution of
its initial variance. Its Brownian integral is evaluated on the same
physical horizon as the affine test. -/
theorem HestonBoundaryProcess.physicalStopData
    (h : HestonBoundaryProcess P F T α κ (σ^2/2) b v₀ M Y C)
    (hα : 0<α) (hα' : α<1) (hb : 0≤b) (hv : 0≤v₀) (hST : S≤T)
    (hB : MathFinBridge.BrownianOn P F S B) (hBm : Martingale B F P) (hB₂ : ∀ t, MemLp (B t) 2 P)
    (hBs : Martingale (fun t ω => B t ω^2-((min t S:ℝ≥0):ℝ)) F P)
    (hY₄ : ∃ K : ℝ, ∀ t, Integrable (fun ω => Y t ω^4) P ∧ (∫ ω,Y t ω^4 ∂P)≤K)
    (hAmp : HasAmplitudeCutoffIntegral F P S B M (varianceAmplitude σ Y)) :
    PhysicalBirthStopCertificate P F S α κ σ B M Y C (fun u => b+v₀*fractionalL α u) := by
  refine ⟨hB,hB₂,hBm,hBs,?_,h.martingale,h.martingale_memLp,h.martingale_continuous,h.martingale_zero,
    h.variance_adapted.isStronglyPredictable_of_leftContinuous
      (fun ω _ => (h.variance_continuous ω).continuousAt.continuousWithinAt),
    h.variance_continuous,h.variance_nonnegative,⟨v₀,h.variance_initial_bound⟩,hY₄,
    h.compensated_square,h.compensator_integrable,h.compensator_monotone,?_,?_,hAmp⟩
  · intro t ht _
    apply affine_input_on_of_initial_and_bounded_rate (C:=‖b‖) hα hα' (NNReal.coe_pos.mpr ht) hv measurable_const
    · exact fun _ _ => hb
    · exact fun _ _ => le_rfl
  · intro t ht
    simpa only [show 2*(σ^2/2)=σ^2 by ring] using h.compensator t (ht.trans hST)
  · filter_upwards [h.inverse] with ω hw t ht
    exact hw t ⟨ht.1,ht.2.trans (NNReal.coe_le_coe.mpr hST)⟩

#print axioms HestonBoundaryProcess.physicalStopData

end RoughHeston
