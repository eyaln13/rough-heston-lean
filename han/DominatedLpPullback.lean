import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace RoughHeston.GirsanovPort

variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
  {P : Measure Ω} {Q : Measure S} {φ : S → Ω} {c : ℝ≥0∞}

private theorem dominatedPullback_ac (hdom : Measure.map φ Q ≤ c • P) :
    Measure.map φ Q ≪ P := Measure.absolutelyContinuous_of_le_smul hdom

private theorem dominatedPullback_memLp
    (hm : Measurable φ) (hc : c≠∞) (hdom : Measure.map φ Q ≤ c • P)
    (u : Lp ℝ 2 P) : MemLp (⇑u ∘ φ) 2 Q :=
  ((Lp.memLp u).of_measure_le_smul hc hdom).comp_measurePreserving ⟨hm,rfl⟩

/-- A bounded change of measure on the image makes pullback a
continuous linear map on the completed square-integrable spaces. -/
noncomputable def dominatedLpPullback (hm : Measurable φ) (hc : c≠∞)
    (hdom : Measure.map φ Q≤c•P) :
    Lp ℝ 2 P →L[ℝ] Lp ℝ 2 Q := by
  let hp : QuasiMeasurePreserving φ Q P := ⟨hm,dominatedPullback_ac hdom⟩
  let L (u : Lp ℝ 2 P) : Lp ℝ 2 Q :=
    (dominatedPullback_memLp hm hc hdom u).toLp (⇑u ∘ φ)
  have hL (u : Lp ℝ 2 P) : ⇑(L u) =ᵐ[Q] (⇑u ∘ φ) :=
    (dominatedPullback_memLp hm hc hdom u).coeFn_toLp
  let T : Lp ℝ 2 P →ₗ[ℝ] Lp ℝ 2 Q := {
    toFun := L
    map_add' := fun u v => by
      apply Lp.ext
      filter_upwards [hL (u+v),hL u,hL v,Lp.coeFn_add (L u) (L v),
        hp.ae (Lp.coeFn_add u v)] with x h₁ h₂ h₃ h₄ h₅
      change L (u+v) x = (L u+L v) x
      rw [h₁,h₄]
      simpa only [Function.comp_apply,Pi.add_apply,h₂,h₃] using h₅
    map_smul' := fun a u => by
      apply Lp.ext
      filter_upwards [hL (a•u),hL u,Lp.coeFn_smul a (L u),
        hp.ae (Lp.coeFn_smul a u)] with x h₁ h₂ h₃ h₄
      change L (a•u) x = (a•L u) x
      rw [h₁,h₃]
      simpa only [Function.comp_apply,Pi.smul_apply,h₂] using h₄
  }
  refine T.mkContinuous (c ^ (1/(2:ℝ≥0∞)).toReal).toReal (fun u => ?_)
  have hu := (Lp.memLp u).of_measure_le_smul hc hdom
  have he := eLpNorm_comp_measurePreserving (p:=2) hu.aestronglyMeasurable (show MeasurePreserving φ Q
    (Measure.map φ Q) from ⟨hm,rfl⟩)
  have hb := eLpNorm_le_of_measure_le_smul (f:=⇑u) (p:=2) hdom
  change ‖L u‖ ≤ _
  rw [show ‖L u‖ = (eLpNorm (⇑u ∘ φ) 2 Q).toReal from Lp.norm_toLp _ _, he,Lp.norm_def]
  rw [← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top
    (by simp [hc]) (Lp.memLp u).eLpNorm_lt_top.ne) hb

theorem dominatedLpPullback_ae (hm : Measurable φ) (hc : c≠∞)
    (hdom : Measure.map φ Q≤c•P) (u : Lp ℝ 2 P) :
    ⇑(dominatedLpPullback hm hc hdom u) =ᵐ[Q] ⇑u ∘ φ :=
  (dominatedPullback_memLp hm hc hdom u).coeFn_toLp

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.dominatedLpPullback_ae
