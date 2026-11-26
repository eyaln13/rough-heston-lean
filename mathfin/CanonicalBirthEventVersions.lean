import CanonicalBirthProbabilities
import ExplicitLebesguePulseLaw

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston

/-- Pointwise changes on a physical null set also agree on the genuine
positive-probability completed birth trace. -/
theorem ae_physical_completed_birthTrace {Ω : Type*} {m : MeasurableSpace Ω}
    {P : Measure Ω} {A : Set Ω} (hA : MeasurableSet[m] A) {f : Ω→Prop}
    (hf : ∀ᵐ p ∂P,f p) :
    let _ : MeasurableSpace Ω := physicalCompletedSpace P
    ∀ᵐ p : A ∂birthTraceLaw (physicalCompletedMeasure P) A,f p := by
  let Pc := physicalCompletedMeasure P
  have hAm : MeasurableSet[physicalCompletedSpace P] A := physical_ambient_le_completion P A hA
  let _ : MeasurableSpace Ω := physicalCompletedSpace P
  let Q := boundaryConditionedMeasure Pc A
  have hPres : MeasurePreserving (Subtype.val : A→Ω) (birthTraceLaw Pc A) Q :=
    ⟨measurable_subtype_coe,birthTraceLaw_map hAm⟩
  have hAC : Q ≪ Pc :=
    ((Measure.AbsolutelyContinuous.refl (Pc.restrict A)).smul_left _).trans
      Measure.restrict_le_self.absolutelyContinuous
  have hh : ∀ᵐ p ∂Pc,f p := hf
  exact hPres.quasiMeasurePreserving.ae (hAC.ae_le hh)

namespace FractionalFixedMeshLaw

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
  {α κ σ : ℝ} {v : Option ι→ℝ} {β : Option ι→ℝ≥0→ℝ}
  (L : FractionalFixedMeshLaw T α κ σ v β)
local notation "Path" => CanonicalPath T (CoupledPhysicalState ι)

/-- The adapted version used to enforce the exact initial age-zero value
agrees simultaneously at all later ages with the physical coordinate. -/
theorem pulseAge_ae_eq_physical {i : ι} {τ : ℝ≥0} {ε d : ℝ}
    (hα : α<1) (hκ : 0≤κ) (hτ : τ≤T) (hv : v (some i)=0)
    (hβ : β (some i)=translatedPulseRate τ ε d) :
    ∀ᵐ p ∂(L.law:Measure Path), ∀ s,
      canonicalPulseAgeVariance T τ i (v (some i)) s p=canonicalPhysicalVariance T (some i) (τ+s) p := by
  have hInv := L.inverse (some i)
  rw [hβ] at hInv
  have hpre := canonical_pulse_zero_through_birth hα hκ hv L.law L.starts L.nonnegative hτ hInv
    (L.residualMartingale (some i))
  filter_upwards [hpre,canonicalRegularVariance_ae_paths L.starts L.nonnegative (some i)] with p hp hV s
  unfold canonicalPulseAgeVariance
  rw [ite_eq_left (hp.1 τ le_rfl),hV]

end FractionalFixedMeshLaw

theorem lebesguePulseDuration_le_of_mass_le {α ε r : ℝ}
    (hα : 0<α) (hε : 0≤ε) (hr : 0≤r) (hεr : ε≤r^α) :
    lebesguePulseDuration α ε≤r := by
  unfold lebesguePulseDuration
  have he := Real.rpow_le_rpow hε hεr (by positivity : 0≤1/α)
  rw [← Real.rpow_mul hr,one_div,mul_inv_cancel₀ hα.ne',Real.rpow_one] at he
  simpa only [one_div] using he

#print axioms ae_physical_completed_birthTrace
#print axioms FractionalFixedMeshLaw.pulseAge_ae_eq_physical
#print axioms lebesguePulseDuration_le_of_mass_le

end RoughHeston
