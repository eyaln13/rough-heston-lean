import CanonicalBirthEventVersions
import PhysicalMeshProductModels

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace RoughHeston
namespace FractionalFixedMeshLaw

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
  {α κ σ : ℝ} {v : Option ι → ℝ} {β : Option ι → ℝ≥0 → ℝ}
local notation "Path" => CanonicalPath T (CoupledPhysicalState ι)
local notation "Ω" => Path × (ℝ≥0 → ℝ)
local notation "G" => canonicalPathNaturalFiltration (E := CoupledPhysicalState ι) T

variable (L : FractionalFixedMeshLaw T α κ σ v β)

/-- Both physical-time changes, the focal increment, and the raw
separation event are identified on the same completed birth trace. -/
theorem physicalMeshBirthIdentities {i : ι} {τ H r : ℝ≥0} {ε d : ℝ}
    (hα : α<1) (hκ : 0≤κ) (hT : τ+H≤T) (hr : r≤H)
    (hv : v (some i)=0) (hβ : β (some i)=translatedPulseRate τ ε d) :
    let P := L.physicalMeshProduct
    let _ : MeasurableSpace Ω := physicalCompletedSpace P
    let A : Set Ω := {z | canonicalRegularVariance T none (v none) τ z.1=0}
    let U (t : ℝ≥0) (ω : A) := canonicalPulseAgeVariance T τ i 0 (min t H) ω.val.1
    let J (t : ℝ≥0) (ω : A) := canonicalPhysicalResidual T (some i) (τ+min t H) ω.val.1
    let Up (t : ℝ≥0) (z : Ω) := canonicalBirthFocalVariance T τ i (min t (τ+H)) z.1
    let Jp (t : ℝ≥0) (z : Ω) := canonicalPhysicalResidual T (some i) (min t (τ+r)) z.1
    let Xp (t : ℝ≥0) (z : Ω) := canonicalBirthDominatingAggregate T τ i t z.1
    let μ := birthTraceLaw (physicalCompletedMeasure P) A
    (∀ t (ω : A),U t ω=Up (τ+t) ω) ∧
    (∀ᵐ ω ∂μ,∀ t≤r,J t ω=Jp (τ+t) ω-Jp τ ω) ∧
    (∀ t≤r, ∀ ω : A,U t ω≤Xp (τ+t) ω) ∧
    (∀ ℓ : ℝ, μ.real {ω : A | ℓ≤ U r ω ∧ canonicalRegularVariance T none (v none) (τ+r) ω.val.1=0} =
      μ.real ((Subtype.val : A→Ω) ⁻¹' (Prod.fst ⁻¹' {p : Path |
        ℓ≤canonicalPhysicalVariance T (some i) (τ+r) p ∧ canonicalPhysicalVariance T none (τ+r) p=0}))) := by
  let P := L.physicalMeshProduct
  let A₀ := {p : Path | canonicalRegularVariance T none (v none) τ p=0}
  let A : Set Ω := Prod.fst ⁻¹' A₀
  have hm : MeasurableSet A₀ := measurableSet_eq_fun
    (((canonicalRegularVariance_adapted (T:=T) (none : Option ι) (v none) τ).mono ((G).le τ)).measurable) measurable_const
  have hτ : τ≤T := (show τ≤τ+H from le_self_add).trans hT
  have hh := L.birthCoordinates_ae hα hκ hτ hv hβ
  have hY := canonicalRegularVariance_ae_paths L.starts L.nonnegative (none : Option ι)
  have hAll := (measurePreserving_fst (μ:=(L.law:Measure Path)) (ν:=gaussianLimit)).quasiMeasurePreserving.ae (hh.and hY)
  have hTrace := ae_physical_completed_birthTrace (P:=P) (measurable_fst hm) hAll
  let _ : MeasurableSpace Ω := physicalCompletedSpace P
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · intro t ω
    rw [min_add_add_left,canonicalBirthFocal_age]
  · filter_upwards [hTrace] with ω hω t ht
    simp only [min_eq_left (ht.trans hr),min_eq_left (add_le_add_right ht τ),
      min_eq_left (show τ≤τ+r from le_self_add), hω.1.2.2,sub_zero]
  · intro t ht ω
    rw [min_eq_left (ht.trans hr),←canonicalBirthFocal_age]
    exact (canonicalBirthDominatingAggregate_data (T:=T) τ i).2.2 _ _
  · intro ℓ
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hTrace] with ω hω
    apply propext
    change (ℓ≤canonicalPulseAgeVariance T τ i 0 (min r H) ω.val.1 ∧ _) ↔ _
    rw [min_eq_left hr,←canonicalBirthFocal_age,hω.1.1,hω.2]
    rfl

#print axioms physicalMeshBirthIdentities

end FractionalFixedMeshLaw
end RoughHeston
