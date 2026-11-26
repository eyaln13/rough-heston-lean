import PhysicalSingleBirthTraceSeparation
import PhysicalCompanionStopData
import PhysicalPulseFocalBrownian

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace RoughHeston.FractionalFixedMeshLaw

open GirsanovPort

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
  {α κ σ : ℝ} {v : Option ι → ℝ} {β : Option ι → ℝ≥0 → ℝ}
local notation "Path" => CanonicalPath T (CoupledPhysicalState ι)
local notation "Ω" => Path × (ℝ≥0 → ℝ)
local notation "G" => canonicalPathNaturalFiltration (E := CoupledPhysicalState ι) T

/-- The actual companion and focal certificates use exactly the same
selected Brownian on the completed physical product at the chosen mesh. -/
theorem meshPhysicalStopCertificates (L : FractionalFixedMeshLaw T α κ σ v β)
    {τ H r : ℝ≥0} {i : ι} {b ε d : ℝ} (hα : 1/2<α) (hα' : α<1)
    (hκ : 0≤κ) (hσ : 0<σ) (hb : 0≤b) (hv₀ : 0≤v none)
    (hT : τ+H≤T) (hr : r≤H) (hv : v (some i)=0)
    (hβ : β (some i)=translatedPulseRate τ ε d) (hbβ : β none=fun _ => b) :
    let P := physicalCompletedMeasure L.physicalMeshProduct
    let F := physicalUsualFiltration L.physicalMeshProduct L.physicalMeshProductFiltration
    let lift (f : ℝ≥0→Path→ℝ) (t : ℝ≥0) (z : Ω) := f t z.1
    let S := τ+r
    let J := fun t => lift (canonicalPhysicalResidual T (some i)) (min t S)
    let U := fun t => lift (canonicalBirthFocalVariance T τ i) (min t (τ+H))
    let X := lift (canonicalBirthDominatingAggregate T τ i)
    let Y := lift (canonicalRegularVariance T none (v none))
    let M := lift (canonicalPhysicalResidual T none)
    let C := lift (canonicalPhysicalCompensator T σ none none)
    ∃ B Cf : ℝ≥0 → Ω → ℝ,
      PhysicalBirthStopCertificate P F S α κ σ B M Y C (fun u => b+(v none)*fractionalL α u) ∧
      PhysicalBirthFocalCertificate P F S σ B J U X Cf := by
  have hST : τ+r≤T := (add_le_add_right hr τ).trans hT
  obtain ⟨B,Cf,hB,hBm,hB₂,hBs,_,hYcut,hJ,hJ₂,hmix,hCf,hUp,hXp,_,hqI⟩ :=
    L.exists_usual_birth_focal_brownian hα' hκ hσ hT hr hv hβ
  have hc := L.productUsualCompanionBoundary hα' hv₀ hbβ
  have hY₄ := L.completedProduct_variance_fourth (none : Option ι)
    (g:=canonicalRegularVariance T none (v none)) (clock:=id)
    (fun t => ((canonicalRegularVariance_adapted (T:=T) (none : Option ι) (v none) t).mono ((G).le t)).measurable)
    (fun t => (canonicalRegularVariance_ae_paths L.starts L.nonnegative none).mono fun _ hp => hp t)
  let _ : MeasurableSpace Ω := physicalCompletedSpace L.physicalMeshProduct
  exact ⟨B,Cf,hc.physicalStopData (by linarith) hα' hb hv₀ hST hB hBm hB₂ hBs hY₄ hYcut,
    ⟨hJ,hJ₂,hUp,hXp,hmix,hqI.mono (fun _ hh => hh (τ+r) le_rfl),hCf⟩⟩

#print axioms meshPhysicalStopCertificates

end RoughHeston.FractionalFixedMeshLaw
