import PhysicalMeshProductModels
import UsualPhysicalPulsedFocalDriver
import FocalDynamicsOnBirthTrace
import CanonicalFocalTraceInputs

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston
namespace FractionalFixedMeshLaw

open GirsanovPort
open MathFin.ItoLocalMartingale (nullAugmentation)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
  {α κ σ : ℝ} {v : Option ι→ℝ} {β : Option ι→ℝ≥0→ℝ}
  (L : FractionalFixedMeshLaw T α κ σ v β)
local notation "Path" => CanonicalPath T (CoupledPhysicalState ι)
local notation "Ω" => Path × (ℝ≥0→ℝ)
local notation "G" => canonicalPathNaturalFiltration (E := CoupledPhysicalState ι) T

/-- The companion zero event is observable at its physical birth time
in the usual filtration of the full product. -/
theorem productCompanionBirthZero_measurable (τ : ℝ≥0) :
    MeasurableSet[(physicalUsualFiltration L.physicalMeshProduct L.physicalMeshProductFiltration) τ]
      {z : Ω | canonicalRegularVariance T none (v none) τ z.1=0} := by
  apply (physicalCompletedFiltration_le_usual L.physicalMeshProduct L.physicalMeshProductFiltration τ)
  apply (show (prodFiltration G canonicalAuxiliaryFiltration) τ≤L.physicalMeshProductFiltration τ from le_sup_left)
  have had := canonicalRegularVariance_adapted (T := T) (none : Option ι) (v none) τ
  exact measurableSet_eq_fun
    (had.comp_measurable (@measurable_fst Path (ℝ≥0→ℝ) (G τ) (canonicalAuxiliaryFiltration τ))).measurable
    measurable_const

/-- An actual focal coordinate on the completed physical mesh product
has its auxiliary driver, pulse equation, and bracket on the companion's
birth-zero trace. All observations through the age horizon retain their
physical values. -/
theorem productBirthTraceFocalDynamics {i : ι} {τ H : ℝ≥0} {ε d : ℝ}
    (hα : α<1) (hκ : 0≤κ) (hτH : τ+H≤T) (hv : v (some i)=0)
    (hβ : β (some i)=translatedPulseRate τ ε d)
    (hApos : 0 < (physicalCompletedMeasure L.physicalMeshProduct)
      {z : Ω | canonicalRegularVariance T none (v none) τ z.1=0}) :
    let P := physicalCompletedMeasure L.physicalMeshProduct
    let F := physicalUsualFiltration L.physicalMeshProduct L.physicalMeshProductFiltration
    let A : Set Ω := {z | canonicalRegularVariance T none (v none) τ z.1=0}
    let _ : MeasurableSpace Ω := physicalCompletedSpace L.physicalMeshProduct
    let Q := birthTraceLaw P A
    ∃ W : ℝ≥0→A→ℝ, FocalPulseDynamics Q (birthTraceFiltration F τ A) H α κ σ ε d
      (fun t (z : A) => canonicalPhysicalResidual T (some i) (τ+min t H) z.val.1)
      (fun t (z : A) => canonicalPulseAgeVariance T τ i 0 (min t H) z.val.1)
      (fun t (z : A) => canonicalPhysicalCompensator T σ (some i) (some i) (τ+min t H) z.val.1) W := by
  let P₀ := L.physicalMeshProduct
  let P := physicalCompletedMeasure P₀
  let F := physicalUsualFiltration P₀ L.physicalMeshProductFiltration
  let A : Set Ω := {z | canonicalRegularVariance T none (v none) τ z.1=0}
  let rawM : MeasurableSpace Ω := inferInstance
  let _ : MeasurableSpace Ω := physicalCompletedSpace P₀
  let J (t : ℝ≥0) (z : Ω) := canonicalPhysicalResidual T (some i) t z.1
  let W (t : ℝ≥0) (z : Ω) := brownian (min t T) z.2
  have hτ : τ≤T := (le_add_of_nonneg_right (show (0:ℝ≥0)≤H from zero_le)).trans hτH
  have hAge : H≤T-τ := le_tsub_of_add_le_right (by simpa only [add_comm] using hτH)
  have hA : MeasurableSet[F τ] A := L.productCompanionBirthZero_measurable τ
  let hQ := birthTraceLaw_isProbability (F.le τ A hA) hApos
  have hPulse := L.productUsualFractionalPulse hα hκ hτ hv hβ
  have hC : ∀ᵐ z : Ω ∂P,Continuous (fun t =>
      canonicalPhysicalCompensator T σ (some i) (some i) (τ+t) z.1) :=
    ae_of_all _ fun z => (canonicalPhysicalCompensator_time_continuous σ (some i) (some i) z.1).comp
      (continuous_const.add continuous_id)
  have hSource : @MeasurePreserving Ω Path (physicalCompletedSpace P₀) inferInstance Prod.fst
      P (L.law:Measure Path) := by
    exact @MeasurePreserving.comp Ω Ω Path (physicalCompletedSpace P₀) rawM inferInstance
      P P₀ (L.law:Measure Path) Prod.fst id
      (measurePreserving_fst (μ := (L.law:Measure Path)) (ν := gaussianLimit))
      (physical_completion_measurePreserving_id P₀)
  obtain ⟨D,hD,hU⟩ := L.lifted_pulse_age_fourth_bound hSource hα hκ hτ hτH hv hβ
  have hFourth (t : ℝ≥0) (ht : t≤H) :
      eLpNorm (fun z : Ω => canonicalPulseAgeVariance T τ i 0 t z.1) 4 P≤D := by
    simpa only [hv] using hU t ht
  have hM (t : ℝ≥0) (_ : t≤H) : J (τ+t)=ᵐ[P] fun z => J (τ+t) z-J τ z :=
    (L.lifted_pulse_residual_ae_increment hSource hα hκ hτ hv hβ).mono fun _ hz => hz t
  have hJ : Martingale J F P :=
    martingale_usual_physical_product_fst (L.residualMartingale (some i))
      (ae_of_all _ (canonicalPhysicalResidual_time_continuous (some i)))
  have hJ₂ (t : ℝ≥0) : MemLp (J t) 2 P :=
    (L.residual_memLp t).comp_measurePreserving hSource
  have hWJ : Martingale (fun t => W t*J t) F P :=
    usual_physical_product_auxiliary_orthogonal T (L.residualMartingale (some i))
      (ae_of_all _ (canonicalPhysicalResidual_time_continuous (some i)))
  obtain ⟨hW,hW₂,_,hWc,hWsq⟩ := usual_physical_product_auxiliary_driver
    (μ := (L.law:Measure Path)) G T
  exact ⟨birthTraceStoppedIncrement A τ H W,
    focalPulseDynamics_onBirthTrace hA hApos hAge hτH hPulse hC hD hFourth hM
      hW hJ hW₂ hJ₂ (ae_of_all _ hWc) hWsq hWJ⟩

#print axioms productBirthTraceFocalDynamics

end FractionalFixedMeshLaw
end RoughHeston
