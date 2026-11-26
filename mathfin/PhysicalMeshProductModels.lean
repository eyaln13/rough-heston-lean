import CompletedProductBirthEvents
import FractionalFixedMeshBrownian

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace RoughHeston

open MathFin.ItoLocalMartingale (nullAugmentation)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
  {α κ σ : ℝ} {v : Option ι → ℝ} {β : Option ι → ℝ≥0 → ℝ}
local notation "Path" => CanonicalPath T (CoupledPhysicalState ι)
local notation "Ω" => Path × (ℝ≥0 → ℝ)
local notation "G" => canonicalPathNaturalFiltration (E := CoupledPhysicalState ι) T

namespace FractionalFixedMeshLaw
variable (L : FractionalFixedMeshLaw T α κ σ v β)

noncomputable abbrev physicalMeshProduct := (L.law:Measure Path).prod gaussianLimit
noncomputable abbrev physicalMeshProductFiltration :=
  nullAugmentation (prodFiltration G canonicalAuxiliaryFiltration) L.physicalMeshProduct

theorem productUsualCompanionBoundary {b : ℝ} (hα : α<1) (hv : 0≤v none) (hb : β none=fun _ => b) :
    HestonBoundaryProcess (physicalCompletedMeasure L.physicalMeshProduct)
      (physicalUsualFiltration L.physicalMeshProduct L.physicalMeshProductFiltration) T α κ (σ^2/2) b (v none)
      (fun t (z : Ω) => canonicalPhysicalResidual T none t z.1)
      (fun t z => canonicalRegularVariance T none (v none) t z.1)
      (fun t z => canonicalPhysicalCompensator T σ none none t z.1) := by
  have h := (L.actualCompanionBoundary hα hv hb).on_independent_product gaussianLimit canonicalAuxiliaryFiltration
  exact h.physicalUsual (fun z => canonicalPhysicalCompensator_time_continuous σ (none : Option ι) none z.1)

theorem productUsualFractionalPulse {i : ι} {τ : ℝ≥0} {ε d : ℝ}
    (hα : α<1) (hκ : 0≤κ) (hτ : τ≤T) (hv : v (some i)=0)
    (hβ : β (some i)=translatedPulseRate τ ε d) :
    FractionalPulseProcess (physicalCompletedMeasure L.physicalMeshProduct)
      (pulseAgeFiltration (physicalUsualFiltration L.physicalMeshProduct L.physicalMeshProductFiltration) τ) (T-τ)
      α κ (σ^2/2) ε d (fun t (z : Ω) => canonicalPhysicalResidual T (some i) (τ+t) z.1)
      (fun t z => canonicalPulseAgeVariance T τ i 0 t z.1)
      (fun t z => canonicalPhysicalCompensator T σ (some i) (some i) (τ+t) z.1) := by
  rw [physicalUsualFiltration_pulseAge]
  have h := (L.actualFractionalPulse hα hκ hτ hv hβ).on_independent_product gaussianLimit canonicalAuxiliaryFiltration
  rw [hv] at h
  exact h.physicalUsual (fun z => (canonicalPhysicalCompensator_time_continuous σ (some i) (some i) z.1).comp
    (continuous_const.add continuous_id))

/-- Any adapted version of a variance coordinate with a deterministic
time change has bounded fourth moments on the completed physical extension. -/
theorem completedProduct_variance_fourth (i : Option ι)
    {g : ℝ≥0 → Path → ℝ} {clock : ℝ≥0 → ℝ≥0}
    (hg : ∀ t, Measurable (g t))
    (he : ∀ t, g t=ᵐ[(L.law:Measure Path)] canonicalPhysicalVariance T i (clock t)) :
    ∃ K : ℝ, ∀ t,
      Integrable (fun z : Ω => (g t z.1)^4) (physicalCompletedMeasure L.physicalMeshProduct) ∧
      (∫ z : Ω,(g t z.1)^4 ∂physicalCompletedMeasure L.physicalMeshProduct)≤K := by
  obtain ⟨K,hK⟩ := L.variance_uniform_memLp 2
  norm_num at hK
  refine ⟨K,?_⟩
  intro t
  let s := min (clock t) T
  have hes : canonicalPhysicalVariance T i (clock t)=canonicalPhysicalVariance T i s := by
    have htime : canonicalEvalTime T (clock t)=canonicalEvalTime T s := Subtype.ext (min_eq_left (min_le_right _ _)).symm
    funext p
    change (p (canonicalEvalTime T (clock t))).1 i=(p (canonicalEvalTime T s)).1 i
    rw [htime]
  have hs := hK i s (min_le_right _ _)
  have heg := he t
  rw [hes] at heg
  have hm : MemLp (g t) 4 (L.law:Measure Path) := hs.1.ae_eq heg.symm
  have hfour : Integrable (fun p => (g t p)^4) (L.law:Measure Path) := by
    have h := hm.integrable_norm_pow (p:=4) (by decide)
    convert h using 1
    ext p
    rw [Real.norm_eq_abs, ←abs_pow,abs_of_nonneg (by positivity : 0≤g t p^4)]
  let pr := measurePreserving_fst (μ:=(L.law:Measure Path)) (ν:=gaussianLimit)
  refine ⟨physical_completion_integrable (pr.integrable_comp_of_integrable hfour),?_⟩
  have hmeas : StronglyMeasurable (fun z : Ω => (g t z.1)^4) :=
    ((hg t).comp measurable_fst).stronglyMeasurable.pow 4
  rw [physical_completion_integral L.physicalMeshProduct hmeas]
  change (∫ z : Ω,(fun p => (g t p)^4) z.1 ∂(L.law:Measure Path).prod gaussianLimit)≤K
  rw [integral_fun_fst (μ:=(L.law:Measure Path)) (ν:=gaussianLimit) (fun p => (g t p)^4),probReal_univ,one_smul]
  refine (integral_congr_ae ?_).le.trans hs.2
  filter_upwards [heg] with p hp
  exact congrArg (fun x : ℝ => x^4) hp

end FractionalFixedMeshLaw

#print axioms FractionalFixedMeshLaw.productUsualCompanionBoundary
#print axioms FractionalFixedMeshLaw.productUsualFractionalPulse
#print axioms FractionalFixedMeshLaw.completedProduct_variance_fourth

end RoughHeston
