import CanonicalUsualModels
import BirthTraceMartingaleShift

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston

open GirsanovPort

/-- Restrict an actual age process to a positive-probability event in
the birth sigma algebra. The model paths and pulse input remain the same
under the conditioned subtype law. -/
theorem FractionalPulseProcess.birthTrace {Ω : Type*} {m : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {F : Filtration ℝ≥0 m} {H : ℝ≥0}
    {α κ a ε d : ℝ} {M U C : ℝ≥0→Ω→ℝ} {A : Set Ω}
    (hP : FractionalPulseProcess P F H α κ a ε d M U C)
    (hA : MeasurableSet[F 0] A) (hp : 0<P A) :
    FractionalPulseProcess (birthTraceLaw P A) (birthTraceFiltration F 0 A) H α κ a ε d
      (fun t (ω : A) => M t ω) (fun t (ω : A) => U t ω) (fun t (ω : A) => C t ω) := by
  let Q := @boundaryConditionedMeasure Ω m P A
  have hPres : MeasurePreserving (Subtype.val : A→Ω) (birthTraceLaw P A) Q :=
    ⟨measurable_subtype_coe,birthTraceLaw_map (F.le 0 A hA)⟩
  have hAC : Q ≪ P :=
    ((Measure.AbsolutelyContinuous.refl (P.restrict A)).smul_left _).trans
      Measure.restrict_le_self.absolutelyContinuous
  have pull {q : Ω→Prop} (hq : ∀ᵐ ω ∂P,q ω) : ∀ᵐ (ω : A) ∂birthTraceLaw P A,q ω :=
    hPres.quasiMeasurePreserving.ae (hAC.ae_le hq)
  have ha : StronglyAdapted (birthTraceFiltration F 0 A) (fun t (ω : A) => U t ω) := by
    intro t
    change StronglyMeasurable[(F (0+t)).comap (Subtype.val : A→Ω)] (fun (ω:A) => U t ω)
    rw [zero_add]
    exact (hP.variance_adapted t).comp_measurable (Measurable.of_comap_le le_rfl)
  have hM := martingale_birthTrace hA hp hP.martingale
  have hC := martingale_birthTrace hA hp hP.compensated_square
  let hQ := birthTraceLaw_isProbability (F.le 0 A hA) hp
  refine ⟨?_,(fun t => birthTrace_memLp hA hp (hP.martingale_memLp t)),
    (fun ω => hP.martingale_continuous ω),pull hP.martingale_zero,
    ha,(fun ω => hP.variance_continuous ω),(fun t ω => hP.variance_nonnegative t ω),
    (fun ω => hP.variance_zero ω),?_,?_,(fun s t hst => pull (hP.compensator_monotone s t hst)),?_,pull hP.inverse⟩
  · simpa only [zero_add] using hM
  · convert hC using 1
    funext t ω
    simp only [zero_add,Pi.sub_apply,Pi.mul_apply]
  · intro t
    exact (birthTrace_memLp hA hp (memLp_one_iff_integrable.mpr (hP.compensator_integrable t))).integrable le_rfl
  · intro t ht
    exact pull (hP.compensator t ht)

theorem birthTraceFiltration_pulseAge {Ω : Type*} {m : MeasurableSpace Ω}
    (F : Filtration ℝ≥0 m) (τ : ℝ≥0) (A : Set Ω) :
    birthTraceFiltration (pulseAgeFiltration F τ) 0 A=birthTraceFiltration F τ A := by
  apply Filtration.ext
  funext t
  change (F (τ+(0+t))).comap (Subtype.val : A→Ω)=(F (τ+t)).comap (Subtype.val : A→Ω)
  rw [zero_add]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
local notation "Path" => CanonicalPath T (CoupledPhysicalState ι)
local notation "ℱ" => canonicalPathNaturalFiltration (E := CoupledPhysicalState ι) T

namespace FractionalFixedMeshLaw

variable {α κ σ : ℝ} {v : Option ι→ℝ} {β : Option ι→ℝ≥0→ℝ}
  (L : FractionalFixedMeshLaw T α κ σ v β)

/-- Birth extinction is measurable at the birth time in the shared usual
physical filtration. -/
theorem usualCompanionZero_measurable (τ : ℝ≥0) :
    MeasurableSet[physicalUsualFiltration (L.law:Measure Path) ℱ τ]
      {p | canonicalRegularVariance T none (v none) τ p=0} :=
  measurableSet_eq_fun
    ((StronglyAdapted.physicalUsual (P := (L.law:Measure Path))
      (canonicalRegularVariance_adapted (T := T) (none : Option ι) (v none)) τ).measurable) measurable_const

/-- The focal pulse appears on the genuinely completed, right continuous
birth trace of the physical law. The observation of its companion is still
the original physical coordinate evaluated at that birth. -/
theorem usualFractionalPulse_onBirthTrace {i : ι} {τ : ℝ≥0} {ε d : ℝ}
    (hα : α<1) (hκ : 0≤κ) (hτ : τ≤T) (hv : v (some i)=0)
    (hβ : β (some i)=translatedPulseRate τ ε d)
    (hA : 0 < (L.law:Measure Path) {p | canonicalRegularVariance T none (v none) τ p=0}) :
    let μ := physicalCompletedMeasure (L.law:Measure Path)
    let F := physicalUsualFiltration (L.law:Measure Path) ℱ
    let A : Set Path := {p | canonicalRegularVariance T none (v none) τ p=0}
    let _ : MeasurableSpace Path := physicalCompletedSpace (L.law:Measure Path)
    FractionalPulseProcess (birthTraceLaw μ A) (birthTraceFiltration F τ A) (T-τ)
      α κ (σ^2/2) ε d (fun t (p : A) => canonicalPhysicalResidual T (some i) (τ+t) p)
      (fun t (p : A) => canonicalPulseAgeVariance T τ i (v (some i)) t p)
      (fun t (p : A) => canonicalPhysicalCompensator T σ (some i) (some i) (τ+t) p) := by
  let P := (L.law:Measure Path)
  let μ := physicalCompletedMeasure P
  let F := physicalUsualFiltration P ℱ
  let A : Set Path := {p | canonicalRegularVariance T none (v none) τ p=0}
  let _ : MeasurableSpace Path := physicalCompletedSpace P
  have hAt : MeasurableSet[F τ] A := L.usualCompanionZero_measurable τ
  have hA0 : MeasurableSet[pulseAgeFiltration F τ 0] A := by
    change MeasurableSet[F (τ+0)] A
    rwa [add_zero]
  have hAμ : 0<μ A := hA
  have hp := (L.usualFractionalPulse hα hκ hτ hv hβ).birthTrace hA0 hAμ
  rw [birthTraceFiltration_pulseAge] at hp
  exact hp

end FractionalFixedMeshLaw

#print axioms FractionalPulseProcess.birthTrace
#print axioms FractionalFixedMeshLaw.usualFractionalPulse_onBirthTrace

end RoughHeston
