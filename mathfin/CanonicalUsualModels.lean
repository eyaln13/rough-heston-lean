import CanonicalFixedMeshPulseModels
import PhysicalUsualAugmentation

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

theorem physical_completion_integrable {Ω : Type*} {m : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {f : Ω→ℝ} (hf : Integrable f P) :
    Integrable f (physicalCompletedMeasure P) :=
  (physical_completion_memLp (memLp_one_iff_integrable.mpr hf)).integrable le_rfl

section Models

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 m} {α κ a b v₀ ε d : ℝ} {H : ℝ≥0} {M V C : ℝ≥0→Ω→ℝ}

/-- All pathwise data of the actual inverse boundary model persist under its
usual augmentation, and both martingales persist by continuity. -/
theorem HestonBoundaryProcess.physicalUsual (hP : HestonBoundaryProcess P F H α κ a b v₀ M V C)
    (hc : ∀ ω, Continuous fun t => C t ω) :
    HestonBoundaryProcess (physicalCompletedMeasure P) (physicalUsualFiltration P F)
      H α κ a b v₀ M V C := by
  have hv (t : ℝ≥0) : StronglyMeasurable[m] (V t) := (hP.variance_adapted t).mono (F.le t)
  refine ⟨martingale_physical_usual hP.martingale (ae_of_all _ hP.martingale_continuous),
    (fun t => physical_completion_memLp (hP.martingale_memLp t)),hP.martingale_continuous,
    hP.martingale_zero,StronglyAdapted.physicalUsual hP.variance_adapted,
    hP.variance_continuous,hP.variance_nonnegative,hP.variance_initial_bound,hP.variance_initial,
    (fun t ht => physical_completion_integrable (hP.variance_integrable t ht)),
    (fun t ht => physical_completion_integrable (hP.variance_second_integrable t ht)),?_,?_,
    martingale_physical_usual hP.compensated_square (ae_of_all _ fun ω => ?_),
    (fun t => physical_completion_integrable (hP.compensator_integrable t)),
    hP.compensator_monotone,hP.compensator,hP.inverse⟩
  · obtain ⟨B,hB,hBV⟩ := hP.variance_mean_bound
    exact ⟨B,hB,fun t ht => (physical_completion_integral P (hv t)).trans_le (hBV t ht)⟩
  · obtain ⟨B,hB,hBV⟩ := hP.variance_second_bound
    exact ⟨B,hB,fun t ht => (physical_completion_integral P ((hv t).pow 2)).trans_le (hBV t ht)⟩
  · change Continuous (fun t => M t ω*M t ω-C t ω)
    exact ((hP.martingale_continuous ω).mul (hP.martingale_continuous ω)).sub (hc ω)

/-- The pulse process and its compensation transfer to its usual filtration
on the genuinely completed ambient probability space. -/
theorem FractionalPulseProcess.physicalUsual (hP : FractionalPulseProcess P F H α κ a ε d M V C)
    (hc : ∀ ω, Continuous fun t => C t ω) :
    FractionalPulseProcess (physicalCompletedMeasure P) (physicalUsualFiltration P F)
      H α κ a ε d M V C := by
  refine ⟨martingale_physical_usual hP.martingale (ae_of_all _ hP.martingale_continuous),
    (fun t => physical_completion_memLp (hP.martingale_memLp t)),hP.martingale_continuous,
    hP.martingale_zero,StronglyAdapted.physicalUsual hP.variance_adapted,
    hP.variance_continuous,hP.variance_nonnegative,hP.variance_zero,
    martingale_physical_usual hP.compensated_square (ae_of_all _ fun ω => ?_),
    (fun t => physical_completion_integrable (hP.compensator_integrable t)),
    hP.compensator_monotone,hP.compensator,hP.inverse⟩
  change Continuous (fun t => M t ω*M t ω-C t ω)
  exact ((hP.martingale_continuous ω).mul (hP.martingale_continuous ω)).sub (hc ω)

end Models

/-- Taking age after completion and right-continuous enlargement agrees
with taking the usual augmentation of the age filtration. -/
theorem physicalUsualFiltration_pulseAge {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) (F : Filtration ℝ≥0 m) (τ : ℝ≥0) :
    pulseAgeFiltration (physicalUsualFiltration P F) τ =
      physicalUsualFiltration P (pulseAgeFiltration F τ) := by
  classical
  let G := MathFin.ItoLocalMartingale.nullAugmentation (physicalCompletedFiltration P F)
    (physicalCompletedMeasure P)
  apply Filtration.ext
  funext t
  change G.rightCont (τ+t) =
    (MathFin.ItoLocalMartingale.nullAugmentation (physicalCompletedFiltration P (pulseAgeFiltration F τ))
      (physicalCompletedMeasure P)).rightCont t
  rw [Filtration.rightCont_eq,Filtration.rightCont_eq]
  change (⨅ u > τ+t, G u) = ⨅ u > t, G (τ+u)
  apply le_antisymm
  · refine le_iInf₂ fun u hu => ?_
    exact iInf₂_le _ (add_lt_add_right hu τ)
  · refine le_iInf₂ fun u hu => ?_
    have hτ : τ≤u := (le_add_of_nonneg_right (show 0≤t from zero_le)).trans hu.le
    have he : τ+(u-τ)=u := add_tsub_cancel_of_le hτ
    have htu : t<u-τ := by
      have hlt : τ+t<τ+(u-τ) := by simpa only [he] using hu
      exact (add_lt_add_iff_left τ).mp hlt
    rw [← he]
    exact iInf₂_le (u-τ) htu

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
local notation "Path" => CanonicalPath T (CoupledPhysicalState ι)
local notation "ℱ" => canonicalPathNaturalFiltration (E := CoupledPhysicalState ι) T

/-- Every path of the physical covariance primitive is continuous, including
the endpoint where its deterministic clock becomes constant. -/
theorem canonicalPhysicalCompensator_time_continuous (σ : ℝ) (i j : Option ι) (p : Path) :
    Continuous (fun t => canonicalPhysicalCompensator T σ i j t p) := by
  let f (r : ℝ≥0) := physicalCouplingDensity σ i j (canonicalPathEval T r p).1
  have hfc : Continuous f := (continuous_physicalCouplingDensity σ i j).comp
    ((p.continuous.comp ((continuous_id.min continuous_const).subtype_mk _)).fst)
  have he (t : ℝ≥0) : canonicalPhysicalCompensator T σ i j t p =
      ∫ r in (0:ℝ)..((min t T:ℝ≥0):ℝ),f r.toNNReal := by
    unfold canonicalPhysicalCompensator canonicalCoefficientIntegral
    change (∫ r,f r ∂MathFin.ItoIntegralCLM.timeMeasureHorizon (min t T)) = _
    rw [← hestonTimeMeasure_eq_horizon,hestonTimeMeasure,
      integral_map continuous_real_toNNReal.measurable.aemeasurable hfc.measurable.aestronglyMeasurable,
      restrict_Ioo_eq_restrict_Ioc,← intervalIntegral.integral_of_le (NNReal.coe_nonneg _)]
  have hg := intervalIntegral.continuous_primitive (μ := volume)
    (fun a b => (hfc.comp continuous_real_toNNReal).intervalIntegrable a b) 0
  exact (hg.comp (NNReal.continuous_coe.comp (continuous_id.min continuous_const))).congr
    fun t => (he t).symm

namespace FractionalFixedMeshLaw

variable {α κ σ : ℝ} {v : Option ι→ℝ} {β : Option ι→ℝ≥0→ℝ}
  (L : FractionalFixedMeshLaw T α κ σ v β)

theorem usualResidualMartingale (i : Option ι) :
    Martingale (canonicalPhysicalResidual T i) (physicalUsualFiltration (L.law:Measure Path) ℱ)
      (physicalCompletedMeasure (L.law:Measure Path)) :=
  martingale_physical_usual (L.residualMartingale i) (ae_of_all _ (canonicalPhysicalResidual_time_continuous i))

theorem usualProductMartingale (i j : Option ι) :
    Martingale (canonicalPhysicalCompensatedProduct T σ i j) (physicalUsualFiltration (L.law:Measure Path) ℱ)
      (physicalCompletedMeasure (L.law:Measure Path)) := by
  apply martingale_physical_usual (L.productMartingale i j)
  refine ae_of_all _ fun p => ?_
  exact ((canonicalPhysicalResidual_time_continuous i p).mul (canonicalPhysicalResidual_time_continuous j p)).sub
    (canonicalPhysicalCompensator_time_continuous σ i j p)

theorem usualCompanionBoundary {b : ℝ} (hα : α<1) (hv : 0≤v none)
    (hb : β none = fun _ => b) :
    HestonBoundaryProcess (physicalCompletedMeasure (L.law:Measure Path))
      (physicalUsualFiltration (L.law:Measure Path) ℱ) T α κ (σ^2/2) b (v none)
      (canonicalPhysicalResidual T none) (canonicalRegularVariance T none (v none))
      (canonicalPhysicalCompensator T σ none none) :=
  (L.actualCompanionBoundary hα hv hb).physicalUsual
    (canonicalPhysicalCompensator_time_continuous σ (none : Option ι) none)

theorem usualFractionalPulse {i : ι} {τ : ℝ≥0} {ε d : ℝ}
    (hα : α<1) (hκ : 0≤κ) (hτ : τ≤T) (hv : v (some i)=0)
    (hβ : β (some i)=translatedPulseRate τ ε d) :
    FractionalPulseProcess (physicalCompletedMeasure (L.law:Measure Path))
      (pulseAgeFiltration (physicalUsualFiltration (L.law:Measure Path) ℱ) τ) (T-τ)
      α κ (σ^2/2) ε d (fun t => canonicalPhysicalResidual T (some i) (τ+t))
      (canonicalPulseAgeVariance T τ i (v (some i)))
      (fun t => canonicalPhysicalCompensator T σ (some i) (some i) (τ+t)) := by
  rw [physicalUsualFiltration_pulseAge]
  exact (L.actualFractionalPulse hα hκ hτ hv hβ).physicalUsual
    (fun p => (canonicalPhysicalCompensator_time_continuous σ (some i) (some i) p).comp
      (continuous_const.add continuous_id))

end FractionalFixedMeshLaw

#print axioms HestonBoundaryProcess.physicalUsual
#print axioms FractionalPulseProcess.physicalUsual
#print axioms FractionalFixedMeshLaw.usualProductMartingale
#print axioms FractionalFixedMeshLaw.usualFractionalPulse

end RoughHeston
