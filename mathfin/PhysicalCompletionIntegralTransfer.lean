import CanonicalUsualModels

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω}

theorem physical_completion_eLpNorm {X : Ω→ℝ} (hX : AEStronglyMeasurable X P) (p : ℝ≥0∞) :
    eLpNorm X p (physicalCompletedMeasure P)=eLpNorm X p P := by
  have h := hX.ae_eq_mk
  have hc : X =ᵐ[physicalCompletedMeasure P] hX.mk X := h
  rw [eLpNorm_congr_ae hc,eLpNorm_congr_ae h,
    ← eLpNorm_trim (physical_ambient_le_completion P) hX.stronglyMeasurable_mk,physical_completion_trim]

/-- A stopped stochastic integral determined by its L² sums has the same
terminal value under true completion whenever both constructions use the
same approximating sums. The stopped sums can be arbitrary original
measurable versions. -/
theorem physical_completion_same_stopped_L2_limit {S : ℕ→Ω→ℝ} {X Y : Ω→ℝ}
    (hS : ∀ n,MemLp (S n) 2 P) (hX : MemLp X 2 P)
    (hY : MemLp Y 2 (physicalCompletedMeasure P))
    (hSX : Tendsto (fun n => eLpNorm (S n-X) 2 P) atTop (𝓝 0))
    (hSY : Tendsto (fun n => eLpNorm (S n-Y) 2 (physicalCompletedMeasure P)) atTop (𝓝 0)) :
    X =ᵐ[physicalCompletedMeasure P] Y := by
  let μ := physicalCompletedMeasure P
  let s (n : ℕ) : Lp ℝ 2 μ := (physical_completion_memLp (hS n)).toLp (S n)
  let hXc : MemLp X 2 μ := physical_completion_memLp hX
  let x := hXc.toLp X
  let y := hY.toLp Y
  have hx (n : ℕ) : edist (s n) x=eLpNorm (S n-X) 2 P := by
    rw [Lp.edist_toLp_toLp,physical_completion_eLpNorm ((hS n).sub hX).aestronglyMeasurable]
  have hy (n : ℕ) : edist (s n) y=eLpNorm (S n-Y) 2 μ := by rw [Lp.edist_toLp_toLp]
  have htx : Tendsto s atTop (𝓝 x) := by
    apply tendsto_iff_edist_tendsto_0.mpr
    simpa only [hx] using hSX
  have hty : Tendsto s atTop (𝓝 y) := by
    apply tendsto_iff_edist_tendsto_0.mpr
    simpa only [hy,μ] using hSY
  have he : x=y := tendsto_nhds_unique htx hty
  have hx' : ⇑x =ᵐ[μ] X := hXc.coeFn_toLp
  have hy' : ⇑y =ᵐ[μ] Y := hY.coeFn_toLp
  rw [he] at hx'
  exact hx'.symm.trans hy'

/-- Original set integrals and probabilities on the birth event agree under
the completed law. The original birth mass is therefore unchanged. -/
theorem physical_completion_birth_trim (P : Measure Ω) (A : Set Ω) :
    (@boundaryConditionedMeasure Ω (physicalCompletedSpace P) (physicalCompletedMeasure P) A).trim
      (physical_ambient_le_completion P) = @boundaryConditionedMeasure Ω m P A := by
  ext E hE
  have hEc : MeasurableSet[physicalCompletedSpace P] E := physical_ambient_le_completion P E hE
  rw [trim_measurableSet_eq (physical_ambient_le_completion P) hE]
  unfold boundaryConditionedMeasure
  rw [Measure.smul_apply,Measure.smul_apply,Measure.restrict_apply hEc,Measure.restrict_apply hE]
  rfl

theorem physical_completion_birth_integral (P : Measure Ω) (A : Set Ω)
    {Z : Ω→ℝ} (hZ : StronglyMeasurable[m] Z) :
    (∫ ω,Z ω ∂@boundaryConditionedMeasure Ω (physicalCompletedSpace P) (physicalCompletedMeasure P) A)=
      ∫ ω,Z ω ∂@boundaryConditionedMeasure Ω m P A := by
  rw [integral_trim (physical_ambient_le_completion P) hZ,physical_completion_birth_trim]

theorem physical_completion_birth_probability (P : Measure Ω) (A : Set Ω)
    {E : Set Ω} (hE : MeasurableSet[m] E) :
    (@boundaryConditionedMeasure Ω (physicalCompletedSpace P) (physicalCompletedMeasure P) A).real E =
      (@boundaryConditionedMeasure Ω m P A).real E := by
  unfold Measure.real
  rw [← trim_measurableSet_eq (physical_ambient_le_completion P) hE,physical_completion_birth_trim]

/-- Evaluating a continuous physical process at a stopping time of its usual
filtration gives an adapted stopped process on the completed space. -/
theorem physicalUsual_stoppedProcess_adapted {F : Filtration ℝ≥0 m} {X : ℝ≥0→Ω→ℝ}
    {τ : Ω→WithTop ℝ≥0} (hX : StronglyAdapted F X)
    (hc : ∀ ω,Continuous (fun t => X t ω))
    (hτ : IsStoppingTime (physicalUsualFiltration P F) τ) :
    StronglyAdapted (physicalUsualFiltration P F) (stoppedProcess X τ) :=
  ((StronglyAdapted.physicalUsual (P := P) hX).isStronglyProgressive_of_continuous hc).stronglyAdapted_stoppedProcess hτ

#print axioms physical_completion_same_stopped_L2_limit
#print axioms physical_completion_birth_trim
#print axioms physicalUsual_stoppedProcess_adapted

end RoughHeston
