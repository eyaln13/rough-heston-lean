import BirthTraceMartingaleShift
import JointHorizonExtension
import SHEStochastic.ScalarIto

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace RoughHeston.GirsanovPort

open SHE.PredictableL2

/-- Translation sends the age Lebesgue clock to the corresponding
physical window. The real-time translation proof follows Han's
`SHE.DeterministicItoShift.time_translation`. -/
theorem hestonTimeMeasure_add_shift {T b r : ℝ≥0} (hr : b+r≤T) :
    MeasurePreserving (fun t : ℝ≥0 => b+t) (hestonTimeMeasure r)
      ((hestonTimeMeasure T).restrict (Ioc b (b+r))) := by
  simp only [hestonTimeMeasure_eq_horizon]
  have h_eq (t : ℝ≥0) : timeMeasure t = MathFin.ItoIntegralCLM.timeMeasureHorizon t := by
    unfold timeMeasure MathFin.ItoIntegralCLM.timeMeasureHorizon MathFin.ItoIntegralL2.timeMeasure
    rw [nonnegative_coe_measurableEmbedding.comap_restrict]
    rfl
  rw [←h_eq r,←h_eq T]
  refine ⟨(continuous_const.add continuous_id).measurable,?_⟩
  apply nonnegative_coe_measurableEmbedding.map_injective
  have hAdd : Measurable (fun t:ℝ≥0 => b+t) := measurable_const.add measurable_id
  have hReal : Measurable (fun t:ℝ => (b:ℝ)+t) := measurable_const.add measurable_id
  rw [Measure.map_map measurable_coe_nnreal_real hAdd, show
    (((↑):ℝ≥0→ℝ)∘(fun t:ℝ≥0=>b+t))=(fun t:ℝ=>(b:ℝ)+t)∘((↑):ℝ≥0→ℝ) from rfl,
    ← Measure.map_map hReal measurable_coe_nnreal_real,timeMeasure_map]
  have hpre : (fun t:ℝ => (b:ℝ)+t) ⁻¹' Ioc (b:ℝ) ((b+r:ℝ≥0):ℝ) = Ioc (0:ℝ) (r:ℝ) := by
    ext t
    simp only [mem_preimage,mem_Ioc,NNReal.coe_add]
    constructor <;> intro ht <;> constructor <;> linarith [ht.1,ht.2]
  have hm := (measurePreserving_add_left volume (b:ℝ)).restrict_preimage
    (s:=Ioc (b:ℝ) ((b+r:ℝ≥0):ℝ)) measurableSet_Ioc
  have hreal : (volume.restrict (Ioc (0:ℝ) (r:ℝ))).map (fun t:ℝ => (b:ℝ)+t) =
      volume.restrict (Ioc (b:ℝ) ((b+r:ℝ≥0):ℝ)) := by
    simpa only [hpre] using hm.map_eq
  rw [hreal]
  have hp : ((↑):ℝ≥0→ℝ) ⁻¹' Ioc (b:ℝ) ((b+r:ℝ≥0):ℝ)=Ioc b (b+r) := by
    ext t
    simp only [mem_preimage,mem_Ioc,NNReal.coe_lt_coe,NNReal.coe_le_coe]
  rw [←hp,←Measure.restrict_map measurable_coe_nnreal_real measurableSet_Ioc,timeMeasure_map,
    Measure.restrict_restrict measurableSet_Ioc]
  congr 1
  exact (inter_eq_left.mpr (Ioc_subset_Ioc (NNReal.coe_nonneg b) (by exact_mod_cast hr))).symm

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 m} {A : Set Ω} {b r T : ℝ≥0}

/-- Exact predictable measure matching for physical time restricted to the
birth event and the same interval in the birth-age filtration. -/
theorem birthTrace_jointPredictableMeasure_shift
    (hA : MeasurableSet[F b] A) (hp : 0<P A) (hr : b+r≤T) :
    @MeasurePreserving (ℝ≥0 × A) (ℝ≥0 × Ω) (birthTraceFiltration F b A).predictable F.predictable
      (fun p : ℝ≥0 × A => (b+p.1,p.2.val))
      (jointPredictableMeasure (birthTraceFiltration F b A) (birthTraceLaw P A) r)
      ((jointPredictableMeasure F (boundaryConditionedMeasure P A) T).restrict
        (Ioc b (b+r) ×ˢ (univ : Set Ω))) := by
  let Q := boundaryConditionedMeasure P A
  let G := birthTraceFiltration F b A
  let W := Ioc b (b+r) ×ˢ (univ : Set Ω)
  let φ (p : ℝ≥0 × A) : ℝ≥0 × Ω := (b+p.1,p.2.val)
  let : IsProbabilityMeasure Q := boundaryConditionedMeasure_isProbability hp
  let : IsProbabilityMeasure (birthTraceLaw P A) := birthTraceLaw_isProbability (F.le b A hA) hp
  have hW : MeasurableSet[F.predictable] W :=
    measurableSet_predictable_Ioc_prod b (b+r) MeasurableSet.univ
  have hφ : @Measurable _ _ G.predictable F.predictable φ := measurable_birthTrace_predictableShift
  have hval : MeasurePreserving (Subtype.val : A → Ω) (birthTraceLaw P A) Q :=
    ⟨measurable_subtype_coe,birthTraceLaw_map (F.le b A hA)⟩
  haveI timeFinite (t : ℝ≥0) : IsFiniteMeasure (hestonTimeMeasure t) := by
    rw [hestonTimeMeasure_eq_horizon]
    infer_instance
  have hPprod : MeasurePreserving φ ((hestonTimeMeasure r).prod (birthTraceLaw P A))
      (((hestonTimeMeasure T).prod Q).restrict W) := by
    rw [show W = Ioc b (b+r) ×ˢ (univ : Set Ω) from rfl,← Measure.prod_restrict,
      Measure.restrict_univ]
    exact (hestonTimeMeasure_add_shift hr).prod hval
  have hpProd (E : Set (ℝ≥0 × Ω)) (hE : MeasurableSet[F.predictable] E) :
      ((hestonTimeMeasure r).prod (birthTraceLaw P A)) (φ ⁻¹' E) =
        ((hestonTimeMeasure T).prod Q) (E∩W) := by
    have hh := congrArg (fun (μ : Measure (ℝ≥0 × Ω)) => μ E) hPprod.map_eq
    rw [Measure.map_apply hPprod.measurable (F.predictable_le_prod E hE),
      Measure.restrict_apply (F.predictable_le_prod E hE)] at hh
    exact hh
  letI : MeasurableSpace (ℝ≥0 × A) := G.predictable
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  refine ⟨hφ,?_⟩
  apply Measure.ext
  intro E hE
  rw [Measure.map_apply hφ hE,Measure.restrict_apply hE]
  change (jointPredictableMeasure G (birthTraceLaw P A) r) (φ ⁻¹' E) =
    (jointPredictableMeasure F Q T) (E∩W)
  unfold jointPredictableMeasure
  rw [trim_measurableSet_eq G.predictable_le_prod (hφ hE),
    trim_measurableSet_eq F.predictable_le_prod (hE.inter hW),←hestonTimeMeasure_eq_horizon,
    ←hestonTimeMeasure_eq_horizon]
  exact hpProd E hE

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.hestonTimeMeasure_add_shift
#print axioms RoughHeston.GirsanovPort.birthTrace_jointPredictableMeasure_shift
