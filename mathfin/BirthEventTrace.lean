import BrownianAfterBirthConditioning
import BrownianMotion.StochasticIntegral.Predictable

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal MeasureTheory.Filtration

namespace RoughHeston

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Realizing the conditioned law on the birth event itself lets us
retain completeness for its null events. -/
noncomputable def birthTraceLaw (P : Measure Ω) (A : Set Ω) : Measure A :=
  (P A)⁻¹ • P.comap Subtype.val

def birthTraceFiltration (F : Filtration ℝ≥0 m) (b : ℝ≥0) (A : Set Ω) :
    Filtration ℝ≥0 (Subtype.instMeasurableSpace : MeasurableSpace A) where
  seq s := (F (b+s)).comap Subtype.val
  mono' := fun _ _ hs => MeasurableSpace.comap_mono (F.mono (add_le_add_right hs b))
  le' _ := MeasurableSpace.comap_mono (F.le _)

omit [IsProbabilityMeasure P] in
theorem birthTraceLaw_map {A : Set Ω} (hA : MeasurableSet A) :
    Measure.map Subtype.val (birthTraceLaw P A) = boundaryConditionedMeasure P A := by
  rw [birthTraceLaw, Measure.map_smul, map_comap_subtype_coe hA, boundaryConditionedMeasure]
  exact measurable_subtype_coe.aemeasurable

theorem birthTraceLaw_isProbability {A : Set Ω} (hA : MeasurableSet A) (hp : 0 < P A) :
    IsProbabilityMeasure (birthTraceLaw P A) := by
  constructor
  rw [birthTraceLaw, Measure.smul_apply, smul_eq_mul, (MeasurableEmbedding.subtype_coe hA).comap_apply,
    image_univ, Subtype.range_coe, ENNReal.inv_mul_cancel hp.ne' (measure_ne_top _ _)]

theorem birthTraceFiltration_complete {F : Filtration ℝ≥0 m} [F.IsComplete P]
    {b : ℝ≥0} {A : Set Ω} (hA : MeasurableSet[F b] A) :
    (birthTraceFiltration F b A).IsComplete (birthTraceLaw P A) := by
  constructor
  intro S hnull t
  have hm := F.le b _ hA
  rw [birthTraceLaw, Measure.smul_apply, smul_eq_mul, (MeasurableEmbedding.subtype_coe hm).comap_apply,
    mul_eq_zero] at hnull
  have he : P (Subtype.val '' S) = 0 :=
    hnull.resolve_left (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
  exact ⟨Subtype.val '' S, Filtration.IsComplete.measurableSet_of_null (𝓕 := F) he (b+t),
    Subtype.val_injective.preimage_image S⟩

private theorem birthTrace_measurable_iff {F : Filtration ℝ≥0 m} {b t : ℝ≥0}
    {A : Set Ω} (hA : MeasurableSet[F b] A) {S : Set A} :
    MeasurableSet[birthTraceFiltration F b A t] S ↔ MeasurableSet[F (b+t)] (Subtype.val '' S) := by
  let : MeasurableSpace Ω := F (b+t)
  exact (MeasurableEmbedding.subtype_coe (F.mono (by simp : b ≤ b+t) A hA)).measurableSet_image.symm

theorem birthTraceFiltration_rightContinuous {F : Filtration ℝ≥0 m} [F.IsRightContinuous]
    {b : ℝ≥0} {A : Set Ω} (hA : MeasurableSet[F b] A) :
    (birthTraceFiltration F b A).IsRightContinuous := by
  constructor
  intro t S hS
  apply (birthTrace_measurable_iff hA).2
  apply Filtration.IsRightContinuous.measurableSet
  rw [Filtration.rightCont_eq] at hS ⊢
  simp only [MeasurableSpace.measurableSet_iInf] at hS ⊢
  intro u hu
  have hb : b ≤ u := (show b ≤ b+t by simp).trans hu.le
  have htu : t < u-b := by
    have hsum : t + b < u := by simpa only [add_comm] using hu
    exact lt_tsub_of_add_lt_right hsum
  have h := (birthTrace_measurable_iff (t := u-b) hA).1 (hS _ htu)
  rwa [show b+(u-b)=u by rw [add_comm, tsub_add_cancel_of_le hb]] at h

omit [IsProbabilityMeasure P] in
/-- Pull back a Brownian path and the whole filtration by the same
measure-preserving observation map. -/
private theorem indep_pullback {S : Type*} [mS : MeasurableSpace S] {ν : Measure S}
    {i : S → Ω} (hi : MeasurePreserving i ν P) {f k : MeasurableSpace Ω}
    (hf : f ≤ m) (hk : k ≤ m) (hind : Indep f k P) :
    Indep (f.comap i) (k.comap i) ν := by
  apply (Indep_iff _ _ _).2
  intro A D hA hD
  obtain ⟨A', ha, rfl⟩ := hA
  obtain ⟨D', hd, rfl⟩ := hD
  let : MeasurableSpace Ω := m
  rw [← preimage_inter, hi.measure_preimage (hf _ ha |>.inter (hk _ hd)).nullMeasurableSet,
    hi.measure_preimage (hf _ ha).nullMeasurableSet, hi.measure_preimage (hk _ hd).nullMeasurableSet]
  exact (Indep_iff _ _ _).1 hind _ _ ha hd

/-- The conditioned Brownian on the trace space is measured in age from
birth, with the entire trace of the physical history available at age zero. -/
theorem brownianOn_birthTrace {F : Filtration ℝ≥0 m} {b H : ℝ≥0} {B : ℝ≥0 → Ω → ℝ}
    (hb : MathFinBridge.BrownianOn P F (b+H) B) {A : Set Ω}
    (hA : MeasurableSet[F b] A) (hp : 0 < P A) :
    MathFinBridge.BrownianOn (birthTraceLaw P A) (birthTraceFiltration F b A) H
      (fun t (ω : A) => B (b+t) ω - B b ω) := by
  let Q := boundaryConditionedMeasure P A
  let M := fun s ω => B (b+s) ω - B b ω
  have hb' : MathFinBridge.BrownianOn Q (ageFiltration F b) H M :=
    brownianOn_after_birth_conditioning hb hA hp
  have hi : MeasurePreserving (Subtype.val : A → Ω) (birthTraceLaw P A) Q :=
    ⟨measurable_subtype_coe, birthTraceLaw_map (F.le b A hA)⟩
  have had (s : ℝ≥0) : Measurable (M s) := (hb'.adapted s).measurable.mono ((ageFiltration F b).le s) le_rfl
  refine ⟨fun s => (hb'.adapted s).comp_measurable (Measurable.of_comap_le le_rfl),
    ae_of_all _ fun ω => by simp, hi.quasiMeasurePreserving.ae hb'.continuous_paths, ?_, ?_⟩
  · intro s t hst ht
    have hmeas : Measurable (fun ω => M t ω - M s ω) := (had t).sub (had s)
    have h := hb'.normal_increment s t hst ht
    rw [← hi.map_eq, Measure.map_map hmeas hi.measurable] at h
    exact h
  · intro s t hst ht
    have hmeas : Measurable (fun ω => M t ω - M s ω) := (had t).sub (had s)
    have h := indep_pullback hi (measurable_iff_comap_le.mp hmeas)
      ((ageFiltration F b).le s) (hb'.independent_of_past s t hst ht)
    rw [MeasurableSpace.comap_comp] at h
    exact h

end RoughHeston

#print axioms RoughHeston.birthTraceLaw_map
#print axioms RoughHeston.birthTraceLaw_isProbability
#print axioms RoughHeston.birthTraceFiltration_complete
#print axioms RoughHeston.birthTraceFiltration_rightContinuous

#print axioms RoughHeston.brownianOn_birthTrace
