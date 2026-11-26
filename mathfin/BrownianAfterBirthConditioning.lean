import FiniteHorizonLevy
import LaplaceBoundary

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace RoughHeston

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- At age zero, all of the information available at the physical time
of birth remains available. -/
def ageFiltration (F : Filtration ℝ≥0 m) (b : ℝ≥0) : Filtration ℝ≥0 m where
  seq s := F (b + s)
  mono' := fun _ _ h => F.mono (add_le_add_right h b)
  le' s := F.le (b + s)

private theorem conditioned_diffusion_event {A S : Set Ω} (hS : MeasurableSet S)
    (hA : 0 < P A) (hSA : P (S ∩ A) = P S * P A) :
    boundaryConditionedMeasure P A S = P S := by
  rw [boundaryConditionedMeasure, Measure.smul_apply, Measure.restrict_apply hS, hSA, smul_eq_mul,
    mul_left_comm, ENNReal.inv_mul_cancel hA.ne' (measure_ne_top _ _), mul_one]

/-- Conditioning on a positive-probability past event preserves independence
of the future increment and the *entire* past sigma-algebra. -/
theorem indep_boundaryConditionedMeasure_of_past {a b : MeasurableSpace Ω}
    (ha : a ≤ m) (hb : b ≤ m) {A : Set Ω} (hA : MeasurableSet[b] A) (hp : 0 < P A)
    (hi : Indep a b P) : Indep a b (boundaryConditionedMeasure P A) := by
  apply (Indep_iff _ _ _).2
  intro S E hS hE
  let : MeasurableSpace Ω := m
  have hold : ∀ S E, MeasurableSet[a] S → MeasurableSet[b] E → P (S ∩ E) = P S * P E := (Indep_iff _ _ _).1 hi
  rw [@conditioned_diffusion_event Ω m P _ A S (ha _ hS) hp (hold S A hS hA)]
  rw [boundaryConditionedMeasure, Measure.smul_apply, Measure.smul_apply,
    Measure.restrict_apply ((ha _ hS).inter (hb _ hE)), Measure.restrict_apply (hb _ hE),
    inter_assoc, hold S (E ∩ A) hS (@MeasurableSet.inter Ω b E A hE hA)]
  simp only [smul_eq_mul]
  ac_rfl

/-- Brownian increments measured from birth are Brownian in the shifted
joint filtration under the law conditioned on the birth event. -/
theorem brownianOn_after_birth_conditioning {F : Filtration ℝ≥0 m} {b H : ℝ≥0}
    {B : ℝ≥0 → Ω → ℝ} (hB : MathFinBridge.BrownianOn P F (b+H) B)
    {A : Set Ω} (hA : MeasurableSet[F b] A) (hp : 0 < P A) :
    MathFinBridge.BrownianOn (boundaryConditionedMeasure P A) (ageFiltration F b) H
      (fun s ω => B (b+s) ω - B b ω) := by
  let Q := boundaryConditionedMeasure P A
  have hac : Q ≪ P := by
    apply Measure.AbsolutelyContinuous.trans (Measure.AbsolutelyContinuous.smul_left
      (Measure.AbsolutelyContinuous.refl (P.restrict A)) _)
    exact Measure.restrict_le_self.absolutelyContinuous
  have heq (s t : ℝ≥0) (ω : Ω) :
      B (b+t) ω - B b ω - (B (b+s) ω - B b ω) = B (b+t) ω - B (b+s) ω := by ring
  refine ⟨fun s => (hB.adapted (b+s)).sub ((hB.adapted b).mono (F.mono (by simp))),
    ae_of_all _ fun ω => by simp, ?_, ?_, ?_⟩
  · filter_upwards [hac.ae_le hB.continuous_paths] with ω hc
    have hmap : MapsTo (fun s : ℝ≥0 => b + s) (Icc 0 H) (Icc 0 (b+H)) :=
      fun _ hs => ⟨zero_le, add_le_add_right hs.2 b⟩
    exact (hc.comp (continuous_const.add continuous_id).continuousOn hmap).sub continuousOn_const
  · intro s t hst ht
    simp_rw [heq]
    let inc := fun ω => B (b+t) ω - B (b+s) ω
    have hinc : Measurable inc := ((hB.adapted (b+t)).measurable.mono (F.le _) le_rfl).sub
      ((hB.adapted (b+s)).measurable.mono (F.le _) le_rfl)
    have hi := hB.independent_of_past (b+s) (b+t) (by gcongr) (by gcongr)
    have hlaw := hB.normal_increment (b+s) (b+t) (by gcongr) (by gcongr)
    have hm : Measure.map inc Q = Measure.map inc P := by
      ext S hS
      rw [Measure.map_apply hinc hS, Measure.map_apply hinc hS]
      apply conditioned_diffusion_event (hinc hS) hp
      exact (Indep_iff _ _ _).1 hi _ A ⟨S,hS,rfl⟩ (F.mono (by simp) _ hA)
    change Measure.map inc Q = _
    rw [hm]
    simpa only [add_tsub_add_eq_tsub_left] using hlaw
  · intro s t hst ht
    simp_rw [heq]
    have hi := hB.independent_of_past (b+s) (b+t) (by gcongr) (by gcongr)
    apply indep_boundaryConditionedMeasure_of_past ?_ (F.le (b+s)) (F.mono (by simp) _ hA) hp hi
    exact (measurable_iff_comap_le.mp
      (((hB.adapted (b+t)).measurable.mono (F.le _) le_rfl).sub
        ((hB.adapted (b+s)).measurable.mono (F.le _) le_rfl)))

end RoughHeston

#print axioms RoughHeston.indep_boundaryConditionedMeasure_of_past
#print axioms RoughHeston.brownianOn_after_birth_conditioning
