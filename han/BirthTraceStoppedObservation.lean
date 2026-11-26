import BirthEventTrace

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston.GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {F : Filtration ℝ≥0 m}
  {A : Set Ω} {b s : ℝ≥0}

/-- Use an age stop to evaluate the old physical martingale. Off
the birth event the original martingale is observed at b+s. The
choice there has no effect on the birth-trace law. -/
noncomputable def physicalObservationOfTrace (τ : A → ℝ≥0) (b s : ℝ≥0)
    (ω : Ω) : ℝ≥0 := by
  classical
  exact if h : ω∈A then b+min s (τ ⟨ω,h⟩) else b+s

omit m in
theorem physicalObservationOfTrace_range (τ : A → ℝ≥0) (b s : ℝ≥0) (ω : Ω) :
    b≤physicalObservationOfTrace τ b s ω ∧ physicalObservationOfTrace τ b s ω≤b+s := by
  classical
  by_cases h : ω∈A
  · simp only [physicalObservationOfTrace,dite_eq_left h]
    exact ⟨le_add_of_nonneg_right zero_le,add_le_add_right (min_le_left _ _) _⟩
  · simp [physicalObservationOfTrace,h]

omit m in
theorem physicalObservationOfTrace_eq (τ : A → ℝ≥0) (b s : ℝ≥0) (ω : A) :
    physicalObservationOfTrace τ b s ω = b+min s (τ ω) := by
  classical
  simp [physicalObservationOfTrace,ω.property]

/-- A trace stopping time translated after a birth event in F_b is a
physical stopping time in F. -/
theorem isStoppingTime_physicalObservationOfTrace (hA : MeasurableSet[F b] A)
    {τ : A → ℝ≥0} (hτ : IsStoppingTime (birthTraceFiltration F b A)
      (fun ω => (τ ω:WithTop ℝ≥0))) :
    IsStoppingTime F (fun ω => (physicalObservationOfTrace τ b s ω:WithTop ℝ≥0)) := by
  classical
  intro t
  have hset : {ω | (physicalObservationOfTrace τ b s ω:WithTop ℝ≥0)≤(t:WithTop ℝ≥0)} =
      {ω | physicalObservationOfTrace τ b s ω≤t} := by ext ω; exact WithTop.coe_le_coe
  rw [hset]
  by_cases htop : b+s≤t
  · have he : {ω | physicalObservationOfTrace τ b s ω≤t} = univ :=
      eq_univ_of_forall fun ω => (physicalObservationOfTrace_range τ b s ω).2.trans htop
    rw [he]
    exact @MeasurableSet.univ _ (F t)
  by_cases ht : t<b
  · have he : {ω | physicalObservationOfTrace τ b s ω≤t} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hv
      exact ht.not_ge ((physicalObservationOfTrace_range τ b s ω).1.trans hv)
    rw [he]
    exact @MeasurableSet.empty _ (F t)
  have hb : b≤t := le_of_not_gt ht
  have hbt : b+(t-b)=t := add_tsub_cancel_of_le hb
  obtain ⟨E,hE,hEq⟩ := hτ.measurableSet_le (t-b)
  have hE' : MeasurableSet[F t] E := by
    change MeasurableSet[F (b+(t-b))] E at hE
    rwa [hbt] at hE
  have he : {ω | physicalObservationOfTrace τ b s ω≤t} = A∩E := by
    ext ω
    by_cases h : ω∈A
    · have hEω : ω∈E ↔ τ ⟨ω,h⟩≤t-b := by
        have hx := Set.ext_iff.mp hEq ⟨ω,h⟩
        simpa only [mem_preimage,mem_ofPred_eq,WithTop.coe_le_coe] using hx
      have hObs : physicalObservationOfTrace τ b s ω = b+min s (τ ⟨ω,h⟩) :=
        physicalObservationOfTrace_eq τ b s ⟨ω,h⟩
      change physicalObservationOfTrace τ b s ω≤t ↔ ω∈A ∧ ω∈E
      rw [hObs,and_iff_right h,hEω]
      have hmin : b+min s (τ ⟨ω,h⟩)≤t ↔ min s (τ ⟨ω,h⟩)≤t-b := by
        constructor <;> intro hh
        · rw [←hbt] at hh
          exact le_of_add_le_add_left hh
        · simpa only [hbt] using add_le_add_right hh b
      rw [hmin,min_le_iff]
      have hs : ¬s≤t-b := by
        intro hs
        exact htop (by simpa only [hbt] using add_le_add_right hs b)
      simp only [hs,false_or]
    · simp [physicalObservationOfTrace,h,htop]
  rw [he]
  exact (F.mono hb A hA).inter hE'

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.isStoppingTime_physicalObservationOfTrace
