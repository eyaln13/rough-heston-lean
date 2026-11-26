import SmoothVarianceNonnegative
import Mathlib.Topology.Bases

/-! Closed half-line hitting times for continuous adapted paths and raw filtrations.
The compact-interval argument follows MathFin's Brownian exit-time construction. -/

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace RoughHeston

private theorem continuous_hittingAfter_nonnegative_le_iff {Ω : Type*}
    {X : ℝ≥0 → Ω → ℝ} (hX : ∀ ω, Continuous (fun t => X t ω)) (s t : ℝ≥0) (ω : Ω) :
    hittingAfter X (Ici (0 : ℝ)) s ω ≤ (t : WithTop ℝ≥0) ↔
      ∃ r ∈ Icc s t, 0 ≤ X r ω := by
  constructor
  · intro h
    have hE : ∃ r : ℝ≥0, s ≤ r ∧ X r ω ∈ Ici (0 : ℝ) := by
      by_contra hN
      simpa only [hittingAfter_def, ite_eq_right hN, top_le_iff, WithTop.coe_ne_top] using h
    let A : Set ℝ≥0 := {r | s ≤ r ∧ X r ω ∈ Ici (0 : ℝ)}
    have hA : IsClosed A := isClosed_Ici.inter (isClosed_Ici.preimage (hX ω))
    have hInf : sInf A ∈ A := hA.csInf_mem hE (OrderBot.bddBelow _)
    simp only [hittingAfter_def, ite_eq_left hE, WithTop.coe_le_coe] at h
    exact ⟨sInf A, ⟨hInf.1, h⟩, hInf.2⟩
  · rintro ⟨r, hr, hXr⟩
    exact (hittingAfter_le_of_mem (u := X) hr.1 (s := Ici (0 : ℝ)) hXr).trans
      (WithTop.coe_le_coe.mpr hr.2)

private theorem exists_nonnegative_on_interval_iff_dense {Ω : Type*}
    {X : ℝ≥0 → Ω → ℝ} (hX : ∀ ω, Continuous (fun t => X t ω)) {s t : ℝ≥0}
    (hst : s ≤ t) (d : ℕ → Icc s t) (hd : DenseRange d) (ω : Ω) :
    (∃ r ∈ Icc s t, 0 ≤ X r ω) ↔
      ∀ m : ℕ, ∃ n : ℕ, -(1 / (m+1) : ℝ) ≤ X (d n) ω := by
  constructor
  · rintro ⟨r, hr, hR⟩ m
    let f : Icc s t → ℝ := fun u => X u ω
    have hf : Continuous f := (hX ω).comp continuous_subtype_val
    have hp : (0 : ℝ) < 1 / (m+1) := by positivity
    obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.mp (hf.continuousAt (x := ⟨r, hr⟩)) _ hp
    obtain ⟨n, hn⟩ := hd.exists_dist_lt ⟨r, hr⟩ hδ
    refine ⟨n, ?_⟩
    have hval := hδf (by simpa only [dist_comm] using hn)
    rw [Real.dist_eq] at hval
    have hpart := (abs_lt.mp hval).1
    change -(1 / (m+1) : ℝ) < X (d n) ω - X r ω at hpart
    linarith
  · intro h
    obtain ⟨r, hr, hR⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hst) (hX ω).continuousOn
    refine ⟨r, hr, ?_⟩
    by_contra! hn
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (neg_pos.mpr hn)
    obtain ⟨n, hN⟩ := h m
    have hmax : X (d n) ω ≤ X r ω := hR (d n).property
    linarith

/-- The first time at or above zero after a deterministic time is a
stopping time in the original filtration for continuous adapted paths. -/
theorem isStoppingTime_hittingAfter_nonnegative_of_continuous {Ω : Type*} {m : MeasurableSpace Ω}
    {𝒢 : Filtration ℝ≥0 m} {X : ℝ≥0 → Ω → ℝ} (hXm : Adapted 𝒢 X)
    (hXc : ∀ ω, Continuous (fun t => X t ω)) (s : ℝ≥0) :
    IsStoppingTime 𝒢 (hittingAfter X (Ici (0 : ℝ)) s) := by
  intro t
  by_cases hst : s ≤ t
  · letI : Nonempty (Icc s t) := ⟨⟨s, le_rfl, hst⟩⟩
    obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq (α := Icc s t)
    have hSet : {ω | hittingAfter X (Ici (0 : ℝ)) s ω ≤ (t : WithTop ℝ≥0)} =
        ⋂ k : ℕ, ⋃ n : ℕ, {ω | -(1 / (k+1) : ℝ) ≤ X (d n) ω} := by
      ext ω
      simp only [mem_ofPred_eq, mem_iInter, mem_iUnion]
      rw [continuous_hittingAfter_nonnegative_le_iff hXc s t ω,
        exists_nonnegative_on_interval_iff_dense hXc hst d hd ω]
    rw [hSet]
    exact MeasurableSet.iInter fun k => MeasurableSet.iUnion fun n =>
      measurableSet_le measurable_const ((hXm _).mono (𝒢.mono (d n).property.2) le_rfl)
  · have hSet : {ω | hittingAfter X (Ici (0 : ℝ)) s ω ≤ (t : WithTop ℝ≥0)} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      intro h
      exact hst (WithTop.coe_le_coe.mp ((le_hittingAfter (u := X) (s := Ici (0 : ℝ)) (n := s) ω).trans h))
    rw [hSet]
    exact @MeasurableSet.empty Ω (𝒢 t)

#print axioms RoughHeston.isStoppingTime_hittingAfter_nonnegative_of_continuous

end RoughHeston
