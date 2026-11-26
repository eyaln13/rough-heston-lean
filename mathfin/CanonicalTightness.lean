import CanonicalPairPath
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-! Tightness and weak subsequence extraction on canonical pair path space. -/

open Filter Set MeasureTheory
open scoped ENNReal NNReal Topology

namespace RoughHeston

/-- A uniformly tight sequence of canonical pair laws has a weakly convergent
subsequence. The convergence is in the probability-measure weak topology. -/
theorem canonicalPairPath_subsequence_of_uniform_tightness {T : ℝ≥0}
    (Pn : ℕ → ProbabilityMeasure (CanonicalPath T (ℝ × ℝ)))
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set (CanonicalPath T (ℝ × ℝ)),
      IsCompact K ∧ ∀ n, (Pn n : Measure (CanonicalPath T (ℝ × ℝ))) Kᶜ ≤ ε) :
    ∃ P : ProbabilityMeasure (CanonicalPath T (ℝ × ℝ)), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (Pn ∘ φ) atTop (𝓝 P) := by
  let S := Set.range Pn
  have hS : IsTightMeasureSet
      {((P : ProbabilityMeasure (CanonicalPath T (ℝ × ℝ))) :
        Measure (CanonicalPath T (ℝ × ℝ))) | P ∈ S} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    obtain ⟨K, hK, hKt⟩ := htight ε hε
    refine ⟨K, hK, ?_⟩
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    exact hKt n
  obtain ⟨P, _, φ, hmono, hconv⟩ :=
    (isCompact_closure_of_isTightMeasureSet hS).tendsto_subseq
      (fun n => subset_closure (Set.mem_range_self n : Pn n ∈ S))
  exact ⟨P, φ, hmono, hconv⟩

/-- Paths in a pair space with a common bound at zero and a common
continuity modulus form a compact set in the topology of uniform convergence. -/
theorem isCompact_canonicalPairPath_modulus (T : ℝ≥0) (A D : ℝ)
    (w : ℝ → ℝ) (hw : Tendsto w (𝓝 0) (𝓝 0))
    (hbounded : ∀ s t : CanonicalPathTime T, w (dist s t) ≤ D) :
    IsCompact {f : CanonicalPath T (ℝ × ℝ) |
      ‖f (canonicalEvalTime T 0)‖ ≤ A ∧
        ∀ s t : CanonicalPathTime T, dist (f s) (f t) ≤ w (dist s t)} := by
  let t₀ := canonicalEvalTime T 0
  let K : Set (BoundedContinuousFunction (CanonicalPathTime T) (ℝ × ℝ)) :=
    {f | ‖f t₀‖ ≤ A ∧ ∀ s t : CanonicalPathTime T, dist (f s) (f t) ≤ w (dist s t)}
  let e := ContinuousMap.isometryEquivBoundedOfCompact (CanonicalPathTime T) (ℝ × ℝ)
  suffices hK : IsCompact K by
    convert hK.image e.symm.continuous using 1
    ext f
    constructor
    · intro hf
      exact ⟨e f, hf, e.symm_apply_apply f⟩
    · rintro ⟨g, hg, rfl⟩
      exact hg
  refine BoundedContinuousFunction.arzela_ascoli₂ (Metric.closedBall 0 (A + D))
    (isCompact_closedBall _ _) K ?_ ?_ ?_
  · have hK : K = {f | ‖f t₀‖ ≤ A} ∩
        ⋂ s : CanonicalPathTime T, ⋂ t : CanonicalPathTime T,
          {f | dist (f s) (f t) ≤ w (dist s t)} := by
      ext f
      simp [K]
    rw [hK]
    apply IsClosed.inter
    · exact isClosed_le (continuous_norm.comp
        ((BoundedContinuousFunction.lipschitz_eval_const t₀).continuous)) continuous_const
    · exact isClosed_iInter fun s => isClosed_iInter fun t =>
        isClosed_le (((BoundedContinuousFunction.lipschitz_eval_const s).continuous).dist
          ((BoundedContinuousFunction.lipschitz_eval_const t).continuous)) continuous_const
  · intro f t hf
    rw [Metric.mem_closedBall]
    change ‖f t₀‖ ≤ A ∧ ∀ s t, dist (f s) (f t) ≤ w (dist s t) at hf
    calc
      dist (f t) 0 ≤ dist (f t) (f t₀) + dist (f t₀) 0 := dist_triangle _ _ _
      _ ≤ D + A := add_le_add ((hf.2 t t₀).trans (hbounded t t₀))
        (by simpa only [dist_zero_right] using hf.1)
      _ = A + D := add_comm _ _
  · exact Metric.equicontinuous_of_continuity_modulus w hw _ fun s t f => f.property.2 s t

/-- A bound on the initial pair value and a Hölder bound give a compact set
of pair paths. -/
theorem isCompact_canonicalPairPath_holder (T : ℝ≥0) (A H γ : ℝ)
    (hH : 0 ≤ H) (hγ : 0 < γ) :
    IsCompact {f : CanonicalPath T (ℝ × ℝ) |
      ‖f (canonicalEvalTime T 0)‖ ≤ A ∧
        ∀ s t : CanonicalPathTime T, dist (f s) (f t) ≤ H * (dist s t) ^ γ} := by
  refine isCompact_canonicalPairPath_modulus T A (H * (T : ℝ) ^ γ)
    (fun r => H * r ^ γ) ?_ ?_
  · have hid : Tendsto (fun r : ℝ => r) (𝓝 0) (𝓝 0) := tendsto_id
    simpa only [mul_zero] using (hid.rpow_const_nhds_zero hγ).const_mul H
  · intro s t
    apply mul_le_mul_of_nonneg_left _ hH
    apply Real.rpow_le_rpow dist_nonneg _ hγ.le
    change |(s.val : ℝ) - (t.val : ℝ)| ≤ (T : ℝ)
    have hs0 : (0 : ℝ) ≤ s.val := s.val.property
    have ht0 : (0 : ℝ) ≤ t.val := t.val.property
    have hsT : (s.val : ℝ) ≤ T := s.property.2
    have htT : (t.val : ℝ) ≤ T := t.property.2
    exact abs_le.2 ⟨by linarith, by linarith⟩

/-- Uniform tails for initial values and Hölder constants give weak
subsequence extraction for canonical pair laws. -/
theorem canonicalPairPath_subsequence_of_holder_tails {T : ℝ≥0} (γ : ℝ) (hγ : 0 < γ)
    (Pn : ℕ → ProbabilityMeasure (CanonicalPath T (ℝ × ℝ)))
    (htail : ∀ ε : ℝ≥0∞, 0 < ε → ∃ A H : ℝ, 0 ≤ H ∧
      ∀ n, (Pn n : Measure (CanonicalPath T (ℝ × ℝ)))
        {f | ‖f (canonicalEvalTime T 0)‖ ≤ A ∧
          ∀ s t : CanonicalPathTime T, dist (f s) (f t) ≤ H * (dist s t) ^ γ}ᶜ ≤ ε) :
    ∃ P : ProbabilityMeasure (CanonicalPath T (ℝ × ℝ)), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (Pn ∘ φ) atTop (𝓝 P) := by
  refine canonicalPairPath_subsequence_of_uniform_tightness Pn fun ε hε => ?_
  obtain ⟨A, H, hH, htails⟩ := htail ε hε
  exact ⟨_, isCompact_canonicalPairPath_holder T A H γ hH hγ, htails⟩

#print axioms canonicalPairPath_subsequence_of_uniform_tightness
#print axioms isCompact_canonicalPairPath_modulus
#print axioms isCompact_canonicalPairPath_holder
#print axioms canonicalPairPath_subsequence_of_holder_tails

end RoughHeston
