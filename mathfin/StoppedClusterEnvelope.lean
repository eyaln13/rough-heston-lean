import StoppedCompetitorDrift
import BrownianMotion.Choquet.Debut

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston

variable {Ω : Type*} [m : MeasurableSpace Ω] {F : Filtration ℝ≥0 m}

/-- The singular envelope expressed as a fixed upper threshold on a
nonnegative rescaled observable. Time is measured from the focal birth. -/
noncomputable def clusterEnvelopeValue (birth : ℝ≥0) (σ p : ℝ)
    (U Z : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  (max 0 ((s : ℝ) - birth)) ^ p * (σ^2 * U s ω / (Z s ω)^2)

theorem clusterEnvelopeValue_predictable (birth : ℝ≥0) (σ p : ℝ) {U Z : ℝ≥0 → Ω → ℝ}
    (hu : IsStronglyPredictable F U) (hz : IsStronglyPredictable F Z) :
    IsStronglyPredictable F (clusterEnvelopeValue birth σ p U Z) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have ht := measurable_subtype_coe.comp (measurable_fst_jointPredictable F)
  exact (((measurable_const.max (ht.sub measurable_const)).pow_const p).mul
    ((measurable_const.mul (StronglyMeasurable.measurable hu)).div
      ((StronglyMeasurable.measurable hz).pow_const 2))).stronglyMeasurable

omit m in
theorem clusterEnvelopeValue_continuous (birth H : ℝ≥0) (σ : ℝ) {p : ℝ} (hp : 0 < p)
    {U Z : ℝ≥0 → Ω → ℝ} (ω : Ω) (hu : ContinuousOn (fun s => U s ω) (Icc 0 H))
    (hz : ContinuousOn (fun s => Z s ω) (Icc 0 H)) (hzpos : ∀ s ≤ H, 0 < Z s ω) :
    ContinuousOn (fun s => clusterEnvelopeValue birth σ p U Z s ω) (Icc 0 H) := by
  refine ContinuousOn.mul ?_ ((continuousOn_const.mul hu).div (hz.pow 2)
    (fun s hs => pow_ne_zero _ (hzpos s hs.2).ne'))
  exact ((continuous_const.max (continuous_subtype_val.sub continuous_const)).rpow_const
    (fun _ => Or.inr hp.le)).continuousOn

/-- The bounded first strict envelope breach. The strict hitting rule lets
equality at the threshold count as a good path. -/
noncomputable def envelopeStop (H : ℝ≥0) (C : ℝ) (E : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0 :=
  ((min (H : WithTop ℝ≥0) (leastGT E C ω)).untopD H)

omit m in
private theorem coe_envelopeStop (H : ℝ≥0) (C : ℝ) (E : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    (envelopeStop H C E ω : WithTop ℝ≥0) = min (H : WithTop ℝ≥0) (leastGT E C ω) := by
  unfold envelopeStop
  cases h : leastGT E C ω with
  | top => rw [min_eq_left (le_top : (H : WithTop ℝ≥0) ≤ ⊤)]; rfl
  | coe t => rw [← WithTop.coe_min]; rfl

omit m in
theorem envelopeStop_le (H : ℝ≥0) (C : ℝ) (E : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    envelopeStop H C E ω ≤ H := by
  apply WithTop.coe_le_coe.mp
  rw [coe_envelopeStop]
  exact min_le_left _ _

theorem envelopeStop_isStoppingTime (Q : Measure Ω) [IsFiniteMeasure Q]
    [F.IsComplete Q] [F.IsRightContinuous] (H : ℝ≥0) (C : ℝ)
    {E : ℝ≥0 → Ω → ℝ} (he : IsStronglyPredictable F E) :
    IsStoppingTime F (fun ω => (envelopeStop H C E ω : WithTop ℝ≥0)) := by
  simp_rw [coe_envelopeStop]
  exact (isStoppingTime_const F H).min (he.isStronglyProgressive.isStoppingTime_leastGT Q C)

omit m in
theorem envelopeStop_lt_horizon_iff (H : ℝ≥0) (C : ℝ) (E : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    envelopeStop H C E ω < H ↔ ∃ t < H, C < E t ω := by
  rw [← WithTop.coe_lt_coe, coe_envelopeStop, min_lt_iff, leastGT_lt_iff, lt_self_iff_false, false_or]

omit m in
/-- The value is still within the bound at the hitting time by continuity.
This gives the pointwise bound throughout the closed stochastic interval. -/
theorem le_threshold_through_envelopeStop {H : ℝ≥0} {C : ℝ} {E : ℝ≥0 → Ω → ℝ}
    (ω : Ω) (hc : ContinuousOn (fun s => E s ω) (Icc 0 H)) (hz : E 0 ω ≤ C)
    (s : ℝ≥0) (hs : s ≤ envelopeStop H C E ω) : E s ω ≤ C := by
  by_contra! hgt
  let k := (C + E s ω)/2
  have hCk : C < k := by dsimp [k]; linarith
  have hks : k < E s ω := by dsimp [k]; linarith
  have hsH := hs.trans (envelopeStop_le H C E ω)
  obtain ⟨u, hu, heq⟩ := intermediate_value_Icc (a := 0) (b := s) zero_le
    (hc.mono (Icc_subset_Icc_right hsH)) (show k ∈ Icc (E 0 ω) (E s ω) from
      ⟨hz.trans hCk.le, hks.le⟩)
  have hus : u < s := lt_of_le_of_ne hu.2 (fun h => by rw [h] at heq; linarith)
  have hhit : leastGT E C ω < (s : WithTop ℝ≥0) := leastGT_lt_iff.2 ⟨u, hus, hCk.trans_eq heq.symm⟩
  have hbad : (envelopeStop H C E ω : WithTop ℝ≥0) < s := by
    rw [coe_envelopeStop]; exact (min_le_right _ _).trans_lt hhit
  exact (not_lt_of_ge hs) (WithTop.coe_lt_coe.mp hbad)

omit m in
/-- On the actual stopped interval, bounding the scaled observable by its
threshold gives the squared drift bound at each positive age. -/
theorem competitor_cost_before_envelopeStop (b H : ℝ≥0) (σ : ℝ) {p C : ℝ}
    (hp : 0 < p) (hC : 0 ≤ C) (U Z X Y : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hu : ContinuousOn (fun s => U s ω) (Icc 0 H))
    (hz : ContinuousOn (fun s => Z s ω) (Icc 0 H)) (hzpos : ∀ s ≤ H, 0 < Z s ω)
    (hun : ∀ s ≤ H, 0 ≤ U s ω) (hux : ∀ s ≤ H, U s ω ≤ X s ω)
    {s : ℝ≥0} (hbs : b < s)
    (hs : s ≤ envelopeStop H C (clusterEnvelopeValue b σ p U Z) ω) :
    competitorAfterBirth b σ U Z X Y s ω ^ 2 ≤ C / ((s : ℝ) - b)^p := by
  let E := clusterEnvelopeValue b σ p U Z
  have hInit : E 0 ω ≤ C := by
    simpa [E, clusterEnvelopeValue, Real.zero_rpow hp.ne'] using hC
  have hE := le_threshold_through_envelopeStop ω
    (clusterEnvelopeValue_continuous b H σ hp ω hu hz hzpos) hInit s hs
  have hsH := hs.trans (envelopeStop_le H C E ω)
  have ha : 0 < (s : ℝ) - b := sub_pos.mpr (by exact_mod_cast hbs)
  have hpow := Real.rpow_pos_of_pos ha p
  simp only [clusterEnvelopeValue, max_eq_right ha.le] at hE
  rw [competitorAfterBirth, ite_eq_left hbs]
  exact (competitorControl_sq_le (hun s hsH) (hux s hsH) (hzpos s hsH)).trans
    ((le_div_iff₀ hpow).2 (by simpa only [mul_comm] using hE))

end RoughHeston

#print axioms RoughHeston.clusterEnvelopeValue_predictable
#print axioms RoughHeston.clusterEnvelopeValue_continuous
#print axioms RoughHeston.envelopeStop_isStoppingTime
#print axioms RoughHeston.envelopeStop_lt_horizon_iff
#print axioms RoughHeston.le_threshold_through_envelopeStop

#print axioms RoughHeston.competitor_cost_before_envelopeStop
