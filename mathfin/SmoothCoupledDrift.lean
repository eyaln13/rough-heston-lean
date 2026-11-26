import SmoothCoupledDiffusion
import SmoothVarianceLift
import EulerLinearGrowthEnergy

/-! Continuous finite-exponential drift and the continuous primitive of deterministic immigration. -/

open MeasureTheory Filter Set
open scoped NNReal

namespace RoughHeston

open MathFin.ItoIntegralCLM

variable {ι η : Type*} [Fintype ι] [Fintype η]

noncomputable def smoothExponentialResolvent (ℓ₀ : ℝ) (q rate : η → ℝ) (t : ℝ) : ℝ :=
  ℓ₀ + ∑ j, q j * Real.exp (-(rate j * t))

theorem continuous_smoothExponentialResolvent (ℓ₀ : ℝ) (q rate : η → ℝ) :
    Continuous (smoothExponentialResolvent ℓ₀ q rate) := by
  unfold smoothExponentialResolvent
  exact continuous_const.add (continuous_finsetSum _ fun j _ => by fun_prop)

theorem smoothExponentialResolvent_nonneg {ℓ₀ : ℝ} {q rate : η → ℝ}
    (hℓ₀ : 0 ≤ ℓ₀) (hq : ∀ j, 0 ≤ q j) (t : ℝ) :
    0 ≤ smoothExponentialResolvent ℓ₀ q rate t :=
  add_nonneg hℓ₀ (Finset.sum_nonneg fun j _ => mul_nonneg (hq j) (Real.exp_nonneg _))

theorem norm_smoothExponentialResolvent_le (ℓ₀ : ℝ) (q rate : η → ℝ)
    (hrate : ∀ j, 0 ≤ rate j) {t : ℝ} (ht : 0 ≤ t) :
    ‖smoothExponentialResolvent ℓ₀ q rate t‖ ≤ ‖ℓ₀‖ + ∑ j, ‖q j‖ := by
  unfold smoothExponentialResolvent
  calc
    _ ≤ ‖ℓ₀‖ + ‖∑ j, q j * Real.exp (-(rate j * t))‖ := norm_add_le _ _
    _ ≤ _ := by
      apply add_le_add_right
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _)]
      have h := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (hrate j) ht))
      simpa only [mul_one] using mul_le_mul_of_nonneg_left h (norm_nonneg (q j))

/-- The physical coordinates start at the initial level, with empty memories. -/
def smoothCoupledInitial (v : Option ι → ℝ) : SmoothCoupledState ι η
  | (i, none) => v i
  | (_, some _) => 0

private def smoothCoupledBlock (z : SmoothCoupledState ι η) (i : Option ι) : ℝ × (η → ℝ) :=
  (z (i, none), fun j => z (i, some j))

private theorem norm_smoothCoupledBlock_le (z : SmoothCoupledState ι η) (i : Option ι) :
    ‖smoothCoupledBlock z i‖ ≤ ‖z‖ := by
  apply norm_prod_le_iff.mpr
  refine ⟨norm_le_pi_norm z (i, none), (pi_norm_le_iff_of_nonneg (norm_nonneg z)).2 ?_⟩
  intro j
  exact norm_le_pi_norm z (i, some j)

/-- The continuous part of the drift, using one copy of the memory lift
for each variance coordinate. -/
noncomputable def smoothCoupledDrift (K₀ κ ℓ₀ : ℝ) (v : Option ι → ℝ) (q rate : η → ℝ)
    (t : ℝ≥0) (z : SmoothCoupledState ι η) : Option ι × Option η → ℝ
  | (i, none) =>
      (smoothVarianceLiftDrift K₀ κ (v i) (fun _ => 0) (smoothExponentialResolvent ℓ₀ q rate)
        q rate t (smoothCoupledBlock z i)).1
  | (i, some j) =>
      (smoothVarianceLiftDrift K₀ κ (v i) (fun _ => 0) (smoothExponentialResolvent ℓ₀ q rate)
        q rate t (smoothCoupledBlock z i)).2 j

theorem smoothCoupledDrift_variance (K₀ κ ℓ₀ : ℝ) (v : Option ι → ℝ) (q rate : η → ℝ)
    (t : ℝ≥0) (z : SmoothCoupledState ι η) (i : Option ι) :
    smoothCoupledDrift K₀ κ ℓ₀ v q rate t z (i, none) =
      K₀ * (v i * smoothExponentialResolvent ℓ₀ q rate t -
        (κ + smoothExponentialResolvent ℓ₀ q rate 0) * smoothVariancePositive z i +
          ∑ j, q j * rate j * z (i, some j)) := by
  simp [smoothCoupledDrift, smoothVarianceLiftDrift, smoothCoupledBlock, smoothVariancePositive]

theorem smoothCoupledDrift_memory (K₀ κ ℓ₀ : ℝ) (v : Option ι → ℝ) (q rate : η → ℝ)
    (t : ℝ≥0) (z : SmoothCoupledState ι η) (i : Option ι) (j : η) :
    smoothCoupledDrift K₀ κ ℓ₀ v q rate t z (i, some j) =
      smoothVariancePositive z i - rate j * z (i, some j) := rfl

theorem continuous_smoothCoupledDrift (K₀ κ ℓ₀ : ℝ) (v : Option ι → ℝ) (q rate : η → ℝ)
    (k : Option ι × Option η) :
    Continuous (fun w : ℝ≥0 × SmoothCoupledState ι η =>
      smoothCoupledDrift K₀ κ ℓ₀ v q rate w.1 w.2 k) := by
  obtain ⟨i, _ | j⟩ := k
  · simp_rw [smoothCoupledDrift_variance]
    have ht := (continuous_smoothExponentialResolvent ℓ₀ q rate).comp
      (NNReal.continuous_coe.comp (continuous_fst : Continuous (Prod.fst : ℝ≥0 × SmoothCoupledState ι η → ℝ≥0)))
    have hz : Continuous (fun w : ℝ≥0 × SmoothCoupledState ι η => smoothVariancePositive w.2 i) :=
      ((continuous_apply (i, none)).comp continuous_snd).max continuous_const
    have hsum : Continuous (fun w : ℝ≥0 × SmoothCoupledState ι η => ∑ j, q j*rate j*w.2 (i, some j)) :=
      continuous_finsetSum _ fun j _ => continuous_const.mul ((continuous_apply _).comp continuous_snd)
    exact continuous_const.mul (((continuous_const.mul ht).sub (continuous_const.mul hz)).add hsum)
  · simp_rw [smoothCoupledDrift_memory, smoothVariancePositive]
    fun_prop

theorem smoothCoupledDrift_linear_growth (K₀ κ ℓ₀ : ℝ) (v : Option ι → ℝ) (q rate : η → ℝ)
    (hrate : ∀ j, 0 ≤ rate j) :
    ∃ C : ℝ, 0 < C ∧ ∀ t z k, ‖smoothCoupledDrift K₀ κ ℓ₀ v q rate t z k‖ ≤ C*(1+‖z‖) := by
  classical
  let ℓ := smoothExponentialResolvent ℓ₀ q rate
  let L : ℝ := ‖ℓ₀‖ + ∑ j, ‖q j‖
  have hL : 0 ≤ L := add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hrow (i : Option ι) := smoothVarianceLiftDrift_linear_growth K₀ κ (v i) (fun _ => 0) ℓ q rate
    (S := Ici 0) (B := 0) (L := L) le_rfl hL (fun _ _ => by simp)
    (fun t ht => norm_smoothExponentialResolvent_le ℓ₀ q rate hrate ht)
  choose C hC hBound using hrow
  have hCs : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ => (hC i).le
  have hCp : 0 < (∑ i, C i)+1 := by linarith
  refine ⟨(∑ i, C i)+1, hCp, ?_⟩
  intro t z k
  obtain ⟨i, k⟩ := k
  let w := smoothVarianceLiftDrift K₀ κ (v i) (fun _ => 0) ℓ q rate t (smoothCoupledBlock z i)
  have hc : C i ≤ (∑ l, C l)+1 :=
    (Finset.single_le_sum (fun l _ => (hC l).le) (Finset.mem_univ i)).trans (le_add_of_nonneg_right zero_le_one)
  have hm : ‖w‖ ≤ ((∑ l, C l)+1)*(1+‖z‖) := by
    exact (hBound i t t.coe_nonneg _).trans (mul_le_mul hc
      (add_le_add_right (norm_smoothCoupledBlock_le z i) 1) (by positivity) hCp.le)
  cases k with
  | none => exact (norm_fst_le w).trans hm
  | some j => exact ((norm_le_pi_norm w.2 j).trans (norm_snd_le w)).trans hm

/-- Forcing acts only on the physical coordinates. -/
noncomputable def smoothCoupledImmigration (K₀ : ℝ) (β : Option ι → ℝ≥0 → ℝ)
    (t : ℝ≥0) : SmoothCoupledState ι η
  | (i, none) => K₀ * β i t
  | (_, some _) => 0

/-- Subtracting this primitive makes the drift continuous even when the
deterministic immigration rate jumps. -/
noncomputable def smoothCoupledImmigrationPrimitive (T : ℝ≥0) (K₀ : ℝ)
    (β : Option ι → ℝ≥0 → ℝ) (t : ℝ≥0) : SmoothCoupledState ι η :=
  fun k => ∫ r, smoothCoupledImmigration K₀ β r k ∂timeMeasureHorizon (min t T)

theorem smoothCoupledImmigrationPrimitive_zero (T : ℝ≥0) (K₀ : ℝ) (β : Option ι → ℝ≥0 → ℝ) :
    smoothCoupledImmigrationPrimitive (η := η) T K₀ β 0 = 0 := by
  ext k
  simp [smoothCoupledImmigrationPrimitive, timeMeasureHorizon]

theorem measurable_smoothCoupledImmigration (K₀ : ℝ) (β : Option ι → ℝ≥0 → ℝ)
    (hβ : ∀ i, Measurable (β i)) (k : Option ι × Option η) :
    Measurable (fun t => smoothCoupledImmigration K₀ β t k) := by
  obtain ⟨i, _ | j⟩ := k
  · exact measurable_const.mul (hβ i)
  · exact measurable_const

theorem norm_smoothCoupledImmigration_le (K₀ : ℝ) (β : Option ι → ℝ≥0 → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i t, ‖β i t‖ ≤ B) (t : ℝ≥0) (k : Option ι × Option η) :
    ‖smoothCoupledImmigration K₀ β t k‖ ≤ ‖K₀‖*B := by
  obtain ⟨i, _ | j⟩ := k
  · rw [smoothCoupledImmigration, norm_mul]
    exact mul_le_mul_of_nonneg_left (hβ _ _) (norm_nonneg _)
  · simpa only [smoothCoupledImmigration, norm_zero] using mul_nonneg (norm_nonneg K₀) hB

theorem continuous_smoothCoupledImmigrationPrimitive (T : ℝ≥0) (K₀ : ℝ) (β : Option ι → ℝ≥0 → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B) :
    Continuous (smoothCoupledImmigrationPrimitive (η := η) T K₀ β) := by
  apply continuous_pi
  intro k
  let f : ℝ≥0 → ℝ := fun r => smoothCoupledImmigration K₀ β r k
  have hf : Measurable f := measurable_smoothCoupledImmigration K₀ β hβ k
  have hI (a b : ℝ) : IntervalIntegrable (fun r : ℝ => f r.toNNReal) volume a b := by
    rw [intervalIntegrable_iff]
    have hc : IntervalIntegrable (fun _ : ℝ => ‖K₀‖*B) volume a b := intervalIntegrable_const
    rw [intervalIntegrable_iff] at hc
    exact hc.mono' (hf.comp continuous_real_toNNReal.measurable).stronglyMeasurable.aestronglyMeasurable
      (Eventually.of_forall (fun r => norm_smoothCoupledImmigration_le K₀ β hB hβB r.toNNReal k))
  change Continuous (fun t => ∫ r, f r ∂timeMeasureHorizon (min t T))
  simp_rw [integral_timeMeasureHorizon_eq_intervalIntegral hf]
  exact (intervalIntegral.continuous_primitive hI 0).comp
    (NNReal.continuous_coe.comp (continuous_id.min continuous_const))

theorem norm_smoothCoupledImmigrationPrimitive_le (T : ℝ≥0) (K₀ : ℝ) (β : Option ι → ℝ≥0 → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hβB : ∀ i t, ‖β i t‖ ≤ B) (t : ℝ≥0) :
    ‖smoothCoupledImmigrationPrimitive (η := η) T K₀ β t‖ ≤ ‖K₀‖*B*(T : ℝ) := by
  have hC : 0 ≤ ‖K₀‖*B := mul_nonneg (norm_nonneg _) hB
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC T.coe_nonneg)).2
  intro k
  have h := norm_integral_le_of_norm_le_const
    (μ := timeMeasureHorizon (min t T)) (f := fun r => smoothCoupledImmigration K₀ β r k)
    (Eventually.of_forall (fun r => norm_smoothCoupledImmigration_le K₀ β hB hβB r k))
  have ht : ((min t T : ℝ≥0) : ℝ) ≤ T := min_le_right _ _
  refine h.trans ?_
  rw [euler_timeMeasureHorizon_mass]
  exact mul_le_mul_of_nonneg_left ht hC

#print axioms RoughHeston.continuous_smoothCoupledDrift
#print axioms RoughHeston.smoothCoupledDrift_linear_growth
#print axioms RoughHeston.continuous_smoothCoupledImmigrationPrimitive
#print axioms RoughHeston.norm_smoothCoupledImmigrationPrimitive_le

end RoughHeston
