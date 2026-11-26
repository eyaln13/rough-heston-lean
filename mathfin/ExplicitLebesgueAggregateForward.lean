import ExplicitLebesguePulseLaw
import ExplicitPulsedCanonicalCenter
import AggregateFixedMeshForward

/-! The literal finite Lebesgue mesh supplies the two rates of the
actual centered fractional aggregate equations. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

open MathFin.ItoLocalMartingale (nullAugmentation nullsAlg)

set_option maxHeartbeats 1800000

theorem explicitPulsedRate_measurable (T b ε d : ℝ) : Measurable (explicitPulsedRate T b ε d) := by
  unfold explicitPulsedRate
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_const.indicator measurableSet_Ioc).comp (measurable_id.sub measurable_const)

theorem norm_explicitPulsedRate_le (T b ε d s : ℝ) :
    ‖explicitPulsedRate T b ε d s‖ ≤ (fullPulseBirthCount T b ε:ℝ)*‖ε/d‖ := by
  unfold explicitPulsedRate
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _i ∈ Finset.range (fullPulseBirthCount T b ε), ‖ε/d‖ := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : s-(i:ℝ)*(ε/b) ∈ Ioc (0:ℝ) d <;> simp [rectangularPulseRate, hi] <;> positivity
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The full aggregate rate on nonnegative times is exactly the sum of the
per-cluster rates used in the separation law. -/
theorem explicitPulsedRate_eq_lebesgueMeshInput_sum {T α b ε s : ℝ}
    (hb : 0 < b) (hε : 0 < ε) (hs : 0 ≤ s) :
    explicitPulsedRate T b ε (lebesguePulseDuration α ε) s =
      ∑ i : FixedMeshClusterIndex T b ε, lebesgueMeshInput T α b ε (some i) s.toNNReal := by
  have hu (i : Fin (⌊T/(ε/b)⌋₊+1)) : lebesgueMeshInput T α b ε (some (some i)) s.toNNReal =
      rectangularPulseRate ε (lebesguePulseDuration α ε) (s-(i.val:ℝ)*(ε/b)) := by
    have ht : 0 ≤ (i.val:ℝ)*(ε/b) := by positivity
    change rectangularPulseRate ε (lebesguePulseDuration α ε)
      ((s.toNNReal:ℝ)-(((i.val:ℝ)*(ε/b)).toNNReal:ℝ)) = _
    rw [Real.coe_toNNReal s hs, Real.coe_toNNReal _ ht]
  have h0 : lebesgueMeshInput T α b ε (some none) s.toNNReal = 0 := rfl
  rw [Fintype.sum_option,h0,zero_add]
  have hEq : (∑ i : Fin (⌊T/(ε/b)⌋₊+1), lebesgueMeshInput T α b ε (some (some i)) s.toNNReal) =
      ∑ i : Fin (⌊T/(ε/b)⌋₊+1), rectangularPulseRate ε (lebesguePulseDuration α ε) (s-(i.val:ℝ)*(ε/b)) :=
    Finset.sum_congr rfl fun i _ => hu i
  rw [hEq]
  let f (n : ℕ) := rectangularPulseRate ε (lebesguePulseDuration α ε) (s-(n:ℝ)*(ε/b))
  change (∑ n ∈ Finset.range (⌊T/(ε/b)⌋₊+1), f n) = ∑ i : Fin (⌊T/(ε/b)⌋₊+1), f i.val
  exact (Fin.sum_univ_eq_sum_range f (⌊T/(ε/b)⌋₊+1)).symm

theorem constant_immigration_fractional_convolution {α b : ℝ} (hα : 0 < α) (t : ℝ) :
    volterraConvolution (fractionalK α) (fun _ => b) t = constantImmigrationConvolution α b t := by
  by_cases ht : 0 ≤ t
  · rw [constantImmigrationConvolution_eq hα ht, ← hestonKernel_eq_fractionalK_explicit,
      volterraConvolution, integral_mul_const, ← intervalIntegral.integral_of_le ht,
      intervalIntegral.integral_comp_sub_left, sub_zero, sub_self, mul_comm]
  · rw [volterraConvolution, Ioc_eq_empty_of_le (le_of_not_ge ht), setIntegral_empty,
      constantImmigrationConvolution, max_eq_right (le_of_not_ge ht), Real.zero_rpow hα.ne', zero_div, mul_zero]

variable {T : ℝ≥0} {α κ σ b ε v₀ : ℝ}
local notation "I" => FixedMeshClusterIndex (T:ℝ) b ε
local notation "Ω" => CanonicalPath T (CoupledPhysicalState I)
local notation "Ω'" => Ω × (ℝ≥0 → ℝ)
local notation "V" => lebesgueMeshInitial (T:ℝ) b ε v₀
local notation "βN" => lebesgueMeshInput (T:ℝ) α b ε
local notation "G" => canonicalPathNaturalFiltration (E := CoupledPhysicalState I) T
local notation "d" => lebesguePulseDuration α ε
local notation "βR" => explicitPulsedRate (T:ℝ) b ε d

/-- The ordinary exact model has a shared Brownian on the same law used
for the focal estimates, and both direct aggregate equations. -/
theorem explicitLebesguePulseLaw_aggregate_forward
    (L : FractionalFixedMeshLaw T α κ σ V βN)
    (hT : 0 < T) (hα : 1/2 < α) (hα' : α < 1) (hσ : 0 ≤ σ) (hb : 0 < b) (hε : 0 < ε) :
    let P := (L.law : Measure Ω).prod gaussianLimit
    let F := nullAugmentation (prodFiltration G canonicalAuxiliaryFiltration) P
    let U := FractionalFixedMeshLaw.liftedAggregateVariance (ι := I) (T := T) canonicalFirstVariance
    let Y := FractionalFixedMeshLaw.liftedAggregateVariance (ι := I) (T := T) canonicalSecondVariance
    ∃ (B : ℝ≥0 → Ω' → ℝ) (hB₂ : ∀ t, MemLp (B t) 2 P),
      MathFinBridge.BrownianOn P F T B ∧
      (∀ S : Set Ω', MeasurableSet S → P S = 0 → MeasurableSet[F 0] S) ∧
      Martingale B F P ∧ Martingale (fun t z => B t z^2-((min t T:ℝ≥0):ℝ)) F P ∧
      Nonempty (CenteredHestonRowData P F T α κ σ hα B U hB₂
        (fun s => v₀+volterraConvolution (hestonKernel α) βR s)) ∧
      Nonempty (CenteredHestonRowData P F T α κ σ hα B Y hB₂
        (fun s => v₀+constantImmigrationConvolution α b s)) := by
  intro P F U Y
  have hα₀ : 0 < α := by linarith
  have hd₀ : 0 < d := Real.rpow_pos_of_pos hε _
  have hDC : Continuous (volterraConvolution (fractionalK α) βR) := by
    rw [← hestonKernel_eq_fractionalK_explicit]
    exact continuous_explicitPulsed_convolution hα₀ hε hb hd₀
  have hDCC : Continuous (volterraConvolution (fractionalK α) (fun _ => b)) := by
    rw [funext (constant_immigration_fractional_convolution hα₀)]
    exact continuous_constantImmigrationConvolution hα₀.le
  obtain ⟨B,hB₂,hB,hBm,hClock,hX,hY⟩ := L.exists_aggregateCommonBrownian_with_forward
    hT hα hα' hσ (lebesgueMeshInitial_cluster_sum T b ε v₀) (by rfl)
    (lebesgueMeshInput_measurable T α b ε) (lebesgueMeshInput_norm_le T α b ε)
    (explicitPulsedRate_measurable T b ε d) (measurable_const (a := b))
    (norm_explicitPulsedRate_le T b ε d) (fun _ => le_rfl)
    (fun s hs => explicitPulsedRate_eq_lebesgueMeshInput_sum hb hε hs) (fun _ _ => rfl) hDC hDCC
  have hNB : MathFinBridge.BrownianOn P F T B :=
    ⟨hB.adapted,hB.zero_at_start,hB.continuous_paths,hB.normal_increment,hB.independent_of_past⟩
  have hNull (S : Set Ω') (hS : MeasurableSet S) (hS₀ : P S = 0) : MeasurableSet[F 0] S :=
    (show nullsAlg _ P ≤ F 0 from le_sup_right) S
      (MeasurableSpace.measurableSet_generateFrom ⟨hS,hS₀⟩)
  rw [← hestonKernel_eq_fractionalK_explicit] at hX
  rw [funext (constant_immigration_fractional_convolution hα₀)] at hY
  exact ⟨B,hB₂,hNB,hNull,hBm,hClock,hX,hY⟩

#print axioms RoughHeston.explicitPulsedRate_eq_lebesgueMeshInput_sum
#print axioms RoughHeston.explicitLebesguePulseLaw_aggregate_forward

end RoughHeston
