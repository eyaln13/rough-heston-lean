import CanonicalFractionalPulseAge
import FractionalFixedMeshLaw
import LebesguePulseMesh

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace RoughHeston

/-- The cluster indices comprise the initial-value component and the
finite pulse mesh. The outer option in the physical law is the companion. -/
abbrev FixedMeshClusterIndex (T b ε : ℝ) :=
  Option (Fin (⌊T/(ε/b)⌋₊+1))

noncomputable def lebesguePulseBirthTime (b ε : ℝ) (i : ℕ) : ℝ≥0 :=
  ((i:ℝ)*(ε/b)).toNNReal

noncomputable def lebesguePulseDuration (α ε : ℝ) : ℝ := ε^(1/α)

def lebesgueMeshInitial (T b ε v₀ : ℝ) : Option (FixedMeshClusterIndex T b ε)→ℝ
  | none => v₀
  | some none => v₀
  | some (some _) => 0

noncomputable def lebesgueMeshInput (T α b ε : ℝ) :
    Option (FixedMeshClusterIndex T b ε)→ℝ≥0→ℝ
  | none => fun _ => b
  | some none => fun _ => 0
  | some (some i) => translatedPulseRate (lebesguePulseBirthTime b ε i.val)
      ε (lebesguePulseDuration α ε)

noncomputable def interiorLebesguePulseIndex {T b ε : ℝ} (hT : 0≤T) (hb : 0<b) (hε : 0<ε)
    (i : {i : ℕ // i ∈ interiorPulseBirths T b ε}) : FixedMeshClusterIndex T b ε :=
  some ⟨i.val,Finset.mem_range.mp (interiorPulseBirths_subset_full hT hb hε i.property)⟩

theorem interiorLebesguePulseIndex_injective {T b ε : ℝ} (hT : 0≤T) (hb : 0<b) (hε : 0<ε) :
    Function.Injective (interiorLebesguePulseIndex hT hb hε) := by
  intro i j h
  exact Subtype.ext (congrArg Fin.val (Option.some.inj h))

theorem interior_lebesguePulseBirthTime {T b ε : ℝ} (hT : 0≤T) (hb : 0<b) (hε : 0<ε)
    {i : ℕ} (hi : i ∈ interiorPulseBirths T b ε) :
    ((lebesguePulseBirthTime b ε i:ℝ≥0):ℝ)∈Icc (T/3) (2*T/3) := by
  have h := (mem_interiorPulseBirths hT hb hε).mp hi
  rwa [lebesguePulseBirthTime,Real.coe_toNNReal _ (by positivity)]

theorem lebesgueMeshInput_measurable (T α b ε : ℝ) (i : Option (FixedMeshClusterIndex T b ε)) :
    Measurable (lebesgueMeshInput T α b ε i) := by
  cases i with
  | none => exact measurable_const
  | some i =>
    cases i with
    | none => exact measurable_const
    | some j => exact translatedPulseRate_measurable _ _ _

theorem lebesgueMeshInput_norm_le (T α b ε : ℝ) (i : Option (FixedMeshClusterIndex T b ε))
    (t : ℝ≥0) :
    ‖lebesgueMeshInput T α b ε i t‖≤‖b‖+‖ε/lebesguePulseDuration α ε‖ := by
  cases i with
  | none => exact le_add_of_nonneg_right (norm_nonneg _)
  | some i =>
    cases i with
    | none => simp only [lebesgueMeshInput,norm_zero]; positivity
    | some j => exact (norm_translatedPulseRate_le _ _ _ _).trans (le_add_of_nonneg_left (norm_nonneg _))

theorem lebesgueMeshInput_nonnegative (T α : ℝ) {b ε : ℝ} (hb : 0≤b) (hε : 0<ε)
    (i : Option (FixedMeshClusterIndex T b ε)) (t : ℝ≥0) :
    0≤lebesgueMeshInput T α b ε i t := by
  cases i with
  | none => exact hb
  | some i =>
    cases i with
    | none => exact le_rfl
    | some j =>
      unfold lebesgueMeshInput translatedPulseRate rectangularPulseRate
      exact Set.indicator_nonneg (fun _ _ => div_nonneg hε.le (Real.rpow_nonneg hε.le _)) _

theorem lebesgueMeshInitial_cluster_sum (T b ε v₀ : ℝ) :
    (∑ i : FixedMeshClusterIndex T b ε,lebesgueMeshInitial T b ε v₀ (some i))=v₀ := by
  rw [Fintype.sum_option]
  simp [lebesgueMeshInitial]

/-- The joint fractional fixed-mesh law exists for the literal deterministic
initial component, Lebesgue pulses, and original immigration companion. -/
theorem exists_explicitLebesguePulseLaw {T : ℝ≥0} {α κ σ b ε v₀ : ℝ}
    (hT : 0<T) (hα : 1/2<α) (hα' : α<1) (hκ : 0≤κ) (hb : 0<b) (hε : 0<ε) (hv₀ : 0≤v₀) :
    Nonempty (FractionalFixedMeshLaw T α κ σ (lebesgueMeshInitial T b ε v₀)
      (lebesgueMeshInput T α b ε)) := by
  have hv (i : Option (FixedMeshClusterIndex (T:ℝ) b ε)) : 0≤lebesgueMeshInitial T b ε v₀ i := by
    cases i with
    | none => exact hv₀
    | some i =>
      cases i with
      | none => exact hv₀
      | some j => exact le_rfl
  exact exists_fractionalFixedMeshLaw hT hα hα' hκ hv (lebesgueMeshInput_nonnegative _ _ hb.le hε)
    (by positivity) (lebesgueMeshInput_measurable _ _ _ _) (lebesgueMeshInput_norm_le _ _ _ _)

#print axioms interiorLebesguePulseIndex_injective
#print axioms exists_explicitLebesguePulseLaw

end RoughHeston
