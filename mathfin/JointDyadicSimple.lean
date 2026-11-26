import JointItoAssembly

/-!
Connect the joint predictable simple-process embedding to the deterministic
grid integrals used to define the rough Heston stochastic convolutions.
-/

open MeasureTheory ProbabilityTheory Set
open scoped MeasureTheory ProbabilityTheory NNReal BigOperators

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {𝒢 : Filtration ℝ≥0 m}

/-- The simple process with coefficient `f` on a single deterministic
cell `(a,b]` and zero value at the time origin. -/
noncomputable def jointCellSP {a b T : ℝ≥0} (hab : a ≤ b) (hbT : b ≤ T)
    {f : Ω → ℝ} (hf : Measurable[𝒢 a] f)
    {C : ℝ} (hC : ∀ ω, ‖f ω‖ ≤ C) : JointTBoundedSP T 𝒢 := by
  classical
  have hp (p : ℝ≥0 × ℝ≥0) (h : p ∈ (Finsupp.single (a, b) f).support) : p = (a, b) :=
    Finset.mem_singleton.mp (Finsupp.support_single_subset h)
  exact ⟨{ valueBot := 0
           value := Finsupp.single (a, b) f
           le_of_mem_support_value := fun p h => by rw [hp p h]; exact hab
           measurable_valueBot := stronglyMeasurable_zero.measurable
           measurable_value' := fun p h => by rw [hp p h, Finsupp.single_eq_same]; exact hf
           bounded_valueBot := ⟨0, fun _ => by simp⟩
           bounded_value := ⟨C, fun p h ω => by rw [hp p h, Finsupp.single_eq_same]; exact hC ω⟩ },
        fun p h => by rw [hp p h]; exact hbT⟩

/-- The uncurried weight of a single cell is its interval indicator
times the adapted coefficient. -/
theorem jointCellSP_uncurry {a b T : ℝ≥0} (hab : a ≤ b) (hbT : b ≤ T)
    {f : Ω → ℝ} (hf : Measurable[𝒢 a] f)
    {C : ℝ} (hC : ∀ ω, ‖f ω‖ ≤ C) :
    Function.uncurry ⇑(jointCellSP hab hbT hf hC).val
      = fun z => (Ioc a b).indicator (fun _ => f z.2) z.1 := by
  classical
  funext ⟨t, ω⟩
  change ⇑(jointCellSP hab hbT hf hC).val t ω = _
  rw [SimpleProcess.apply_eq]
  simp [jointCellSP, Finsupp.sum_single_index]

/-- The elementary integral of a single cell is the coefficient times
the increment over that cell. -/
theorem jointItoSimple_jointCellSP (M : ℝ≥0 → Ω → ℝ)
    {a b T : ℝ≥0} (hab : a ≤ b) (hbT : b ≤ T)
    {f : Ω → ℝ} (hf : Measurable[𝒢 a] f) {C : ℝ} (hC : ∀ ω, ‖f ω‖ ≤ C) :
    jointItoSimple M (jointCellSP hab hbT hf hC).val = f * (M b - M a) := by
  classical
  funext ω
  simp [jointItoSimple, jointCellSP, Finsupp.sum_single_index]

/-- The simple integrand on the first `n` deterministic grid cells. -/
noncomputable def jointGridSP (grid : ℕ →o ℝ≥0) {n : ℕ} {T : ℝ≥0}
    (hT : grid n ≤ T) {f : ℕ → Ω → ℝ} (hf : ∀ k, Measurable[𝒢 (grid k)] (f k))
    {C : ℝ} (hC : ∀ k ω, ‖f k ω‖ ≤ C) : JointTBoundedSP T 𝒢 :=
  ∑ k : Fin n, jointCellSP (grid.monotone k.val.le_succ)
    ((grid.monotone (Nat.succ_le_of_lt k.isLt)).trans hT) (hf k) (hC k)

private noncomputable def jointItoSimpleAdd (M : ℝ≥0 → Ω → ℝ) :
    SimpleProcess ℝ 𝒢 →+ (Ω → ℝ) where
  toFun := jointItoSimple M
  map_zero' := by funext ω; simp [jointItoSimple]
  map_add' V W := by
    funext ω
    simp only [jointItoSimple, Pi.add_apply, show (V + W).value = V.value + W.value from rfl]
    exact Finsupp.sum_add_index' (fun p => by simp) (fun p v w => by simp [add_mul])

/-- Integrating the grid simple process agrees with the corresponding
terminal sum used in the stochastic convolution. -/
theorem jointItoSimple_jointGridSP (M : ℝ≥0 → Ω → ℝ)
    (grid : ℕ →o ℝ≥0) {n : ℕ} {T : ℝ≥0}
    (hT : grid n ≤ T) {f : ℕ → Ω → ℝ} (hf : ∀ k, Measurable[𝒢 (grid k)] (f k))
    {C : ℝ} (hC : ∀ k ω, ‖f k ω‖ ≤ C) :
    jointItoSimple M (jointGridSP grid hT hf hC).val = gridIntegral grid f M n := by
  classical
  unfold jointGridSP
  change ((jointItoSimpleAdd (𝒢 := 𝒢) M).comp (JointTBoundedSP T 𝒢).subtype.toAddMonoidHom) _ = _
  rw [map_sum]
  change (∑ k : Fin n, jointItoSimple M (jointCellSP
    (grid.monotone k.val.le_succ) ((grid.monotone (Nat.succ_le_of_lt k.isLt)).trans hT)
    (hf k) (hC k)).val) = _
  simp only [jointItoSimple_jointCellSP]
  exact Fin.sum_univ_eq_sum_range (fun k : ℕ => f k * (M (grid (k + 1)) - M (grid k))) n

/-- The weight on the grid is the sum of the interval weights of its cells. -/
theorem jointGridSP_uncurry (grid : ℕ →o ℝ≥0) {n : ℕ} {T : ℝ≥0}
    (hT : grid n ≤ T) {f : ℕ → Ω → ℝ} (hf : ∀ k, Measurable[𝒢 (grid k)] (f k))
    {C : ℝ} (hC : ∀ k ω, ‖f k ω‖ ≤ C) :
    Function.uncurry ⇑(jointGridSP grid hT hf hC).val
      = fun z => ∑ k ∈ Finset.range n,
        (Ioc (grid k) (grid (k + 1))).indicator (fun _ => f k z.2) z.1 := by
  classical
  let cell (k : Fin n) := jointCellSP (grid.monotone k.val.le_succ)
    ((grid.monotone (Nat.succ_le_of_lt k.isLt)).trans hT) (hf k) (hC k)
  have he : (jointGridSP grid hT hf hC).val = ∑ k : Fin n, (cell k).val :=
    map_sum (JointTBoundedSP T 𝒢).subtype cell Finset.univ
  funext ⟨t, ω⟩
  change ⇑(jointGridSP grid hT hf hC).val t ω = _
  rw [he, SimpleProcess.coe_finset_sum, Finset.sum_apply, Finset.sum_apply]
  have hc (k : Fin n) : ⇑(cell k).val t ω
      = (Ioc (grid k) (grid (k.val + 1))).indicator (fun _ => f k ω) t :=
    congrFun (jointCellSP_uncurry (grid.monotone k.val.le_succ)
      ((grid.monotone (Nat.succ_le_of_lt k.isLt)).trans hT) (hf k) (hC k)) (t, ω)
  simp only [hc]
  exact Fin.sum_univ_eq_sum_range
    (fun k : ℕ => (Ioc (grid k) (grid (k + 1))).indicator (fun _ => f k ω) t) n

end RoughHeston

#print axioms RoughHeston.jointCellSP_uncurry
#print axioms RoughHeston.jointItoSimple_jointCellSP
#print axioms RoughHeston.jointItoSimple_jointGridSP
#print axioms RoughHeston.jointGridSP_uncurry
