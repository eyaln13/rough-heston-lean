import EulerLinearInterpolation
import EulerGridStateFourthMoment

/-! Fourth moments of the continuous interpolation of Euler grid states. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

private theorem gridLinearInterpolate_sub_fourth_le_of_cell
    (grid : ℕ →o ℝ≥0) (X : ℕ → Ω → ℝ) {n k : ℕ}
    (hgrid : ∀ q < n, grid q < grid (q+1)) (hk : k < n)
    {s t : ℝ≥0} (hst : s ≤ t) (hs : s ∈ Icc (grid k) (grid (k+1)))
    (ht : t ∈ Icc (grid k) (grid (k+1))) {Q : ℝ} (hQ : 0 ≤ Q)
    (hX : MemLp (fun ω => X (k+1) ω - X k ω) 4 μ)
    (hB : (∫ ω, (X (k+1) ω - X k ω)^4 ∂μ) ≤
      Q * ((grid (k+1) : ℝ) - (grid k : ℝ))^2) :
    let I (u : ℝ≥0) (ω : Ω) := gridLinearInterpolate grid (fun j => X j ω) n u
    MemLp (fun ω => I t ω - I s ω) 4 μ ∧
      (∫ ω, (I t ω - I s ω)^4 ∂μ) ≤ Q * ((t : ℝ) - (s : ℝ))^2 := by
  dsimp only
  let I (u : ℝ≥0) (ω : Ω) := gridLinearInterpolate grid (fun j => X j ω) n u
  let D (ω : Ω) := X (k+1) ω - X k ω
  let h := (grid (k+1) : ℝ) - (grid k : ℝ)
  let d := (t : ℝ) - (s : ℝ)
  let r := d / h
  have hh : 0 < h := sub_pos.mpr (NNReal.coe_lt_coe.mpr (hgrid k hk))
  have hd : 0 ≤ d := sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst)
  have hdh : d ≤ h := sub_le_sub (NNReal.coe_le_coe.mpr ht.2) (NNReal.coe_le_coe.mpr hs.1)
  have hr : 0 ≤ r := div_nonneg hd hh.le
  have hr₁ : r ≤ 1 := (div_le_iff₀ hh).2 (by simpa only [one_mul] using hdh)
  have hrh : r * h = d := div_mul_cancel₀ _ hh.ne'
  have hEq (ω : Ω) : I t ω - I s ω = r * D ω := by
    rw [show I t ω = _ from gridLinearInterpolate_eq_on_cell grid _ hgrid hk ht,
      show I s ω = _ from gridLinearInterpolate_eq_on_cell grid _ hgrid hk hs]
    change X k ω + (((t : ℝ) - (grid k : ℝ)) / h) * D ω -
      (X k ω + (((s : ℝ) - (grid k : ℝ)) / h) * D ω) = (d / h) * D ω
    dsimp only [d]
    ring
  change MemLp (fun ω => I t ω - I s ω) 4 μ ∧
    (∫ ω, (I t ω - I s ω)^4 ∂μ) ≤ Q * d^2
  refine ⟨MemLp.ae_eq (Eventually.of_forall fun ω => (hEq ω).symm) (hX.const_mul r), ?_⟩
  simp_rw [hEq, mul_pow]
  rw [integral_const_mul]
  calc
    _ ≤ r^4 * (Q * h^2) := mul_le_mul_of_nonneg_left hB (by positivity)
    _ = Q * ((r*h)^2) * r^2 := by ring
    _ ≤ Q * d^2 := by
      rw [hrh]
      have hR : r^2 ≤ 1 := by simpa using pow_le_pow_left₀ hr hr₁ 2
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hR (mul_nonneg hQ (sq_nonneg _))

private theorem memLp_and_integral_add_three_fourth_le {A B C : Ω → ℝ} {H : ℝ}
    (ha : MemLp A 4 μ) (hb : MemLp B 4 μ) (hc : MemLp C 4 μ)
    (hA : (∫ ω, A ω^4 ∂μ) ≤ H) (hB : (∫ ω, B ω^4 ∂μ) ≤ H)
    (hC : (∫ ω, C ω^4 ∂μ) ≤ H) :
    MemLp (fun ω => A ω + B ω + C ω) 4 μ ∧
      (∫ ω, (A ω + B ω + C ω)^4 ∂μ) ≤ 81 * H := by
  let D : Fin 3 → Ω → ℝ := ![A, B, C]
  have hD (j : Fin 3) : MemLp (D j) 4 μ := by
    fin_cases j
    · exact ha
    · exact hb
    · exact hc
  have hMom (j : Fin 3) : (∫ ω, D j ω^4 ∂μ) ≤ H := by
    fin_cases j
    · exact hA
    · exact hB
    · exact hC
  have h := memLp_and_integral_weighted_sum_fourth_le (a := fun _ _ => 1)
    (C := 1) (d := D) (fun _ => aestronglyMeasurable_const) (fun _ _ => by norm_num) hD hMom
  simpa [Fin.sum_univ_succ, D, add_assoc, show (3 : ℝ)^4 = 81 by norm_num] using h

/-- A uniform fourth-moment bound with time exponent two survives
continuous interpolation of a strictly increasing finite grid. -/
theorem integral_gridLinearInterpolate_sub_fourth_le
    (grid : ℕ →o ℝ≥0) (X : ℕ → Ω → ℝ) (n : ℕ)
    (hgrid : ∀ q < n, grid q < grid (q+1)) {Q : ℝ} (hQ : 0 ≤ Q)
    (hX : ∀ a b, a ≤ b → b ≤ n →
      MemLp (fun ω => X b ω - X a ω) 4 μ ∧
        (∫ ω, (X b ω - X a ω)^4 ∂μ) ≤ Q * ((grid b : ℝ) - (grid a : ℝ))^2)
    {s t : ℝ≥0} (hst : s ≤ t) (hs : s ∈ Icc (grid 0) (grid n))
    (ht : t ∈ Icc (grid 0) (grid n)) :
    let I (u : ℝ≥0) (ω : Ω) := gridLinearInterpolate grid (fun j => X j ω) n u
    MemLp (fun ω => I t ω - I s ω) 4 μ ∧
      (∫ ω, (I t ω - I s ω)^4 ∂μ) ≤ 81 * Q * ((t : ℝ) - (s : ℝ))^2 := by
  dsimp only
  let I (u : ℝ≥0) (ω : Ω) := gridLinearInterpolate grid (fun j => X j ω) n u
  let d := (t : ℝ) - (s : ℝ)
  change MemLp (fun ω => I t ω - I s ω) 4 μ ∧
    (∫ ω, (I t ω - I s ω)^4 ∂μ) ≤ 81 * Q * d^2
  have hZero (h : s = t) :
      MemLp (fun ω => I t ω - I s ω) 4 μ ∧
        (∫ ω, (I t ω - I s ω)^4 ∂μ) ≤ 81 * Q * d^2 := by
    subst t
    constructor <;> simp [d]
  by_cases hn : n = 0
  · exact hZero (hst.antisymm ((show t ≤ grid 0 by simpa [hn] using ht.2).trans hs.1))
  have hn' : 0 < n := Nat.pos_of_ne_zero hn
  obtain ⟨k, hk, hks⟩ := exists_grid_closed_cell grid hn' hs
  obtain ⟨l, hl, hlt⟩ := exists_grid_closed_cell grid hn' ht
  have hCell {q : ℕ} (hq : q < n) {u v : ℝ≥0} (huv : u ≤ v)
      (hu : u ∈ Icc (grid q) (grid (q+1))) (hv : v ∈ Icc (grid q) (grid (q+1))) :=
    gridLinearInterpolate_sub_fourth_le_of_cell grid X hgrid hq huv hu hv hQ
      (hX q (q+1) q.le_succ hq).1 (hX q (q+1) q.le_succ hq).2
  rcases lt_trichotomy k l with hkl | he | hlk
  · have hMid : grid (k+1) ≤ grid l := grid.monotone (Nat.succ_le_of_lt hkl)
    have hA := hCell hk hks.2 hks ⟨grid.monotone k.le_succ, le_rfl⟩
    have hC := hCell hl hlt.1 ⟨le_rfl, grid.monotone l.le_succ⟩ hlt
    have hB := hX (k+1) l (Nat.succ_le_of_lt hkl) hl.le
    let A (ω : Ω) := I (grid (k+1)) ω - I s ω
    let B (ω : Ω) := X l ω - X (k+1) ω
    let C (ω : Ω) := I t ω - I (grid l) ω
    have hLen (u v : ℝ≥0) (hu : s ≤ u) (huv : u ≤ v) (hv : v ≤ t) :
        Q * ((v : ℝ) - (u : ℝ))^2 ≤ Q * d^2 := by
      apply mul_le_mul_of_nonneg_left _ hQ
      apply pow_le_pow_left₀ (sub_nonneg.mpr (NNReal.coe_le_coe.mpr huv)) _ 2
      exact sub_le_sub (NNReal.coe_le_coe.mpr hv) (NNReal.coe_le_coe.mpr hu)
    have hA' : (∫ ω, A ω ^ 4 ∂μ) ≤ Q * d^2 :=
      hA.2.trans (hLen s (grid (k+1)) le_rfl hks.2 (hMid.trans hlt.1))
    have hB' : (∫ ω, B ω ^ 4 ∂μ) ≤ Q * d^2 :=
      hB.2.trans (hLen (grid (k+1)) (grid l) hks.2 hMid hlt.1)
    have hC' : (∫ ω, C ω ^ 4 ∂μ) ≤ Q * d^2 :=
      hC.2.trans (hLen (grid l) t (hks.2.trans hMid) hlt.1 le_rfl)
    have h := memLp_and_integral_add_three_fourth_le hA.1 hB.1 hC.1 hA' hB' hC'
    have hEq (ω : Ω) : I t ω - I s ω = A ω + B ω + C ω := by
      dsimp only [A, B, C]
      rw [show I (grid (k+1)) ω = X (k+1) ω from gridLinearInterpolate_at_vertex grid _ hgrid hk,
        show I (grid l) ω = X l ω from gridLinearInterpolate_at_vertex grid _ hgrid hl.le]
      ring
    simp_rw [hEq]
    exact ⟨h.1, h.2.trans_eq (by ring)⟩
  · subst l
    have h := hCell hk hst hks hlt
    exact ⟨h.1, h.2.trans (by nlinarith [mul_nonneg hQ (sq_nonneg d)])⟩
  · exact hZero (hst.antisymm
      (hlt.2.trans ((grid.monotone (Nat.succ_le_of_lt hlk)).trans hks.1)))

/-- A grid-independent fourth-moment coefficient for bounded Euler states. -/
noncomputable def boundedEulerGridFourthConstant (κ : Type*) [Fintype κ] (B C T : ℝ) : ℝ :=
  8 * B^4 * T^2 + 8 * (4 * ((Fintype.card κ : ℝ) * C^2)^2 +
    3 * ((Fintype.card κ : ℝ)^4 * C^4 * standardGaussianFourthMoment))

theorem boundedEulerGridFourthConstant_nonneg (κ : Type*) [Fintype κ] (B C T : ℝ) :
    0 ≤ boundedEulerGridFourthConstant κ B C T := by
  unfold boundedEulerGridFourthConstant
  have := standardGaussianFourthMoment_nonneg
  positivity

/-- A continuous Euler coordinate with bounded coefficients has a uniform
fourth-moment estimate at all pairs of deterministic horizon times. -/
theorem integral_eulerLinearInterpolate_sub_fourth_le {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ] [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} (grid : ℕ →o ℝ≥0) (n : ℕ)
    (hgrid : ∀ q < n, grid q < grid (q+1))
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ}
    {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ} {W : κ → ℝ≥0 → Ω → ℝ} (x : ι → ℝ) (i : ι)
    (hb : ∀ t i, Measurable (fun y => b t y i))
    (hσ : ∀ t i j, Measurable (fun y => σ t y i j))
    (hW : ∀ j, Martingale (W j) 𝒢 μ) (hW₂ : ∀ j t, MemLp (W j t) 2 μ)
    {B C : ℝ} (hB₀ : 0 ≤ B) (hC₀ : 0 ≤ C)
    (hB : ∀ t y i, ‖b t y i‖ ≤ B) (hC : ∀ t y i j, ‖σ t y i j‖ ≤ C)
    (hGaussian : ∀ k j, HasLaw (W j (grid (k + 1)) - W j (grid k))
      (gaussianReal 0 (grid (k + 1) - grid k)) μ)
    (hCov : ∀ k j l, μ[(W j (grid (k + 1)) - W j (grid k)) *
        (W l (grid (k + 1)) - W l (grid k)) | 𝒢 (grid k)] =ᵐ[μ]
      fun _ => if j = l then ((grid (k + 1) : ℝ) - (grid k : ℝ)) else 0)
    {T s t : ℝ≥0} (horizon : grid n ≤ T) (hst : s ≤ t)
    (hs : s ∈ Icc (grid 0) (grid n)) (ht : t ∈ Icc (grid 0) (grid n)) :
    let I (u : ℝ≥0) (ω : Ω) := gridLinearInterpolate grid
      (fun k => eulerGridState grid b σ W x k ω i) n u
    MemLp (fun ω => I t ω - I s ω) 4 μ ∧
      (∫ ω, (I t ω - I s ω)^4 ∂μ) ≤
      81 * boundedEulerGridFourthConstant κ B C T * ((t : ℝ) - (s : ℝ))^2 := by
  dsimp only
  refine integral_gridLinearInterpolate_sub_fourth_le grid
    (fun k ω => eulerGridState grid b σ W x k ω i) n hgrid
    (boundedEulerGridFourthConstant_nonneg κ B C T) ?_ hst hs ht
  intro a z haz hzn
  have h := integral_eulerGridState_sub_fourth_le grid x i hb hσ hW hW₂
    hB₀ hC₀ hB hC hGaussian hCov haz
  refine ⟨h.1, h.2.trans ?_⟩
  let Δ := (grid z : ℝ) - (grid a : ℝ)
  have hΔ : 0 ≤ Δ := sub_nonneg.mpr (NNReal.coe_le_coe.mpr (grid.monotone haz))
  have hΔT : Δ ≤ (T : ℝ) := by
    dsimp only [Δ]
    exact (sub_le_self _ (grid a).coe_nonneg).trans
      (NNReal.coe_le_coe.mpr ((grid.monotone hzn).trans horizon))
  have hPow : (B * Δ)^4 ≤ B^4 * (T : ℝ)^2 * Δ^2 := by
    calc
      _ = B^4 * Δ^2 * Δ^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hΔ hΔT 2) (by positivity)) (by positivity)
  simp only [boundedEulerGridFourthConstant]
  nlinarith [hPow]

#print axioms RoughHeston.integral_gridLinearInterpolate_sub_fourth_le
#print axioms RoughHeston.integral_eulerLinearInterpolate_sub_fourth_le

end RoughHeston
