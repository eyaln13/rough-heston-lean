import EulerDyadicEndpointConvergence
import EulerStoppedCovarianceTests
import Mathlib.Topology.ContinuousMap.Algebra

/-! Compact convergence of canonical Euler martingale-problem observables. -/

open Filter Set
open scoped NNReal Topology BoundedContinuousFunction

namespace RoughHeston

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype κ] in
theorem continuous_canonicalGridCoefficientSum (T : ℝ≥0) (grid : ℕ →o ℝ≥0)
    {c : ℝ≥0 → (ι → ℝ) → ℝ} (hc : Continuous (Function.uncurry c)) (a : ℕ) :
    Continuous (canonicalGridCoefficientSum T grid c a) := by
  let d (k : ℕ) (p : CanonicalPath T (ι → ℝ)) :=
    c (grid k) (canonicalPathEval T (grid k) p) * ((grid (k+1) : ℝ) - (grid k : ℝ))
  have hd (k : ℕ) : Continuous (d k) :=
    (hc.comp (continuous_const.prodMk (continuous_canonicalPathEval T (grid k)))).mul continuous_const
  change Continuous (∑ k ∈ Finset.range a, d k)
  have he : (∑ k ∈ Finset.range a, d k) = fun p => ∑ k ∈ Finset.range a, d k p := by
    funext p
    simp only [Finset.sum_apply]
  rw [he]
  exact continuous_finsetSum _ fun k _ => hd k

omit [Fintype κ] in
theorem continuous_canonicalGridEulerNoise (T : ℝ≥0) (grid : ℕ →o ℝ≥0)
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} (x : ι → ℝ) (i : ι) (a : ℕ)
    (hb : Continuous (fun z : ℝ≥0 × (ι → ℝ) => b z.1 z.2 i)) :
    Continuous (canonicalGridEulerNoise T grid b x i a) :=
  (((continuous_apply i).comp (continuous_canonicalPathEval T (grid a))).sub continuous_const).sub
    (continuous_canonicalGridCoefficientSum T grid hb a)

omit [Fintype κ] in
private theorem tendsto_canonicalPathEval_coordinate_ceiling (T t : ℝ≥0) (i : ι) :
    let U (s : ℝ≥0) : C(CanonicalPath T (ι → ℝ), ℝ) :=
      ⟨fun p => canonicalPathEval T s p i, (continuous_apply i).comp (continuous_canonicalPathEval T s)⟩
    Tendsto (fun j : ℕ => U ((uniformDyadicGrids T).grid j (eulerDyadicCeiling T j t)))
      atTop (𝓝 (U t)) := by
  dsimp only
  let U (s : ℝ≥0) : C(CanonicalPath T (ι → ℝ), ℝ) :=
    ⟨fun p => canonicalPathEval T s p i, (continuous_apply i).comp (continuous_canonicalPathEval T s)⟩
  have hEvalTime : Continuous (canonicalEvalTime T) :=
    (continuous_id.min continuous_const).subtype_mk _
  have hU : Continuous U := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (continuous_apply i).comp <|
      continuous_eval.comp (continuous_snd.prodMk (hEvalTime.comp continuous_fst))
  have he : U (min t T) = U t := by
    ext p
    change p (canonicalEvalTime T (min t T)) i = p (canonicalEvalTime T t) i
    have he' : canonicalEvalTime T (min t T) = canonicalEvalTime T t :=
      Subtype.ext (min_eq_left (min_le_right t T))
    rw [he']
  change Tendsto (fun j : ℕ => U ((uniformDyadicGrids T).grid j (eulerDyadicCeiling T j t)))
    atTop (𝓝 (U t))
  rw [← he]
  exact (hU.tendsto (min t T)).comp (tendsto_eulerDyadicCeiling_time T t)

omit [Fintype κ] in
private theorem tendsto_canonicalGridCoefficientSum_ceiling (T t : ℝ≥0)
    {c : ℝ≥0 → (ι → ℝ) → ℝ} (hc : Continuous (Function.uncurry c))
    {B : ℝ} (hB : ∀ r y, ‖c r y‖ ≤ B) :
    Tendsto (fun j : ℕ => (⟨canonicalGridCoefficientSum T ((uniformDyadicGrids T).grid j) c
      (eulerDyadicCeiling T j t), continuous_canonicalGridCoefficientSum T _ hc _⟩ :
      C(CanonicalPath T (ι → ℝ), ℝ))) atTop
      (𝓝 ⟨canonicalCoefficientIntegral T c t, continuous_canonicalCoefficientIntegral T t hc hB⟩) := by
  rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [uniform_canonicalGridCoefficientSum_ceiling_approx T t hc hB hK hε] with j hj p hp
  simpa only [ContinuousMap.coe_mk, dist_comm, dist_eq_norm] using hj p hp

omit [Fintype κ] in
/-- The drift-subtracted discrete observable converges in the
compact-open topology on real-valued canonical path tests. -/
theorem tendsto_canonicalGridEulerNoise_ceiling (T t : ℝ≥0)
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} (x : ι → ℝ) (i : ι)
    (hb : Continuous (fun z : ℝ≥0 × (ι → ℝ) => b z.1 z.2 i))
    {B : ℝ} (hB : ∀ r y, ‖b r y i‖ ≤ B) :
    Tendsto (fun j : ℕ => (⟨canonicalGridEulerNoise T ((uniformDyadicGrids T).grid j) b x i
      (eulerDyadicCeiling T j t), continuous_canonicalGridEulerNoise T _ x i _ hb⟩ :
      C(CanonicalPath T (ι → ℝ), ℝ))) atTop
      (𝓝 ⟨canonicalEulerMartingaleCoordinate T b x i t,
        continuous_canonicalEulerMartingaleCoordinate T t x i hb hB⟩) := by
  exact ((tendsto_canonicalPathEval_coordinate_ceiling T t i).sub
    (tendsto_const_nhds (x := (ContinuousMap.const _ (x i))))).sub
      (tendsto_canonicalGridCoefficientSum_ceiling T t hb hB)

/-- The continuous covariance-compensated coordinate product appropriate
for the canonical martingale problem. -/
noncomputable def canonicalEulerCompensatedProduct (T : ℝ≥0)
    (b : ℝ≥0 → (ι → ℝ) → ι → ℝ) (σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ)
    (x : ι → ℝ) (i l : ι) (t : ℝ≥0) (p : CanonicalPath T (ι → ℝ)) : ℝ :=
  canonicalEulerMartingaleCoordinate T b x i t p * canonicalEulerMartingaleCoordinate T b x l t p -
    canonicalCoefficientIntegral T (eulerCovarianceCoefficient σ i l) t p

theorem continuous_canonicalEulerCompensatedProduct (T t : ℝ≥0)
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    (x : ι → ℝ) (i l : ι)
    (hb : ∀ i, Continuous (fun z : ℝ≥0 × (ι → ℝ) => b z.1 z.2 i))
    (hσ : ∀ i j, Continuous (fun z : ℝ≥0 × (ι → ℝ) => σ z.1 z.2 i j))
    {B C : ℝ} (hB : ∀ r y i, ‖b r y i‖ ≤ B)
    (hC₀ : 0 ≤ C) (hC : ∀ r y i j, ‖σ r y i j‖ ≤ C) :
    Continuous (canonicalEulerCompensatedProduct T b σ x i l t) :=
  ((continuous_canonicalEulerMartingaleCoordinate T t x i (hb i) (fun r y => hB r y i)).mul
    (continuous_canonicalEulerMartingaleCoordinate T t x l (hb l) (fun r y => hB r y l))).sub
      (continuous_canonicalCoefficientIntegral T t (continuous_eulerCovarianceCoefficient hσ i l)
        (norm_eulerCovarianceCoefficient_le hC₀ hC i l))

theorem stronglyAdapted_canonicalEulerCompensatedProduct (T : ℝ≥0)
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    (x : ι → ℝ) (i l : ι)
    (hb : ∀ i, Continuous (fun z : ℝ≥0 × (ι → ℝ) => b z.1 z.2 i))
    (hσ : ∀ i j, Continuous (fun z : ℝ≥0 × (ι → ℝ) => σ z.1 z.2 i j))
    {B C : ℝ} (hB : ∀ r y i, ‖b r y i‖ ≤ B)
    (hC₀ : 0 ≤ C) (hC : ∀ r y i j, ‖σ r y i j‖ ≤ C) :
    MeasureTheory.StronglyAdapted (canonicalPathNaturalFiltration (E := ι → ℝ) T)
      (canonicalEulerCompensatedProduct T b σ x i l) := fun t =>
  (((stronglyAdapted_canonicalEulerMartingaleCoordinate T x i (hb i) (fun r y => hB r y i)) t).mul
    ((stronglyAdapted_canonicalEulerMartingaleCoordinate T x l (hb l) (fun r y => hB r y l)) t)).sub
      (stronglyAdapted_canonicalCoefficientIntegral T (continuous_eulerCovarianceCoefficient hσ i l)
        (norm_eulerCovarianceCoefficient_le hC₀ hC i l) t)

theorem continuous_canonicalGridEulerCompensatedProduct (T : ℝ≥0) (grid : ℕ →o ℝ≥0)
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    (x : ι → ℝ) (i l : ι) (a : ℕ)
    (hb : ∀ i, Continuous (fun z : ℝ≥0 × (ι → ℝ) => b z.1 z.2 i))
    (hσ : ∀ i j, Continuous (fun z : ℝ≥0 × (ι → ℝ) => σ z.1 z.2 i j)) :
    Continuous (canonicalGridEulerCompensatedProduct T grid b σ x i l a) :=
  ((continuous_canonicalGridEulerNoise T grid x i a (hb i)).mul
    (continuous_canonicalGridEulerNoise T grid x l a (hb l))).sub
      (continuous_canonicalGridCoefficientSum T grid (continuous_eulerCovarianceCoefficient hσ i l) a)

/-- Pointwise products of locally uniformly convergent real-valued
continuous maps converge in the compact-open topology. -/
theorem tendsto_continuousMap_pointwise_mul {Z J : Type*} [TopologicalSpace Z]
    {l : Filter J} {f g : J → C(Z, ℝ)} {F G : C(Z, ℝ)}
    (hf : Tendsto f l (𝓝 F)) (hg : Tendsto g l (𝓝 G)) :
    Tendsto (fun j => f j * g j) l (𝓝 (F * G)) := by
  let U (j : J) := (f j).prodMk (g j)
  have hu : Tendsto U l (𝓝 (F.prodMk G)) := by
    rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
    intro K hK
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have h₁ := Metric.tendstoUniformlyOn_iff.mp
      (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hf K hK) ε hε
    have h₂ := Metric.tendstoUniformlyOn_iff.mp
      (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hg K hK) ε hε
    filter_upwards [h₁, h₂] with j hj hj' z hz
    change dist (F z, G z) (f j z, g j z) < ε
    rw [Prod.dist_eq]
    exact max_lt_iff.mpr ⟨hj z hz, hj' z hz⟩
  let mul : C(ℝ × ℝ, ℝ) := ⟨fun x => x.1 * x.2, continuous_fst.mul continuous_snd⟩
  exact ((ContinuousMap.continuous_postcomp mul).tendsto (F.prodMk G)).comp hu

/-- The actual quadratic covariance observable converges to the
continuous compensated product in the compact-open topology. -/
theorem tendsto_canonicalGridEulerCompensatedProduct_ceiling (T t : ℝ≥0)
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    (x : ι → ℝ) (i l : ι)
    (hb : ∀ i, Continuous (fun z : ℝ≥0 × (ι → ℝ) => b z.1 z.2 i))
    (hσ : ∀ i j, Continuous (fun z : ℝ≥0 × (ι → ℝ) => σ z.1 z.2 i j))
    {B C : ℝ} (hB : ∀ r y i, ‖b r y i‖ ≤ B)
    (hC₀ : 0 ≤ C) (hC : ∀ r y i j, ‖σ r y i j‖ ≤ C) :
    Tendsto (fun j : ℕ => (⟨canonicalGridEulerCompensatedProduct T ((uniformDyadicGrids T).grid j) b σ x i l
      (eulerDyadicCeiling T j t), continuous_canonicalGridEulerCompensatedProduct T _ x i l _ hb hσ⟩ :
      C(CanonicalPath T (ι → ℝ), ℝ))) atTop
      (𝓝 ⟨canonicalEulerCompensatedProduct T b σ x i l t,
        continuous_canonicalEulerCompensatedProduct T t x i l hb hσ hB hC₀ hC⟩) := by
  exact (tendsto_continuousMap_pointwise_mul
    (tendsto_canonicalGridEulerNoise_ceiling T t x i (hb i) (fun r y => hB r y i))
    (tendsto_canonicalGridEulerNoise_ceiling T t x l (hb l) (fun r y => hB r y l))).sub
      (tendsto_canonicalGridCoefficientSum_ceiling T t (continuous_eulerCovarianceCoefficient hσ i l)
        (norm_eulerCovarianceCoefficient_le hC₀ hC i l))

#print axioms RoughHeston.tendsto_canonicalGridEulerNoise_ceiling
#print axioms RoughHeston.tendsto_canonicalGridEulerCompensatedProduct_ceiling
#print axioms RoughHeston.stronglyAdapted_canonicalEulerCompensatedProduct

end RoughHeston
