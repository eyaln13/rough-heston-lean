import CanonicalAuxiliaryDriver
import ProductFiltrationLift

/-! Finite vectors of Gaussian martingale drivers in their common product filtration. -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace RoughHeston

private structure EulerDriverSpace (n : ℕ) where
  Ω : Type
  [meas : MeasurableSpace Ω]
  μ : Measure Ω
  [prob : IsProbabilityMeasure μ]
  F : Filtration ℝ≥0 meas
  W : Fin n → ℝ≥0 → Ω → ℝ
  hm : ∀ i, Martingale (W i) F μ
  h₂ : ∀ i t, MemLp (W i t) 2 μ
  law : ∀ i s t, s ≤ t → HasLaw (W i t - W i s) (gaussianReal 0 (t - s)) μ
  cross : ∀ i j, Martingale (fun t ω => W i t ω * W j t ω -
    if i = j then (t : ℝ) else 0) F μ

attribute [instance] EulerDriverSpace.meas EulerDriverSpace.prob

private noncomputable def extendEulerDriver {n : ℕ} (D : EulerDriverSpace n) :
    EulerDriverSpace (n+1) := by
  let S := ℝ≥0 → ℝ
  let G := canonicalAuxiliaryFiltration
  have pre := isBrownianReal_brownian.toIsPreBrownianReal
  let _ : IsFilteredPreBrownian brownian G gaussianLimit :=
    pre.isFilteredPreBrownian measurable_brownian
  have hb := IsPreBrownianReal.isMartingale brownian G gaussianLimit
  let W (i : Fin (n+1)) : ℝ≥0 → D.Ω × S → ℝ := Fin.cases
    (fun t (z : D.Ω × S) => brownian t z.2)
    (fun j t (z : D.Ω × S) => D.W j t z.1) i
  refine { Ω := D.Ω × S, μ := D.μ.prod gaussianLimit, F := prodFiltration D.F G,
           W := W, hm := ?_, h₂ := ?_, law := ?_, cross := ?_ }
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact martingale_prod_snd hb
    · exact martingale_prod_fst (D.hm j)
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro t
      exact (hasLaw_brownian_eval.memLp (memLp_id_gaussianReal 2)).comp_measurePreserving
        (measurePreserving_snd (μ := D.μ) (ν := gaussianLimit))
    · intro t
      exact (D.h₂ j t).comp_measurePreserving
        (measurePreserving_fst (μ := D.μ) (ν := gaussianLimit))
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro s t hst
      have hd : nndist (t : ℝ) (s : ℝ) = t-s := by
        apply NNReal.eq
        rw [← dist_nndist, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (show (s : ℝ) ≤ (t : ℝ) from hst)), NNReal.coe_sub hst]
      exact (hd ▸ pre.hasLaw_sub t s).comp
        (measurePreserving_snd (μ := D.μ) (ν := gaussianLimit)).hasLaw
    · intro s t hst
      exact (D.law j s t hst).comp
        (measurePreserving_fst (μ := D.μ) (ν := gaussianLimit)).hasLaw
  · intro i
    refine Fin.cases ?_ (fun a => ?_) i <;> intro j
    · refine Fin.cases ?_ (fun b => ?_) j
      · simpa [W, sq] using martingale_prod_snd (F := D.F) (μ := D.μ)
          (IsFilteredPreBrownian.squareSubTime_isMartingale
            (X := brownian) (𝓕 := G) (P := gaussianLimit))
      · simpa [W, Fin.succ_ne_zero b |>.symm, mul_comm] using martingale_prod_mul (D.hm b) hb
    · refine Fin.cases ?_ (fun b => ?_) j
      · simpa [W] using martingale_prod_mul (D.hm a) hb
      · simpa [W] using martingale_prod_fst (G := G) (ν := gaussianLimit) (D.cross a b)

private noncomputable def finiteEulerDriver : (n : ℕ) → EulerDriverSpace n
  | 0 => { Ω := ℝ≥0 → ℝ, μ := gaussianLimit, F := canonicalAuxiliaryFiltration,
           W := Fin.elim0, hm := fun i => i.elim0, h₂ := fun i => i.elim0, law := fun i => i.elim0, cross := fun i => i.elim0 }
  | n+1 => extendEulerDriver (finiteEulerDriver n)

/-- Existence of the vector driving an Euler scheme, including the conditional
covariance of its increments given the entire product past. -/
theorem exists_finite_gaussian_euler_driver (κ : Type*) [Fintype κ] [DecidableEq κ] :
    ∃ (Ω : Type) (m : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (F : Filtration ℝ≥0 m) (W : κ → ℝ≥0 → Ω → ℝ),
      (∀ a, Martingale (W a) F μ) ∧ (∀ a t, MemLp (W a t) 2 μ) ∧
      (∀ a s t, s ≤ t → HasLaw (W a t - W a s) (gaussianReal 0 (t-s)) μ) ∧
      (∀ a b s t, s ≤ t →
        μ[(W a t - W a s) * (W b t - W b s) | F s] =ᵐ[μ]
          fun _ => if a = b then ((t : ℝ) - s) else 0) := by
  let D := finiteEulerDriver (Fintype.card κ)
  let e := Fintype.equivFin κ
  refine ⟨D.Ω, D.meas, D.μ, D.prob, D.F, fun a => D.W (e a),
    fun a => D.hm _, fun a => D.h₂ _, fun a => D.law _, ?_⟩
  intro a b s t hst
  have h := conditional_covariance_of_compensated_product
    (C := fun (u : ℝ≥0) (_ : D.Ω) => if e a = e b then (u : ℝ) else 0)
    (D.hm _) (D.hm _) (D.cross (e a) (e b)) (D.h₂ _) (D.h₂ _) hst
  by_cases hab : a = b
  · simpa [hab, Pi.sub_def, condExp_const (D.F.le s)] using h
  · change _ =ᵐ[D.μ] fun _ => if a = b then ((t : ℝ) - s) else 0
    rw [ite_eq_right hab]
    exact (by simpa [hab, e.injective.ne hab, Pi.sub_def] using h : _ =ᵐ[D.μ] (0 : D.Ω → ℝ))

#print axioms exists_finite_gaussian_euler_driver

end RoughHeston
