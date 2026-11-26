import BrownianMotion.Gaussian.BrownianMotion
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open MeasureTheory ProbabilityTheory
open scoped NNReal RealInnerProductSpace

namespace RoughHeston
namespace GirsanovPort

section Reindex

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

noncomputable def euclideanReindex (f : κ → ι) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun j => x (f j))
      map_add' := by intros; ext; rfl
      map_smul' := by intros; ext; rfl }

@[simp] theorem euclideanReindex_apply (f : κ → ι) (x : EuclideanSpace ℝ ι) (j : κ) :
    euclideanReindex f x j = x (f j) := rfl

variable [DecidableEq ι] [DecidableEq κ]

/-- Pullback along an arbitrary finite index map, allowing repeated
observations. The covariance proof uses Mathlib's `IsGaussian.ext` and
the same coordinate calculation as `measurePreserving_restrict₂_multivariateGaussian`. -/
theorem measurePreserving_euclideanReindex_multivariateGaussian
    {m : EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (f : κ → ι) :
    MeasurePreserving (euclideanReindex f) (multivariateGaussian m S)
      (multivariateGaussian (euclideanReindex f m) (S.submatrix f f)) where
  measurable := (euclideanReindex f).measurable
  map_eq := by
    apply IsGaussian.ext
    · simp only [id_eq, integral_id_multivariateGaussian]
      rw [ContinuousLinearMap.integral_id_map, integral_id_multivariateGaussian]
      exact IsGaussian.integrable_id
    rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun κ ℝ).toBasis fun i j => ?_
    rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
      covarianceBilin_apply_eq_cov, covariance_map]
    · have h (i : κ) : (fun u => ⟪(EuclideanSpace.basisFun κ ℝ).toBasis i, u⟫) ∘
          euclideanReindex f = fun u => u (f i) := by
        ext
        simp [PiLp.inner_apply]
      simp_rw [h, covariance_eval_multivariateGaussian hS,
        covarianceBilin_multivariateGaussian (hS.submatrix _)]
      simp
    any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
    · fun_prop
    · exact IsGaussian.memLp_two_id

end Reindex

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
  {F : Filtration ℝ≥0 mΩ}

/-- The scalar Brownian law sampled at arbitrarily repeated times.
This gives the finite observations of a one-coordinate Brownian family. -/
theorem hasLaw_sampled_preBrownian (hB : IsPreBrownianReal B μ) {n : ℕ} (t : Fin n → ℝ≥0) :
    HasLaw (fun ω => WithLp.toLp 2 (fun i => B (t i) ω))
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
        (fun i j => ((min (t i) (t j) : ℝ≥0) : ℝ))) μ := by
  classical
  let I : Finset ℝ≥0 := Finset.univ.image t
  let f (i : Fin n) : I := ⟨t i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  have hI := (measurePreserving_equiv_gaussianProjectiveFamily I).hasLaw.comp (hB.hasLaw I)
  have hh := (measurePreserving_euclideanReindex_multivariateGaussian
    (m := 0) (posSemidef_brownianCovMatrix I) f).hasLaw.comp hI
  rw [map_zero] at hh
  exact hh

/-- Repeating a scalar Brownian increment in a finite vector preserves
its independence from the entire supplied filtration at the earlier time. -/
theorem indep_repeated_increment_of_filtered_preBrownian [hB : IsFilteredPreBrownian B F μ]
    (n : ℕ) {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (MeasurableSpace.comap
      (fun ω => WithLp.toLp 2 (fun _ : Fin n => B t ω - B s ω))
      (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n)))) (F s) μ := by
  apply indep_of_indep_of_le_left (hB.indep s t hst)
  let V (a : ℝ) : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun _ => a
  change MeasurableSpace.comap (V ∘ (B t - B s)) _ ≤ _
  rw [← MeasurableSpace.comap_comp]
  apply MeasurableSpace.comap_mono (Measurable.comap_le _)
  fun_prop

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.measurePreserving_euclideanReindex_multivariateGaussian
#print axioms RoughHeston.GirsanovPort.hasLaw_sampled_preBrownian
#print axioms RoughHeston.GirsanovPort.indep_repeated_increment_of_filtered_preBrownian
