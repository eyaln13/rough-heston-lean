import SHEStochastic.FiniteCylindricalIto
import FiniteHorizonBrownianSampling
import FiniteHorizonBrownianContinuous
import BridgeFiniteScalarItoJoint

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace RoughHeston
namespace GirsanovPort

open SHEStochastic

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} {H : ℝ≥0} {B M : ℝ≥0 → Ω → ℝ}

/-- Package a real Brownian motion adapted to the supplied filtration
as a native one-coordinate family. Repeated coordinates may be sampled
at different times. -/
noncomputable def scalarNativeFamily (hB : MathFinBridge.BrownianOn μ F H B)
    (hcts : ∀ ω, Continuous (fun t => B t ω)) : FiniteScalarIto.Family F μ H Unit where
  W := fun _ => B
  adapted := fun _ t => (hB.adapted t).measurable
  law n a := by
    constructor
    · intro t ht
      have he (i j : Fin n) : a i = a j := Subsingleton.elim _ _
      simpa only [he, ite_true, mul_one] using
        hasLaw_sampled_brownianOn hB t ht
    · intro s t hst ht
      exact indep_repeated_increment_of_brownianOn hB n hst ht
  continuous := fun _ => hcts

/-- A finite-horizon Brownian driver gives a native scalar family on
the same supplied filtration when it contains the measurable null sets. -/
theorem exists_scalarNativeFamily_of_brownianOn (hB : MathFinBridge.BrownianOn μ F H B)
    (hnull : ∀ N : Set Ω, MeasurableSet N → μ N = 0 → MeasurableSet[F 0] N) :
    ∃ P : FiniteScalarIto.Family F μ H Unit, ∀ t ≤ H, P.W () t =ᵐ[μ] B t := by
  obtain ⟨_, hB', hcts, hsame⟩ := exists_continuous_modification_of_brownianOn hB hnull
  exact ⟨scalarNativeFamily hB' hcts, hsame⟩

noncomputable def scalarHilbertBasis : HilbertBasis Unit ℝ ℝ :=
  (OrthonormalBasis.singleton Unit ℝ).toHilbertBasis

@[simp] theorem scalarHilbertBasis_apply : scalarHilbertBasis () = 1 := by
  change ((OrthonormalBasis.singleton Unit ℝ).toHilbertBasis : Unit → ℝ) () = 1
  rw [OrthonormalBasis.coe_toHilbertBasis, OrthonormalBasis.singleton_apply]

/-- The cylindrical integral in one real coordinate agrees with the
project's joint Itô integral against the same driver through `H`. -/
theorem scalarNativeIntegral_eq_joint (P : FiniteScalarIto.Coordinates F μ H Unit)
    (hM₂ : ∀ u, MemLp (M u) 2 μ) (hM : Martingale M F μ)
    (hclock : Martingale (fun u ω => M u ω ^ 2 - ((min u H : ℝ≥0) : ℝ)) F μ)
    (hagree : ∀ u ≤ H, P.W () u =ᵐ[μ] M u)
    (f : Lp ℝ 2 (jointPredictableMeasure F μ H)) :
    FiniteCylindricalIto.rawIntegral P scalarHilbertBasis f = jointItoIntegralCLM H hM₂ f := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hunit : L2HilbertSum.lift (FiniteScalarIto.inputMeasure F μ H)
      (ColumnsHilbertSum.unit scalarHilbertBasis ()) f = f := by
    apply Lp.ext
    filter_upwards [L2HilbertSum.lift_ae (FiniteScalarIto.inputMeasure F μ H)
      (ColumnsHilbertSum.unit scalarHilbertBasis ()) f] with p hp
    rw [hp]
    simp [ColumnsHilbertSum.unit, LinearIsometry.toSpanSingleton_apply]
  have hraw := FiniteCylindricalIto.rawIntegral_unit P scalarHilbertBasis () f
  rw [hunit] at hraw
  rw [hraw]
  exact finiteScalarIntegralCLM_eq_joint P () hM₂ hM hclock hagree f

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.scalarNativeFamily
#print axioms RoughHeston.GirsanovPort.exists_scalarNativeFamily_of_brownianOn
#print axioms RoughHeston.GirsanovPort.scalarHilbertBasis_apply
#print axioms RoughHeston.GirsanovPort.scalarNativeIntegral_eq_joint
