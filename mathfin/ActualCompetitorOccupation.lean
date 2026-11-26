import HestonBoundaryBirth
import StoppedBoundaryOccupation

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace RoughHeston

/-- Once the stopped conditional-affine martingale is transported to
the reverse law, its expectation is the original birth expectation.
The resulting occupation bound uses only the original boundary estimate. -/
theorem actual_competitor_stopped_positive_le
    {Ω : Type*} {m : MeasurableSpace Ω}
    {P R : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    {𝒢 : Filtration ℝ≥0 m} {M V C : ℝ≥0 → Ω → ℝ}
    {α κ a b v₀ : ℝ} {U T s : ℝ≥0}
    (hα : 1/2<α) (hα' : α<1) (ha : 0≤a) (hb : 0≤b) (hv₀ : 0≤v₀)
    (hT : T≤U) (hs : s<T) (hP : HestonBoundaryProcess P 𝒢 U α κ a b v₀ M V C)
    {w : ℕ → ℝ → ℝ}
    (hw : ∀ n : ℕ, PointChargeRiccatiOn α (n:ℝ) (-κ) (-a) (T:ℝ) (w n))
    (hwn : ∀ (n : ℕ) t, 0<t → 0≤w n t)
    (hZ : 0<P {ω | V s ω=0}) {B : ℝ}
    (hOriginal : (@boundaryConditionedMeasure Ω m P {ω | V s ω=0}).real {ω | 0<V T ω}≤B)
    {τ : Ω → ℝ≥0} (hτ : Measurable[m] τ) {r : ℝ≥0} {F : ℕ → Ω → ℝ}
    (hFi : ∀ n, Integrable (F n) R)
    (hFn : ∀ n, ∀ᵐ ω ∂R, 0≤F n ω)
    (hFT : ∀ n, ∀ᵐ ω ∂R, r≤τ ω →
      F n ω=1-Real.exp (-(n:ℝ)*V T ω))
    (hFM : ∀ n, (∫ ω,F n ω ∂R) =
      ∫ ω,1-Real.exp (-affineFuturePayoff α (w n) (fun r => b+v₀*fractionalL α r)
        (fun r => V r.toNNReal ω) T s) ∂@boundaryConditionedMeasure Ω m P {ω | V s ω=0}) :
    R.real {ω | r≤τ ω ∧ 0<V T ω}≤B := by
  let _ : MeasurableSpace Ω := m
  let S := {ω | r≤τ ω}
  let Q := boundaryConditionedMeasure P {ω | V s ω=0}
  let G (n : ℕ) (ω : Ω) := if ω∈S then 1-Real.exp (-(n:ℝ)*V T ω) else F n ω
  have hSm : MeasurableSet S := measurableSet_le measurable_const hτ
  have hVm : Measurable (V T) := ((hP.variance_adapted T).mono (𝒢.le T)).measurable
  have hGF (n : ℕ) : G n =ᵐ[R] F n := by
    filter_upwards [hFT n] with ω hω
    by_cases h : ω∈S
    · exact (ite_eq_left h).trans (hω h).symm
    · exact ite_eq_right h
  have hGm (n : ℕ) : (∫ ω,G n ω ∂R)≤B := by
    have hEq := heston_boundary_birth_expectation hα hα' ha hb hv₀ hT hs hP
      (hw n) (hwn n) hZ
    rw [integral_congr_ae (hGF n),hFM n]
    exact hEq.2.trans hOriginal
  have hGn (n : ℕ) : ∀ᵐ ω ∂R, 0≤G n ω := by
    filter_upwards [hFn n,hGF n] with ω hn he
    rw [he]
    exact hn
  exact stopped_positive_le_of_laplace_test hSm hVm (hP.variance_nonnegative T)
    (fun n => (hFi n).congr (hGF n).symm) hGn
    (fun n ω hω => ite_eq_left hω) hGm

#print axioms actual_competitor_stopped_positive_le

end RoughHeston
