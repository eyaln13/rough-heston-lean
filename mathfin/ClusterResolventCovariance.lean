import ClusterMomentCovariance
import TiltingItoPairing
import ProductKernelEnergy

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Interval

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 m} {T : ℝ≥0}
  {B M C U : ℝ≥0 → Ω → ℝ} {σ ε : ℝ}

private theorem predictable_time_measurable :
    @Measurable (ℝ≥0 × Ω) ℝ≥0 F.predictable _ Prod.fst := by
  let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  apply measurable_of_Ioi
  intro s
  rw [show (Prod.fst : ℝ≥0 × Ω → ℝ≥0) ⁻¹' Ioi s = Ioi s ×ˢ (univ : Set Ω) by ext p; simp]
  exact measurableSet_predictable_Ioi_prod (𝓕 := F) MeasurableSet.univ

private theorem deterministic_kernel_sqrt_predictable {k : ℝ≥0 → ℝ}
    (hk : Measurable k) (hU : IsStronglyPredictable F U) :
    StronglyMeasurable[F.predictable] (fun p => k p.1 * Real.sqrt (U p.1 p.2)) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact ((hk.comp predictable_time_measurable).mul hU.measurable.sqrt).stronglyMeasurable

/-- The real-time bracket density integrates to the time integral of
the actual cluster mean. -/
theorem expected_clusterClock_eq
    (hCeq : C T =ᵐ[P] fun ω => ∫ s in (0 : ℝ)..(T : ℝ), σ ^ 2 * U s.toNNReal ω)
    (hU : Integrable (fun p : ℝ × Ω => U p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod P)) :
    (∫ ω, C T ω ∂P) =
      σ ^ 2 * (∫ s in (0 : ℝ)..(T : ℝ), (∫ ω, U s.toNNReal ω ∂P)) := by
  let τ := volume.restrict (Ioc (0 : ℝ) (T : ℝ))
  have ht : (0 : ℝ) ≤ (T : ℝ) := NNReal.coe_nonneg _
  rw [integral_congr_ae hCeq]
  simp only [intervalIntegral.integral_of_le ht]
  have hUI : Integrable (fun p : ℝ × Ω => σ ^ 2 * U p.1.toNNReal p.2) (τ.prod P) := hU.const_mul _
  rw [← integral_prod_symm _ hUI, integral_prod _ hUI]
  simp_rw [integral_const_mul]
  rfl

/-- Pointwise covariance for a cluster represented through the
second-kind resolvent and its own variance martingale amplitude. -/
theorem clusterResolvent_jointIto_pairing
    (hB₂ : ∀ t, MemLp (B t) 2 P) (hB : Martingale B F P)
    (hBclock : Martingale (fun t ω => B t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) F P)
    (hU : IsStronglyPredictable F U) (hU₀ : ∀ t ω, 0 ≤ U t ω)
    {R : ℝ → ℝ} (hR : Measurable R)
    (f g : Lp ℝ 2 (jointPredictableMeasure F P T))
    (hf : ⇑f =ᵐ[jointPredictableMeasure F P T]
      fun p => (σ * R ((T : ℝ) - p.1)) * Real.sqrt (U p.1 p.2))
    (hg : ⇑g =ᵐ[jointPredictableMeasure F P T] fun p => σ * Real.sqrt (U p.1 p.2)) :
    (∫ ω, jointItoIntegralCLM T hB₂ f ω * jointItoIntegralCLM T hB₂ g ω ∂P) =
      σ ^ 2 * (∫ s, R ((T : ℝ) - s) * (∫ ω, U s ω ∂P) ∂hestonTimeMeasure T) := by
  let k (s : ℝ≥0) := σ * R ((T : ℝ) - (s : ℝ))
  let w (_ : ℝ≥0) := σ
  let D (s : ℝ≥0) (ω : Ω) : ℝ := 1
  have hkm : Measurable k := (hR.comp (measurable_const.sub measurable_subtype_coe)).const_mul σ
  have hwm : Measurable w := measurable_const
  have hgm : ⇑g =ᵐ[jointPredictableMeasure F P T] fun p => D p.1 p.2 * w p.1 * Real.sqrt (U p.1 p.2) := by
    simpa only [D, w, one_mul] using hg
  have hgsm : StronglyMeasurable[F.predictable] (fun p => D p.1 p.2 * w p.1 * Real.sqrt (U p.1 p.2)) := by
    simpa only [D, one_mul] using deterministic_kernel_sqrt_predictable hwm hU
  rw [integral_jointItoIntegralCLM_product T hB₂ hB hBclock]
  simp_rw [mul_comm (f _)]
  have hPair := integral_jointHeston_predictable_pairing T f g k w D U hU₀ hf hgm
    (deterministic_kernel_sqrt_predictable hkm hU) hgsm
  rw [hPair, hestonTimeMeasure_eq_horizon, ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun s => by simp only [D, one_mul, k, w]; ring

/-- The first moment under the exact terminal tilt follows from the
cluster equation through the same joint Itô isometry. -/
theorem clusterResolvent_sizeBiased_mean
    (hM : Martingale M F P) (hC : Martingale (fun t => M t * M t - C t) F P)
    (hM₂ : MemLp (M T) 2 P) (hM₀ : M 0 =ᵐ[P] 0) (hC₀ : C 0 =ᵐ[P] 0)
    (hB₂ : ∀ t, MemLp (B t) 2 P) (hB : Martingale B F P)
    (hBclock : Martingale (fun t ω => B t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) F P)
    (hU : IsStronglyPredictable F U) (hU₀ : ∀ t ω, 0 ≤ U t ω)
    {R : ℝ → ℝ} (hR : Measurable R)
    (f g : Lp ℝ 2 (jointPredictableMeasure F P T))
    (hf : ⇑f =ᵐ[jointPredictableMeasure F P T]
      fun p => (σ * R ((T : ℝ) - p.1)) * Real.sqrt (U p.1 p.2))
    (hg : ⇑g =ᵐ[jointPredictableMeasure F P T] fun p => σ * Real.sqrt (U p.1 p.2))
    (hMt : M T =ᵐ[P] jointItoIntegralCLM T hB₂ g)
    {u : ℝ} (hUt : U T =ᵐ[P] fun ω => u + jointItoIntegralCLM T hB₂ f ω)
    (hε : 0 < ε) (hZ : ∀ᵐ ω ∂P, 0 ≤ ε + M T ω) :
    let Z (ω : Ω) := ε + M T ω
    let Q := sizeBiasedLaw P Z ε
    IsProbabilityMeasure Q ∧
      (∫ ω, Z ω ^ 2 ∂P) = ε ^ 2 + (∫ ω, C T ω ∂P) ∧
      (∫ ω, U T ω ∂Q) = u + (σ ^ 2 / ε) *
        (∫ s, R ((T : ℝ) - s) * (∫ ω, U s ω ∂P) ∂hestonTimeMeasure T) ∧
      (∫ ω, Z ω ∂Q) = ε + (∫ ω, C T ω ∂P) / ε := by
  let S := jointItoIntegralCLM T hB₂ f
  have hCross : (∫ ω, S ω * M T ω ∂P) = σ ^ 2 *
      (∫ s, R ((T : ℝ) - s) * (∫ ω, U s ω ∂P) ∂hestonTimeMeasure T) := by
    calc
      _ = ∫ ω, S ω * jointItoIntegralCLM T hB₂ g ω ∂P :=
        integral_congr_ae (EventuallyEq.rfl.mul hMt)
      _ = _ := clusterResolvent_jointIto_pairing hB₂ hB hBclock hU hU₀ hR f g hf hg
  obtain ⟨hP, hSq, hUmean, hZmean⟩ := sizeBiased_cluster_terminal_means (show (0 : ℝ≥0) ≤ T from zero_le)
    hM hM₂ hM₀ hC₀ hC hε (Lp.memLp S) (integral_jointItoIntegralCLM_eq_zero T hB₂ hB hBclock f)
    hCross hUt hZ
  refine ⟨hP, hSq, hUmean.trans ?_, hZmean⟩
  ring

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.expected_clusterClock_eq
#print axioms RoughHeston.GirsanovPort.clusterResolvent_jointIto_pairing
#print axioms RoughHeston.GirsanovPort.clusterResolvent_sizeBiased_mean
