import CanonicalPhysicalDrivePath
import WeakMovingZeroSet
import FractionalKernelL1

/-! Integrated direct-kernel identities on fixed-dimensional canonical
laws, and their stability in the weak limit. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

set_option maxHeartbeats 1000000

variable {ι : Type*} [Fintype ι]
local notation "J" => CoupledPhysicalState ι

/-- The scalar residual of the integrated direct-kernel equation. -/
noncomputable def canonicalPhysicalIntegratedError (T : ℝ≥0) (v κ : ℝ) (i : Option ι)
    {b : ℝ≥0 → ℝ} {B : ℝ} (hb : Measurable b) (hB : ∀ t, ‖b t‖ ≤ B)
    (k : ℝ → ℝ) (t : CanonicalPathTime T) (p : CanonicalPath T J) : ℝ :=
  canonicalScalarPrimitive T (canonicalPhysicalVariancePath T i p) t - v*(t.val : ℝ) -
    volterraConvolution k (fun r => canonicalPhysicalDrivePath T κ i hb hB p (realTimeOnHorizon T r)) t.val

theorem continuous_canonicalPhysicalIntegratedError (T : ℝ≥0) (v κ : ℝ) (i : Option ι)
    {b : ℝ≥0 → ℝ} {B : ℝ} (hb : Measurable b) (hB : ∀ t, ‖b t‖ ≤ B)
    {k : ℝ → ℝ} (t : CanonicalPathTime T)
    (hk : IntegrableOn (fun r => k ((t.val : ℝ)-r)) (Ioc 0 (t.val : ℝ))) :
    Continuous (canonicalPhysicalIntegratedError T v κ i hb hB k t) := by
  have h := ((continuous_eval_const t).comp
    ((continuous_canonicalScalarPrimitive T).comp (continuous_canonicalPhysicalVariancePath T i))).sub
      (continuous_const (y := v*(t.val : ℝ)))
  have h' := (continuous_weighted_path_integral (realTimeOnHorizon T).continuous.measurable hk).comp
    (continuous_canonicalPhysicalDrivePath T κ i hb hB)
  exact h.sub h'

private theorem integrable_reflected_weight_mul_path (T : ℝ≥0) {k : ℝ → ℝ} (t : CanonicalPathTime T)
    (hk : IntegrableOn (fun r => k ((t.val : ℝ)-r)) (Ioc 0 (t.val : ℝ)))
    (p : CanonicalPath T ℝ) :
    IntegrableOn (fun r => k ((t.val : ℝ)-r)*p (realTimeOnHorizon T r)) (Ioc 0 (t.val : ℝ)) := by
  refine (hk.norm.mul_const ‖p‖).mono' (hk.aestronglyMeasurable.mul
    (p.continuous.comp (realTimeOnHorizon T).continuous).aestronglyMeasurable) ?_
  apply Eventually.of_forall
  intro r
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (p.norm_coe_le_norm (realTimeOnHorizon T r)) (norm_nonneg _)

/-- Kernel convergence in the reflected L¹ norm gives uniform-on-compact
convergence of the integrated path equation. -/
theorem canonicalPhysicalIntegratedError_close (T : ℝ≥0) (v κ : ℝ) (i : Option ι)
    {b : ℝ≥0 → ℝ} {B : ℝ} (hb : Measurable b) (hB : ∀ t, ‖b t‖ ≤ B)
    {k : ℝ → ℝ} {kn : ℕ → ℝ → ℝ} (t : CanonicalPathTime T)
    (hk : IntegrableOn (fun r => k ((t.val : ℝ)-r)) (Ioc 0 (t.val : ℝ)))
    (hkn : ∀ n, IntegrableOn (fun r => kn n ((t.val : ℝ)-r)) (Ioc 0 (t.val : ℝ)))
    (hK : Tendsto (fun n => ∫ r in Ioc (0 : ℝ) (t.val : ℝ),
      ‖kn n ((t.val : ℝ)-r)-k ((t.val : ℝ)-r)‖) atTop (𝓝 0))
    (C : Set (CanonicalPath T J)) (hC : IsCompact C) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ p ∈ C,
      ‖canonicalPhysicalIntegratedError T v κ i hb hB k t p -
        canonicalPhysicalIntegratedError T v κ i hb hB (kn n) t p‖ < ε := by
  let Dr := canonicalPhysicalDrivePath T κ i hb hB
  let L (n : ℕ) := ∫ r in Ioc (0 : ℝ) (t.val : ℝ), ‖kn n ((t.val : ℝ)-r)-k ((t.val : ℝ)-r)‖
  have hDr := continuous_canonicalPhysicalDrivePath T κ i hb hB
  obtain ⟨A, hA⟩ := (hC.image hDr).isBounded.exists_norm_le
  let A' := max A 0
  have hA' : 0 ≤ A' := le_max_right _ _
  filter_upwards [(Metric.tendsto_nhds.1 (show Tendsto L atTop (𝓝 0) from hK))
    (ε/(A'+1)) (by positivity)] with n hn p hp
  have hL₀ : 0 ≤ L n := integral_nonneg fun r => norm_nonneg _
  have hLn : L n < ε/(A'+1) := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hL₀] using hn
  have hP : ‖Dr p‖ ≤ A' := (hA _ ⟨p, hp, rfl⟩).trans (le_max_left _ _)
  have hBound :
      ‖canonicalPhysicalIntegratedError T v κ i hb hB k t p -
        canonicalPhysicalIntegratedError T v κ i hb hB (kn n) t p‖ ≤ A' * L n := by
    let D (r : ℝ) := (kn n ((t.val : ℝ)-r)-k ((t.val : ℝ)-r))
    let z (r : ℝ) := Dr p (realTimeOnHorizon T r)
    have hI1 := integrable_reflected_weight_mul_path T t hk (Dr p)
    have hI2 := integrable_reflected_weight_mul_path T t (hkn n) (Dr p)
    have hI : IntegrableOn (fun r => D r*z r) (Ioc 0 (t.val : ℝ)) :=
      integrable_reflected_weight_mul_path T (k := fun u => kn n u-k u) t ((hkn n).sub hk) (Dr p)
    have hDI : IntegrableOn D (Ioc 0 (t.val : ℝ)) := (hkn n).sub hk
    unfold canonicalPhysicalIntegratedError volterraConvolution
    have hs (x y z : ℝ) : x-y-(x-z) = z-y := by ring
    rw [hs, ← integral_sub hI2 hI1]
    simp_rw [← sub_mul]
    refine (norm_integral_le_integral_norm _).trans ?_
    have he : (∫ r in Ioc (0 : ℝ) (t.val : ℝ), A'*‖D r‖) = A'*L n := integral_const_mul _ _
    rw [← he]
    apply integral_mono hI.norm (hDI.norm.const_mul A')
    intro r
    change ‖D r*z r‖ ≤ A'*‖D r‖
    rw [norm_mul, mul_comm A']
    exact mul_le_mul_of_nonneg_left ((ContinuousMap.norm_coe_le_norm (Dr p) _).trans hP) (norm_nonneg _)
  refine hBound.trans_lt ?_
  have he := (lt_div_iff₀ (show 0 < A'+1 by positivity)).mp hLn
  nlinarith

/-- Every weak limit preserves the integrated equations when the
deterministic direct kernel converges in reflected L¹. -/
theorem ae_canonicalPhysicalIntegratedError_of_weak
    (T : ℝ≥0) (v κ : ℝ) (i : Option ι) {b : ℝ≥0 → ℝ} {B : ℝ}
    (hb : Measurable b) (hB : ∀ t, ‖b t‖ ≤ B)
    {k : ℝ → ℝ} {kn : ℕ → ℝ → ℝ} (t : CanonicalPathTime T)
    {Pn : ℕ → ProbabilityMeasure (CanonicalPath T J)} {P : ProbabilityMeasure (CanonicalPath T J)}
    (hweak : Tendsto Pn atTop (𝓝 P))
    (hk : IntegrableOn (fun r => k ((t.val : ℝ)-r)) (Ioc 0 (t.val : ℝ)))
    (hkn : ∀ n, IntegrableOn (fun r => kn n ((t.val : ℝ)-r)) (Ioc 0 (t.val : ℝ)))
    (hK : Tendsto (fun n => ∫ r in Ioc (0 : ℝ) (t.val : ℝ),
      ‖kn n ((t.val : ℝ)-r)-k ((t.val : ℝ)-r)‖) atTop (𝓝 0))
    (hZero : ∀ n, canonicalPhysicalIntegratedError T v κ i hb hB (kn n) t =ᵐ[(Pn n : Measure _)] 0) :
    canonicalPhysicalIntegratedError T v κ i hb hB k t =ᵐ[(P : Measure _)] 0 :=
  ae_eq_zero_of_weak_of_continuous_moving_zero hweak
    (continuous_canonicalPhysicalIntegratedError T v κ i hb hB t hk)
    (fun n => continuous_canonicalPhysicalIntegratedError T v κ i hb hB t (hkn n)) hZero
    (canonicalPhysicalIntegratedError_close T v κ i hb hB t hk hkn hK)

#print axioms RoughHeston.ae_canonicalPhysicalIntegratedError_of_weak

end RoughHeston
