import FractionalCoupledFixedMeshExistence
import BanachHestonInversion

/-! Deterministic recovery of the fractional inverse equation from the
integrated weak-limit equation, simultaneously on the whole horizon. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

set_option maxHeartbeats 1100000

theorem fractional_integrated_direct_implies_inverse
    {α A : ℝ} (hα : 0 < α) (hα' : α < 1) (hA : 0 < A)
    {U J : ℝ → ℝ} (hU : Continuous U) (hJ : Continuous J)
    (he : ∀ t ∈ Icc 0 A, (∫ s in (0:ℝ)..t, U s) = volterraConvolution (fractionalK α) J t) :
    ∀ t ∈ Icc 0 A, volterraConvolution (fractionalL α) U t = J t := by
  let R := volterraSmulConvolution (fractionalL α) U
  let C (x : ℝ) := max 0 (min x A)
  have hC : Continuous C := continuous_const.max (continuous_id.min continuous_const)
  have hCm (x : ℝ) : C x ∈ Icc (0:ℝ) A :=
    ⟨le_max_left _ _, max_le hA.le (min_le_right _ _)⟩
  have hEq (x : ℝ) (hx : x ∈ Icc (0:ℝ) A) : C x = x := by
    dsimp [C]
    rw [min_eq_left hx.2, max_eq_right hx.1]
  have hRc : Continuous (R ∘ C) :=
    (continuousOn_volterra_forcing hA.le (fractionalL_measurable α)
      (fractionalL_integrableOn_Ioc hα' A) hU.continuousOn).comp_continuous hC hCm
  let F := (R ∘ C) - J
  have hF : Continuous F := hRc.sub hJ
  have hK : fractionalL (1-α) = fractionalK α := by
    funext t
    simp only [fractionalK, fractionalL, show -(1-α) = α-1 by ring,
      show 1-(1-α) = α by ring]
  have hL : fractionalK (1-α) = fractionalL α := by
    funext t
    simp only [fractionalK, fractionalL, show 1-α-1 = -α by ring]
  have hKFin : ∀ t ∈ Icc 0 A, volterraSmulConvolution (fractionalL (1-α)) F t = 0 := by
    intro t ht
    have hInv := fractional_volterra_smul_inverts_drift (α := 1-α) (t := t)
      (sub_pos.mpr hα') (by linarith : 1-α < 1) hU.stronglyMeasurable
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).1 (hU.intervalIntegrable _ _))
    rw [hK, hL] at hInv
    change volterraSmulConvolution (fractionalK α) R t = _ at hInv
    rw [← intervalIntegral.integral_of_le ht.1, he t ht] at hInv
    have hkI : IntegrableOn (fun s => fractionalK α (t-s)) (Ioc 0 t) := by
      have hk := fractionalL_reflected_integrableOn_Ioc (α := 1-α) (by linarith : 1-α < 1) ht.1
      simpa only [hK] using hk
    have hi {g : ℝ → ℝ} (hg : Continuous g) : IntegrableOn
        (fun s => fractionalK α (t-s) • g s) (Ioc 0 t) := by
      obtain ⟨D, hD⟩ := (isCompact_Icc (a := (0:ℝ)) (b := t)).exists_bound_of_continuousOn hg.continuousOn
      refine (hkI.norm.mul_const D).mono' (hkI.aestronglyMeasurable.smul
        hg.aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hD s (Ioc_subset_Icc_self hs)) (norm_nonneg _)
    rw [hK]
    unfold volterraSmulConvolution
    simp only [F, Pi.sub_apply, smul_sub]
    rw [integral_sub (hi hRc) (hi hJ), sub_eq_zero]
    apply Eq.trans _ hInv
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    change fractionalK α (t-s) • R (C s) = fractionalK α (t-s) • R s
    rw [hEq s ⟨hs.1.le, hs.2.trans ht.2⟩]
  intro t ht
  have h := fractionalL_smul_zero_implies_path_zero (α := 1-α) (sub_pos.mpr hα')
    (by linarith : 1-α < 1) hA hF.stronglyMeasurable hF.continuousOn hKFin t ht
  change R (C t)-J t = 0 at h
  rwa [hEq t ht, sub_eq_zero] at h

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
local notation "Ω" => CanonicalPath T (CoupledPhysicalState ι)

private theorem fractionalK_eq_hestonKernel (α : ℝ) : fractionalK α = hestonKernel α := by
  funext x
  by_cases hx : 0 < x
  · simp [fractionalK, hestonKernel, hx, not_le.mpr hx]
  · simp [fractionalK, hestonKernel, hx, le_of_not_gt hx]

/-- The fixed-time integrated weak-limit identities imply one
samplewise fractional inverse identity at all times. -/
theorem ae_canonicalPhysical_inverse_of_integrated
    (hT : 0 < T) {α κ v : ℝ} (hα : 0 < α) (hα' : α < 1)
    (i : Option ι) {b : ℝ≥0 → ℝ} {B : ℝ} (hb : Measurable b) (hB : ∀ t, ‖b t‖ ≤ B)
    (P : ProbabilityMeasure Ω)
    (he : ∀ t : CanonicalPathTime T, canonicalPhysicalIntegratedError T v κ i hb hB
      (hestonKernel α) t =ᵐ[(P : Measure Ω)] 0) :
    ∀ᵐ p ∂(P : Measure Ω), ∀ t ≤ T,
      volterraConvolution (fractionalL α) (fun s => canonicalPhysicalVariance T i s.toNNReal p-v) (t:ℝ) =
        canonicalPhysicalResidual T i t p +
          ∫ r in (0:ℝ)..(t:ℝ), (b r.toNNReal-κ*canonicalPhysicalVariance T i r.toNNReal p) := by
  let U (p : Ω) (r : ℝ) := canonicalPhysicalVariancePath T i p (realTimeOnHorizon T r)-v
  let J (p : Ω) (r : ℝ) := canonicalPhysicalDrivePath T κ i hb hB p (realTimeOnHorizon T r)
  have hUc (p : Ω) : Continuous (U p) :=
    (((canonicalPhysicalVariancePath T i p).continuous).comp (realTimeOnHorizon T).continuous).sub continuous_const
  have hJc (p : Ω) : Continuous (J p) :=
    (canonicalPhysicalDrivePath T κ i hb hB p).continuous.comp (realTimeOnHorizon T).continuous
  have hEval (p : Ω) (r : ℝ) :
      U p r = canonicalPhysicalVariance T i r.toNNReal p-v := rfl
  let X (t : ℝ≥0) (p : Ω) := ∫ s in (0:ℝ)..(t:ℝ), U p s
  let Y (t : ℝ≥0) (p : Ω) := volterraConvolution (fractionalK α) (J p) t.val
  have hX (p : Ω) : Continuous (fun t => X t p) :=
    (intervalIntegral.differentiable_integral_of_continuous (a := (0:ℝ)) (hUc p)).continuous.comp
      NNReal.continuous_coe
  have hY (p : Ω) : ContinuousOn (fun t => Y t p) (Icc 0 T) := by
    have h := continuousOn_volterra_forcing (T := (T:ℝ)) T.coe_nonneg
      (fractionalK_measurable α) (fractionalK_integrableOn_Ioc hα T) (hJc p).continuousOn
    exact h.comp NNReal.continuous_coe.continuousOn fun t ht =>
      ⟨t.coe_nonneg, NNReal.coe_le_coe.mpr ht.2⟩
  have hSame (t : ℝ≥0) (ht : t ∈ Icc (0:ℝ≥0) T) : X t =ᵐ[(P : Measure Ω)] Y t := by
    let τ : CanonicalPathTime T := ⟨t,ht⟩
    filter_upwards [he τ] with p hp
    change canonicalPhysicalIntegratedError T v κ i hb hB (hestonKernel α) τ p = 0 at hp
    apply sub_eq_zero.mp at hp
    let V (r : ℝ) := canonicalPhysicalVariancePath T i p (realTimeOnHorizon T r)
    have hVc : Continuous V :=
      (canonicalPhysicalVariancePath T i p).continuous.comp (realTimeOnHorizon T).continuous
    have hVi : IntervalIntegrable V volume (0:ℝ) (t:ℝ) := hVc.intervalIntegrable _ _
    change (∫ r in (0:ℝ)..(t:ℝ), V r-v) =
      volterraConvolution (fractionalK α) (J p) (t:ℝ)
    rw [intervalIntegral.integral_sub hVi intervalIntegrable_const, intervalIntegral.integral_const,
      sub_zero, smul_eq_mul, mul_comm (t:ℝ) v, fractionalK_eq_hestonKernel]
    exact hp
  have hSameAll := MathFin.LocalisationInMeasure.ae_forall_eq_of_continuousOn
    (Eventually.of_forall fun p => (hX p).continuousOn) (Eventually.of_forall hY) hSame
  filter_upwards [hSameAll] with p hp t ht
  have hSameReal (r : ℝ) (hr : r ∈ Icc (0:ℝ) T) :
      (∫ s in (0:ℝ)..r, U p s) = volterraConvolution (fractionalK α) (J p) r := by
    have hr' : r.toNNReal ∈ Icc (0:ℝ≥0) T := ⟨zero_le, by
      exact NNReal.coe_le_coe.mp ((Real.coe_toNNReal r hr.1).trans_le hr.2)⟩
    have hh := hp r.toNNReal hr'
    change (∫ s in (0:ℝ)..(r.toNNReal:ℝ), U p s) =
      volterraConvolution (fractionalK α) (J p) (r.toNNReal:ℝ) at hh
    rwa [Real.coe_toNNReal r hr.1] at hh
  have hInv := fractional_integrated_direct_implies_inverse hα hα'
    (NNReal.coe_pos.mpr hT) (hUc p) (hJc p) hSameReal (t:ℝ)
    ⟨t.coe_nonneg, NNReal.coe_le_coe.mpr ht⟩
  let τ : CanonicalPathTime T := ⟨t,⟨zero_le,ht⟩⟩
  have hτ : realTimeOnHorizon T (t:ℝ) = τ := by
    apply Subtype.ext
    change min (t:ℝ).toNNReal T = t
    rw [Real.toNNReal_coe, min_eq_left ht]
  change volterraConvolution (fractionalL α) (U p) (t:ℝ) = _
  rw [hInv]
  change canonicalPhysicalDrivePath T κ i hb hB p (realTimeOnHorizon T (t:ℝ)) = _
  rw [hτ]
  exact canonicalPhysicalDrivePath_apply T κ i hb hB p τ

#print axioms RoughHeston.fractional_integrated_direct_implies_inverse
#print axioms RoughHeston.ae_canonicalPhysical_inverse_of_integrated

end RoughHeston
