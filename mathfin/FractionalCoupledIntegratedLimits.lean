import CanonicalPhysicalIntegratedEquation
import FractionalExponentialApproximation

/-! The actual smooth approximations satisfy the measurable integrated
equation on their common canonical path space. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

set_option maxHeartbeats 1000000

theorem hestonKernel_integrableOn_reflected_Ioc {α t : ℝ}
    (hα : 0 < α) (ht : 0 ≤ t) :
    IntegrableOn (fun s : ℝ => hestonKernel α (t - s)) (Ioc 0 t) := by
  have hK : hestonKernel α = fractionalK α := by
    funext x
    unfold hestonKernel fractionalK
    by_cases hx : 0 < x
    · simp [hx, not_le.mpr hx]
    · simp [hx, le_of_not_gt hx]
  rw [hK]
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).2
    (fractionalK_integrableOn_Ioc hα t)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).1
    (by simpa only [sub_zero, sub_self] using (hi.comp_sub_left t).symm)

theorem fractionalExponentialApproximation_integrableOn_reflected_Ioc {α t : ℝ}
    (hα : 0 < α) (hα' : α < 1) (n : ℕ) :
    IntegrableOn (fun s : ℝ => fractionalExponentialApproximation α n (t-s)) (Ioc 0 t) :=
  (((fractionalExponentialApproximation_properties hα hα' n).1.comp
    (continuous_const.sub continuous_id)).integrableOn_Icc (μ := volume)).mono_set Ioc_subset_Icc_self

/-- The smooth approximation converges in reflected L¹ at every
finite observation time. -/
theorem fractionalExponentialApproximation_tendsto_reflected_L1 {α t : ℝ}
    (hα : 0 < α) (hα' : α < 1) (ht : 0 ≤ t) :
    Tendsto (fun n => ∫ r in Ioc (0 : ℝ) t,
      ‖fractionalExponentialApproximation α n (t-r)-hestonKernel α (t-r)‖) atTop (𝓝 0) := by
  let ν := volume.restrict (Ioc (0 : ℝ) t)
  let k (s : ℝ) := hestonKernel α (t-s)
  let kn (n : ℕ) (s : ℝ) := fractionalExponentialApproximation α n (t-s)
  have hki : Integrable k ν := hestonKernel_integrableOn_reflected_Ioc hα ht
  have hkm : Measurable k := (hestonKernel_measurable α).comp (measurable_const.sub measurable_id)
  have hkn (n : ℕ) : Measurable (kn n) :=
    (fractionalExponentialApproximation_properties hα hα' n).1.measurable.comp
      (measurable_const.sub measurable_id)
  have hpos : ∀ᵐ r ∂ν, 0 < t-r := by
    have hne : ∀ᵐ r ∂ν, r ≠ t := (volume.ae_ne t).filter_mono (ae_mono Measure.restrict_le_self)
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hne] with r hr hn
    exact sub_pos.mpr (lt_of_le_of_ne hr.2 hn)
  have h := tendsto_integral_of_dominated_convergence (μ := ν) (f := fun _ => (0 : ℝ)) k
    (fun n => ((hkn n).sub hkm).norm.aestronglyMeasurable) hki ?_ ?_
  · simpa only [integral_zero, Pi.sub_apply, ν, kn, k] using h
  · intro n
    filter_upwards [hpos] with r hr
    have hle := fractionalExponentialApproximation_le_hestonKernel hα hα' hr n
    have hN := (fractionalExponentialApproximation_properties hα hα' n).2.1 (t-r)
    change ‖‖kn n r-k r‖‖ ≤ k r
    rw [Real.norm_of_nonneg (norm_nonneg _), Real.norm_eq_abs]
    exact abs_le.2 ⟨by dsimp [kn, k]; linarith, by dsimp [kn, k]; linarith⟩
  · filter_upwards [hpos] with r hr
    simpa only [Pi.sub_apply, kn, k, sub_self, norm_zero] using
      ((fractionalExponentialApproximation_tendsto hα hα' hr).sub_const (k r)).norm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {T : ℝ≥0} {α κ σ : ℝ} {n : ℕ} {v : Option ι → ℝ} {β : Option ι → ℝ≥0 → ℝ}

namespace FractionalCoupledSmoothLaw

theorem ae_fixedPhysical_integrated_zero (L : FractionalCoupledSmoothLaw T α n κ σ v β)
    (hα : 0 < α) (hα' : α < 1) {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i))
    (hβB : ∀ i t, ‖β i t‖ ≤ B) (i : Option ι) (t : CanonicalPathTime T) :
    canonicalPhysicalIntegratedError T (v i) κ i (hβ i) (hβB i)
      (fractionalExponentialApproximation α n) t =ᵐ[(L.fixedPhysicalLaw hB hβ hβB : Measure _)] 0 := by
  let φ := L.fixedPhysicalPath hB hβ hβB
  let F := canonicalPhysicalIntegratedError T (v i) κ i (hβ i) (hβB i)
    (fractionalExponentialApproximation α n) t
  have hF : Continuous F := continuous_canonicalPhysicalIntegratedError T (v i) κ i (hβ i) (hβB i) t
    (fractionalExponentialApproximation_integrableOn_reflected_Ioc hα hα' n)
  change ∀ᵐ p ∂Measure.map φ (L.law : Measure _), F p = 0
  rw [ae_map_iff (L.measurable_fixedPhysicalPath hB hβ hβB).aemeasurable
    (measurableSet_eq_fun hF.measurable measurable_const)]
  filter_upwards [L.inverse] with q hInverse
  let p := φ q
  let U (r : ℝ) := canonicalPhysicalVariance T i r.toNNReal p - v i
  let J (r : ℝ) := canonicalPhysicalDrivePath T κ i (hβ i) (hβB i) p (realTimeOnHorizon T r)
  let ℓ := smoothExponentialResolvent L.ℓ₀ L.q L.rate
  let K := fractionalExponentialApproximation α n
  have hU : Continuous U := (((continuous_apply i).comp continuous_fst).comp
    (p.continuous.comp (realTimeOnHorizon T).continuous)).sub continuous_const
  have hPath (r : ℝ≥0) : canonicalPhysicalVariance T i r p = L.variance i r q ∧
      canonicalPhysicalResidual T i r p = L.residual i r q := by
    unfold canonicalPhysicalVariance canonicalPhysicalResidual p φ
    rw [L.canonicalPathEval_fixedPhysicalPath hB hβ hβB]
    exact ⟨rfl, rfl⟩
  have hJ (s : ℝ) (hs : s ∈ Icc 0 (t.val : ℝ)) :
      J s = (1/K 0)*U s + volterraConvolution ℓ U s := by
    have hcast : (s.toNNReal : ℝ) = s := Real.coe_toNNReal _ hs.1
    have hsT : s.toNNReal ≤ T := NNReal.coe_le_coe.mp
      (hcast.trans_le (hs.2.trans (NNReal.coe_le_coe.mpr t.property.2)))
    have hEval : (realTimeOnHorizon T s).val = s.toNNReal := min_eq_left hsT
    have h : L.residual i s.toNNReal q +
        (∫ r in (0 : ℝ)..(s.toNNReal : ℝ), (β i r.toNNReal - κ*L.variance i r.toNNReal q)) =
      smoothExponentialInverse (K 0) L.ℓ₀ L.q L.rate (v i)
        (fun r : ℝ => L.variance i r.toNNReal q) s.toNNReal :=
      (hInverse i s.toNNReal ⟨zero_le, hsT⟩).symm
    rw [hcast] at h
    have hJ0 := canonicalPhysicalDrivePath_apply T κ i (hβ i) (hβB i) p (realTimeOnHorizon T s)
    change J s = _ at hJ0
    rw [hJ0, hEval, hcast, (hPath _).2]
    simp_rw [(fun r : ℝ => (hPath r.toNNReal).1)]
    change L.residual i s.toNNReal q +
      (∫ r in (0 : ℝ)..s, (β i r.toNNReal - κ*L.variance i r.toNNReal q)) = _
    rw [h]
    unfold smoothExponentialInverse volterraConvolution U ℓ
    rw [intervalIntegral.integral_of_le hs.1]
    simp_rw [(fun r : ℝ => (hPath r.toNNReal).1)]
    ring
  have h := smooth_firstKind_inverse_integrated_forward t.val.coe_nonneg
    (fractionalExponentialApproximation_properties hα hα' n).1
    (continuous_smoothExponentialResolvent L.ℓ₀ L.q L.rate) hU
    (fun s hs => L.resolves s hs.1) hJ
  have h0 : ∫ r in (0 : ℝ)..(t.val : ℝ), U r =
      canonicalScalarPrimitive T (canonicalPhysicalVariancePath T i p) t-v i*(t.val : ℝ) := by
    unfold U
    have hvC : Continuous (fun r : ℝ => canonicalPhysicalVariance T i r.toNNReal p) :=
      ((continuous_apply i).comp continuous_fst).comp (p.continuous.comp (realTimeOnHorizon T).continuous)
    rw [intervalIntegral.integral_sub (hvC.intervalIntegrable _ _) intervalIntegrable_const]
    simp [canonicalScalarPrimitive, canonicalPhysicalVariancePath, canonicalPhysicalVariance,
      canonicalPathEval, realTimeOnHorizon, mul_comm]
    rfl
  change canonicalPhysicalIntegratedError T (v i) κ i (hβ i) (hβB i) K t p = 0
  unfold canonicalPhysicalIntegratedError
  rw [← h0, h, sub_self]

end FractionalCoupledSmoothLaw

#print axioms RoughHeston.fractionalExponentialApproximation_tendsto_reflected_L1
#print axioms RoughHeston.FractionalCoupledSmoothLaw.ae_fixedPhysical_integrated_zero

end RoughHeston
