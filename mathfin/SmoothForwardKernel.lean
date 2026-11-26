import SmoothLiftInverseIdentity
import AffineDeterministicIntegrability

/-! Deterministic forward representations for smooth first-kind resolvents. -/

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RoughHeston

set_option maxHeartbeats 800000

private theorem volterra_causal_left {L U : ℝ → ℝ} (s : ℝ) :
    volterraConvolution ((Ioi (0 : ℝ)).indicator L) U s = volterraConvolution L U s := by
  apply setIntegral_congr_ae measurableSet_Ioc
  filter_upwards [volume.ae_ne s] with r hr hI
  have hPos : 0 < s-r := sub_pos.mpr (lt_of_le_of_ne hI.2 hr)
  simp [Set.indicator_of_mem (show s-r ∈ Ioi (0 : ℝ) from hPos)]

private theorem volterra_causal_right {K L : ℝ → ℝ} (s : ℝ) :
    volterraConvolution K ((Ioi (0 : ℝ)).indicator L) s = volterraConvolution K L s := by
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r hr
  simp [Set.indicator_of_mem (show r ∈ Ioi (0 : ℝ) from hr.1)]

private theorem volterra_reflect {K L : ℝ → ℝ} {s : ℝ} (hs : 0 ≤ s) :
    volterraConvolution K L s = volterraConvolution L K s := by
  simp_rw [volterraConvolution, ← intervalIntegral.integral_of_le hs]
  have h := intervalIntegral.integral_comp_sub_left
    (f := fun r => K (s-r)*L r) (a := 0) (b := s) s
  simp only [sub_self, sub_zero, sub_sub_cancel] at h
  simpa only [mul_comm] using h.symm

private theorem volterra_left_iter_integrable {K L U : ℝ → ℝ} {t : ℝ}
    (hL₀ : ∀ s ≤ 0, L s = 0)
    (hTri : Integrable (fun z : ℝ × ℝ => K (t-z.1)*L (z.1-z.2)*U z.2)
      ((volume.restrict (Ioc 0 t)).prod (volume.restrict (Ioc 0 t)))) :
    IntegrableOn (fun s => K (t-s)*volterraConvolution L U s) (Ioc 0 t) := by
  refine hTri.integral_prod_left.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hsub : Ioc (0:ℝ) s ⊆ Ioc 0 t := Ioc_subset_Ioc_right hs.2
  have hZero (r : ℝ) (hr : r ∈ Ioc 0 t \ Ioc 0 s) : K (t-s)*L (s-r)*U r = 0 := by
    have hsr : s ≤ r := le_of_not_gt fun h => hr.2 ⟨hr.1.1,h.le⟩
    rw [hL₀ (s-r) (sub_nonpos.mpr hsr), mul_zero, zero_mul]
  change (∫ r in Ioc (0:ℝ) t, K (t-s)*L (s-r)*U r) = K (t-s)*volterraConvolution L U s
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc hsub hZero,
    volterraConvolution, ← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioc fun _ _ => mul_assoc _ _ _

/-- Convolving the first-kind inverse path by the direct kernel recovers
the time primitive of the centered variance path. -/
theorem smooth_firstKind_inverse_integrated_forward
    {K L U J : ℝ → ℝ} {a t : ℝ} (ht : 0 ≤ t)
    (hK : Continuous K) (hL : Continuous L) (hU : Continuous U)
    (hKL : ∀ s ∈ Icc (0 : ℝ) t, a*K s + volterraConvolution L K s = 1)
    (hJ : ∀ s ∈ Icc (0 : ℝ) t, J s = a*U s + volterraConvolution L U s) :
    volterraConvolution K J t = ∫ s in (0 : ℝ)..t, U s := by
  let Lp := (Ioi (0 : ℝ)).indicator L
  have hLp₀ (s : ℝ) (hs : s ≤ 0) : Lp s = 0 := by simp [Lp, hs]
  have hLpi : IntegrableOn Lp (Ioc 0 t) := by
    have hLi : IntegrableOn L (Ioc 0 t) := (hL.integrableOn_Icc (μ := volume)).mono_set Ioc_subset_Icc_self
    refine hLi.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    simp [Lp, hs.1]
  have hUi : IntegrableOn U (Ioc 0 t) :=
    (hU.integrableOn_Icc (μ := volume)).mono_set Ioc_subset_Icc_self
  obtain ⟨B, hB⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := t)).image hK).isBounded.exists_norm_le
  have hTri := affine_volterra_triangle_integrable (l := K) (k := Lp) (f := U) ht
    (le_max_left (0 : ℝ) B) hK.measurable (hL.measurable.indicator measurableSet_Ioi)
    hU.measurable hLp₀ hLpi hUi (fun s hs => (hB _ ⟨s, hs, rfl⟩).trans (le_max_right _ _))
  have hiA : IntegrableOn (fun s => (a*K (t-s))*U s) (Ioc 0 t) := by
    have hc : Continuous (fun s => (a*K (t-s))*U s) :=
      (continuous_const.mul (hK.comp (continuous_const.sub continuous_id))).mul hU
    exact (hc.integrableOn_Icc (μ := volume)).mono_set Ioc_subset_Icc_self
  have hiB : IntegrableOn (fun s => K (t-s)*volterraConvolution Lp U s) (Ioc 0 t) :=
    volterra_left_iter_integrable hLp₀ hTri
  have hiC : IntegrableOn (fun s => volterraConvolution K Lp (t-s)*U s) (Ioc 0 t) := by
    refine hTri.integral_prod_right.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    change (∫ r in Ioc (0 : ℝ) t, K (t-r)*Lp (r-s)*U s) = _
    rw [integral_mul_const, volterra_shifted_kernel_integral hLp₀ hs]
  calc
    _ = ∫ s in Ioc (0 : ℝ) t, (a*K (t-s))*U s +
          K (t-s)*volterraConvolution Lp U s := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      change K (t-s)*J s = (a*K (t-s))*U s + K (t-s)*volterraConvolution Lp U s
      rw [hJ s ⟨hs.1.le, hs.2⟩, show volterraConvolution Lp U s = _ from volterra_causal_left s]
      ring
    _ = (∫ s in Ioc (0 : ℝ) t, (a*K (t-s))*U s) +
        volterraConvolution K (volterraConvolution Lp U) t := integral_add hiA hiB
    _ = (∫ s in Ioc (0 : ℝ) t, (a*K (t-s))*U s) +
        volterraConvolution (volterraConvolution K Lp) U t := by
      rw [volterra_convolution_assoc hLp₀ hTri]
    _ = ∫ s in Ioc (0 : ℝ) t, ((a*K (t-s))*U s + volterraConvolution K Lp (t-s)*U s) :=
      (integral_add hiA hiC).symm
    _ = _ := by
      rw [intervalIntegral.integral_of_le ht]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      change (a*K (t-s))*U s + volterraConvolution K Lp (t-s)*U s = U s
      have hs0 := sub_nonneg.mpr hs.2
      rw [volterra_causal_right, volterra_reflect hs0, ← add_mul,
        hKL _ ⟨hs0, sub_le_self t hs.1.le⟩, one_mul]

#print axioms RoughHeston.smooth_firstKind_inverse_integrated_forward

end RoughHeston
