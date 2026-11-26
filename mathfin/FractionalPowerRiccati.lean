import FractionalBoundaryHistory
import FractionalKernelL1

open MeasureTheory Filter Set
open scoped MeasureTheory Topology

namespace RoughHeston

/-- Candidate singular solution for the undamped point-charge limit. -/
noncomputable def singularRiccatiProfile (α c t : ℝ) : ℝ :=
  if 0 < t then c * t ^ (-α) else 0

/-- The Riemann–Liouville primitive of the singular profile, as an
ordinary Volterra integral of the actual inverse kernel. -/
theorem singularRiccatiProfile_primitive {α c t : ℝ} (hα : α < 1) (ht : 0 < t) :
    volterraConvolution (fractionalL α) (singularRiccatiProfile α c) t =
      (c * (Real.Gamma (1 - α) / Real.Gamma (2 - 2 * α))) * t ^ (1 - 2 * α) := by
  obtain ⟨_, hβ⟩ := real_beta_weight_scaled (sub_pos.mpr hα) (sub_pos.mpr hα) ht
  have hβ' : (∫ s in Ioo (0 : ℝ) t, s ^ (-α) * (t - s) ^ (-α)) =
      t ^ (1 - 2 * α) * (Real.Gamma (1 - α) * Real.Gamma (1 - α) / Real.Gamma (2 - 2 * α)) := by
    rw [setIntegral_congr_set Ioo_ae_eq_Ioc]
    simpa only [show 1 - α - 1 = -α by ring,
      show 1 - α + (1 - α) = 2 - 2 * α by ring,
      show 2 - 2 * α - 1 = 1 - 2 * α by ring] using hβ
  unfold volterraConvolution
  rw [← setIntegral_congr_set (Ioo_ae_eq_Ioc : Ioo (0 : ℝ) t =ᵐ[volume] Ioc 0 t)]
  calc
    _ = ∫ s in Ioo (0 : ℝ) t, (c / Real.Gamma (1 - α)) * (s ^ (-α) * (t - s) ^ (-α)) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro s hs
      change fractionalL α (t - s) * singularRiccatiProfile α c s =
        (c / Real.Gamma (1 - α)) * (s ^ (-α) * (t - s) ^ (-α))
      rw [fractionalL, ite_eq_right (not_le_of_gt (sub_pos.mpr hs.2)),
        singularRiccatiProfile, ite_eq_left hs.1]
      ring
    _ = _ := by
      rw [integral_const_mul, hβ']
      field_simp [(Real.Gamma_pos_of_pos (sub_pos.mpr hα)).ne']

/-- Coefficient in the singular Riccati profile, for quadratic
coefficient a. -/
noncomputable def singularRiccatiCoefficient (α a : ℝ) : ℝ :=
  (2 * α - 1) * Real.Gamma (1 - α) / (a * Real.Gamma (2 - 2 * α))

theorem singularRiccatiCoefficient_pos {α a : ℝ}
    (hα : 1 / 2 < α) (hα' : α < 1) (ha : 0 < a) :
    0 < singularRiccatiCoefficient α a := by
  unfold singularRiccatiCoefficient
  exact div_pos (mul_pos (by linarith) (Real.Gamma_pos_of_pos (sub_pos.mpr hα')))
    (mul_pos ha (Real.Gamma_pos_of_pos (by linarith)))

/-- The positive singular profile solves the undamped fractional
Riccati differential equation at every strictly positive time. -/
theorem singularRiccatiProfile_solves {α a t : ℝ}
    (hα : α < 1) (ha : 0 < a) (ht : 0 < t) :
    let c := singularRiccatiCoefficient α a
    HasDerivAt (volterraConvolution (fractionalL α) (singularRiccatiProfile α c))
      (-a * (singularRiccatiProfile α c t) ^ 2) t := by
  dsimp only
  let c := singularRiccatiCoefficient α a
  let C := c * (Real.Gamma (1 - α) / Real.Gamma (2 - 2 * α))
  have hd := (Real.hasDerivAt_rpow_const (x := t) (p := 1 - 2 * α)
    (Or.inl ht.ne')).const_mul C
  have hval : C * ((1 - 2 * α) * t ^ (1 - 2 * α - 1)) =
      -a * (singularRiccatiProfile α c t) ^ 2 := by
    unfold singularRiccatiProfile
    have hs : (t ^ (-α)) ^ 2 = t ^ (-α + -α) := by rw [pow_two, ← Real.rpow_add ht]
    rw [ite_eq_left ht, mul_pow, hs, show 1 - 2 * α - 1 = -α + -α by ring]
    unfold C c singularRiccatiCoefficient
    field_simp [ha.ne', (Real.Gamma_pos_of_pos (by linarith : 0 < 2 - 2 * α)).ne']
    ring
  rw [hval] at hd
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ht] with u hu
  exact singularRiccatiProfile_primitive (c := c) hα hu

end RoughHeston

#print axioms RoughHeston.singularRiccatiProfile_primitive
#print axioms RoughHeston.singularRiccatiCoefficient_pos
#print axioms RoughHeston.singularRiccatiProfile_solves
