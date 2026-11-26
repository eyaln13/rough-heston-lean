import AffineTestInstantiation
import RiccatiGlobalBoundary
import LaplaceBoundary

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace RoughHeston

private theorem affine_L_eq_fractionalK (α : ℝ) : fractionalL α=fractionalK (1-α) := by
  funext u
  simp only [fractionalK,fractionalL,show 1-α-1 = -α by ring]

private theorem affine_L_nonnegative (α : ℝ) (hα : α<1) (r : ℝ) : 0≤fractionalL α r := by
  by_cases hr : 0<r
  · rw [fractionalL,ite_eq_right (not_le.mpr hr)]
    exact div_nonneg (Real.rpow_nonneg hr.le _) (Real.Gamma_pos_of_pos (sub_pos.mpr hα)).le
  · rw [fractionalL,ite_eq_left (le_of_not_gt hr)]

private theorem affine_L_pair_integrable {α t : ℝ} (hα : α<1) (ht : 0<t) :
    IntegrableOn (fun r => fractionalL α (t-r)*fractionalL α r) (Ioc 0 t) := by
  let δ := 1-α
  have hδ : 0<δ := sub_pos.mpr hα
  have h := (real_beta_weight_scaled hδ hδ ht).1
  refine (h.div_const (Real.Gamma δ*Real.Gamma δ)).congr ?_
  rw [← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  rw [affine_L_eq_fractionalK, fractionalK, fractionalK,
    ite_eq_right (not_le.mpr (sub_pos.mpr hr.2)),ite_eq_right (not_le.mpr hr.1)]
  dsimp [δ]
  rw [div_mul_div_comm,mul_comm (r^(1-α-1))]

/-- Uniform affine normalization on a compact positive time interval
from the singular Riccati profile bound and the original initial input. -/
theorem point_riccati_input_convolution_uniform
    {α κ a q lo hi t b v₀ : ℝ} {w : ℝ → ℝ}
    (hα : 1/2<α) (hα' : α<1) (hκ : 0≤κ) (ha : 0<a)
    (hlo : 0<lo) (ht : t∈Icc lo hi) (hb : 0≤b) (hv₀ : 0≤v₀)
    (hw : PointChargeRiccatiOn α q (-κ) (-a) t w) :
    volterraConvolution w (fun r => b+v₀*fractionalL α r) t ≤
      singularRiccatiCoefficient α a*Real.Gamma (1-α)*
        (b*(hi^(1-α)/Real.Gamma (2-α))+
          v₀*(lo^(1-2*α)/Real.Gamma (2-2*α))) := by
  have hα₀ : 0<α := by linarith
  have ht₀ : 0<t := hlo.trans_le ht.1
  let j (r : ℝ) := b+v₀*fractionalL α r
  let A := singularRiccatiCoefficient α a*Real.Gamma (1-α)
  have hA : 0≤A := mul_nonneg (singularRiccatiCoefficient_pos hα hα' ha).le
    (Real.Gamma_pos_of_pos (sub_pos.mpr hα')).le
  have hj : AffineInputOn t j := affine_input_on_of_initial_and_bounded_rate
    hα₀ hα' ht₀ hv₀ measurable_const (fun _ _ => hb) (C := ‖b‖) (fun _ _ => le_rfl)
  obtain ⟨hwi,_⟩ := integrableOn_riccati_powers_of_weighted_asymptotic hα ht₀
    hw.measurable hw.continuousOn_pos hw.asymptotic
  have hwi' := affine_terminal_input_pairing_integrable ht₀ hw.measurable hw.continuousOn_pos hwi hj
  have hW (u : ℝ) (hu : u∈Ioo 0 t) : w u ≤ A*fractionalL α u := by
    have h := point_charge_riccati_lt_singular_profile hα hα' hκ ha ht₀
      hw.measurable hw.contDiffAt_pos hw.volterra hw.asymptotic u (Ioo_subset_Ioc_self hu)
    refine h.le.trans_eq ?_
    rw [singularRiccatiProfile,ite_eq_left hu.1,fractionalL,ite_eq_right (not_le.mpr hu.1)]
    dsimp [A]
    field_simp [(Real.Gamma_pos_of_pos (sub_pos.mpr hα')).ne']
  let G (r : ℝ) := b*fractionalL α (t-r)
  let R (r : ℝ) := v₀*(fractionalL α (t-r)*fractionalL α r)
  have hGi : IntegrableOn G (Ioc 0 t) :=
    (fractionalL_reflected_integrableOn_Ioc hα' ht₀.le).const_mul b
  have hRi : IntegrableOn R (Ioc 0 t) := (affine_L_pair_integrable hα' ht₀).const_mul v₀
  have hDom : (∫ r in Ioc (0:ℝ) t,w (t-r)*j r) ≤
      ∫ r in Ioc (0:ℝ) t,A*(G r+R r) := by
    rw [← restrict_Ioo_eq_restrict_Ioc]
    refine setIntegral_mono_on (IntegrableOn.mono_set hwi' Ioo_subset_Ioc_self)
      (IntegrableOn.mono_set ((hGi.add hRi).const_mul A) Ioo_subset_Ioc_self) measurableSet_Ioo (fun r hr => ?_)
    have hru : t-r∈Ioo 0 t := ⟨sub_pos.mpr hr.2,by linarith [hr.1]⟩
    refine (mul_le_mul_of_nonneg_right (hW (t-r) hru) (hj.nonnegative r (Ioo_subset_Ioc_self hr))).trans_eq ?_
    dsimp [G,R,j]
    ring
  have hG : (∫ r in Ioc (0:ℝ) t,G r) = b*(t^(1-α)/Real.Gamma (2-α)) := by
    unfold G
    rw [integral_const_mul,affine_L_eq_fractionalK,density_fractionalK_mass (sub_pos.mpr hα') ht₀.le,
      show 1-α+1=2-α by ring]
  have hR : (∫ r in Ioc (0:ℝ) t,R r) = v₀*(t^(1-2*α)/Real.Gamma (2-2*α)) := by
    unfold R
    rw [integral_const_mul]
    change v₀*volterraConvolution (fractionalL α) (fractionalL α) t=_
    rw [affine_L_eq_fractionalK,fractionalK_convolution_add (sub_pos.mpr hα') (sub_pos.mpr hα') ht₀,
      fractionalK,ite_eq_right (not_le.mpr ht₀),
      show 1-α+(1-α)=2-2*α by ring,show 2-2*α-1=1-2*α by ring]
  have hbnd : b*(t^(1-α)/Real.Gamma (2-α))≤b*(hi^(1-α)/Real.Gamma (2-α)) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
      (Real.rpow_le_rpow ht₀.le ht.2 (sub_pos.mpr hα').le)
      (Real.Gamma_pos_of_pos (by linarith)).le) hb
  have hvbnd : v₀*(t^(1-2*α)/Real.Gamma (2-2*α))≤v₀*(lo^(1-2*α)/Real.Gamma (2-2*α)) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hlo ht.1 (by linarith))
      (Real.Gamma_pos_of_pos (by linarith)).le) hv₀
  have hAdd := integral_add hGi hRi
  rw [integral_const_mul,hAdd,hG,hR] at hDom
  exact hDom.trans (mul_le_mul_of_nonneg_left (add_le_add hbnd hvbnd) hA)

#print axioms point_riccati_input_convolution_uniform

end RoughHeston
