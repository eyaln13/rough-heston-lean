import RiccatiDifferential
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RoughHeston

/-- Absolute integrability on a positive finite interval gives
continuity of the anchored cumulative integral, including both endpoints. -/
theorem continuousOn_affine_ordinary_primitive {T : ℝ} {f : ℝ → ℝ}
    (hi : IntegrableOn f (Ioc 0 T)) :
    ContinuousOn (fun t => ∫ r in Ioc (0:ℝ) t,f r) (Icc 0 T) := by
  have hi' : IntegrableOn f (Icc 0 T) := by
    unfold IntegrableOn at *
    rw [← restrict_Ioc_eq_restrict_Icc]
    exact hi
  exact intervalIntegral.continuousOn_primitive hi'

/-- For a point-plus-density affine Riccati test, the fractional
primitive has its point charge as right limit and has the density
Riccati drift as its positive-time derivative. -/
theorem affine_test_primitive_and_derivative
    {α q T : ℝ} {w R : ℝ → ℝ}
    (hα : 0 < α) (hα' : α < 1) (hT : 0 < T)
    (hm : Measurable R) (hi : IntegrableOn R (Ioc 0 T))
    (hRc : ContinuousOn R (Ioi 0))
    (hVol : ∀ t ∈ Ioc 0 T, w t = q*fractionalK α t+
      volterraConvolution (fractionalK α) R t) :
    (∀ t ∈ Ioc 0 T, IntegrableOn (fun r => fractionalL α (t-r)*w r) (Ioc 0 t)) ∧
      (∀ t ∈ Ioo 0 T, HasDerivAt (volterraConvolution (fractionalL α) w) (R t) t) ∧
      Tendsto (volterraConvolution (fractionalL α) w) (𝓝[>] (0:ℝ)) (𝓝 q) := by
  have hPrim (s : ℝ) (hs : s ∈ Ioc 0 T) :
      IntegrableOn (fun r => fractionalL α (s-r)*w r) (Ioc 0 s) ∧
        volterraConvolution (fractionalL α) w s = q+∫ r in Ioc (0:ℝ) s,R r :=
    fractional_rl_inverse_of_point_charge hα hα' hs.1 hm
      (hi.mono_set (Ioc_subset_Ioc_right hs.2)) (fun r hr => hVol r ⟨hr.1,hr.2.trans hs.2⟩)
  refine ⟨fun t ht => (hPrim t ht).1, ?_, ?_⟩
  · intro t ht
    have hI : IntervalIntegrable R volume 0 t :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1.le).mpr
        (hi.mono_set (Ioc_subset_Ioc_right ht.2.le))
    have hC : ContinuousAt R t := hRc.continuousAt (Ioi_mem_nhds ht.1)
    have hDer := (intervalIntegral.integral_hasDerivAt_right hI
      hm.aestronglyMeasurable.stronglyMeasurableAtFilter hC).const_add q
    refine hDer.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    have hs' : s ∈ Ioo (0:ℝ) T := hs
    rw [intervalIntegral.integral_of_le hs'.1.le]
    exact (hPrim s ⟨hs'.1,hs'.2.le⟩).2
  · have hW := continuousOn_affine_ordinary_primitive hi
    have hNear : 𝓝[>] (0:ℝ) ≤ 𝓝[Icc 0 T] 0 := by
      refine le_inf nhdsWithin_le_nhds (le_principal_iff.mpr ?_)
      filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds hT)] with s hs hst
      exact ⟨(show 0<s from hs).le,(show s<T from hst).le⟩
    have hLim := hW 0 ⟨le_rfl,hT.le⟩
    change Tendsto (fun t => ∫ r in Ioc (0:ℝ) t,R r) (𝓝[Icc 0 T] 0)
      (𝓝 (∫ r in Ioc (0:ℝ) 0,R r)) at hLim
    have hLim' := (hLim.mono_left hNear).const_add q
    simp only [Ioc_self,setIntegral_empty,add_zero] at hLim'
    refine hLim'.congr' ?_
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds hT)] with s hs hst
    exact (hPrim s ⟨hs,(show s<T from hst).le⟩).2.symm

/-- A positive-time initial input v₀L is bounded near any strictly
positive terminal time, together with a bounded immigrant rate. -/
theorem affine_input_bounded_near_positive_terminal
    {α T v₀ C : ℝ} {j b : ℝ → ℝ}
    (hα : 0 < α) (hα' : α < 1) (hT : 0 < T)
    (hb : ∀ s ∈ Icc (T/2) T, ‖b s‖ ≤ C)
    (hj : ∀ s ∈ Icc (T/2) T, j s = b s+v₀*fractionalL α s) :
    ∀ s ∈ Icc (T/2) T, ‖j s‖ ≤ C+‖v₀‖*fractionalL α (T/2) := by
  intro s hs
  have hhalf : 0 < T/2 := half_pos hT
  have hs' := hhalf.trans_le hs.1
  have hGs := Real.Gamma_pos_of_pos (show 0<1-α by linarith)
  have hLs : 0 ≤ fractionalL α s := by
    rw [fractionalL,ite_eq_right (not_le.mpr hs')]
    exact div_nonneg (Real.rpow_nonneg hs'.le _) hGs.le
  have hLm : fractionalL α s ≤ fractionalL α (T/2) := by
    rw [fractionalL,fractionalL,ite_eq_right (not_le.mpr hs'),ite_eq_right (not_le.mpr hhalf)]
    exact div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hhalf hs.1 (neg_nonpos.mpr hα.le)) hGs.le
  rw [hj s hs]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul,Real.norm_of_nonneg hLs]
  exact add_le_add (hb s hs) (mul_le_mul_of_nonneg_left hLm (norm_nonneg _))

#print axioms affine_test_primitive_and_derivative
#print axioms affine_input_bounded_near_positive_terminal

end RoughHeston
