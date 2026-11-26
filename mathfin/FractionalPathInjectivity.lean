import Verification
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Set Filter
open scoped MeasureTheory Topology

namespace RoughHeston

/-- Fractional convolution by the inverse kernel is injective on
continuous paths on a positive finite horizon. -/
theorem fractionalL_zero_implies_path_zero {α T : ℝ} {f : ℝ → ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1) (hT : 0 < T) (hf : Measurable f)
    (hfc : ContinuousOn f (Icc 0 T))
    (hzero : ∀ t ∈ Icc 0 T, volterraConvolution (fractionalL α) f t = 0) :
    ∀ t ∈ Icc 0 T, f t = 0 := by
  have hK : fractionalK (1 - α) = fractionalL α := by
    funext t
    simp only [fractionalK, fractionalL, show 1 - α - 1 = -α by ring]
  have hL : fractionalL (1 - α) = fractionalK α := by
    funext t
    simp only [fractionalL, fractionalK, show -(1 - α) = α - 1 by ring,
      show 1 - (1 - α) = α by ring]
  have hi (t : ℝ) (ht : t ∈ Icc 0 T) : IntervalIntegrable f volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1 (hfc.mono (Icc_subset_Icc le_rfl ht.2))
  have hprim (t : ℝ) (ht : t ∈ Icc 0 T) : (∫ s in (0 : ℝ)..t, f s) = 0 := by
    have hfin := (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).1 (hi t ht)
    have hidentity := fractional_volterra_inverts_drift (α := 1 - α)
      (sub_pos.mpr hα₁) (by linarith : 1 - α < 1) hf hfin
    rw [hK, hL] at hidentity
    rw [intervalIntegral.integral_of_le ht.1, ← hidentity]
    unfold volterraConvolution
    calc
      _ = ∫ _ in Ioc (0 : ℝ) t, (0 : ℝ) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro s hs
        change fractionalK α (t - s) * volterraConvolution (fractionalL α) f s = 0
        rw [hzero s ⟨hs.1.le, hs.2.trans ht.2⟩, mul_zero]
      _ = 0 := integral_zero _ _
  have hint : EqOn f (fun _ : ℝ => (0 : ℝ)) (Ioo 0 T) := by
    intro t ht
    have hmem : Ioo 0 T ∈ 𝓝 t := Ioo_mem_nhds ht.1 ht.2
    have hfc' : ContinuousAt f t :=
      (hfc t (Ioo_subset_Icc_self ht)).continuousAt (Icc_mem_nhds ht.1 ht.2)
    have hd := intervalIntegral.integral_hasDerivAt_right (hi t (Ioo_subset_Icc_self ht))
      hf.stronglyMeasurable.stronglyMeasurableAtFilter hfc'
    have he : (fun t => ∫ s in (0 : ℝ)..t, f s) =ᶠ[𝓝 t] fun _ => (0 : ℝ) :=
      Filter.Eventually.mono hmem (fun u hu => hprim u (Ioo_subset_Icc_self hu))
    exact hd.unique ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq he)
  exact hint.of_subset_closure hfc continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo hT.ne])

end RoughHeston

#print axioms RoughHeston.fractionalL_zero_implies_path_zero
