import AffineContinuousEnergyClock
import StoppedEnergyClock

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston.GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {F : Filtration ℝ≥0 m}

private theorem integral_indicator_le_hestonTime {H t : ℝ≥0} (ht : t ≤ H)
    {f : ℝ≥0 → ℝ} (hf : Measurable f) :
    (∫ r, (Iic t).indicator f r ∂hestonTimeMeasure H) =
      ∫ r in (0 : ℝ)..(t : ℝ), f r.toNNReal := by
  rw [hestonTimeMeasure, integral_map continuous_real_toNNReal.measurable.aemeasurable
    (hf.indicator measurableSet_Iic).aestronglyMeasurable,
    Measure.restrict_congr_set Ioo_ae_eq_Ioc,
    intervalIntegral.integral_of_le (μ := volume) (f := fun r : ℝ => f r.toNNReal) t.coe_nonneg]
  have hEq : (fun r : ℝ => (Iic t).indicator f r.toNNReal) =ᵐ[volume.restrict (Ioc 0 (H : ℝ))]
      (Iic (t : ℝ)).indicator (fun r => f r.toNNReal) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have he : r.toNNReal ≤ t ↔ r ≤ (t : ℝ) := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1.le]
    simp only [indicator, mem_Iic, he]
  rw [integral_congr_ae hEq, integral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic]
  congr 1
  congr 1
  ext r
  have hm : (t : ℝ) ≤ (H : ℝ) := NNReal.coe_le_coe.mpr ht
  simp only [mem_inter_iff, mem_Iic, mem_Ioc]
  exact ⟨fun h => ⟨h.2.1,h.1⟩,fun h => ⟨h.2,h.1,h.2.trans hm⟩⟩

omit m in
theorem affineEnergyClock_controlThrough {g : ℝ≥0 → Ω → ℝ}
    (τ : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    affineEnergyClock (controlThrough g τ) t ω = affineEnergyClock g (min t (τ ω)) ω := by
  let a (s : ℝ) := g s.toNNReal ω ^ 2
  rw [affineEnergyClock, affineEnergyClock, intervalIntegral.integral_of_le t.coe_nonneg,
    intervalIntegral.integral_of_le (min t (τ ω)).coe_nonneg]
  have hleft : (fun s : ℝ => controlThrough g τ s.toNNReal ω ^ 2) =ᵐ[volume.restrict (Ioc 0 (t:ℝ))]
      (Iic (τ ω : ℝ)).indicator a := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have he : s.toNNReal ≤ τ ω ↔ s ≤ (τ ω : ℝ) := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1.le]
    by_cases h : s ≤ (τ ω : ℝ)
    · simp [a, controlThrough, Set.indicator, he.mpr h, h]
    · simp [controlThrough, Set.indicator, mt he.mp h, h]
  rw [integral_congr_ae hleft, integral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic]
  congr 2
  ext s
  simp only [mem_inter_iff, mem_Iic, mem_Ioc, NNReal.coe_min, le_min_iff]
  tauto

theorem affineEnergyClock_controlThrough_stronglyAdapted {g : ℝ≥0 → Ω → ℝ}
    {τ : Ω → ℝ≥0}
    (h : IsStronglyPredictable F (controlThrough g τ)) :
    StronglyAdapted F (affineEnergyClock (controlThrough g τ)) := by
  intro t
  have he : affineEnergyClock (controlThrough g τ) t = controlEnergyClock t (controlThrough g τ) t := by
    funext ω
    rw [controlEnergyClock, ← integral_indicator measurableSet_Iic, affineEnergyClock]
    exact (integral_indicator_le_hestonTime le_rfl (((h.mono F.predictable_le_prod).measurable.comp
      (measurable_id.prodMk measurable_const)).pow_const 2)).symm
  rw [he]
  exact controlEnergyClock_adapted t h t

omit m in
theorem affineEnergyClock_exp_identity_controlThrough {H : ℝ≥0} {g : ℝ≥0 → Ω → ℝ}
    (hc : ∀ ω, Continuous (fun s => g s ω)) {τ : Ω → ℝ≥0} (hτ : ∀ ω, τ ω ≤ H) (ω : Ω) :
    let g' := controlThrough g τ
    let Φ := fun t => Real.exp (affineEnergyClock g' t ω) * (g' t ω)^2
    Integrable Φ (hestonTimeMeasure H) ∧
      Real.exp (affineEnergyClock g' H ω) = 1 + ∫ t, Φ t ∂hestonTimeMeasure H := by
  let g' := controlThrough g τ
  let Φ := fun t => Real.exp (affineEnergyClock g' t ω) * (g' t ω)^2
  let Ψ := fun t => Real.exp (affineEnergyClock g t ω) * (g t ω)^2
  have hΨ : Continuous Ψ := ((Real.continuous_exp.comp (affineEnergyClock_continuous hc ω)).mul
    ((hc ω).pow 2))
  have heq : Φ = (Iic (τ ω)).indicator Ψ := by
    funext t
    by_cases ht : t ≤ τ ω
    · simp [Φ, g', Ψ, controlThrough, ht, Set.indicator, affineEnergyClock_controlThrough]
    · simp [Φ, g', controlThrough, ht, Set.indicator]
  have hI := (affineEnergyClock_exp_identity (H := H) hc ω).1
  have hJ := (affineEnergyClock_exp_identity (H := τ ω) hc ω).2
  have hH : (∫ t, Φ t ∂hestonTimeMeasure H) = ∫ t, Ψ t ∂hestonTimeMeasure (τ ω) := by
    rw [heq, integral_indicator_le_hestonTime (hτ ω) hΨ.measurable]
    rw [← integral_indicator_le_hestonTime (t := τ ω) (H := τ ω) le_rfl hΨ.measurable]
    apply integral_congr_ae
    filter_upwards [ae_time_lt_hestonTimeMeasure (τ ω)] with t ht
    exact indicator_of_mem (show t ∈ Iic (τ ω) from ht.le) Ψ
  refine ⟨?_, ?_⟩
  · change Integrable Φ _
    rw [heq]
    exact hI.indicator measurableSet_Iic
  · change Real.exp (affineEnergyClock g' H ω) = 1 + ∫ t, Φ t ∂hestonTimeMeasure H
    rw [affineEnergyClock_controlThrough, min_eq_right (hτ ω), hH]
    exact hJ

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.affineEnergyClock_controlThrough
#print axioms RoughHeston.GirsanovPort.affineEnergyClock_controlThrough_stronglyAdapted
#print axioms RoughHeston.GirsanovPort.affineEnergyClock_exp_identity_controlThrough
