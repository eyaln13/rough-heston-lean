import ClusterEarlyPulseLowerTail

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace RoughHeston

/-- Input from a rectangular pulse accrued up to the observation time.
Changing the endpoints of its time interval has the same Lebesgue density. -/
noncomputable def rectangularPulseMeasure (ε d s : ℝ) : Measure ℝ :=
  ENNReal.ofReal (ε/d) • volume.restrict (Ioc 0 (min d s))

theorem rectangularPulseMeasure_isFiniteMeasure (ε d s : ℝ) :
    IsFiniteMeasure (rectangularPulseMeasure ε d s) := by
  constructor
  rw [rectangularPulseMeasure,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul,Real.volume_Ioc]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

theorem rectangularPulseMeasure_real_univ
    {ε d s : ℝ} (hε : 0 ≤ ε) (hd : 0 < d) (hs : 0 ≤ s) :
    (rectangularPulseMeasure ε d s).real univ = (ε/d)*min d s := by
  rw [measureReal_def,rectangularPulseMeasure,Measure.smul_apply,Measure.restrict_apply_univ,
    smul_eq_mul,Real.volume_Ioc,sub_zero,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (div_nonneg hε hd.le), ENNReal.toReal_ofReal (le_min hd.le hs)]

theorem rectangularPulseMeasure_ae_age
    {ε d s : ℝ} (_hs : 0 ≤ s) :
    ∀ᵐ v ∂rectangularPulseMeasure ε d s, s-v ∈ Icc 0 s := by
  apply Measure.ae_smul_measure _ _
  filter_upwards [ae_restrict_mem (μ := volume) (s := Ioc 0 (min d s)) measurableSet_Ioc] with v hv
  exact ⟨sub_nonneg.mpr (hv.2.trans (min_le_right _ _)), sub_le_self s hv.1.le⟩

/-- After twice the pulse duration, all input has landed and its
ages lie in the last half of the observation interval. -/
theorem rectangularPulseMeasure_postpulse
    {ε d s : ℝ} (hε : 0 ≤ ε) (hd : 0 < d) (hds : 2*d ≤ s) :
    (rectangularPulseMeasure ε d s).real univ = ε ∧
      ∀ᵐ v ∂rectangularPulseMeasure ε d s, s-v ∈ Icc (s/2) s := by
  have hle : d ≤ s := by linarith
  constructor
  · rw [rectangularPulseMeasure_real_univ hε hd (hd.le.trans hle), min_eq_left hle,
      div_mul_cancel₀ _ hd.ne']
  · apply Measure.ae_smul_measure _ _
    filter_upwards [ae_restrict_mem (μ := volume) (s := Ioc 0 (min d s)) measurableSet_Ioc] with v hv
    have hvd : v ≤ d := hv.2.trans (min_le_left _ _)
    exact ⟨by linarith, sub_le_self s hv.1.le⟩

/-- At one quarter of the pulse duration, exactly one eighth of the
initial mass has age at least half the observation time. -/
theorem rectangularPulseMeasure_earlypulse_mass
    {ε d : ℝ} (hε : 0 ≤ ε) (hd : 0 < d) :
    (rectangularPulseMeasure ε d (d/4)).real {v | (d/4)/2 ≤ d/4-v} = ε/8 := by
  have hsmall : d/4 ≤ d := by linarith
  have hSet : {v : ℝ | (d/4)/2 ≤ d/4-v} = Iic (d/8) := by
    ext v
    change ((d/4)/2 ≤ d/4-v) ↔ v ≤ d/8
    constructor <;> intro hv <;> linarith
  have hInter : Iic (d/8) ∩ Ioc 0 (d/4) = Ioc 0 (d/8) := by
    ext v
    constructor
    · rintro ⟨hv₁,hv₂⟩
      exact ⟨hv₂.1,hv₁⟩
    · intro hv
      exact ⟨hv.2,hv.1,hv.2.trans (by linarith)⟩
  rw [hSet,measureReal_def,rectangularPulseMeasure,Measure.smul_apply,
    Measure.restrict_apply measurableSet_Iic,min_eq_right hsmall,hInter,Real.volume_Ioc,
    smul_eq_mul,sub_zero,ENNReal.toReal_mul,ENNReal.toReal_ofReal (div_nonneg hε hd.le),
    ENNReal.toReal_ofReal (by positivity)]
  field_simp

/-- The manuscript scaling d = ε^(1/α) gives a fixed-fraction lower
mass at the early-pulse observation time. -/
theorem rectangularPulseMeasure_earlypulse_scaled
    {ε α : ℝ} (hε : 0 < ε) (hα : 0 < α) :
    let d := ε^(1/α)
    let s := d/4
    s^α/8 ≤ (rectangularPulseMeasure ε d s).real {v | s/2 ≤ s-v} := by
  intro d s
  have hd : 0 < d := Real.rpow_pos_of_pos hε _
  have hsd : s ≤ d := by dsimp [s]; linarith
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hEq : d^α = ε := by
    dsimp [d]
    rw [← Real.rpow_mul hε.le, div_mul_cancel₀ _ hα.ne', Real.rpow_one]
  change s^α/8 ≤ (rectangularPulseMeasure ε d (d/4)).real {v | (d/4)/2≤d/4-v}
  rw [rectangularPulseMeasure_earlypulse_mass hε.le hd]
  exact div_le_div_of_nonneg_right ((Real.rpow_le_rpow hs hsd hα.le).trans_eq hEq) (by norm_num)

/-- Rectangular input rate, defined with a representative integrable
on the causal time interval. -/
noncomputable def rectangularPulseRate (ε d : ℝ) : ℝ → ℝ :=
  (Ioc 0 d).indicator (fun _ => ε/d)

theorem rectangularPulseRate_ae_eq_closed (ε d : ℝ) :
    rectangularPulseRate ε d =ᵐ[volume] (Icc 0 d).indicator (fun _ => ε/d) := by
  filter_upwards [volume.ae_ne (0:ℝ)] with v hv
  by_cases h : v ∈ Ioc (0:ℝ) d
  · rw [rectangularPulseRate, indicator_of_mem h, indicator_of_mem (Ioc_subset_Icc_self h)]
  · have h' : v ∉ Icc (0:ℝ) d := fun hi => h ⟨lt_of_le_of_ne hi.1 hv.symm, hi.2⟩
    rw [rectangularPulseRate, indicator_of_notMem h, indicator_of_notMem h']

theorem rectangularPulseMeasure_integral_eq_convolution
    {ε d s : ℝ} (hε : 0 ≤ ε) (hd : 0 < d) (w : ℝ → ℝ) :
    (∫ v,w (s-v) ∂rectangularPulseMeasure ε d s) =
      volterraConvolution w (rectangularPulseRate ε d) s := by
  rw [rectangularPulseMeasure, integral_smul_measure,
    ENNReal.toReal_ofReal (div_nonneg hε hd.le), smul_eq_mul]
  unfold volterraConvolution rectangularPulseRate
  have he : EqOn (fun v : ℝ => w (s-v)*((Ioc 0 d).indicator (fun _ => ε/d)) v)
      ((Ioc 0 d).indicator (fun v => w (s-v)*(ε/d))) (Ioc 0 s) := by
    intro v _
    by_cases hv : v ∈ Ioc (0:ℝ) d <;> simp [indicator, hv]
  have hInter : Ioc (0:ℝ) s ∩ Ioc 0 d = Ioc 0 (min d s) := by
    ext v
    change ((0 < v ∧ v ≤ s) ∧ (0 < v ∧ v ≤ d)) ↔ (0 < v ∧ v ≤ min d s)
    constructor
    · intro h
      exact ⟨h.1.1,le_min h.2.2 h.1.2⟩
    · intro h
      exact ⟨⟨h.1,h.2.trans (min_le_right _ _)⟩,⟨h.1,h.2.trans (min_le_left _ _)⟩⟩
  rw [setIntegral_congr_fun measurableSet_Ioc he, setIntegral_indicator measurableSet_Ioc,
    hInter, integral_mul_const, mul_comm]

/-- The accrued input mass is the mass of the age measure. -/
theorem rectangularPulse_accumulatedMass_eq_real_univ
    {ε d s : ℝ} (hε : 0 ≤ ε) (hd : 0 < d) :
    (∫ v in Ioc (0 : ℝ) s, rectangularPulseRate ε d v) =
      (rectangularPulseMeasure ε d s).real univ := by
  have he := rectangularPulseMeasure_integral_eq_convolution hε hd (s := s) (fun _ => (1:ℝ))
  simpa only [volterraConvolution,one_mul,integral_const,smul_eq_mul,mul_one] using he.symm

#print axioms rectangularPulseMeasure_postpulse
#print axioms rectangularPulseMeasure_earlypulse_mass
#print axioms rectangularPulseMeasure_earlypulse_scaled
#print axioms rectangularPulseMeasure_integral_eq_convolution
#print axioms rectangularPulse_accumulatedMass_eq_real_univ

end RoughHeston
