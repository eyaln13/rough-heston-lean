import AffineLocalExponential

open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal Interval

namespace RoughHeston

/-- The ordinary cumulative bracket, stopped at the positive
preterminal horizon where its rate is continuous. -/
noncomputable def affineStoppedBracket {Ω : Type*} (H : ℝ≥0) (b : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ r in (0:ℝ)..((min t H:ℝ≥0):ℝ), b r.toNNReal ω

/-- A genuine continuous compensated square with this stopped bracket
gives the local exponential with the ordinary bracket compensation. -/
theorem affine_exp_isLocalMartingale_of_stopped_bracket
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} {N b : ℝ≥0 → Ω → ℝ} (H : ℝ≥0)
    (hNad : StronglyAdapted 𝒢 N) (hAad : StronglyAdapted 𝒢 (affineStoppedBracket H b))
    (hbad : StronglyAdapted 𝒢 b)
    (hNc : ∀ ω, Continuous fun t => N t ω) (hbc : ∀ ω, Continuous fun t => b t ω)
    (hN : IsLocalMartingale N 𝒢 μ)
    (hComp : IsLocalMartingale (fun t ω => N t ω^2-affineStoppedBracket H b t ω) 𝒢 μ)
    (hb₀ : ∀ t ω, 0 ≤ b t ω) {K : ℝ} (hstart : ∀ ω, |N 0 ω|+b 0 ω ≤ K) :
    IsLocalMartingale (fun t ω => Real.exp (-N t ω-affineStoppedBracket H b t ω/2)) 𝒢 μ := by
  let A := affineStoppedBracket H b
  let f (ω : Ω) (s : ℝ) := b s.toNNReal ω
  have hfc (ω : Ω) : Continuous (f ω) := (hbc ω).comp continuous_real_toNNReal
  have hA₀ (ω : Ω) : A 0 ω = 0 := by simp [A,affineStoppedBracket]
  have hAc (ω : Ω) : Continuous (fun t => A t ω) := by
    have hP : Continuous (fun t : ℝ => ∫ r in (0:ℝ)..t, f ω r) :=
      intervalIntegral.continuous_primitive (fun a b => (hfc ω).intervalIntegrable a b) 0
    exact hP.comp (NNReal.continuous_coe.comp (continuous_id.min continuous_const))
  have hIncr (ω : Ω) (s t : ℝ≥0) :
      A t ω-A s ω = ∫ r in ((min s H:ℝ≥0):ℝ)..((min t H:ℝ≥0):ℝ), f ω r := by
    have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      ((hfc ω).intervalIntegrable (0:ℝ) (min s H:ℝ≥0))
      ((hfc ω).intervalIntegrable (min s H:ℝ≥0) (min t H:ℝ≥0))
    change ((∫ r in (0:ℝ)..((min s H:ℝ≥0):ℝ),f ω r)+
      (∫ r in ((min s H:ℝ≥0):ℝ)..((min t H:ℝ≥0):ℝ),f ω r)) =
      ∫ r in (0:ℝ)..((min t H:ℝ≥0):ℝ), f ω r at he
    change (∫ r in (0:ℝ)..((min t H:ℝ≥0):ℝ),f ω r) -
      (∫ r in (0:ℝ)..((min s H:ℝ≥0):ℝ),f ω r) = _
    rw [← he, add_sub_cancel_left]
  have hAmon (ω : Ω) : Monotone (fun t => A t ω) := by
    intro s t hst
    apply sub_nonneg.mp
    rw [hIncr]
    exact intervalIntegral.integral_nonneg (by exact_mod_cast min_le_min_right H hst)
      (fun r _ => hb₀ r.toNNReal ω)
  refine affine_exp_isLocalMartingale_of_bracket_rate hNad hAad hbad hNc hAc hbc
    hN hComp hA₀ hAmon hb₀ hstart ?_
  intro ω s t hst D hD hbound
  rw [hIncr]
  by_cases hsH : s ≤ H
  · rw [min_eq_left hsH]
    have hsto : s ≤ min t H := le_min hst hsH
    have hsto' : (s:ℝ) ≤ (min t H:ℝ≥0) := by exact_mod_cast hsto
    have hle : ∀ r ∈ Icc (s:ℝ) ((min t H:ℝ≥0):ℝ), f ω r ≤ D := by
      intro r hr
      have hr0 : 0 ≤ r := (NNReal.coe_nonneg s).trans hr.1
      apply hbound r.toNNReal
      constructor
      · exact NNReal.coe_le_coe.mp (by simpa only [Real.coe_toNNReal r hr0] using hr.1)
      · apply NNReal.coe_le_coe.mp
        simpa only [Real.coe_toNNReal r hr0] using
          hr.2.trans (NNReal.coe_le_coe.mpr (min_le_left t H))
    have hi := intervalIntegral.integral_mono_on hsto'
      ((hfc ω).intervalIntegrable (s:ℝ) (min t H:ℝ≥0)) (intervalIntegrable_const (μ := volume) (c := D)) hle
    rw [intervalIntegral.integral_const,smul_eq_mul,mul_comm _ D] at hi
    exact hi.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right
      (NNReal.coe_le_coe.mpr (min_le_left t H)) (s:ℝ)) hD)
  · have hHs : H ≤ s := le_of_not_ge hsH
    rw [min_eq_right hHs,min_eq_right (hHs.trans hst),intervalIntegral.integral_same]
    exact mul_nonneg hD (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst))

#print axioms affine_exp_isLocalMartingale_of_stopped_bracket

end RoughHeston
