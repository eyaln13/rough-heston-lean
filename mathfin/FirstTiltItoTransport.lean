import CommonSimpleApproximation
import FiniteBrownianFrozenMartingales
import MathFin.Probability.Analysis.FiniteMeasureCauchySchwarz
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {P Q : Measure Ω} [IsFiniteMeasure P] [IsFiniteMeasure Q]
  {F : Filtration ℝ≥0 m} {H : ℝ≥0}

local instance firstTiltTimeMeasureFinite (t : ℝ≥0) : IsFiniteMeasure (hestonTimeMeasure t) := by
  rw [hestonTimeMeasure_eq_horizon]
  infer_instance

private theorem timeMeasure_restrict_horizon {a b : ℝ≥0} (hab : a ≤ b) :
    hestonTimeMeasure a = (hestonTimeMeasure b).restrict (Ioc 0 a) := by
  simp only [hestonTimeMeasure_eq_horizon, MathFin.ItoIntegralCLM.timeMeasureHorizon]
  rw [Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr (Ioc_subset_Ioc le_rfl hab)]

private theorem physical_primitive_difference {g : ℝ≥0 → ℝ}
    (hg : Integrable g (hestonTimeMeasure H)) {a b : ℝ≥0} (hab : a ≤ b) (hb : b ≤ H) :
    (∫ r, g r ∂hestonTimeMeasure b) - (∫ r, g r ∂hestonTimeMeasure a) =
      ∫ r in Ioc a b, g r ∂hestonTimeMeasure H := by
  have hsplit : hestonTimeMeasure b = hestonTimeMeasure a + (hestonTimeMeasure H).restrict (Ioc a b) := by
    rw [timeMeasure_restrict_horizon hb, timeMeasure_restrict_horizon (hab.trans hb)]
    rw [← Ioc_union_Ioc_eq_Ioc (show (0 : ℝ≥0) ≤ a from zero_le) hab]
    exact Measure.restrict_union
      (disjoint_left.mpr fun _ hx hy => (not_lt_of_ge hx.2) hy.1) measurableSet_Ioc
  have hga : Integrable g (hestonTimeMeasure a) := by
    rw [timeMeasure_restrict_horizon (hab.trans hb)]
    exact hg.integrableOn
  rw [hsplit, integral_add_measure hga hg.integrableOn]
  ring

/-- The shifted driver identity on an elementary predictable integral
uses only additivity of the ordinary integral on a time rectangle. -/
theorem jointItoSimple_sub_physical_drift
    {B W : ℝ≥0 → Ω → ℝ} {g : ℝ≥0 × Ω → ℝ} {ω : Ω}
    (hg : Integrable (fun t => g (t, ω)) (hestonTimeMeasure H))
    (hW : ∀ t ≤ H, W t ω = B t ω - ∫ r, g (r, ω) ∂hestonTimeMeasure t)
    (V : JointTBoundedSP H F) :
    jointItoSimple W V.val ω = jointItoSimple B V.val ω -
      ∫ r, V.val r ω * g (r, ω) ∂hestonTimeMeasure H := by
  let w (p : ℝ≥0 × ℝ≥0) (r : ℝ≥0) :=
    (Ioc p.1 p.2).indicator (fun r => V.val.value p ω * g (r, ω)) r
  have hwI (p : ℝ≥0 × ℝ≥0) : Integrable (w p) (hestonTimeMeasure H) :=
    (hg.const_mul _).indicator measurableSet_Ioc
  have hsum : (∫ r, V.val r ω * g (r, ω) ∂hestonTimeMeasure H) =
      ∑ p ∈ V.val.value.support, ∫ r, w p r ∂hestonTimeMeasure H := by
    rw [← integral_finsetSum _ (fun p _ => hwI p)]
    apply integral_congr_ae
    rw [hestonTimeMeasure_eq_horizon, MathFin.ItoIntegralCLM.timeMeasureHorizon]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc (a := (0 : ℝ≥0)) (b := H))] with r hr
    have hr₀ : r ∉ ({⊥} : Set ℝ≥0) := notMem_singleton_iff.mpr hr.1.ne'
    rw [SimpleProcess.apply_eq, indicator_of_notMem hr₀, zero_add, Finsupp.sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : r ∈ Ioc p.1 p.2 <;> simp [w, h]
  simp only [jointItoSimple, Finsupp.sum, hsum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hab := V.val.le_of_mem_support_value p hp
  have hb := V.property p hp
  rw [hW p.1 (hab.trans hb), hW p.2 hb, show (∫ r, w p r ∂hestonTimeMeasure H) =
    V.val.value p ω * ∫ r in Ioc p.1 p.2, g (r, ω) ∂hestonTimeMeasure H from by
      dsimp only [w]
      rw [integral_indicator measurableSet_Ioc, integral_const_mul],
    ← physical_primitive_difference hg hab hb]
  ring

private theorem timeProduct_L2_multiplication_L1_limit
    {f : ℕ → ℝ≥0 × Ω → ℝ} {v g : ℝ≥0 × Ω → ℝ}
    (hf : ∀ n, MemLp (f n) 2 ((hestonTimeMeasure H).prod Q))
    (hv : MemLp v 2 ((hestonTimeMeasure H).prod Q))
    (hg : MemLp g 2 ((hestonTimeMeasure H).prod Q))
    (hConv : Tendsto (fun n => eLpNorm (f n - v) 2 ((hestonTimeMeasure H).prod Q)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm
      ((fun ω => ∫ r, f n (r, ω) * g (r, ω) ∂hestonTimeMeasure H) -
        (fun ω => ∫ r, v (r, ω) * g (r, ω) ∂hestonTimeMeasure H))
      1 Q) atTop (𝓝 0) := by
  let θ := hestonTimeMeasure H
  let R := θ.prod Q
  let e (n : ℕ) := f n - v
  let w (n : ℕ) (p : ℝ≥0 × Ω) := e n p * g p
  let E (n : ℕ) (ω : Ω) := ∫ r, w n (r, ω) ∂θ
  let A (n : ℕ) (ω : Ω) := ∫ r, f n (r, ω) * g (r, ω) ∂θ
  let B (ω : Ω) := ∫ r, v (r, ω) * g (r, ω) ∂θ
  have he (n : ℕ) : MemLp (e n) 2 R := (hf n).sub hv
  have hi (n : ℕ) : Integrable (w n) R := (he n).integrable_mul hg
  have hA (n : ℕ) : Integrable (fun p => f n p * g p) R := (hf n).integrable_mul hg
  have hB : Integrable (fun p => v p * g p) R := hv.integrable_mul hg
  have hEq (n : ℕ) : E n =ᵐ[Q] A n - B := by
    filter_upwards [(hA n).prod_left_ae, hB.prod_left_ae] with ω hAf hBf
    change (∫ r, (f n (r, ω) - v (r, ω)) * g (r, ω) ∂θ) =
      (∫ r, f n (r, ω) * g (r, ω) ∂θ) - ∫ r, v (r, ω) * g (r, ω) ∂θ
    simp_rw [sub_mul]
    exact integral_sub hAf hBf
  have hL (n : ℕ) : (∫ ω, ‖E n ω‖ ∂Q) ≤
      (eLpNorm (e n) 2 R).toReal * Real.sqrt (∫ p, g p ^ 2 ∂R) := by
    have hCS := MathFin.integral_abs_mul_le_sqrt_mul_sqrt (he n) hg
    have hUse : Real.sqrt (∫ p, (e n p) ^ 2 ∂R) = (eLpNorm (e n) 2 R).toReal := by
      rw [← Lp.norm_toLp (e n) (he n), ← norm_toLp_two_sq (he n),
        Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [hUse] at hCS
    calc
      _ ≤ ∫ ω, (∫ r, ‖w n (r, ω)‖ ∂θ) ∂Q :=
        integral_mono ((hi n).integral_prod_right.norm) (hi n).integral_norm_prod_right
          (fun ω => norm_integral_le_integral_norm _)
      _ = ∫ p, |w n p| ∂R := by
        rw [integral_prod_symm _ ((hi n).abs)]
        simp_rw [Real.norm_eq_abs]
      _ ≤ _ := hCS
  have hconvR : Tendsto (fun n => ∫ ω, ‖E n ω‖ ∂Q) atTop (𝓝 0) := by
    have h := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hConv
    have h' : Tendsto (fun n => (eLpNorm (e n) 2 R).toReal * Real.sqrt (∫ p, g p ^ 2 ∂R)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, ENNReal.toReal_zero, zero_mul] using
        h.mul_const (Real.sqrt (∫ p, g p ^ 2 ∂R))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h'
      (fun _ => integral_nonneg fun _ => norm_nonneg _) hL
  have hconvN := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hconvR
  simp only [Function.comp_def, ENNReal.ofReal_zero] at hconvN
  refine hconvN.congr ?_
  intro n
  rw [← eLpNorm_congr_ae (hEq n), eLpNorm_one_eq_lintegral_enorm
    ((hi n).integral_prod_right.aestronglyMeasurable),
    ofReal_integral_norm_eq_lintegral_enorm ((hi n).integral_prod_right)]

/-- A Brownian shift on the supplied filtration transports the completed
terminal Itô integral. Both integrands represent the same measurable
function. The old stochastic limit is transported to the new law by
absolute continuity. The drift convergence uses product L² on each factor. -/
theorem jointIto_transport_of_physicalShift
    {B W : ℝ≥0 → Ω → ℝ}
    (hB : Martingale B F P) (hW : Martingale W F Q)
    (hB₂ : ∀ t, MemLp (B t) 2 P) (hW₂ : ∀ t, MemLp (W t) 2 Q)
    (hBclock : Martingale (fun t ω => B t ω ^ 2 - ((min t H : ℝ≥0) : ℝ)) F P)
    (hWclock : Martingale (fun t ω => W t ω ^ 2 - ((min t H : ℝ≥0) : ℝ)) F Q)
    (hAC : Q ≪ P) {g f : ℝ≥0 × Ω → ℝ}
    (hShift : ∀ᵐ ω ∂Q, ∀ t ≤ H, W t ω = B t ω - ∫ r, g (r, ω) ∂hestonTimeMeasure t)
    (hg : MemLp g 2 ((hestonTimeMeasure H).prod Q))
    (hf : StronglyMeasurable[F.predictable] f)
    (hfP : MemLp f 2 (jointPredictableMeasure F P H))
    (hfQ : MemLp f 2 (jointPredictableMeasure F Q H)) :
    ⇑(jointItoIntegralCLM H hW₂ (hfQ.toLp f)) =ᵐ[Q]
      fun ω => jointItoIntegralCLM H hB₂ (hfP.toLp f) ω -
        ∫ r, f (r, ω) * g (r, ω) ∂hestonTimeMeasure H := by
  let θ := hestonTimeMeasure H
  let R := θ.prod Q
  obtain ⟨V, hVP, hVQ, hVL2⟩ := exists_jointSimpleApproximation_two_measures hf hfP hfQ
  let Fv (n : ℕ) := Function.uncurry ⇑(V n).val
  let D (n : ℕ) (ω : Ω) := ∫ r, Fv n (r, ω) * g (r, ω) ∂θ
  let Dlim (ω : Ω) := ∫ r, f (r, ω) * g (r, ω) ∂θ
  let BP := jointItoIntegralCLM H hB₂ (hfP.toLp f)
  let WQ := jointItoIntegralCLM H hW₂ (hfQ.toLp f)
  let BS (n : ℕ) := jointItoSimple B (V n).val
  let WS (n : ℕ) := jointItoSimple W (V n).val
  have hv (n : ℕ) : MemLp (Fv n) 2 R := by
    change MemLp (Fv n) 2 (θ.prod Q)
    rw [show θ = MathFin.ItoIntegralCLM.timeMeasureHorizon H from hestonTimeMeasure_eq_horizon H]
    exact memLp_of_memLp_trim F.predictable_le_prod (simpleProcessUncurry_memLp_joint (μ := Q) H (V n).val)
  have hfQraw : MemLp f 2 R := by
    change MemLp f 2 (θ.prod Q)
    rw [show θ = MathFin.ItoIntegralCLM.timeMeasureHorizon H from hestonTimeMeasure_eq_horizon H]
    exact memLp_of_memLp_trim F.predictable_le_prod hfQ
  have hDL := timeProduct_L2_multiplication_L1_limit hv hfQraw hg hVL2
  have hDLim : TendstoInMeasure Q D atTop Dlim :=
    tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero hDL
  have hStochP : Tendsto (fun n => jointItoAssembly H hB₂ (V n)) atTop (𝓝 BP) := by
    have h := (jointItoIntegralCLM H hB₂).continuous.continuousAt.tendsto.comp hVP
    exact h.congr fun n => jointItoIntegralCLM_agrees H hB₂ hB hBclock (V n)
  have hStochQ : Tendsto (fun n => jointItoAssembly H hW₂ (V n)) atTop (𝓝 WQ) := by
    have h := (jointItoIntegralCLM H hW₂).continuous.continuousAt.tendsto.comp hVQ
    exact h.congr fun n => jointItoIntegralCLM_agrees H hW₂ hW hWclock (V n)
  have hPmem : TendstoInMeasure P BS atTop BP := by
    apply TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl
    apply tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hStochP
    exact (memLp_jointItoSimple hB₂ (V n).val).coeFn_toLp
  have hQmem : TendstoInMeasure Q WS atTop WQ := by
    apply TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl
    apply tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hStochQ
    exact (memLp_jointItoSimple hW₂ (V n).val).coeFn_toLp
  have hG₁ : Integrable g R := hg.integrable one_le_two
  have hSimple : ∀ᵐ ω ∂Q, ∀ n, WS n ω = BS n ω - D n ω := by
    filter_upwards [hShift, hG₁.prod_left_ae] with ω hw hω n
    exact jointItoSimple_sub_physical_drift hω hw (V n)
  obtain ⟨a, ha, haP⟩ := hPmem.exists_seq_tendsto_ae
  obtain ⟨b, hb, hbQ⟩ := (hQmem.comp ha.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨c, hc, hcD⟩ := ((hDLim.comp ha.tendsto_atTop).comp hb.tendsto_atTop).exists_seq_tendsto_ae
  filter_upwards [hAC.ae_le haP, hbQ, hcD, hSimple] with ω hP hQ hD hS
  have hP' := (hP.comp hb.tendsto_atTop).comp hc.tendsto_atTop
  have hQ' := hQ.comp hc.tendsto_atTop
  have hLimit := hP'.sub hD
  have hQ'' : Tendsto (fun n => BS (a (b (c n))) ω - D (a (b (c n))) ω) atTop (𝓝 (WQ ω)) :=
    hQ'.congr fun n => hS _
  exact tendsto_nhds_unique hQ'' hLimit

/-- Transport expressed directly through finite Brownian laws. The
completed integrals use the processes frozen at the observation horizon. -/
theorem jointIto_transport_of_BrownianOn_physicalShift
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {B W : ℝ≥0 → Ω → ℝ}
    (hB : MathFinBridge.BrownianOn P F H B) (hW : MathFinBridge.BrownianOn Q F H W)
    (hAC : Q ≪ P) {g f : ℝ≥0 × Ω → ℝ}
    (hShift : ∀ᵐ ω ∂Q, ∀ t ≤ H, W t ω = B t ω - ∫ r, g (r, ω) ∂hestonTimeMeasure t)
    (hg : MemLp g 2 ((hestonTimeMeasure H).prod Q))
    (hf : StronglyMeasurable[F.predictable] f)
    (hfP : MemLp f 2 (jointPredictableMeasure F P H))
    (hfQ : MemLp f 2 (jointPredictableMeasure F Q H)) :
    let hB₂ (t : ℝ≥0) := finiteBrownianOn_memLp hB (min t H) (min_le_right _ _) 2 (by simp)
    let hW₂ (t : ℝ≥0) := finiteBrownianOn_memLp hW (min t H) (min_le_right _ _) 2 (by simp)
    ⇑(jointItoIntegralCLM H hW₂ (hfQ.toLp f)) =ᵐ[Q]
      fun ω => jointItoIntegralCLM H hB₂ (hfP.toLp f) ω -
        ∫ r, f (r, ω) * g (r, ω) ∂hestonTimeMeasure H := by
  dsimp only
  obtain ⟨hB₂, hBm, hBc⟩ := finiteBrownianOn_frozen_martingales hB
  obtain ⟨hW₂, hWm, hWc⟩ := finiteBrownianOn_frozen_martingales hW
  refine jointIto_transport_of_physicalShift hBm hWm hB₂ hW₂ hBc hWc hAC ?_ hg hf hfP hfQ
  filter_upwards [hShift] with ω hw t ht
  simpa only [min_eq_left ht] using hw t ht

/-- The focal drift subtraction and the capped drift restoration compose
at the level of the same completed terminal Itô integral. -/
theorem jointIto_transport_two_physicalShifts
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {R : Measure Ω} [IsProbabilityMeasure R]
    {B W V : ℝ≥0 → Ω → ℝ}
    (hB : MathFinBridge.BrownianOn P F H B) (hW : MathFinBridge.BrownianOn Q F H W)
    (hV : MathFinBridge.BrownianOn R F H V) (hQP : Q ≪ P) (hRQ : R ≪ Q)
    {g h f : ℝ≥0 × Ω → ℝ}
    (hFirst : ∀ᵐ ω ∂Q, ∀ t ≤ H, W t ω = B t ω - ∫ r, g (r, ω) ∂hestonTimeMeasure t)
    (hSecond : ∀ᵐ ω ∂R, ∀ t ≤ H, V t ω = W t ω + ∫ r, h (r, ω) ∂hestonTimeMeasure t)
    (hg : MemLp g 2 ((hestonTimeMeasure H).prod Q))
    (hh : MemLp h 2 ((hestonTimeMeasure H).prod R))
    (hf : StronglyMeasurable[F.predictable] f)
    (hfP : MemLp f 2 (jointPredictableMeasure F P H))
    (hfQ : MemLp f 2 (jointPredictableMeasure F Q H))
    (hfR : MemLp f 2 (jointPredictableMeasure F R H)) :
    let hB₂ (t : ℝ≥0) := finiteBrownianOn_memLp hB (min t H) (min_le_right _ _) 2 (by simp)
    let hV₂ (t : ℝ≥0) := finiteBrownianOn_memLp hV (min t H) (min_le_right _ _) 2 (by simp)
    ⇑(jointItoIntegralCLM H hV₂ (hfR.toLp f)) =ᵐ[R]
      fun ω => jointItoIntegralCLM H hB₂ (hfP.toLp f) ω -
        (∫ r, f (r, ω) * g (r, ω) ∂hestonTimeMeasure H) +
        ∫ r, f (r, ω) * h (r, ω) ∂hestonTimeMeasure H := by
  have hu := jointIto_transport_of_BrownianOn_physicalShift hB hW hQP hFirst hg hf hfP hfQ
  have hTwo : ∀ᵐ ω ∂R, ∀ t ≤ H, V t ω = W t ω - ∫ r, (-h) (r, ω) ∂hestonTimeMeasure t := by
    filter_upwards [hSecond] with ω hw t ht
    change V t ω = W t ω - ∫ r, -h (r, ω) ∂hestonTimeMeasure t
    rw [integral_neg, sub_neg_eq_add, hw t ht]
  have hv := jointIto_transport_of_BrownianOn_physicalShift hW hV hRQ hTwo hh.neg hf hfQ hfR
  filter_upwards [hRQ.ae_eq hu, hv] with ω hw hv
  rw [hv, hw]
  simp_rw [Pi.neg_apply, mul_neg, integral_neg, sub_neg_eq_add]

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.jointItoSimple_sub_physical_drift
#print axioms RoughHeston.GirsanovPort.jointIto_transport_of_physicalShift
#print axioms RoughHeston.GirsanovPort.jointIto_transport_of_BrownianOn_physicalShift
#print axioms RoughHeston.GirsanovPort.jointIto_transport_two_physicalShifts
