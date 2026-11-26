import WeakCompactTestConvergence
import WeakLimitTimeMoments
import EulerObservableMoments

/-! Transfer exact Euler tests with moving observables to the continuous martingale problem. -/

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BoundedContinuousFunction

namespace RoughHeston

/-- Exact tests of an approximating observable imply the limit martingale
property when the observable converges on compact sets and both families
of random variables have uniform second moments under the approximating laws. -/
theorem martingale_of_exact_moving_continuous_tests
    {X E I : Type*} [MetricSpace X] [SecondCountableTopology X] [CompleteSpace X]
    [mX : MeasurableSpace X] [BorelSpace X] [PseudoMetricSpace E]
    [mE : MeasurableSpace E] [BorelSpace E] [Preorder I]
    {Pn : ℕ → ProbabilityMeasure X} {P : ProbabilityMeasure X}
    (hweak : Tendsto Pn atTop (𝓝 P))
    {F : Filtration I mX} {M : I → C(X, ℝ)} {Mn : ℕ → I → C(X, ℝ)}
    (ha : StronglyAdapted F (fun t => M t))
    {past : I → X → E} (hpast : ∀ s, Continuous (past s))
    (hAlg : ∀ s, F s = mE.comap (past s))
    (hConv : ∀ t, Tendsto (fun n => Mn n t) atTop (𝓝 (M t)))
    (hTest : ∀ s t, s ≤ t → ∀ f : E →ᵇ ℝ, ∀ n,
      (∫ x, (Mn n t x - Mn n s x) * f (past s x) ∂(Pn n : Measure X)) = 0)
    (hM : ∀ t, ∃ C : ℝ, 0 ≤ C ∧ ∀ n, MemLp (M t) 2 (Pn n : Measure X) ∧
      (∫ x, M t x ^ 2 ∂(Pn n : Measure X)) ≤ C)
    (hMn : ∀ t, ∃ C : ℝ, 0 ≤ C ∧ ∀ n, MemLp (Mn n t) 2 (Pn n : Measure X) ∧
      (∫ x, Mn n t x ^ 2 ∂(Pn n : Measure X)) ≤ C) :
    Martingale (fun t => M t) F (P : Measure X) := by
  refine martingale_of_weak_limit_of_uniform_time_sq_moments hweak ha
    (fun t => (M t).continuous) hpast hAlg ?_ (fun t => ?_)
  · intro s t hst f
    let w : C(X, ℝ) := ⟨fun x => f (past s x), f.continuous.comp (hpast s)⟩
    let A : C(X, ℝ) := (M t - M s) * w
    let B (n : ℕ) : C(X, ℝ) := (Mn n t - Mn n s) * w
    let D (n : ℕ) : C(X, ℝ) := A - B n
    have hB : Tendsto B atTop (𝓝 A) :=
      tendsto_continuousMap_pointwise_mul ((hConv t).sub (hConv s)) tendsto_const_nhds
    have hD : Tendsto D atTop (𝓝 0) := by
      simpa only [sub_self] using (tendsto_const_nhds (x := A)).sub hB
    obtain ⟨Cs, hCs₀, hCs⟩ := hM s
    obtain ⟨Ct, hCt₀, hCt⟩ := hM t
    obtain ⟨Ds, hDs₀, hDs⟩ := hMn s
    obtain ⟨Dt, hDt₀, hDt⟩ := hMn t
    have hW (n : ℕ) : MemLp w ⊤ (Pn n : Measure X) :=
      memLp_top_of_bound w.continuous.stronglyMeasurable.aestronglyMeasurable ‖f‖
        (Eventually.of_forall fun x => f.norm_coe_le_norm (past s x))
    have hA₂ (n : ℕ) : MemLp A 2 (Pn n : Measure X) :=
      ((hCt n).1.sub (hCs n).1).mul (hW n)
    have hB₂ (n : ℕ) : MemLp (B n) 2 (Pn n : Measure X) :=
      ((hDt n).1.sub (hDs n).1).mul (hW n)
    have hSqBound (n : ℕ) {U V : X → ℝ} (hU : MemLp U 2 (Pn n : Measure X))
        (hV : MemLp V 2 (Pn n : Measure X)) :
        (∫ x, ((U x - V x) * w x)^2 ∂(Pn n : Measure X)) ≤
          (‖f‖^2) * (2 * ((∫ x, U x^2 ∂(Pn n : Measure X)) + ∫ x, V x^2 ∂(Pn n : Measure X))) := by
      have hUV : MemLp (fun x => (U x - V x) * w x) 2 (Pn n : Measure X) :=
        (hU.sub hV).mul (hW n)
      have hDiff : Integrable (fun x => (U x - V x)^2) (Pn n : Measure X) :=
        (hU.sub hV).integrable_sq
      calc
        _ ≤ ∫ x, ‖f‖^2 * (U x - V x)^2 ∂(Pn n : Measure X) := by
          apply integral_mono hUV.integrable_sq (hDiff.const_mul _)
          intro x
          have hWb : |w x| ≤ ‖f‖ := f.norm_coe_le_norm (past s x)
          have hWsq : (w x)^2 ≤ ‖f‖^2 := by
            rw [← sq_abs (w x)]
            exact pow_le_pow_left₀ (abs_nonneg _) hWb 2
          change ((U x - V x) * w x)^2 ≤ ‖f‖^2 * (U x - V x)^2
          rw [mul_pow, mul_comm ((U x - V x)^2)]
          exact mul_le_mul_of_nonneg_right hWsq (sq_nonneg _)
        _ ≤ _ := by
          rw [integral_const_mul]
          exact mul_le_mul_of_nonneg_left (integral_sq_sub_le hU hV) (sq_nonneg _)
    let C := 2 * (‖f‖^2 * (2 * (Ct + Cs)) + ‖f‖^2 * (2 * (Dt + Ds)))
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hD₂ (n : ℕ) : MemLp (D n) 2 (Pn n : Measure X) := (hA₂ n).sub (hB₂ n)
    have hD₂b (n : ℕ) : (∫ x, D n x ^ 2 ∂(Pn n : Measure X)) ≤ C := by
      refine (integral_sq_sub_le (hA₂ n) (hB₂ n)).trans ?_
      have ha := hSqBound n (hCt n).1 (hCs n).1
      have hb := hSqBound n (hDt n).1 (hDs n).1
      have ha' := ha.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (add_le_add (hCt n).2 (hCs n).2) (show (0 : ℝ) ≤ 2 by norm_num))
        (sq_nonneg _))
      have hb' := hb.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (add_le_add (hDt n).2 (hDs n).2) (show (0 : ℝ) ≤ 2 by norm_num))
        (sq_nonneg _))
      exact mul_le_mul_of_nonneg_left (add_le_add ha' hb') (by norm_num)
    have hDsmall :
        Tendsto (fun n => ∫ x, ‖D n x‖ ∂(Pn n : Measure X)) atTop (𝓝 0) := by
      refine tendsto_integral_norm_zero_of_uniform_on_compacts_of_weak hweak hC hD₂ hD₂b
        (fun K hK ε hε => ?_)
      have h := Metric.tendstoUniformlyOn_iff.mp
        (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hD K hK) ε hε
      filter_upwards [h] with n hn x hx
      simpa only [ContinuousMap.zero_apply, dist_zero_left] using hn x hx
    have hInt (n : ℕ) : (∫ x, D n x ∂(Pn n : Measure X)) = ∫ x, A x ∂(Pn n : Measure X) := by
      change (∫ x, A x - B n x ∂(Pn n : Measure X)) = _
      rw [integral_sub ((hA₂ n).integrable one_le_two) ((hB₂ n).integrable one_le_two),
        show (∫ x, B n x ∂(Pn n : Measure X)) = 0 from hTest s t hst f n, sub_zero]
    change Tendsto (fun n => ∫ x, A x ∂(Pn n : Measure X)) atTop (𝓝 0)
    apply tendsto_iff_norm_sub_tendsto_zero.2
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => by
      rw [sub_zero, ← hInt n]
      exact norm_integral_le_integral_norm _) hDsmall
  · obtain ⟨C, _, h⟩ := hM t
    exact ⟨C, h⟩

#print axioms RoughHeston.martingale_of_exact_moving_continuous_tests

end RoughHeston
