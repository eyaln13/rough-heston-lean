import FractionalKernelIncrements
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace RoughHeston

/-- The positive Laplace density for the fractional Heston kernel. -/
noncomputable def fractionalLaplaceDensity (α x : ℝ) : ℝ :=
  x ^ (-α) / (Real.Gamma α * Real.Gamma (1 - α))

private theorem fractionalLaplaceDensity_pos {α x : ℝ} (hα : 0 < α) (hα' : α < 1)
    (hx : 0 < x) : 0 < fractionalLaplaceDensity α x :=
  div_pos (Real.rpow_pos_of_pos hx _)
    (mul_pos (Real.Gamma_pos_of_pos hα) (Real.Gamma_pos_of_pos (sub_pos.mpr hα')))

private theorem fractionalLaplaceDensity_measurable (α : ℝ) :
    Measurable (fractionalLaplaceDensity α) :=
  (measurable_id.pow_const _).div_const _

private theorem fractionalLaplaceDensity_integrableOn_Ioc {α b : ℝ} (hα' : α < 1) :
    IntegrableOn (fractionalLaplaceDensity α) (Ioc 0 b) := by
  have hp : -1 < -α := by linarith
  unfold fractionalLaplaceDensity
  simpa only [div_eq_mul_inv] using
    ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := b) hp).mul_const
      (Real.Gamma α * Real.Gamma (1 - α))⁻¹).1

private theorem fractionalLaplaceIntegrable {α t : ℝ} (hα' : α < 1) (ht : 0 < t) :
    IntegrableOn (fun x => fractionalLaplaceDensity α x * Real.exp (- (t * x))) (Ioi 0) := by
  have hp : -1 < -α := by linarith
  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) hp zero_lt_one ht
  have he : (fun x : ℝ => fractionalLaplaceDensity α x * Real.exp (-(t * x))) =
      fun x : ℝ => x ^ (-α) * Real.exp (-t * x ^ (1 : ℝ)) *
        (Real.Gamma α * Real.Gamma (1 - α))⁻¹ := by
    funext x
    simp only [fractionalLaplaceDensity, Real.rpow_one, div_eq_mul_inv, neg_mul]
    ring
  rw [he]
  exact hi.mul_const _

/-- The fractional kernel is the Laplace transform of its positive mixing density. -/
theorem hestonKernel_eq_laplace_density_integral {α t : ℝ}
    (hα : 0 < α) (hα' : α < 1) (ht : 0 < t) :
    hestonKernel α t =
      ∫ x in Ioi (0 : ℝ), fractionalLaplaceDensity α x * Real.exp (- (t * x)) := by
  rw [hestonKernel_laplace_integral hα hα' ht]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  change Real.exp (-(x * t)) * (x ^ (-α) / (Real.Gamma α * Real.Gamma (1 - α))) =
    fractionalLaplaceDensity α x * Real.exp (-(t * x))
  rw [fractionalLaplaceDensity, mul_comm x t, mul_comm]

/-- Right endpoints of positive bins of length `1/(n+1)`. -/
noncomputable def fractionalApproximationRate (n j : ℕ) : ℝ :=
  (j : ℝ) / ((n : ℝ) + 1)

/-- Bin indices up to the truncation point `n+1`. -/
def fractionalApproximationIndices (n : ℕ) : Finset ℕ := Finset.Icc 1 ((n + 1) ^ 2)

private noncomputable def fractionalApproximationBin (n j : ℕ) : Set ℝ :=
  Ioc (fractionalApproximationRate n (j - 1)) (fractionalApproximationRate n j)

/-- The mass of the positive Laplace density in one bin. -/
noncomputable def fractionalApproximationWeight (α : ℝ) (n j : ℕ) : ℝ :=
  ∫ x in fractionalApproximationBin n j, fractionalLaplaceDensity α x

/-- A finite-exponential approximation to the fractional Heston kernel. -/
noncomputable def fractionalExponentialApproximation (α : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ fractionalApproximationIndices n,
    fractionalApproximationWeight α n j * Real.exp (- (t * fractionalApproximationRate n j))

private theorem fractionalApproximationRate_nonneg (n j : ℕ) :
    0 ≤ fractionalApproximationRate n j := by unfold fractionalApproximationRate; positivity

theorem fractionalApproximationRate_pos {n j : ℕ} (hj : j ∈ fractionalApproximationIndices n) :
    0 < fractionalApproximationRate n j := by
  have hj' : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  unfold fractionalApproximationRate
  positivity

private theorem fractionalApproximationBin_subset_Ioi (n j : ℕ) :
    fractionalApproximationBin n j ⊆ Ioi 0 := by
  intro x hx
  exact (fractionalApproximationRate_nonneg n (j - 1)).trans_lt hx.1

private theorem fractionalDensity_integrableOn_approximationBin {α : ℝ} (hα' : α < 1) (n j : ℕ) :
    IntegrableOn (fractionalLaplaceDensity α) (fractionalApproximationBin n j) :=
  (fractionalLaplaceDensity_integrableOn_Ioc hα').mono_set (Ioc_subset_Ioc
    (fractionalApproximationRate_nonneg n (j - 1)) le_rfl)

theorem fractionalApproximationWeight_pos {α : ℝ} (hα : 0 < α) (hα' : α < 1)
    {n j : ℕ} (hj : j ∈ fractionalApproximationIndices n) :
    0 < fractionalApproximationWeight α n j := by
  have hbin : 0 < volume (fractionalApproximationBin n j) := by
    rw [fractionalApproximationBin, Real.volume_Ioc, ENNReal.ofReal_pos]
    apply sub_pos.mpr
    apply div_lt_div_of_pos_right _ (by positivity)
    have hj' : 0 < j := (Finset.mem_Icc.mp hj).1
    exact_mod_cast Nat.sub_lt hj' (by decide : 0 < 1)
  unfold fractionalApproximationWeight
  refine (setIntegral_pos_iff_support_of_nonneg_ae ?_
    (fractionalDensity_integrableOn_approximationBin hα' n j)).2 ?_
  · filter_upwards [ae_restrict_mem (by exact measurableSet_Ioc :
      MeasurableSet (fractionalApproximationBin n j))] with x hx
    exact (fractionalLaplaceDensity_pos hα hα' (fractionalApproximationBin_subset_Ioi n j hx)).le
  · apply hbin.trans_le (measure_mono ?_)
    intro x hx
    exact ⟨(fractionalLaplaceDensity_pos hα hα' (fractionalApproximationBin_subset_Ioi n j hx)).ne', hx⟩

theorem fractionalExponentialApproximation_properties {α : ℝ} (hα : 0 < α) (hα' : α < 1) (n : ℕ) :
    Continuous (fractionalExponentialApproximation α n) ∧
      (∀ t, 0 ≤ fractionalExponentialApproximation α n t) ∧
      Antitone (fractionalExponentialApproximation α n) := by
  have h := positive_exponential_mixture_properties (fractionalApproximationIndices n)
    (fractionalApproximationWeight α n) (fractionalApproximationRate n)
    (fun _ hj => (fractionalApproximationWeight_pos hα hα' hj).le)
    (fun j _ => fractionalApproximationRate_nonneg n j)
  unfold fractionalExponentialApproximation
  simpa only [mul_comm (fractionalApproximationRate _ _) _] using h

private noncomputable def fractionalApproximationIndex (n : ℕ) (x : ℝ) : ℕ :=
  Nat.ceil (x * ((n : ℝ) + 1))

private theorem fractionalApproximationIndex_mem {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hxtop : x ≤ (n : ℝ) + 1) :
    fractionalApproximationIndex n x ∈ fractionalApproximationIndices n := by
  rw [fractionalApproximationIndices, Finset.mem_Icc, fractionalApproximationIndex]
  refine ⟨Nat.one_le_ceil_iff.mpr (by positivity), Nat.ceil_le.mpr ?_⟩
  push_cast
  nlinarith

private theorem fractionalApproximationBin_iff {n j : ℕ} {x : ℝ} (hj : 0 < j) :
    x ∈ fractionalApproximationBin n j ↔ fractionalApproximationIndex n x = j := by
  rw [fractionalApproximationIndex, Nat.ceil_eq_iff hj.ne', fractionalApproximationBin,
    mem_Ioc, fractionalApproximationRate, fractionalApproximationRate]
  rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1),
    le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]

private theorem fractionalApproximationBin_le_cutoff {n j : ℕ} {x : ℝ}
    (hj : j ∈ fractionalApproximationIndices n) (hx : x ∈ fractionalApproximationBin n j) :
    x ≤ (n : ℝ) + 1 := by
  apply hx.2.trans
  rw [fractionalApproximationRate, div_le_iff₀ (by positivity)]
  have hj' : (j : ℝ) ≤ (((n + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hj).2
  push_cast at hj'
  nlinarith

private noncomputable def fractionalApproximationIntegrand (α : ℝ) (n : ℕ) (t x : ℝ) : ℝ :=
  (Iic ((n : ℝ) + 1)).indicator
    (fun x => fractionalLaplaceDensity α x *
      Real.exp (- (t * fractionalApproximationRate n (fractionalApproximationIndex n x)))) x

private theorem fractionalApproximationIntegrand_measurable (α : ℝ) (n : ℕ) (t : ℝ) :
    Measurable (fractionalApproximationIntegrand α n t) := by
  unfold fractionalApproximationIntegrand
  apply Measurable.indicator _ measurableSet_Iic
  apply (fractionalLaplaceDensity_measurable α).mul
  apply Real.measurable_exp.comp
  apply (measurable_const.mul _).neg
  have hn : Measurable (fractionalApproximationIndex n) :=
    Nat.measurable_ceil.comp (measurable_id.mul_const _)
  exact (measurable_of_countable (fractionalApproximationRate n)).comp hn

theorem fractionalExponentialApproximation_eq_integral {α : ℝ} (hα' : α < 1)
    (n : ℕ) (t : ℝ) :
    fractionalExponentialApproximation α n t =
      ∫ x in Ioi (0 : ℝ), fractionalApproximationIntegrand α n t x := by
  classical
  let F : ℕ → ℝ → ℝ := fun j => (fractionalApproximationBin n j).indicator
    (fun x => fractionalLaplaceDensity α x * Real.exp (- (t * fractionalApproximationRate n j)))
  have hFi (j : ℕ) : Integrable (F j) (volume.restrict (Ioi 0)) := by
    have hb : MeasurableSet (fractionalApproximationBin n j) := measurableSet_Ioc
    dsimp only [F]
    rw [integrable_indicator_iff hb, IntegrableOn, Measure.restrict_restrict hb,
      inter_eq_left.mpr (fractionalApproximationBin_subset_Ioi n j)]
    exact (fractionalDensity_integrableOn_approximationBin hα' n j).mul_const _
  have hF (j : ℕ) : (∫ x in Ioi (0 : ℝ), F j x) =
      fractionalApproximationWeight α n j * Real.exp (- (t * fractionalApproximationRate n j)) := by
    have hb : MeasurableSet (fractionalApproximationBin n j) := measurableSet_Ioc
    dsimp only [F]
    rw [integral_indicator hb, Measure.restrict_restrict hb,
      inter_eq_left.mpr (fractionalApproximationBin_subset_Ioi n j), integral_mul_const]
    rfl
  unfold fractionalExponentialApproximation
  simp_rw [← hF]
  rw [← integral_finsetSum _ (fun j _ => hFi j)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change (∑ i ∈ fractionalApproximationIndices n, F i x) = _
  by_cases hxtop : x ≤ (n : ℝ) + 1
  · let j := fractionalApproximationIndex n x
    have hj : j ∈ fractionalApproximationIndices n := fractionalApproximationIndex_mem hx hxtop
    rw [Finset.sum_eq_single_of_mem j hj]
    · rw [fractionalApproximationIntegrand, indicator_of_mem (show x ∈ Iic _ from hxtop)]
      have hxb : x ∈ fractionalApproximationBin n j :=
        (fractionalApproximationBin_iff (Finset.mem_Icc.mp hj).1).mpr rfl
      dsimp only [F]
      rw [indicator_of_mem hxb]
    · intro i hi hij
      have hxb : x ∉ fractionalApproximationBin n i := by
        rw [fractionalApproximationBin_iff (Finset.mem_Icc.mp hi).1]
        exact Ne.symm hij
      dsimp only [F]
      rw [indicator_of_notMem hxb]
  · rw [fractionalApproximationIntegrand, indicator_of_notMem (show x ∉ Iic _ from hxtop)]
    apply Finset.sum_eq_zero
    intro j hj
    have hxb : x ∉ fractionalApproximationBin n j :=
      fun hb => hxtop (fractionalApproximationBin_le_cutoff hj hb)
    dsimp only [F]
    rw [indicator_of_notMem hxb]

private theorem le_fractionalApproximationRoundedRate (n : ℕ) (x : ℝ) :
    x ≤ fractionalApproximationRate n (fractionalApproximationIndex n x) := by
  unfold fractionalApproximationRate fractionalApproximationIndex
  exact (le_div_iff₀ (by positivity)).mpr (Nat.le_ceil _)

private theorem tendsto_fractionalApproximationRoundedRate {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n => fractionalApproximationRate n (fractionalApproximationIndex n x))
      atTop (𝓝 x) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) _ tendsto_one_div_add_atTop_nhds_zero_nat
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (le_fractionalApproximationRoundedRate n x))]
  unfold fractionalApproximationIndex fractionalApproximationRate
  have hm : 0 < (n : ℝ) + 1 := by positivity
  have hc := Nat.ceil_lt_add_one (mul_nonneg hx hm.le)
  apply le_of_lt
  calc
    _ = ((⌈x * ((n : ℝ) + 1)⌉₊ : ℝ) - x * ((n : ℝ) + 1)) / ((n : ℝ) + 1) := by
      field_simp
    _ < 1 / ((n : ℝ) + 1) := (div_lt_div_iff_of_pos_right hm).mpr (by linarith)

private theorem fractionalApproximationIntegrand_bound {α : ℝ} (hα : 0 < α) (hα' : α < 1)
    {t x : ℝ} (ht : 0 < t) (hx : 0 < x) (n : ℕ) :
    0 ≤ fractionalApproximationIntegrand α n t x ∧
    fractionalApproximationIntegrand α n t x ≤ fractionalLaplaceDensity α x * Real.exp (-(t * x)) := by
  have hD := (fractionalLaplaceDensity_pos hα hα' hx).le
  unfold fractionalApproximationIntegrand
  by_cases hxmem : x ∈ Iic ((n : ℝ) + 1)
  · rw [indicator_of_mem hxmem]
    refine ⟨mul_nonneg hD (Real.exp_pos _).le, mul_le_mul_of_nonneg_left ?_ hD⟩
    exact Real.exp_le_exp.mpr
      (neg_le_neg (mul_le_mul_of_nonneg_left (le_fractionalApproximationRoundedRate n x) ht.le))
  · rw [indicator_of_notMem hxmem]
    exact ⟨le_rfl, mul_nonneg hD (Real.exp_pos _).le⟩

private theorem fractionalApproximationIntegrand_tendsto (α : ℝ) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n => fractionalApproximationIntegrand α n t x)
      atTop (𝓝 (fractionalLaplaceDensity α x * Real.exp (-(t * x)))) := by
  have hc : Tendsto (fun _ : ℕ => t) atTop (𝓝 t) := tendsto_const_nhds
  have h := tendsto_const_nhds.mul (a := fractionalLaplaceDensity α x)
    ((hc.mul (tendsto_fractionalApproximationRoundedRate hx.le)).neg.rexp)
  apply h.congr'
  obtain ⟨N, hN⟩ := exists_nat_ge x
  filter_upwards [eventually_ge_atTop N] with n hn
  have hxn : x ≤ (n : ℝ) + 1 := hN.trans ((Nat.cast_le.mpr hn).trans (by linarith))
  change _ = fractionalApproximationIntegrand α n t x
  rw [fractionalApproximationIntegrand, indicator_of_mem (show x ∈ Iic _ from hxn)]

/-- Rounding rates upward and truncating the density both decrease the
Laplace integral at every positive time. -/
theorem fractionalExponentialApproximation_le_hestonKernel {α t : ℝ}
    (hα : 0 < α) (hα' : α < 1) (ht : 0 < t) (n : ℕ) :
    fractionalExponentialApproximation α n t ≤ hestonKernel α t := by
  rw [fractionalExponentialApproximation_eq_integral hα', hestonKernel_eq_laplace_density_integral hα hα' ht]
  have hD := fractionalLaplaceIntegrable hα' ht
  have hb : ∀ᵐ x ∂volume.restrict (Ioi 0),
      ‖fractionalApproximationIntegrand α n t x‖ ≤ fractionalLaplaceDensity α x * Real.exp (-(t * x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    obtain ⟨h₁, h₂⟩ := fractionalApproximationIntegrand_bound hα hα' ht hx n
    simpa only [Real.norm_eq_abs, abs_of_nonneg h₁] using h₂
  have hI : Integrable (fractionalApproximationIntegrand α n t) (volume.restrict (Ioi 0)) :=
    hD.mono' (fractionalApproximationIntegrand_measurable α n t).aestronglyMeasurable hb
  refine integral_mono_ae hI hD ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (fractionalApproximationIntegrand_bound hα hα' ht hx n).2

/-- The positive mixtures converge pointwise to the fractional Heston kernel
at each strictly positive time. -/
theorem fractionalExponentialApproximation_tendsto {α t : ℝ}
    (hα : 0 < α) (hα' : α < 1) (ht : 0 < t) :
    Tendsto (fun n => fractionalExponentialApproximation α n t)
      atTop (𝓝 (hestonKernel α t)) := by
  simp_rw [fractionalExponentialApproximation_eq_integral hα',
    hestonKernel_eq_laplace_density_integral hα hα' ht]
  refine tendsto_integral_of_dominated_convergence
    (fun x => fractionalLaplaceDensity α x * Real.exp (-(t * x)))
    (fun n => (fractionalApproximationIntegrand_measurable α n t).aestronglyMeasurable)
    (fractionalLaplaceIntegrable hα' ht) ?_ ?_
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    obtain ⟨h₁, h₂⟩ := fractionalApproximationIntegrand_bound hα hα' ht hx n
    simpa only [Real.norm_eq_abs, abs_of_nonneg h₁] using h₂
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact fractionalApproximationIntegrand_tendsto α t hx

/-- The same positive approximants converge in squared integral over any
finite positive-time horizon when the fractional kernel is square integrable. -/
theorem fractionalExponentialApproximation_tendsto_integral_sq {α : ℝ}
    (hα : 1 / 2 < α) (hα' : α < 1) (T : NNReal) :
    Tendsto (fun n => ∫ t in Ioc (0 : ℝ) (T : ℝ),
      (fractionalExponentialApproximation α n t - hestonKernel α t) ^ 2) atTop (𝓝 0) := by
  have hαpos : 0 < α := by linarith
  have hb : Integrable (fun t => hestonKernel α t ^ 2) (volume.restrict (Ioc 0 (T : ℝ))) :=
    (hestonKernel_memLp_two hα T).integrable_sq
  have hm n : Measurable (fun t => (fractionalExponentialApproximation α n t - hestonKernel α t) ^ 2) :=
    (((fractionalExponentialApproximation_properties hαpos hα' n).1.measurable).sub
      (hestonKernel_measurable α)).pow_const 2
  have h := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ))
    (fun t => hestonKernel α t ^ 2) (fun n => (hm n).aestronglyMeasurable) hb ?_ ?_
  · simpa only [integral_zero] using h
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hle := fractionalExponentialApproximation_le_hestonKernel hαpos hα' ht.1 n
    have hn := (fractionalExponentialApproximation_properties hαpos hα' n).2.1 t
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact sq_le_sq' (by linarith) (by linarith)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using
      ((fractionalExponentialApproximation_tendsto hαpos hα' ht.1).sub_const
        (hestonKernel α t)).pow 2

#print axioms fractionalApproximationWeight_pos
#print axioms fractionalExponentialApproximation_properties
#print axioms fractionalExponentialApproximation_le_hestonKernel
#print axioms fractionalExponentialApproximation_tendsto
#print axioms fractionalExponentialApproximation_tendsto_integral_sq

end RoughHeston
