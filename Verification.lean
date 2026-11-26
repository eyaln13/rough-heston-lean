import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Deterministic fractional estimates and measure-theoretic reductions from
"Pathwise Nonuniqueness in the Rough Heston Model".

These statements do not formalize the stochastic Volterra equation.
In particular, the conditional boundary estimate, change of measure, and
construction and convergence of the coupled stochastic processes remain
in the manuscript.
-/

open Set Filter
open scoped BigOperators Topology

namespace RoughHeston

noncomputable def caputoCoefficient (α p : ℝ) : ℝ :=
  p * Real.Gamma (α - p) / Real.Gamma (1 - p)

noncomputable def boundaryCoefficient (α : ℝ) : ℝ :=
  2 * (2 * α - 1) * Real.Gamma (1 - α) / Real.Gamma (2 - 2 * α)

theorem boundaryCoefficient_pos {α : ℝ} (hα₀ : 1 / 2 < α) (hα₁ : α < 1) :
    0 < boundaryCoefficient α := by
  unfold boundaryCoefficient
  have hβ : 0 < 2 * α - 1 := by linarith
  have hg₁ : 0 < Real.Gamma (1 - α) := Real.Gamma_pos_of_pos (by linarith)
  have hg₂ : 0 < Real.Gamma (2 - 2 * α) := Real.Gamma_pos_of_pos (by linarith)
  positivity

theorem caputo_at_critical (α : ℝ) :
    2 * caputoCoefficient α (2 * α - 1) = boundaryCoefficient α := by
  unfold caputoCoefficient boundaryCoefficient
  rw [show α - (2 * α - 1) = 1 - α by ring,
      show 1 - (2 * α - 1) = 2 - 2 * α by ring]
  ring

private theorem gamma_continuous_pos {x : ℝ} (hx : 0 < x) :
    ContinuousAt Real.Gamma x :=
  (Real.differentiableAt_Gamma (fun n => by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith)).continuousAt

/-- The choice of exponent in the fractional supersolution is possible. -/
theorem comparison_exponent {α : ℝ} (hα₀ : 1 / 2 < α) (hα₁ : α < 1) :
    ∃ p : ℝ, 2 * α - 1 < p ∧ p < α ∧ caputoCoefficient α p < boundaryCoefficient α := by
  let β : ℝ := 2 * α - 1
  have hArg₁ : 0 < α - β := by dsimp [β]; linarith
  have hArg₂ : 0 < 1 - β := by dsimp [β]; linarith
  have h₁ : ContinuousAt (fun p : ℝ => Real.Gamma (α - p)) β :=
    (gamma_continuous_pos hArg₁).comp (continuousAt_const.sub continuousAt_id)
  have h₂ : ContinuousAt (fun p : ℝ => Real.Gamma (1 - p)) β :=
    (gamma_continuous_pos hArg₂).comp (continuousAt_const.sub continuousAt_id)
  have hc : ContinuousAt (caputoCoefficient α) β :=
    (continuousAt_id.mul h₁).div h₂ (Real.Gamma_pos_of_pos hArg₂).ne'
  have hlt : caputoCoefficient α β < boundaryCoefficient α := by
    have hb := boundaryCoefficient_pos hα₀ hα₁
    have he : 2 * caputoCoefficient α β = boundaryCoefficient α := caputo_at_critical α
    linarith
  have hn : {p : ℝ | caputoCoefficient α p < boundaryCoefficient α} ∈ 𝓝 β :=
    hc.preimage_mem_nhds (Iio_mem_nhds hlt)
  obtain ⟨l, u, hmem, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hn
  obtain ⟨hl, hu⟩ := hmem
  have hβα : β < α := by dsimp [β]; linarith
  obtain ⟨p, hpβ, hpmin⟩ := exists_between (lt_min hu hβα)
  exact ⟨p, hpβ, lt_of_lt_of_le hpmin (min_le_right _ _),
    hsub ⟨lt_trans hl hpβ, lt_of_lt_of_le hpmin (min_le_left _ _)⟩⟩

/-- The weighted integral used to bound the stopped change-of-measure cost. -/
theorem occupation_cost_integral {r η γ : ℝ} (hr : 0 < r) (hgap : 3 * γ < η) :
    (∫ s in (0 : ℝ)..r, r ^ (3 * γ) * s ^ (η - 3 * γ - 1)) =
      r ^ η / (η - 3 * γ) := by
  have hpos : 0 < η - 3 * γ := sub_pos.mpr hgap
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)),
    show η - 3 * γ - 1 + 1 = η - 3 * γ by ring,
    Real.zero_rpow hpos.ne', sub_zero, ← mul_div_assoc,
    ← Real.rpow_add hr, show 3 * γ + (η - 3 * γ) = η by ring]

/-- The normalized sum has unit instantaneous variance where either input is active. -/
theorem normalized_sum_variance {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hactive : 0 < Real.sqrt x + Real.sqrt y) :
    (x + y + 2 * (Real.sqrt x * Real.sqrt y)) /
      (Real.sqrt x + Real.sqrt y)^2 = 1 := by
  rw [div_eq_iff (pow_ne_zero 2 hactive.ne'), one_mul]
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy]

/-- The covariation with one component after normalizing the sum. -/
theorem normalized_sum_covariation {x y : ℝ} (hx : 0 ≤ x)
    (hactive : 0 < Real.sqrt x + Real.sqrt y) :
    (x + Real.sqrt x * Real.sqrt y) / (Real.sqrt x + Real.sqrt y) = Real.sqrt x := by
  rw [div_eq_iff hactive.ne']
  nlinarith [Real.sq_sqrt hx]

/-- The squared tilt on the competing driver is dominated by the cluster cost. -/
theorem tilt_cost_bound {σ u x z : ℝ} (hu : 0 ≤ u) (hux : u ≤ x)
    (hx : 0 < x) (hz : 0 < z) :
    (σ * u / (z * Real.sqrt x))^2 ≤ σ^2 * u / z^2 := by
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hx.le]
  apply (div_le_div_iff₀ (mul_pos (sq_pos_of_pos hz) hx) (sq_pos_of_pos hz)).mpr
  have h₁ : u ^ 2 ≤ u * x := by nlinarith [mul_nonneg hu (sub_nonneg.mpr hux)]
  have h₂ : 0 ≤ σ^2 * z^2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h₁ h₂]

/-- Transfer the second moment inequality to a uniform positive probability. -/
theorem count_lower_bound {a b mean second prob : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hmean : a ≤ mean) (hsecond : second ≤ b) (hprob : 0 ≤ prob)
    (hcauchy : mean ^ 2 ≤ second * prob) :
    0 < a ^ 2 / b ∧ a ^ 2 / b ≤ prob := by
  refine ⟨by positivity, (div_le_iff₀ hb).mpr ?_⟩
  calc
    a ^ 2 ≤ mean ^ 2 := by nlinarith
    _ ≤ second * prob := hcauchy
    _ ≤ prob * b := by simpa [mul_comm] using mul_le_mul_of_nonneg_right hsecond hprob

/-- The shared Brownian coordinate and its orthogonal complement reproduce the
identity covariance for the vector of cluster noises. -/
theorem cluster_projection {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → ℝ)
    (hnorm : ∑ k, (u k)^2 = 1) (i j : ι) :
    u i * u j +
      (∑ k, ((if i = k then (1 : ℝ) else 0) - u i * u k) *
        ((if j = k then (1 : ℝ) else 0) - u j * u k)) =
      (if i = j then 1 else 0) := by
  let δ (i k : ι) : ℝ := if i = k then 1 else 0
  change u i * u j + (∑ k, (δ i k - u i * u k) * (δ j k - u j * u k)) = δ i j
  have selector (k : ι) (f : ι → ℝ) :
      (∑ l, δ k l * f l) = f k := by
    rw [Finset.sum_eq_single k]
    · simp [δ]
    · intro l _ h
      simp [δ, Ne.symm h]
    · simp
  have hsym : δ j i = δ i j := by simp [δ, eq_comm]
  have expand (k : ι) :
      (δ i k - u i * u k) * (δ j k - u j * u k) =
        δ i k * δ j k - δ i k * (u j * u k) -
        δ j k * (u i * u k) + (u i * u j) * (u k)^2 := by
    ring
  simp_rw [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [selector, selector, selector, ← Finset.mul_sum, hnorm, hsym]
  ring

/-- The beta integral at the exponents of the two fractional kernels. -/
theorem fractional_beta_integral {α t : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) (ht : 0 < t) :
    (∫ s in (0 : ℝ)..t, (s : ℂ) ^ (-(α : ℂ)) *
      ((t : ℂ) - (s : ℂ)) ^ ((α : ℂ) - 1)) =
    Complex.Gamma (1 - (α : ℂ)) * Complex.Gamma (α : ℂ) := by
  have hleft : 0 < (1 - (α : ℂ)).re := by simp [Complex.sub_re, hα₁]
  have hright : 0 < (α : ℂ).re := hα₀
  have hs : (1 - (α : ℂ)) + (α : ℂ) = 1 := by ring
  have hb := Complex.betaIntegral_scaled (1 - (α : ℂ)) (α : ℂ) ht
  rw [hs, sub_self, Complex.cpow_zero, one_mul] at hb
  have hpow : (1 - (α : ℂ)) - 1 = -(α : ℂ) := by ring
  rw [hpow] at hb
  have hg := Complex.Gamma_mul_Gamma_eq_betaIntegral hleft hright
  rw [hs, Complex.Gamma_one, one_mul] at hg
  exact hb.trans hg.symm

/-- The fractional kernels convolve to the constant one. -/
theorem fractional_kernel_inverse {α t : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) (ht : 0 < t) :
    (∫ s in (0 : ℝ)..t, (s ^ (-α) / Real.Gamma (1 - α)) *
      ((t - s) ^ (α - 1) / Real.Gamma α)) = 1 := by
  have hb : (∫ s in (0 : ℝ)..t, s ^ (-α) * (t - s) ^ (α - 1)) =
      Real.Gamma (1 - α) * Real.Gamma α := by
    apply Complex.ofReal_injective
    rw [← intervalIntegral.integral_ofReal]
    have hEq : (∫ s in (0 : ℝ)..t, ((s ^ (-α) * (t - s) ^ (α - 1) : ℝ) : ℂ)) =
        (∫ s in (0 : ℝ)..t, (s : ℂ) ^ (-(α : ℂ)) *
          ((t : ℂ) - (s : ℂ)) ^ ((α : ℂ) - 1)) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht.le] at hs
      push_cast
      rw [Complex.ofReal_cpow hs.1, Complex.ofReal_cpow (sub_nonneg.mpr hs.2)]
      push_cast
      rfl
    rw [hEq, fractional_beta_integral hα₀ hα₁ ht, Complex.ofReal_mul]
    simp only [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.Gamma_ofReal]
  have hΓ₁ : 0 < Real.Gamma (1 - α) := Real.Gamma_pos_of_pos (by linarith)
  have hΓ₂ : 0 < Real.Gamma α := Real.Gamma_pos_of_pos hα₀
  simp_rw [div_mul_div_comm, div_eq_mul_inv]
  rw [intervalIntegral.integral_mul_const, hb, mul_inv_cancel₀ (mul_pos hΓ₁ hΓ₂).ne']

open MeasureTheory

/-- A uniform separation probability passes to a weak limit.
For the application, the continuous statistic is the uniform distance
between the two paths. -/
theorem separation_of_weak_limit {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [HasOuterApproxClosed Ω] [OpensMeasurableSpace Ω]
    {μ : FiniteMeasure Ω} {μn : ℕ → FiniteMeasure Ω}
    (hμ : Tendsto μn atTop (𝓝 μ)) {distance : Ω → ℝ} (hd : Continuous distance)
    {ℓ : ℝ} {p : ENNReal}
    (hp : ∀ n, p ≤ (μn n : Measure Ω) {x | ℓ ≤ distance x}) :
    p ≤ (μ : Measure Ω) {x | ℓ ≤ distance x} := by
  have hclosed : IsClosed {x | ℓ ≤ distance x} := isClosed_le continuous_const hd
  apply le_trans ?_ (FiniteMeasure.limsup_measure_closed_le_of_tendsto hμ hclosed)
  refine le_limsup_of_le (by isBoundedDefault) ?_
  intro b h
  obtain ⟨n, hn⟩ := h.exists
  exact le_trans (hp n) hn

/-- Formula used at a contact point. Setting `initial = 0` gives the
Riemann–Liouville expression, and `initial = g 0` gives the Caputo expression.
The assertions below concern this integral formula at times where it is integrable. -/
noncomputable def fractionalMemory (α initial : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  (g t - initial) * (t ^ (-α) / Real.Gamma (1 - α)) +
    ∫ u in (0 : ℝ)..t,
      (α * u ^ (-α - 1) / Real.Gamma (1 - α)) * (g t - g (t - u))

/-- A strictly positive past forces a strictly negative memory derivative
at the first zero. -/
theorem fractional_memory_negative_at_contact {α initial t : ℝ} {g : ℝ → ℝ}
    (hα : 0 < α) (hα₁ : α < 1) (hi : 0 ≤ initial) (ht : 0 < t)
    (hzero : g t = 0) (hpast : ∀ s ∈ Ioo 0 t, 0 < g s)
    (hint : IntervalIntegrable
      (fun u => (α * u ^ (-α - 1) / Real.Gamma (1 - α)) * (g t - g (t - u)))
      volume 0 t) :
    fractionalMemory α initial g t < 0 := by
  have hΓ : 0 < Real.Gamma (1 - α) := Real.Gamma_pos_of_pos (by linarith)
  have hpos : 0 < ∫ u in (0 : ℝ)..t,
      -((α * u ^ (-α - 1) / Real.Gamma (1 - α)) * (g t - g (t - u))) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on hint.neg _ ht
    intro u hu
    have he : 0 < α * u ^ (-α - 1) / Real.Gamma (1 - α) :=
      div_pos (mul_pos hα (Real.rpow_pos_of_pos hu.1 _)) hΓ
    have hg : 0 < g (t - u) := hpast _ ⟨by linarith [hu.2], by linarith [hu.1]⟩
    simpa [Pi.neg_apply, hzero] using mul_pos he hg
  rw [intervalIntegral.integral_neg, neg_pos] at hpos
  unfold fractionalMemory
  rw [hzero]
  have hfirst : (0 - initial) * (t ^ (-α) / Real.Gamma (1 - α)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  exact add_neg_of_nonpos_of_neg hfirst (by simpa only [hzero] using hpos)

/-- First-contact comparison, allowing the earlier history to have a
singularity at zero. The continuity assumption starts at the initial
comparison time, rather than at zero. -/
theorem fractional_first_contact_comparison {α initial a b : ℝ} {g : ℝ → ℝ}
    (hα : 0 < α) (hα₁ : α < 1) (hi : 0 ≤ initial) (ha : 0 < a)
    (hg : ContinuousOn g (Icc a b))
    (hstart : ∀ s ∈ Ioc 0 a, 0 < g s)
    (hd : ∀ t ∈ Icc a b, g t = 0 →
      IntervalIntegrable
        (fun u => (α * u ^ (-α - 1) / Real.Gamma (1 - α)) * (g t - g (t - u)))
        volume 0 t ∧ 0 ≤ fractionalMemory α initial g t) :
    ∀ t ∈ Icc a b, 0 < g t := by
  classical
  intro t ht
  by_contra! hbad
  have hga : 0 < g a := hstart a ⟨ha, le_rfl⟩
  let S := {s ∈ Icc a t | g s ≤ 0}
  have hc : IsCompact S := by
    have hclosed : IsClosed S :=
      isClosed_Icc.isClosed_le (hg.mono (Icc_subset_Icc_right ht.2)) continuousOn_const
    exact isCompact_Icc.of_isClosed_subset hclosed (fun _ hx => hx.1)
  have hS : S.Nonempty := ⟨t, ⟨ht.1, le_rfl⟩, hbad⟩
  obtain ⟨z, hz, hleast⟩ := hc.exists_isLeast hS
  have hza : a < z := lt_of_le_of_ne hz.1.1 (by
    intro he
    exact (not_le_of_gt hga) (he ▸ hz.2))
  have hz₀ : g z = 0 := by
    apply le_antisymm hz.2
    by_contra! hn
    have hiv := intermediate_value_Icc' hza.le (hg.mono (Icc_subset_Icc_right (hz.1.2.trans ht.2)))
    obtain ⟨z', hz', hzero'⟩ := hiv (show 0 ∈ Icc (g z) (g a) from ⟨hn.le, hga.le⟩)
    have hmem : z' ∈ S := ⟨⟨hz'.1, hz'.2.trans hz.1.2⟩, hzero'.le⟩
    have he : z' = z := le_antisymm hz'.2 (hleast hmem)
    exact (ne_of_lt hn) (he ▸ hzero')
  have hpast : ∀ s ∈ Ioo 0 z, 0 < g s := by
    intro s hs
    by_cases hsa : s ≤ a
    · exact hstart s ⟨hs.1, hsa⟩
    · by_contra! hnonpos
      have hmem : s ∈ S := ⟨⟨(lt_of_not_ge hsa).le, hs.2.le.trans hz.1.2⟩, hnonpos⟩
      exact (not_le_of_gt hs.2) (hleast hmem)
  obtain ⟨hint, hdiff⟩ := hd z ⟨hz.1.1, hz.1.2.trans ht.2⟩ hz₀
  exact (not_le_of_gt (fractional_memory_negative_at_contact hα hα₁ hi
    (ha.trans hza) hz₀ hpast hint)) hdiff

/-- Undo the change of measure on an event on which its density is bounded. -/
theorem undo_size_bias {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {density : Ω → ENNReal} {event : Set Ω} {cap p : ENNReal}
    (hevent : MeasurableSet event) (hcap : ∀ x ∈ event, density x ≤ cap)
    (hp : p ≤ (μ.withDensity density) event) :
    p ≤ cap * μ event := by
  rw [withDensity_apply _ hevent] at hp
  refine hp.trans ?_
  calc
    ∫⁻ x in event, density x ∂μ ≤ ∫⁻ _ in event, cap ∂μ :=
      lintegral_mono_ae ((ae_restrict_iff' hevent).mpr (Eventually.of_forall hcap))
    _ = cap * μ event := by simp

/-- Removing the envelope, cost, and positivity failures from a burst event. -/
theorem remove_bad_events {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (burst e₁ e₂ e₃ : Set Ω) :
    μ burst ≤ μ (burst \ (e₁ ∪ e₂ ∪ e₃)) + (μ e₁ + μ e₂ + μ e₃) := by
  have hsub : burst ⊆ (burst \ (e₁ ∪ e₂ ∪ e₃)) ∪ (e₁ ∪ e₂ ∪ e₃) := by
    intro x hx
    by_cases h : x ∈ e₁ ∪ e₂ ∪ e₃
    · exact Or.inr h
    · exact Or.inl ⟨hx, h⟩
  have hbad : μ (e₁ ∪ e₂ ∪ e₃) ≤ μ e₁ + μ e₂ + μ e₃ :=
    (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add le_rfl hbad))

/-- The real second-moment argument applied under an actual finite measure.
The event is the positive support of the nonnegative random variable. -/
theorem second_moment_support {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) (hx₀ : ∀ x, 0 ≤ X x) (hL2 : MemLp X 2 μ) :
    (∫ x, X x ∂μ)^2 ≤ (∫ x, (X x)^2 ∂μ) * μ.real {x | 0 < X x} := by
  let A := {x | 0 < X x}
  have hA : MeasurableSet A := measurableSet_lt measurable_const hX
  have hconj : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hL2' : MemLp X (ENNReal.ofReal (2 : ℝ)) (μ.restrict A) := by
    simpa using hL2.mono_measure Measure.restrict_le_self
  have h1 : MemLp (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) (μ.restrict A) :=
    memLp_const _
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hconj
    (Eventually.of_forall hx₀) (Eventually.of_forall fun _ => zero_le_one) hL2' h1
  have hfirst : ∫ x in A, X x ∂μ = ∫ x, X x ∂μ := by
    rw [← integral_indicator hA]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hh : x ∈ A
    · simp [hh]
    · have hx : X x = 0 := le_antisymm (le_of_not_gt hh) (hx₀ x)
      simp [hh, hx]
  have hsecond : ∫ x in A, (X x)^2 ∂μ = ∫ x, (X x)^2 ∂μ := by
    rw [← integral_indicator hA]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hh : x ∈ A
    · simp [hh]
    · have hx : X x = 0 := le_antisymm (le_of_not_gt hh) (hx₀ x)
      simp [hh, hx]
  have hnonneg : 0 ≤ ∫ x, X x ∂μ := integral_nonneg hx₀
  simp only [mul_one, Real.rpow_two, integral_const,
    smul_eq_mul, Measure.real, Measure.restrict_apply_univ] at hh
  rw [hfirst, hsecond] at hh
  have hsqrt : ∀ x : ℝ, x ^ ((1 : ℝ) / 2) = Real.sqrt x := by
    intro x
    apply Eq.symm
    apply Real.sqrt_eq_rpow
  simp only [one_pow, mul_one, hsqrt] at hh
  calc
    (∫ x, X x ∂μ)^2 ≤
        (Real.sqrt (∫ x, (X x)^2 ∂μ) * Real.sqrt (μ (A)).toReal)^2 :=
      pow_le_pow_left₀ hnonneg hh 2
    _ = _ := by
      rw [mul_pow, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _),
        Real.sq_sqrt ENNReal.toReal_nonneg]
      rfl

private theorem beta_weight_integral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    let g := fun x : ℝ => x ^ (a - 1) * (1 - x) ^ (b - 1)
    IntegrableOn g (Ioo 0 1) ∧
    (∫ x in Ioo (0 : ℝ) 1, g x) = Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  let g := fun x : ℝ => x ^ (a - 1) * (1 - x) ^ (b - 1)
  let gc := fun x : ℝ => (x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((b : ℂ) - 1)
  have hreal : ∀ x ∈ Ioo (0 : ℝ) 1, gc x = (g x : ℂ) := by
    intro x hx
    dsimp [gc, g]
    push_cast
    rw [Complex.ofReal_cpow hx.1.le, Complex.ofReal_cpow (sub_nonneg.mpr hx.2.le)]
    push_cast
    rfl
  have hCg : IntegrableOn gc (Ioo 0 1) :=
    (Complex.betaIntegral_convergent (u := (a : ℂ)) (v := (b : ℂ))
      ha hb).1.mono_set Ioo_subset_Ioc_self
  have hInt : IntegrableOn g (Ioo (0 : ℝ) 1) := by
    have hr : IntegrableOn (fun x => (gc x).re) (Ioo 0 1) := hCg.re
    apply hr.congr_fun _ measurableSet_Ioo
    intro x hx
    change (gc x).re = g x
    rw [hreal x hx, Complex.ofReal_re]
  refine ⟨hInt, ?_⟩
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have heq : (∫ x in Ioo (0 : ℝ) 1, (g x : ℂ)) = Complex.betaIntegral (a : ℂ) (b : ℂ) := by
    rw [Complex.betaIntegral, intervalIntegral.integral_of_le zero_le_one,
      ← setIntegral_congr_set (Ioo_ae_eq_Ioc : Ioo (0 : ℝ) 1 =ᵐ[volume] Ioc 0 1)]
    exact setIntegral_congr_fun measurableSet_Ioo (fun x hx => (hreal x hx).symm)
  rw [heq]
  have hG : 0 < Real.Gamma (a + b) := Real.Gamma_pos_of_pos (add_pos ha hb)
  have hBeta := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (a : ℂ)) (t := (b : ℂ)) ha hb
  rw [Complex.ofReal_div, Complex.ofReal_mul]
  apply (eq_div_iff (Complex.ofReal_ne_zero.mpr hG.ne')).mpr
  rw [← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal] at hBeta
  simpa [mul_comm, Complex.ofReal_mul] using hBeta.symm

/-- Change of variable used for the Caputo comparison. -/
private theorem fractional_tail_kernel {α p y : ℝ} (hα : α < 1) (hp : p < α) (hy : 0 < y) :
    let f := fun v : ℝ => v ^ (-α) * (y + v) ^ (p - 1)
    IntegrableOn f (Ioi 0) ∧
    (∫ v in Ioi (0 : ℝ), f v) =
      y ^ (p - α) * (Real.Gamma (1 - α) * Real.Gamma (α - p) / Real.Gamma (1 - p)) := by
  let f := fun v : ℝ => v ^ (-α) * (y + v) ^ (p - 1)
  let φ := fun v : ℝ => v / (y + v)
  let φ' := fun v : ℝ => y / (y + v)^2
  let g := fun x : ℝ => x ^ (-α) * (1 - x) ^ (α - p - 1)
  have hφ (v : ℝ) (hv : v ∈ Ioi 0) : HasDerivWithinAt φ (φ' v) (Ioi 0) v := by
    have hpv : 0 < y + v := add_pos hy hv
    apply HasDerivAt.hasDerivWithinAt
    convert (hasDerivAt_id v).div ((hasDerivAt_const v y).add (hasDerivAt_id v))
      hpv.ne' using 1
    · rfl
    · dsimp [φ']
      ring
  have hinj : InjOn φ (Ioi 0) := by
    intro v hv w hw h
    have hv' : 0 < y + v := add_pos hy hv
    have hw' : 0 < y + w := add_pos hy hw
    have he := (div_eq_div_iff hv'.ne' hw'.ne').mp h
    have hm : y * (v - w) = 0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hy.ne')
  have himage : φ '' Ioi 0 = Ioo 0 1 := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      change 0 < v at hv
      exact ⟨div_pos hv (add_pos hy hv), (div_lt_iff₀ (add_pos hy hv)).mpr (by linarith)⟩
    · intro hx
      change 0 < x ∧ x < 1 at hx
      have hx' : 0 < 1 - x := sub_pos.mpr hx.2
      have hv : 0 < y * x / (1 - x) := div_pos (mul_pos hy hx.1) hx'
      refine ⟨y * x / (1 - x), hv, ?_⟩
      dsimp [φ]
      apply (div_eq_iff (add_pos hy hv).ne').mpr
      field_simp [hx'.ne']
      ring
  have hweight {v : ℝ} (hv : v ∈ Ioi 0) :
      y ^ (p - α) * (|φ' v| • g (φ v)) = f v := by
    have hv₀ : 0 < v := hv
    have huv : 0 < y + v := add_pos hy hv₀
    have h1 : 1 - v / (y + v) = y / (y + v) := by
      apply (eq_div_iff huv.ne').mpr
      rw [sub_mul, one_mul, div_mul_cancel₀ _ huv.ne']
      ring
    dsimp [φ', g, φ, f]
    rw [abs_of_nonneg (by positivity : 0 ≤ y / (y + v)^2), h1,
      Real.div_rpow hv₀.le huv.le, Real.div_rpow hy.le huv.le]
    have hnum : y ^ (p - α) * y * y ^ (α - p - 1) = 1 := by
      calc
        _ = y ^ (p - α) * y ^ (1 : ℝ) * y ^ (α - p - 1) :=
          congrArg (fun z : ℝ => y ^ (p - α) * z * y ^ (α - p - 1)) (Real.rpow_one y).symm
        _ = _ := by
          rw [← Real.rpow_add hy, ← Real.rpow_add hy,
            show (p - α + (1 : ℝ)) + (α - p - 1) = 0 by ring, Real.rpow_zero]
    have hden : (y + v)^2 * (y + v) ^ (-α) * (y + v) ^ (α - p - 1) =
        ((y + v) ^ (p - 1))⁻¹ := by
      rw [← Real.rpow_two, ← Real.rpow_add huv, ← Real.rpow_add huv,
        ← Real.rpow_neg huv.le]
      congr 1
      ring
    calc
      _ = (y ^ (p - α) * y * y ^ (α - p - 1)) * v ^ (-α) /
        ((y + v)^2 * (y + v) ^ (-α) * (y + v) ^ (α - p - 1)) := by
          field_simp [huv.ne', (Real.rpow_pos_of_pos huv (-α)).ne',
            (Real.rpow_pos_of_pos huv (α - p - 1)).ne']
      _ = _ := by rw [hnum, hden, one_mul, div_inv_eq_mul]
  have hG := beta_weight_integral (a := 1 - α) (b := α - p) (by linarith) (by linarith)
  simp only [show 1 - α - 1 = -α by ring, show 1 - α + (α - p) = 1 - p by ring] at hG
  have hgi : IntegrableOn g (φ '' Ioi 0) := himage.symm ▸ hG.1
  have hsubi := (integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi hφ hinj g).mp hgi
  have hInt : IntegrableOn f (Ioi 0) := by
    have hmul : IntegrableOn (fun v => y ^ (p - α) * (|φ' v| • g (φ v))) (Ioi 0) :=
      hsubi.const_mul (y ^ (p - α))
    apply hmul.congr_fun _ measurableSet_Ioi
    intro v hv
    exact hweight hv
  refine ⟨hInt, ?_⟩
  have hsub := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hφ hinj g
  calc
    (∫ v in Ioi (0 : ℝ), f v) =
        ∫ v in Ioi (0 : ℝ), y ^ (p - α) * (|φ' v| • g (φ v)) :=
      setIntegral_congr_fun measurableSet_Ioi (fun _ hv => (hweight hv).symm)
    _ = y ^ (p - α) * ∫ v in Ioi (0 : ℝ), |φ' v| • g (φ v) := integral_const_mul _ _
    _ = _ := by rw [← hsub, himage, hG.2]

/-- Rigorous power barrier estimate, with the Caputo derivative written
as its defining convolution integral. -/
theorem caputo_terminal_power_bound {α p y s : ℝ}
    (hα : α < 1) (hp : 0 < p) (hpα : p < α) (hy : 0 < y) (hs : 0 ≤ s) :
    - (p / Real.Gamma (1 - α)) *
        (∫ v in (0 : ℝ)..s, v ^ (-α) * (y + v) ^ (p - 1)) ≥
      - caputoCoefficient α p * y ^ (p - α) := by
  have hΓ : 0 < Real.Gamma (1 - α) := Real.Gamma_pos_of_pos (by linarith)
  obtain ⟨hi, hv⟩ := fractional_tail_kernel hα hpα hy
  have hle : (∫ v in (0 : ℝ)..s, v ^ (-α) * (y + v) ^ (p - 1)) ≤
      ∫ v in Ioi (0 : ℝ), v ^ (-α) * (y + v) ^ (p - 1) := by
    rw [intervalIntegral.integral_of_le hs]
    apply setIntegral_mono_set hi ?_
      (show Ioc (0 : ℝ) s ⊆ Ioi 0 from fun _ h => h.1).eventuallyLE
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    filter_upwards with v hv
    have hv₀ : 0 < v := hv
    exact mul_nonneg (Real.rpow_nonneg hv₀.le _)
      (Real.rpow_nonneg (add_pos hy hv₀).le _)
  rw [hv] at hle
  have hh := mul_le_mul_of_nonneg_left hle (div_nonneg hp.le hΓ.le)
  unfold caputoCoefficient
  simp only [neg_mul, neg_le_neg_iff]
  have hΓ' : 0 < Real.Gamma (1 - p) := Real.Gamma_pos_of_pos (by linarith)
  have he : p / Real.Gamma (1 - α) *
      (y ^ (p - α) * (Real.Gamma (1 - α) * Real.Gamma (α - p) / Real.Gamma (1 - p))) =
      (p * Real.Gamma (α - p) / Real.Gamma (1 - p)) * y ^ (p - α) := by
    field_simp [hΓ.ne', hΓ'.ne']
  exact hh.trans_eq he

/-- Lower bound after excluding three bad events under the tilted law and
then returning to the original law. The probability bounds under the
tilted law are inputs, not a formalization of Girsanov's theorem. -/
theorem separation_from_tilt_bounds {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {d : Ω → ENNReal}
    {burst e₁ e₂ e₃ : Set Ω} {p error cap : ENNReal}
    (herror : error ≠ ⊤) (hcap₀ : cap ≠ 0) (hcap_top : cap ≠ ⊤)
    (hgood : MeasurableSet (burst \ (e₁ ∪ e₂ ∪ e₃)))
    (hlarge : p + error ≤ (μ.withDensity d) burst)
    (hsmall : (μ.withDensity d) e₁ + (μ.withDensity d) e₂ +
      (μ.withDensity d) e₃ ≤ error)
    (hcap : ∀ x ∈ burst, d x ≤ cap) :
    p / cap ≤ μ (burst \ (e₁ ∪ e₂ ∪ e₃)) := by
  have hsplit := remove_bad_events (μ := μ.withDensity d) burst e₁ e₂ e₃
  have hlower : p ≤ (μ.withDensity d) (burst \ (e₁ ∪ e₂ ∪ e₃)) :=
    ENNReal.le_of_add_le_add_right herror
      (hlarge.trans (hsplit.trans (add_le_add le_rfl hsmall)))
  exact (ENNReal.div_le_iff' hcap₀ hcap_top).mpr
    (undo_size_bias hgood (fun x hx => hcap x hx.1) hlower)

/-- Weak-limit separation derived from the count moments. The random count
and the weak limit must come from the coupled approximations. -/
theorem weak_limit_distinct_from_count_moments
    {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [HasOuterApproxClosed Ω] [OpensMeasurableSpace Ω]
    {μ : FiniteMeasure Ω} {μn : ℕ → FiniteMeasure Ω}
    (hμ : Tendsto μn atTop (𝓝 μ)) {distance : Ω → ℝ}
    (hd : Continuous distance) {count : ℕ → Ω → ℝ}
    {ℓ a b : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) (hb : 0 < b)
    (hmeas : ∀ n, Measurable (count n)) (hnonneg : ∀ n x, 0 ≤ count n x)
    (hL2 : ∀ n, MemLp (count n) 2 (μn n : Measure Ω))
    (hmean : ∀ n, a ≤ ∫ x, count n x ∂(μn n : Measure Ω))
    (hsecond : ∀ n, (∫ x, (count n x)^2 ∂(μn n : Measure Ω)) ≤ b)
    (hpath : ∀ n x, 0 < count n x → ℓ ≤ distance x) :
    0 < (μ : Measure Ω) {x | 0 < distance x} := by
  have huniform (n : ℕ) : ENNReal.ofReal (a ^ 2 / b) ≤
      (μn n : Measure Ω) {x | ℓ ≤ distance x} := by
    have hcs := second_moment_support (hmeas n) (hnonneg n) (hL2 n)
    have hreal := (count_lower_bound ha hb (hmean n) (hsecond n)
      ENNReal.toReal_nonneg hcs).2
    have hp : ENNReal.ofReal (a ^ 2 / b) ≤
        (μn n : Measure Ω) {x | 0 < count n x} :=
      (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr hreal
    exact hp.trans (measure_mono (fun x hx => hpath n x hx))
  have hweak := separation_of_weak_limit hμ hd huniform
  have hpos : 0 < ENNReal.ofReal (a ^ 2 / b) := ENNReal.ofReal_pos.mpr (by positivity)
  exact hpos.trans_le (hweak.trans (measure_mono fun x hx => hℓ.trans_le hx))

/-- A uniform bound on the Laplace complements gives the same bound on
positive occupation. This applies, in particular, to a conditional law
given that the variance was zero at an earlier time. -/
theorem positive_probability_of_laplace_bounds {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ} {C : ℝ}
    (hX : Measurable X) (h₀ : ∀ x, 0 ≤ X x)
    (hLaplace : ∀ n : ℕ, (∫ x, 1 - Real.exp (-(n : ℝ) * X x) ∂μ) ≤ C) :
    μ.real {x | 0 < X x} ≤ C := by
  let A := {x | 0 < X x}
  let F : ℕ → Ω → ℝ := fun n x => 1 - Real.exp (-(n : ℝ) * X x)
  have hA : MeasurableSet A := measurableSet_lt measurable_const hX
  have hpoint (x : Ω) : Tendsto (fun n => F n x) atTop
      (𝓝 (A.indicator (fun _ => (1 : ℝ)) x)) := by
    by_cases hx : 0 < X x
    · have hxA : x ∈ A := hx
      have htop : Tendsto (fun n : ℕ => (n : ℝ) * X x) atTop atTop :=
        (tendsto_mul_const_atTop_of_pos hx).mpr tendsto_natCast_atTop_atTop
      have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp htop
      simpa [F, Function.comp_def, neg_mul, hxA] using tendsto_const_nhds.sub he
    · have hxA : x ∉ A := hx
      have hzero : X x = 0 := le_antisymm (le_of_not_gt hx) (h₀ x)
      simp [F, hzero, hxA]
  have hmeas (n : ℕ) : AEStronglyMeasurable (F n) μ :=
    (measurable_const.sub (((measurable_const : Measurable (fun _ : Ω => -(n : ℝ))).mul
      hX).exp)).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ x ∂μ, ‖F n x‖ ≤ (1 : ℝ) := by
    filter_upwards with x
    have hneg : -(n : ℝ) * X x ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) (h₀ x)
    have hle : Real.exp (-(n : ℝ) * X x) ≤ 1 := Real.exp_le_one_iff.mpr hneg
    rw [Real.norm_of_nonneg (show 0 ≤ F n x from sub_nonneg.mpr hle)]
    exact sub_le_self _ (Real.exp_nonneg _)
  have hlim := tendsto_integral_of_dominated_convergence (fun _ : Ω => (1 : ℝ))
    hmeas (integrable_const _) hbound (Eventually.of_forall hpoint)
  change Tendsto (fun n => ∫ x, F n x ∂μ) atTop
    (𝓝 (∫ x, A.indicator (1 : Ω → ℝ) x ∂μ)) at hlim
  rw [integral_indicator_one hA] at hlim
  exact le_of_tendsto hlim (Eventually.of_forall hLaplace)

/-- Volterra convolution with a Lebesgue integral over the elapsed time. -/
noncomputable def volterraConvolution (k f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in Ioc (0 : ℝ) t, k (t - s) * f s

/-- Shift the lower endpoint on a Volterra triangle when the inner
kernel vanishes at nonpositive arguments. -/
theorem volterra_shifted_kernel_integral {l k : ℝ → ℝ} {t u : ℝ}
    (hk : ∀ x ≤ 0, k x = 0) (hu : u ∈ Ioc (0 : ℝ) t) :
    (∫ s in Ioc (0 : ℝ) t, l (t - s) * k (s - u)) =
      volterraConvolution l k (t - u) := by
  classical
  have hsub : Ioc u t ⊆ Ioc 0 t := Ioc_subset_Ioc_left hu.1.le
  have hz (s : ℝ) (hs : s ∈ Ioc 0 t \ Ioc u t) :
      l (t - s) * k (s - u) = 0 := by
    have hsu : s ≤ u := by
      by_contra! h
      exact hs.2 ⟨h, hs.1.2⟩
    rw [hk _ (sub_nonpos.mpr hsu), mul_zero]
  have hshort := setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (μ := volume) measurableSet_Ioc hsub hz
  rw [hshort, ← intervalIntegral.integral_of_le hu.2]
  have hr := intervalIntegral.integral_comp_sub_right
    (f := fun v => l ((t - u) - v) * k v) (a := u) (b := t) u
  simp only [sub_self] at hr
  rw [intervalIntegral.integral_of_le (sub_nonneg.mpr hu.2)] at hr
  apply Eq.trans _ hr
  apply intervalIntegral.integral_congr
  intro s _
  simp only
  congr 2
  ring

/-- Ordinary Fubini on the Volterra triangle. The rectangle integrability
assumption is discharged for the fractional kernel pair below. -/
theorem volterra_convolution_assoc {l k f : ℝ → ℝ} {t : ℝ}
    (hk : ∀ u ≤ 0, k u = 0)
    (hI : Integrable (fun z : ℝ × ℝ => l (t - z.1) * k (z.1 - z.2) * f z.2)
      ((volume.restrict (Ioc 0 t)).prod (volume.restrict (Ioc 0 t)))) :
    volterraConvolution l (volterraConvolution k f) t =
      volterraConvolution (volterraConvolution l k) f t := by
  classical
  have hleft (s : ℝ) (hs : s ∈ Ioc 0 t) :
      l (t - s) * volterraConvolution k f s =
        ∫ u in Ioc (0 : ℝ) t, l (t - s) * k (s - u) * f u := by
    unfold volterraConvolution
    rw [← integral_const_mul]
    have hsub : Ioc 0 s ⊆ Ioc 0 t := Ioc_subset_Ioc_right hs.2
    have hz (u : ℝ) (hu : u ∈ Ioc 0 t \ Ioc 0 s) :
        l (t - s) * (k (s - u) * f u) = 0 := by
      have hus : s ≤ u := by
        by_contra! h
        exact hu.2 ⟨hu.1.1, h.le⟩
      rw [hk _ (sub_nonpos.mpr hus), zero_mul, mul_zero]
    have hext := setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (μ := volume) measurableSet_Ioc hsub hz
    rw [← hext]
    simp only [mul_assoc]
  have hright (u : ℝ) (hu : u ∈ Ioc 0 t) :
      (∫ s in Ioc (0 : ℝ) t, l (t - s) * k (s - u) * f u) =
        volterraConvolution l k (t - u) * f u := by
    rw [integral_mul_const, volterra_shifted_kernel_integral hk hu]
  calc
    _ = ∫ s in Ioc (0 : ℝ) t, ∫ u in Ioc (0 : ℝ) t,
        l (t - s) * k (s - u) * f u := setIntegral_congr_fun measurableSet_Ioc hleft
    _ = ∫ u in Ioc (0 : ℝ) t, ∫ s in Ioc (0 : ℝ) t,
        l (t - s) * k (s - u) * f u := integral_integral_swap hI
    _ = _ := setIntegral_congr_fun measurableSet_Ioc hright

noncomputable def fractionalK (α t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else t ^ (α - 1) / Real.Gamma α

noncomputable def fractionalL (α t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else t ^ (-α) / Real.Gamma (1 - α)

/-- Positive-time fractional convolution identity in the causal
conventions used for the Volterra operators. -/
theorem fractional_causal_kernel_inverse {α t : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1) (ht : 0 < t) :
    volterraConvolution (fractionalL α) (fractionalK α) t = 1 := by
  unfold volterraConvolution
  rw [← intervalIntegral.integral_of_le ht.le]
  have hflip := intervalIntegral.integral_comp_sub_left
    (f := fun v => fractionalL α v * fractionalK α (t - v))
    (a := 0) (b := t) t
  simp only [sub_self, sub_zero, sub_sub_cancel] at hflip
  rw [hflip, ← fractional_kernel_inverse hα₀ hα₁ ht]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.le] at hs
  have hL {x : ℝ} (hx : 0 ≤ x) :
      fractionalL α x = x ^ (-α) / Real.Gamma (1 - α) := by
    by_cases hp : 0 < x
    · simp [fractionalL, not_le_of_gt hp]
    · have he : x = 0 := le_antisymm (le_of_not_gt hp) hx
      simp [he, fractionalL, Real.zero_rpow (by linarith : -α ≠ 0)]
  have hK {x : ℝ} (hx : 0 ≤ x) :
      fractionalK α x = x ^ (α - 1) / Real.Gamma α := by
    by_cases hp : 0 < x
    · simp [fractionalK, not_le_of_gt hp]
    · have he : x = 0 := le_antisymm (le_of_not_gt hp) hx
      simp [he, fractionalK, Real.zero_rpow (by linarith : α - 1 ≠ 0)]
  change fractionalL α s * fractionalK α (t - s) =
    s ^ (-α) / Real.Gamma (1 - α) * ((t - s) ^ (α - 1) / Real.Gamma α)
  rw [hL hs.1, hK (sub_nonneg.mpr hs.2)]

/-- Absolute integrability of the fractional Fubini triangle for an L¹ input. -/
theorem fractional_volterra_triangle_integrable {α t : ℝ} {f : ℝ → ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1) (hf : Measurable f)
    (hfint : IntegrableOn f (Ioc 0 t)) :
    Integrable (fun z : ℝ × ℝ =>
      fractionalL α (t - z.1) * fractionalK α (z.1 - z.2) * f z.2)
      ((volume.restrict (Ioc 0 t)).prod (volume.restrict (Ioc 0 t))) := by
  let ν := volume.restrict (Ioc 0 t)
  have hK : Measurable (fractionalK α) := by
    unfold fractionalK
    exact Measurable.ite measurableSet_Iic measurable_const
      ((measurable_id.pow_const _).div_const _)
  have hL : Measurable (fractionalL α) := by
    unfold fractionalL
    exact Measurable.ite measurableSet_Iic measurable_const
      ((measurable_id.pow_const _).div_const _)
  have hnK (u : ℝ) : 0 ≤ fractionalK α u := by
    unfold fractionalK
    split
    · exact le_rfl
    · exact div_nonneg (Real.rpow_nonneg (le_of_lt (lt_of_not_ge ‹¬u ≤ 0›)) _)
        (Real.Gamma_pos_of_pos hα₀).le
  have hnL (u : ℝ) : 0 ≤ fractionalL α u := by
    unfold fractionalL
    split
    · exact le_rfl
    · exact div_nonneg (Real.rpow_nonneg (le_of_lt (lt_of_not_ge ‹¬u ≤ 0›)) _)
        (Real.Gamma_pos_of_pos (by linarith)).le
  have hpair : Measurable (fun z : ℝ × ℝ =>
      fractionalL α (t - z.1) * fractionalK α (z.1 - z.2) * f z.2) :=
    ((hL.comp (measurable_const.sub measurable_fst)).mul
      (hK.comp (measurable_fst.sub measurable_snd))).mul (hf.comp measurable_snd)
  have hae : ∀ᵐ u ∂ν, u ∈ Ioo 0 t := by
    unfold ν
    rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc : Ioo (0 : ℝ) t =ᵐ[volume] Ioc 0 t)]
    exact ae_restrict_mem measurableSet_Ioo
  have hinv (u : ℝ) (hu : u ∈ Ioo 0 t) :
      ∫ s, fractionalL α (t - s) * fractionalK α (s - u) ∂ν = 1 := by
    change (∫ s in Ioc (0 : ℝ) t, fractionalL α (t - s) * fractionalK α (s - u)) = 1
    rw [volterra_shifted_kernel_integral (fun x hx => by simp [fractionalK, hx])
      (show u ∈ Ioc 0 t from ⟨hu.1, hu.2.le⟩)]
    exact fractional_causal_kernel_inverse hα₀ hα₁ (sub_pos.mpr hu.2)
  refine (integrable_prod_iff' hpair.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · filter_upwards [hae] with u hu
    have hkint : Integrable (fun s => fractionalL α (t - s) * fractionalK α (s - u)) ν := by
      by_contra h
      exact one_ne_zero ((hinv u hu).symm.trans (integral_undef h))
    exact hkint.mul_const (f u)
  · refine (hfint.norm : Integrable (fun u => ‖f u‖) ν).congr ?_
    filter_upwards [hae] with u hu
    have heq :
        (fun s => ‖fractionalL α (t - s) * fractionalK α (s - u) * f u‖) =
        fun s => fractionalL α (t - s) * fractionalK α (s - u) * ‖f u‖ := by
      funext s
      rw [norm_mul, Real.norm_of_nonneg (mul_nonneg (hnL _) (hnK _))]
    rw [heq, integral_mul_const, hinv u hu, one_mul]

/-- Fractional inversion of the ordinary drift convolution.
Stochastic Fubini requires a separate proof. -/
theorem fractional_volterra_inverts_drift {α t : ℝ} {f : ℝ → ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1) (hf : Measurable f)
    (hfint : IntegrableOn f (Ioc 0 t)) :
    volterraConvolution (fractionalL α) (volterraConvolution (fractionalK α) f) t =
      ∫ s in Ioc (0 : ℝ) t, f s := by
  rw [volterra_convolution_assoc (fun x hx => by simp [fractionalK, hx])
    (fractional_volterra_triangle_integrable hα₀ hα₁ hf hfint)]
  unfold volterraConvolution
  rw [← setIntegral_congr_set (Ioo_ae_eq_Ioc : Ioo (0 : ℝ) t =ᵐ[volume] Ioc 0 t),
    ← setIntegral_congr_set (Ioo_ae_eq_Ioc : Ioo (0 : ℝ) t =ᵐ[volume] Ioc 0 t)]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro s hs
  change volterraConvolution (fractionalL α) (fractionalK α) (t - s) * f s = f s
  rw [fractional_causal_kernel_inverse hα₀ hα₁ (sub_pos.mpr hs.2), one_mul]

end RoughHeston

#print axioms RoughHeston.comparison_exponent
#print axioms RoughHeston.occupation_cost_integral
#print axioms RoughHeston.normalized_sum_variance
#print axioms RoughHeston.normalized_sum_covariation
#print axioms RoughHeston.tilt_cost_bound
#print axioms RoughHeston.count_lower_bound

#print axioms RoughHeston.cluster_projection

#print axioms RoughHeston.fractional_beta_integral
#print axioms RoughHeston.separation_of_weak_limit
#print axioms RoughHeston.fractional_kernel_inverse
#print axioms RoughHeston.fractional_memory_negative_at_contact
#print axioms RoughHeston.fractional_first_contact_comparison
#print axioms RoughHeston.undo_size_bias
#print axioms RoughHeston.remove_bad_events
#print axioms RoughHeston.second_moment_support
#print axioms RoughHeston.caputo_terminal_power_bound
#print axioms RoughHeston.separation_from_tilt_bounds
#print axioms RoughHeston.weak_limit_distinct_from_count_moments
#print axioms RoughHeston.positive_probability_of_laplace_bounds

#print axioms RoughHeston.volterra_convolution_assoc
#print axioms RoughHeston.fractional_causal_kernel_inverse
#print axioms RoughHeston.fractional_volterra_triangle_integrable
#print axioms RoughHeston.fractional_volterra_inverts_drift

#print axioms RoughHeston.volterra_shifted_kernel_integral
