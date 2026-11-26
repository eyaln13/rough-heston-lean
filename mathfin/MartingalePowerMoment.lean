import DyadicStepApproximation
import BrownianMotion.Auxiliary.Martingale
import MathFin.Probability.Discrete.DoobLpMaximalInequality
import MathFin.Probability.Discrete.DiscreteIto
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! The moment estimate obtained from the integrated Itô power identity
and a maximal moment inequality. -/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace RoughHeston

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

private theorem lintegral_mul_partial_power_le {F G : Ω → ℝ≥0∞}
    (hF : Measurable F) (hG : Measurable G) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    (∫⁻ ω, F ω ^ a * G ω ∂μ) ≤
      (∫⁻ ω, F ω ∂μ) ^ a * (∫⁻ ω, G ω ^ b⁻¹ ∂μ) ^ b := by
  have hexp : (1 / a).HolderConjugate (1 / b) := Real.holderConjugate_one_div ha hb hab
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hexp (f := fun ω => F ω ^ a)
    ((ENNReal.continuous_rpow_const.measurable.comp hF).aemeasurable) hG.aemeasurable
  have hid (x : ℝ≥0∞) : (x ^ a) ^ a⁻¹ = x := by
    rw [← ENNReal.rpow_mul, mul_inv_cancel₀ ha.ne', ENNReal.rpow_one]
  simpa only [Pi.mul_apply, hid, one_div, inv_inv] using h

private theorem le_mul_rpow_of_le_mul_self_rpow {A B D : ℝ≥0∞} {m : ℝ}
    (hm : 1 < m) (hA : A ≠ ⊤)
    (h : A ≤ D * A ^ (1 - m⁻¹) * B ^ m⁻¹) : A ≤ D ^ m * B := by
  have hm0 : 0 < m := zero_lt_one.trans hm
  have hb : 0 < m⁻¹ := inv_pos.mpr hm0
  have ha : 0 < 1 - m⁻¹ := sub_pos.mpr ((inv_lt_one₀ hm0).2 hm)
  by_cases hA0 : A = 0
  · simp [hA0]
  have hP0 : A ^ (1 - m⁻¹) ≠ 0 := fun he =>
    hA0 ((ENNReal.rpow_eq_zero_iff_of_pos ha).1 he)
  have hPtop : A ^ (1 - m⁻¹) ≠ ⊤ := fun he =>
    hA ((ENNReal.rpow_eq_top_iff_of_pos ha).1 he)
  have hsplit : A ^ (1 - m⁻¹) * A ^ m⁻¹ = A := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ ha.le hb.le,
      sub_add_cancel, ENNReal.rpow_one]
  have hcancel : A ^ m⁻¹ ≤ D * B ^ m⁻¹ := by
    apply (ENNReal.mul_le_mul_iff_left hP0 hPtop).1
    rw [mul_comm (A ^ m⁻¹), hsplit]
    exact h.trans_eq (by ac_rfl)
  have hpow := ENNReal.rpow_le_rpow hcancel hm0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hm0.le, ← ENNReal.rpow_mul, inv_mul_cancel₀ hm0.ne',
    ENNReal.rpow_one, ← ENNReal.rpow_mul, inv_mul_cancel₀ hm0.ne', ENNReal.rpow_one] at hpow
  exact hpow

/-- Moment bound for a finite-moment localized martingale. Here X is the
terminal norm, S the running norm supremum, and Q the terminal quadratic
variation. The two input inequalities come from the integrated Itô identity
and Doob's maximal inequality respectively. -/
theorem terminal_even_moment_le_of_power_identity_and_doob {m : ℝ} (hm : 1 < m)
    {X S Q : Ω → ℝ≥0∞} (hS : Measurable S) (hQ : Measurable Q)
    {D K : ℝ≥0∞}
    (hX : (∫⁻ ω, X ω ^ (2 * m) ∂μ) ≠ ⊤)
    (hIto : (∫⁻ ω, X ω ^ (2 * m) ∂μ) ≤
      D * (∫⁻ ω, S ω ^ (2 * (m - 1)) * Q ω ∂μ))
    (hDoob : (∫⁻ ω, S ω ^ (2 * m) ∂μ) ≤ K * (∫⁻ ω, X ω ^ (2 * m) ∂μ)) :
    (∫⁻ ω, X ω ^ (2 * m) ∂μ) ≤
      (D * K ^ (1 - m⁻¹)) ^ m * (∫⁻ ω, Q ω ^ m ∂μ) := by
  have hm0 : 0 < m := zero_lt_one.trans hm
  have hb : 0 < m⁻¹ := inv_pos.mpr hm0
  have ha : 0 < 1 - m⁻¹ := sub_pos.mpr ((inv_lt_one₀ hm0).2 hm)
  let F (ω : Ω) := S ω ^ (2 * m)
  have hF : Measurable F := ENNReal.continuous_rpow_const.measurable.comp hS
  have hholder := lintegral_mul_partial_power_le (μ := μ) hF hQ ha hb (sub_add_cancel _ _)
  have hexp : 2 * m * (1 - m⁻¹) = 2 * (m - 1) := by field_simp
  have hFpower (ω : Ω) : F ω ^ (1 - m⁻¹) = S ω ^ (2 * (m - 1)) := by
    unfold F
    rw [← ENNReal.rpow_mul, hexp]
  simp only [hFpower, inv_inv] at hholder
  apply le_mul_rpow_of_le_mul_self_rpow hm hX
  calc
    _ ≤ D * (∫⁻ ω, S ω ^ (2 * (m - 1)) * Q ω ∂μ) := hIto
    _ ≤ D * ((∫⁻ ω, S ω ^ (2 * m) ∂μ) ^ (1 - m⁻¹) *
        (∫⁻ ω, Q ω ^ m ∂μ) ^ m⁻¹) := mul_right_mono hholder
    _ ≤ D * ((K * (∫⁻ ω, X ω ^ (2 * m) ∂μ)) ^ (1 - m⁻¹) *
        (∫⁻ ω, Q ω ^ m ∂μ) ^ m⁻¹) :=
      mul_right_mono (mul_left_mono (ENNReal.rpow_le_rpow hDoob ha.le))
    _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ ha.le]; ac_rfl

/-- The weighted power-mean estimate used for the terminal quadratic
variation. The weight need not have been normalized to mass one. -/
theorem lintegral_weighted_rpow_le {w f : Ω → ℝ≥0∞} (hw : Measurable w)
    (hf : Measurable f) {m : ℝ} (hm : 1 < m) :
    (∫⁻ ω, w ω * f ω ∂μ) ^ m ≤
      (∫⁻ ω, w ω ∂μ) ^ (m - 1) * (∫⁻ ω, w ω * f ω ^ m ∂μ) := by
  have hm0 : 0 < m := zero_lt_one.trans hm
  have ha : 0 < 1 - m⁻¹ := sub_pos.mpr ((inv_lt_one₀ hm0).2 hm)
  have hb : 0 < m⁻¹ := inv_pos.mpr hm0
  have h := lintegral_mul_partial_power_le (μ := μ.withDensity w) (F := fun _ => 1)
    measurable_const hf ha hb (sub_add_cancel _ _)
  simp only [ENNReal.one_rpow, one_mul, inv_inv] at h
  have hp := ENNReal.rpow_le_rpow h hm0.le
  have he : (1 - m⁻¹) * m = m - 1 := by field_simp
  rw [ENNReal.mul_rpow_of_nonneg _ _ hm0.le, ← ENNReal.rpow_mul, he,
    ← ENNReal.rpow_mul, inv_mul_cancel₀ hm0.ne', ENNReal.rpow_one] at hp
  rw [lintegral_withDensity_eq_lintegral_mul μ hw hf,
    lintegral_withDensity_eq_lintegral_mul μ hw (measurable_const (a := (1 : ℝ≥0∞))),
    lintegral_withDensity_eq_lintegral_mul μ hw
      (show Measurable (fun ω => f ω ^ m) from ENNReal.continuous_rpow_const.measurable.comp hf)] at hp
  simpa only [Pi.mul_apply, mul_one] using hp

/-- A uniform stopped power inequality passes to the original terminal
random variable by Fatou's lemma. This theorem takes the stopped Itô and
Doob inequalities, together with the bracket domination under stopping. -/
theorem terminal_even_moment_le_of_localized_power_identities {m : ℝ} (hm : 1 < m)
    {X Q : Ω → ℝ≥0∞} {Xn Sn Qn : ℕ → Ω → ℝ≥0∞}
    (hXn : ∀ n, Measurable (Xn n)) (hSn : ∀ n, Measurable (Sn n))
    (hQn : ∀ n, Measurable (Qn n)) {D K : ℝ≥0∞}
    (hconv : ∀ᵐ ω ∂μ, Tendsto (fun n => Xn n ω) atTop (𝓝 (X ω)))
    (hdom : ∀ n, Qn n ≤ᵐ[μ] Q)
    (hFin : ∀ n, (∫⁻ ω, Xn n ω ^ (2 * m) ∂μ) ≠ ⊤)
    (hIto : ∀ n, (∫⁻ ω, Xn n ω ^ (2 * m) ∂μ) ≤
      D * (∫⁻ ω, Sn n ω ^ (2 * (m - 1)) * Qn n ω ∂μ))
    (hDoob : ∀ n, (∫⁻ ω, Sn n ω ^ (2 * m) ∂μ) ≤
      K * (∫⁻ ω, Xn n ω ^ (2 * m) ∂μ)) :
    (∫⁻ ω, X ω ^ (2 * m) ∂μ) ≤
      (D * K ^ (1 - m⁻¹)) ^ m * (∫⁻ ω, Q ω ^ m ∂μ) := by
  have hm0 : 0 ≤ m := (zero_lt_one.trans hm).le
  have hF (n : ℕ) : Measurable (fun ω => Xn n ω ^ (2 * m)) :=
    ENNReal.continuous_rpow_const.measurable.comp (hXn n)
  have hlim : (fun ω => X ω ^ (2 * m)) =ᵐ[μ]
      fun ω => liminf (fun n => Xn n ω ^ (2 * m)) atTop := by
    filter_upwards [hconv] with ω hω
    exact ((ENNReal.continuous_rpow_const.tendsto (X ω)).comp hω).liminf_eq.symm
  let R := (D * K ^ (1 - m⁻¹)) ^ m * (∫⁻ ω, Q ω ^ m ∂μ)
  have hn (n : ℕ) : (∫⁻ ω, Xn n ω ^ (2 * m) ∂μ) ≤ R := by
    refine (terminal_even_moment_le_of_power_identity_and_doob hm (hSn n) (hQn n)
      (hFin n) (hIto n) (hDoob n)).trans (mul_right_mono (lintegral_mono_ae ?_))
    exact (hdom n).mono fun ω h => ENNReal.rpow_le_rpow h hm0
  calc
    _ = ∫⁻ ω, liminf (fun n => Xn n ω ^ (2 * m)) atTop ∂μ := lintegral_congr_ae hlim
    _ ≤ liminf (fun n => ∫⁻ ω, Xn n ω ^ (2 * m) ∂μ) atTop := lintegral_liminf_le hF
    _ ≤ liminf (fun _ : ℕ => R) atTop := liminf_le_liminf (Eventually.of_forall hn)
    _ = R := liminf_const R

/-- A measurable norm envelope and Doob's strong moment bound on a continuous
martingale horizon. The envelope is constructed from dyadic observations,
and almost-sure path continuity makes it dominate every observation at once. -/
theorem exists_continuous_martingale_norm_envelope [IsFiniteMeasure μ]
    {𝒢 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {X : ℝ≥0 → Ω → ℝ}
    (hX : Martingale X 𝒢 μ) (T : ℝ≥0)
    (hcont : ∀ᵐ ω ∂μ, ContinuousOn (fun t => X t ω) (Icc 0 T))
    {p : ℝ} (hp : 1 < p) :
    ∃ S : Ω → ℝ≥0∞, Measurable S ∧
      (∀ᵐ ω ∂μ, ∀ t ≤ T, ‖X t ω‖ₑ ≤ S ω) ∧
      (∫⁻ ω, S ω ^ p ∂μ) ≤ ENNReal.ofReal (p / (p - 1)) ^ p *
        (∫⁻ ω, ‖X T ω‖ₑ ^ p ∂μ) := by
  let G := uniformDyadicGrids T
  let V (j : ℕ) (ω : Ω) :=
    (Finset.range (2 ^ j + 1)).sup' Finset.nonempty_range_add_one (fun k => ‖X (G.grid j k) ω‖)
  let U (j : ℕ) (ω : Ω) := ENNReal.ofReal (V j ω)
  let S (ω : Ω) := ⨆ j, U j ω
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hXm (t : ℝ≥0) : Measurable (X t) :=
    ((hX.stronglyMeasurable t).mono (𝒢.le t)).measurable
  have hVm (j : ℕ) : Measurable (V j) :=
    Finset.measurable_range_sup'' fun k _ => (hXm (G.grid j k)).norm
  have hUm (j : ℕ) : Measurable (U j) := (hVm j).ennreal_ofReal
  have hSm : Measurable S := Measurable.iSup hUm
  have horig (j k : ℕ) (ω : Ω) (hk : k ≤ 2 ^ j) : ‖X (G.grid j k) ω‖ ≤ V j ω :=
    Finset.le_sup' (f := fun k => ‖X (G.grid j k) ω‖)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  have hV0 (j : ℕ) (ω : Ω) : 0 ≤ V j ω :=
    (norm_nonneg _).trans (horig j 0 ω (Nat.zero_le _))
  have hmono (ω : Ω) : Monotone (fun j => U j ω) := by
    refine monotone_nat_of_le_succ fun j => ENNReal.ofReal_le_ofReal ?_
    apply Finset.sup'_le
    intro k hk
    have hk' : k ≤ 2 ^ j := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have he : G.grid j k = G.grid (j + 1) (2 * k) := by
      simpa only [pow_one] using G.vertex_at_refinement j 1 k
    rw [he]
    apply horig
    rw [pow_succ']
    exact Nat.mul_le_mul_left _ hk'
  have hgrid (j k : ℕ) (ω : Ω) (hk : k ≤ 2 ^ j) : ‖X (G.grid j k) ω‖ₑ ≤ S ω := by
    rw [← ofReal_norm]
    exact (ENNReal.ofReal_le_ofReal (horig j k ω hk)).trans (le_iSup (fun i => U i ω) j)
  have hSdom : ∀ᵐ ω ∂μ, ∀ t ≤ T, ‖X t ω‖ₑ ≤ S ω := by
    filter_upwards [hcont] with ω hω
    intro t ht
    rcases eq_or_lt_of_le (zero_le : 0 ≤ t) with ht0 | htpos
    · rw [← ht0, ← uniform_dyadic_first_vertex T 0]
      exact hgrid 0 0 ω (Nat.zero_le _)
    have hlim := tendsto_uniformDyadicStep hω (show t ∈ Ioc 0 T from ⟨htpos, ht⟩)
    apply le_of_tendsto' ((continuous_enorm.tendsto (X t ω)).comp hlim)
    intro j
    obtain ⟨k, hk, _, he⟩ := uniformDyadicStep_eq_coeff (fun s => X s ω) ⟨htpos, ht⟩ j
    change ‖uniformDyadicStep T j (fun s => X s ω) t‖ₑ ≤ _
    rw [he]
    exact hgrid j k ω hk.le
  have hlevel (j : ℕ) : (∫⁻ ω, U j ω ^ p ∂μ) ≤ ENNReal.ofReal (p / (p - 1)) ^ p *
      (∫⁻ ω, ‖X T ω‖ₑ ^ p ∂μ) := by
    have hD := (hX.indexComap (G.grid j).monotone).eLpNorm_norm_runMax_le hp (2 ^ j)
    change eLpNorm (V j) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (p / (p - 1)) * eLpNorm (X (G.grid j (2 ^ j))) (ENNReal.ofReal p) μ at hD
    have hterm : G.grid j (2 ^ j) = T := uniform_dyadic_terminal_vertex T j
    rw [hterm, eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp0).ne'
      ENNReal.ofReal_ne_top (hVm j).aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp0).ne'
        ENNReal.ofReal_ne_top (hXm T).aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le] at hD
    have hpow := ENNReal.rpow_le_rpow hD hp0.le
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      one_div_mul_cancel hp0.ne', ENNReal.rpow_one, ENNReal.rpow_one] at hpow
    have he (ω : Ω) : ‖V j ω‖ₑ = U j ω := by
      rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hV0 j ω)]
    simpa only [he] using hpow
  refine ⟨S, hSm, hSdom, ?_⟩
  have hpower (ω : Ω) : S ω ^ p = ⨆ j, U j ω ^ p :=
    MeasureTheory.LpDominator.iSup_rpow_of_monotone (hmono ω) hp0.le
  calc
    _ = ∫⁻ ω, ⨆ j, U j ω ^ p ∂μ := lintegral_congr hpower
    _ = ⨆ j, ∫⁻ ω, U j ω ^ p ∂μ := lintegral_iSup
      (fun j => ENNReal.continuous_rpow_const.measurable.comp (hUm j))
      (fun _ _ hij ω => ENNReal.rpow_le_rpow (hmono ω hij) hp0.le)
    _ ≤ _ := iSup_le hlevel

/-- Sum of squared increments of a process along the first n grid cells. -/
def gridQuadraticSum {ι : Type*} [Preorder ι] (grid : ℕ →o ι)
    (X : ι → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, (X (grid (k + 1)) ω - X (grid k) ω) ^ 2

omit [MeasurableSpace Ω] in
/-- Discrete quadratic variation is a difference of endpoint squares minus
twice the predictable left-endpoint stochastic sum. -/
theorem gridQuadraticSum_eq_square_sub_integral {ι : Type*} [Preorder ι]
    (grid : ℕ →o ι) (X : ι → Ω → ℝ) (n : ℕ) (ω : Ω) :
    gridQuadraticSum grid X n ω = (X (grid n) ω) ^ 2 - (X (grid 0) ω) ^ 2 -
      2 * gridIntegral grid (fun k => X (grid k)) X n ω := by
  induction n with
  | zero => simp [gridQuadraticSum, gridIntegral, runningSum]
  | succ n ih =>
      have he : gridQuadraticSum grid X (n + 1) ω =
          gridQuadraticSum grid X n ω + (X (grid (n + 1)) ω - X (grid n) ω) ^ 2 := by
        simp only [gridQuadraticSum, Finset.sum_range_succ]
      rw [he, ih, gridIntegral_succ]
      simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
      ring

/-- Squared-increment sums of a bounded martingale have a uniform second
moment on any grid with a common pair of endpoints. The random compensator
must be nondecreasing almost surely at every pair of deterministic times. -/
theorem gridQuadraticSum_sq_integral_le {ι : Type*} [Preorder ι] [IsFiniteMeasure μ]
    {𝒢 : Filtration ι (inferInstance : MeasurableSpace Ω)} {X C : ι → Ω → ℝ}
    (grid : ℕ →o ι) (hX : Martingale X 𝒢 μ)
    (hC : Martingale (fun t => X t * X t - C t) 𝒢 μ)
    (hmono : ∀ s t, s ≤ t → C s ≤ᵐ[μ] C t)
    {B : ℝ} (hbound : ∀ t, ∀ᵐ ω ∂μ, ‖X t ω‖ ≤ B) (n : ℕ) :
    MemLp (gridQuadraticSum grid X n) 2 μ ∧
      (∫ ω, (gridQuadraticSum grid X n ω) ^ 2 ∂μ) ≤
        (2 * B ^ 4) * μ.real univ + 8 * B ^ 2 * (∫ ω, C (grid n) ω - C (grid 0) ω ∂μ) := by
  let I := gridIntegral grid (fun k => X (grid k)) X n
  let d (k : ℕ) (ω : Ω) := C (grid (k + 1)) ω - C (grid k) ω
  have hXtop (t : ι) : MemLp (X t) ⊤ μ := memLp_top_of_bound
    ((hX.stronglyMeasurable t).mono (𝒢.le t)).aestronglyMeasurable B (hbound t)
  have hX₂ (t : ι) : MemLp (X t) 2 μ := (hXtop t).mono_exponent le_top
  have hsq (t : ι) : MemLp (fun ω => X t ω ^ 2) ⊤ μ := by
    simp only [pow_two]
    change MemLp (X t * X t) ⊤ μ
    exact (hXtop t).mul (hXtop t)
  have hI : MemLp I 2 μ := grid_integral_memLp_two grid hX₂ (fun k => hXtop (grid k)) n
  have hCint (t : ι) : Integrable (C t) μ := by
    have h := (hX₂ t).integrable_sq
    simp only [pow_two] at h
    change Integrable (X t * X t) μ at h
    simpa only [sub_sub_cancel] using h.sub (hC.integrable t)
  have hd (k : ℕ) : Integrable (d k) μ := (hCint _).sub (hCint _)
  have hIntW (k : ℕ) : Integrable (fun ω => X (grid k) ω ^ 2 * d k ω) μ :=
    memLp_one_iff_integrable.1 ((hsq (grid k)).mul (memLp_one_iff_integrable.2 (hd k)))
  have hsquare (t : ι) : ∀ᵐ ω ∂μ, X t ω ^ 2 ≤ B ^ 2 := by
    filter_upwards [hbound t] with ω hω
    rw [Real.norm_eq_abs] at hω
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hω 2
  have hIenergy : (∫ ω, I ω ^ 2 ∂μ) ≤ B ^ 2 *
      (∫ ω, C (grid n) ω - C (grid 0) ω ∂μ) := by
    rw [grid_integral_square_compensator grid hX hX₂ hC
      (fun k => hX.stronglyMeasurable (grid k)) (fun k => hXtop (grid k)) n]
    change (∑ k ∈ Finset.range n, ∫ ω, X (grid k) ω ^ 2 * d k ω ∂μ) ≤ _
    calc
      _ ≤ ∑ k ∈ Finset.range n, ∫ ω, B ^ 2 * d k ω ∂μ := by
        apply Finset.sum_le_sum
        intro k _
        refine integral_mono_ae (hIntW k) ((hd k).const_mul _) ?_
        filter_upwards [hsquare (grid k), hmono _ _ (grid.monotone k.le_succ)] with ω hx hc
        exact mul_le_mul_of_nonneg_right hx (sub_nonneg.mpr hc)
      _ = B ^ 2 * ∑ k ∈ Finset.range n, ∫ ω, d k ω ∂μ := by
        simp only [integral_const_mul, Finset.mul_sum]
      _ = _ := by
        rw [← integral_finsetSum _ (fun k _ => hd k)]
        congr 1
        apply integral_congr_ae
        apply Eventually.of_forall
        intro ω
        exact Finset.sum_range_sub (fun k => C (grid k) ω) n
  have hQ₂ : MemLp (gridQuadraticSum grid X n) 2 μ := by
    have hdiff : MemLp (fun ω => (X (grid n) ω) ^ 2 - (X (grid 0) ω) ^ 2) 2 μ :=
      ((hsq (grid n)).mono_exponent le_top).sub ((hsq (grid 0)).mono_exponent le_top)
    rw [show gridQuadraticSum grid X n =
      fun ω => (X (grid n) ω) ^ 2 - (X (grid 0) ω) ^ 2 - 2 * I ω from
        funext (gridQuadraticSum_eq_square_sub_integral grid X n)]
    exact hdiff.sub (hI.const_mul 2)
  refine ⟨hQ₂, ?_⟩
  have hdet (x y z : ℝ) (hx : x ^ 2 ≤ B ^ 2) (hy : y ^ 2 ≤ B ^ 2) :
      (x ^ 2 - y ^ 2 - 2 * z) ^ 2 ≤ 2 * B ^ 4 + 8 * z ^ 2 := by
    have hD : |x ^ 2 - y ^ 2| ≤ B ^ 2 := by
      apply abs_le.2
      constructor <;> linarith [sq_nonneg x, sq_nonneg y]
    have hD₂ := pow_le_pow_left₀ (abs_nonneg _) hD 2
    rw [sq_abs, ← pow_mul] at hD₂
    norm_num at hD₂
    nlinarith [sq_nonneg (x ^ 2 - y ^ 2 + 2 * z)]
  calc
    _ ≤ ∫ ω, 2 * B ^ 4 + 8 * I ω ^ 2 ∂μ := by
      refine integral_mono_ae hQ₂.integrable_sq ((integrable_const _).add (hI.integrable_sq.const_mul _)) ?_
      filter_upwards [hsquare (grid n), hsquare (grid 0)] with ω hn h0
      rw [gridQuadraticSum_eq_square_sub_integral]
      exact hdet _ _ _ hn h0
    _ = (2 * B ^ 4) * μ.real univ + 8 * (∫ ω, I ω ^ 2 ∂μ) := by
      rw [integral_add (integrable_const _) (hI.integrable_sq.const_mul _), integral_const,
        integral_const_mul, smul_eq_mul, mul_comm (μ.real univ)]
    _ ≤ _ := by
      rw [mul_assoc 8]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hIenergy (by norm_num))

private theorem integrable_compensator_of_square_martingale {ι : Type*} [Preorder ι]
    {𝒢 : Filtration ι (inferInstance : MeasurableSpace Ω)} {X C : ι → Ω → ℝ}
    (hX₂ : ∀ t, MemLp (X t) 2 μ)
    (hC : Martingale (fun t => X t * X t - C t) 𝒢 μ) (t : ι) : Integrable (C t) μ := by
  have h := (hX₂ t).integrable_sq
  simp only [pow_two] at h
  change Integrable (X t * X t) μ at h
  simpa only [sub_sub_cancel] using h.sub (hC.integrable t)

/-- A bounded predictable multiplier identifies the expected weighted
square increment with the expected weighted compensator increment. -/
theorem integral_predictable_mul_increment_sq_eq {ι : Type*} [Preorder ι] [IsFiniteMeasure μ]
    {𝒢 : Filtration ι (inferInstance : MeasurableSpace Ω)} {X C : ι → Ω → ℝ}
    (hX : Martingale X 𝒢 μ) (hX₂ : ∀ t, MemLp (X t) 2 μ)
    (hC : Martingale (fun t => X t * X t - C t) 𝒢 μ)
    {s t : ι} (hst : s ≤ t) {w : Ω → ℝ} (hw : StronglyMeasurable[𝒢 s] w)
    (hwTop : MemLp w ⊤ μ) :
    (∫ ω, w ω * (X t ω - X s ω) ^ 2 ∂μ) =
      ∫ ω, w ω * (C t ω - C s ω) ∂μ := by
  let d := X t - X s
  let c := C t - C s
  have hd₂ : MemLp d 2 μ := (hX₂ t).sub (hX₂ s)
  have hD : Integrable (d * d) μ := by
    have h := hd₂.integrable_sq
    simp only [pow_two] at h
    exact h
  have hc : Integrable c μ := (integrable_compensator_of_square_martingale hX₂ hC t).sub
    (integrable_compensator_of_square_martingale hX₂ hC s)
  have hwD : Integrable (w * (d * d)) μ :=
    memLp_one_iff_integrable.1 (hwTop.mul (memLp_one_iff_integrable.2 hD))
  have hwc : Integrable (w * c) μ :=
    memLp_one_iff_integrable.1 (hwTop.mul (memLp_one_iff_integrable.2 hc))
  have hcond : μ[d * d | 𝒢 s] =ᵐ[μ] μ[c | 𝒢 s] :=
    conditional_covariance_of_compensated_product hX hX hC hX₂ hX₂ hst
  have hEq : μ[w * (d * d) | 𝒢 s] =ᵐ[μ] μ[w * c | 𝒢 s] :=
    (condExp_mul_of_stronglyMeasurable_left hw hwD hD).trans
      ((EventuallyEq.rfl.mul hcond).trans (condExp_mul_of_stronglyMeasurable_left hw hwc hc).symm)
  simp only [pow_two]
  change (∫ ω, (w * (d * d)) ω ∂μ) = ∫ ω, (w * c) ω ∂μ
  exact (integral_condExp (𝒢.le s)).symm.trans
    ((integral_congr_ae hEq).trans (integral_condExp (𝒢.le s)))

/-- Expected discrete Itô expansion on an arbitrary deterministic grid.
The predictable linear term has zero expectation. The second-order term
uses the increments of the compensator. -/
theorem integral_grid_ito_expansion {ι : Type*} [Preorder ι] [IsFiniteMeasure μ]
    {𝒢 : Filtration ι (inferInstance : MeasurableSpace Ω)} {X C : ι → Ω → ℝ}
    (grid : ℕ →o ι) (hX : Martingale X 𝒢 μ) (hX₂ : ∀ t, MemLp (X t) 2 μ)
    (hC : Martingale (fun t => X t * X t - C t) 𝒢 μ) (f f' f'' : ℝ → ℝ)
    (hf : ∀ k, Integrable (fun ω => f (X (grid k) ω)) μ)
    (hf' : ∀ k, StronglyMeasurable[𝒢 (grid k)] (fun ω => f' (X (grid k) ω)) ∧
      MemLp (fun ω => f' (X (grid k) ω)) ⊤ μ)
    (hf'' : ∀ k, StronglyMeasurable[𝒢 (grid k)] (fun ω => f'' (X (grid k) ω)) ∧
      MemLp (fun ω => f'' (X (grid k) ω)) ⊤ μ) (n : ℕ) :
    (∫ ω, f (X (grid n) ω) - f (X (grid 0) ω) ∂μ) =
      (1 / 2) * (∑ k ∈ Finset.range n,
        ∫ ω, f'' (X (grid k) ω) * (C (grid (k + 1)) ω - C (grid k) ω) ∂μ) +
      ∫ ω, ∑ k ∈ Finset.range n,
        MathFin.discreteTaylorRemainder f f' f'' (X (grid k) ω) (X (grid (k + 1)) ω) ∂μ := by
  let d (k : ℕ) := X (grid (k + 1)) - X (grid k)
  let a (k : ℕ) (ω : Ω) := f' (X (grid k) ω)
  let b (k : ℕ) (ω : Ω) := f'' (X (grid k) ω)
  let L (k : ℕ) := a k * d k
  let W (k : ℕ) := b k * (d k * d k)
  let R (k : ℕ) (ω : Ω) :=
    MathFin.discreteTaylorRemainder f f' f'' (X (grid k) ω) (X (grid (k + 1)) ω)
  have hd₂ (k : ℕ) : MemLp (d k) 2 μ := (hX₂ _).sub (hX₂ _)
  have hL (k : ℕ) : Integrable (L k) μ := ((hf' k).2.mul (hd₂ k)).integrable one_le_two
  have hW (k : ℕ) : Integrable (W k) μ := by
    have hint := (hd₂ k).integrable_sq
    simp only [pow_two] at hint
    change Integrable (d k * d k) μ at hint
    exact memLp_one_iff_integrable.1 ((hf'' k).2.mul (memLp_one_iff_integrable.2 hint))
  have hR (k : ℕ) : Integrable (R k) μ := by
    rw [show R k = (fun ω => f (X (grid (k + 1)) ω) - f (X (grid k) ω) -
      L k ω - (1 / 2) * W k ω) from funext (fun ω => by
        simp only [R, MathFin.discreteTaylorRemainder, L, W, a, b, d,
          Pi.mul_apply, Pi.sub_apply, pow_two])]
    exact (((hf (k + 1)).sub (hf k)).sub (hL k)).sub ((hW k).const_mul _)
  have hL0 (k : ℕ) : (∫ ω, L k ω ∂μ) = 0 := by
    have hcancel := centered_predictable_increment
      (𝒢 := gridFiltration 𝒢 grid) (k := k) (hf' k).1 (hf' k).2 (hd₂ k)
      (conditional_mean_martingale_increment hX (grid.monotone k.le_succ))
    exact (integral_condExp (𝒢.le (grid k))).symm.trans
      ((integral_congr_ae hcancel).trans (integral_zero Ω ℝ))
  have hLsum : (∫ ω, ∑ k ∈ Finset.range n, L k ω ∂μ) = 0 := by
    rw [integral_finsetSum _ (fun k _ => hL k)]
    exact Finset.sum_eq_zero fun k _ => hL0 k
  have hWsum : (∫ ω, ∑ k ∈ Finset.range n, W k ω ∂μ) =
      ∑ k ∈ Finset.range n, ∫ ω, b k ω * (C (grid (k + 1)) ω - C (grid k) ω) ∂μ := by
    rw [integral_finsetSum _ (fun k _ => hW k)]
    apply Finset.sum_congr rfl
    intro k _
    simpa only [pow_two, d, W, Pi.mul_apply, Pi.sub_apply] using
      integral_predictable_mul_increment_sq_eq hX hX₂ hC (grid.monotone k.le_succ)
        (hf'' k).1 (hf'' k).2
  have he (ω : Ω) : f (X (grid n) ω) - f (X (grid 0) ω) =
      (∑ k ∈ Finset.range n, L k ω) +
        (1 / 2) * (∑ k ∈ Finset.range n, W k ω) + ∑ k ∈ Finset.range n, R k ω := by
    simpa only [L, a, W, b, d, pow_two, Pi.mul_apply, Pi.sub_apply, R] using
      MathFin.discrete_ito_formula n (fun k => X (grid k) ω) f f' f''
  have hLi := integrable_finsetSum (Finset.range n) (fun k _ => hL k)
  have hWi := (integrable_finsetSum (Finset.range n) (fun k _ => hW k)).const_mul (1 / 2)
  have hRi := integrable_finsetSum (Finset.range n) (fun k _ => hR k)
  let Ls (ω : Ω) := ∑ k ∈ Finset.range n, L k ω
  let Ws (ω : Ω) := (1 / 2) * ∑ k ∈ Finset.range n, W k ω
  let Rs (ω : Ω) := ∑ k ∈ Finset.range n, R k ω
  calc
    _ = ∫ ω, (Ls + Ws) ω + Rs ω ∂μ := integral_congr_ae (Eventually.of_forall he)
    _ = (∫ ω, Ls ω ∂μ) + (∫ ω, Ws ω ∂μ) + (∫ ω, Rs ω ∂μ) := by
      rw [integral_add (hLi.add hWi) hRi]
      change (∫ ω, Ls ω + Ws ω ∂μ) + (∫ ω, Rs ω ∂μ) = _
      rw [integral_add hLi hWi]
    _ = _ := by
      dsimp only [Ls, Ws, Rs]
      rw [hLsum, zero_add, integral_const_mul, hWsum]

#print axioms gridQuadraticSum_eq_square_sub_integral
#print axioms gridQuadraticSum_sq_integral_le
#print axioms integral_predictable_mul_increment_sq_eq
#print axioms integral_grid_ito_expansion
#print axioms exists_continuous_martingale_norm_envelope
#print axioms terminal_even_moment_le_of_power_identity_and_doob
#print axioms lintegral_weighted_rpow_le
#print axioms terminal_even_moment_le_of_localized_power_identities

end RoughHeston
