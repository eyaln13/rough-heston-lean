import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
Stochastic foundations for the rough Heston draft.

The simple stochastic integral here is the running sum of predictable weights
times driving increments, indexed by a discrete time grid. We prove the
martingale identity, the compensated product identity, and the cross-isometry
on that grid. No continuous-time stochastic integral is assumed or defined
by these results. The last two lemmas handle the zero-square-martingale
and continuity arguments used in the common-driver identification.
-/

open MeasureTheory Filter Set
open scoped BigOperators MeasureTheory ProbabilityTheory

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

def runningSum (d : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  ∑ k ∈ Finset.range n, d k

@[simp] theorem runningSum_zero (d : ℕ → Ω → ℝ) : runningSum d 0 = 0 := by
  simp [runningSum]

theorem runningSum_succ (d : ℕ → Ω → ℝ) (n : ℕ) :
    runningSum d (n + 1) = runningSum d n + d n := by
  simp [runningSum, Finset.sum_range_succ]

theorem adapted_runningSum {𝒢 : Filtration ℕ m} {d : ℕ → Ω → ℝ}
    (hd : ∀ k, StronglyMeasurable[𝒢 (k + 1)] (d k)) :
    StronglyAdapted 𝒢 (runningSum d) := by
  intro n
  induction n with
  | zero =>
    change StronglyMeasurable[𝒢 0] (fun _ : Ω => (0 : ℝ))
    exact stronglyMeasurable_const
  | succ n ih =>
    rw [runningSum_succ]
    exact (ih.mono (𝒢.mono n.le_succ)).add (hd n)

theorem memLp_runningSum {d : ℕ → Ω → ℝ} {p : ENNReal}
    (hd : ∀ k, MemLp (d k) p μ) (n : ℕ) : MemLp (runningSum d n) p μ := by
  induction n with
  | zero => simp
  | succ n ih => exact runningSum_succ d n ▸ ih.add (hd n)

theorem integrable_runningSum {d : ℕ → Ω → ℝ}
    (hd : ∀ k, Integrable (d k) μ) (n : ℕ) : Integrable (runningSum d n) μ := by
  induction n with
  | zero => rw [runningSum_zero]; exact integrable_zero Ω ℝ μ
  | succ n ih =>
    rw [runningSum_succ]
    exact ih.add (hd n)

theorem runningSum_martingale [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m} {d : ℕ → Ω → ℝ}
    (had : ∀ k, StronglyMeasurable[𝒢 (k + 1)] (d k))
    (hint : ∀ k, Integrable (d k) μ)
    (hcenter : ∀ k, μ[d k | 𝒢 k] =ᵐ[μ] 0) :
    Martingale (runningSum d) 𝒢 μ := by
  refine martingale_of_condExp_sub_eq_zero_nat (adapted_runningSum had)
    (integrable_runningSum hint) ?_
  intro k
  rw [runningSum_succ, add_sub_cancel_left]
  exact hcenter k

section FiniteMeasure

variable [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m}

private theorem integrable_mul_of_memLp_two {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) : Integrable (f * g) μ :=
  (show MemLp (f * g) 1 μ from hf.mul hg).integrable (by norm_num)

/-- Conditional covariance of two increments given the past. -/
noncomputable def stepCovariance (μ : Measure Ω) (𝒢 : Filtration ℕ m)
    (d e : ℕ → Ω → ℝ) (k : ℕ) : Ω → ℝ :=
  μ[d k * e k | 𝒢 k]

private theorem condExp_product_increment {x y d e : Ω → ℝ} {k : ℕ}
    (hx : StronglyMeasurable[𝒢 k] x) (hy : StronglyMeasurable[𝒢 k] y)
    (hx₂ : MemLp x 2 μ) (hy₂ : MemLp y 2 μ) (hd₂ : MemLp d 2 μ) (he₂ : MemLp e 2 μ)
    (hd : μ[d | 𝒢 k] =ᵐ[μ] 0) (he : μ[e | 𝒢 k] =ᵐ[μ] 0) :
    μ[x * e + y * d + (d * e - μ[d * e | 𝒢 k]) | 𝒢 k] =ᵐ[μ] 0 := by
  have hxe := integrable_mul_of_memLp_two hx₂ he₂
  have hyd := integrable_mul_of_memLp_two hy₂ hd₂
  have hde := integrable_mul_of_memLp_two hd₂ he₂
  have hh₁ := condExp_mul_of_stronglyMeasurable_left hx hxe
    (he₂.integrable (by norm_num))
  have hh₂ := condExp_mul_of_stronglyMeasurable_left hy hyd
    (hd₂.integrable (by norm_num))
  have hh₃ := condExp_sub hde (integrable_condExp (f := d * e) (m := 𝒢 k)) (𝒢 k)
  have hcint : Integrable (μ[d * e | 𝒢 k]) μ := integrable_condExp
  have hh₄ := condExp_add (hxe.add hyd) (hde.sub hcint) (𝒢 k)
  have hh₅ := condExp_add hxe hyd (𝒢 k)
  have hfix : μ[μ[d * e | 𝒢 k] | 𝒢 k] = μ[d * e | 𝒢 k] :=
    condExp_of_stronglyMeasurable (𝒢.le k) stronglyMeasurable_condExp integrable_condExp
  filter_upwards [hh₁, hh₂, hh₃, hh₄, hh₅, hd, he] with ω h₁ h₂ h₃ h₄ h₅ hdz hez
  simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.zero_apply] at *
  rw [h₄, h₅, h₁, h₂, h₃, hfix, hez, hdz]
  ring

/-- The product of two simple stochastic integrals minus the sum of their
conditional increment covariances is itself a martingale. -/
theorem compensated_running_product_martingale {d e : ℕ → Ω → ℝ}
    (hdA : ∀ k, StronglyMeasurable[𝒢 (k + 1)] (d k))
    (heA : ∀ k, StronglyMeasurable[𝒢 (k + 1)] (e k))
    (hd₂ : ∀ k, MemLp (d k) 2 μ) (he₂ : ∀ k, MemLp (e k) 2 μ)
    (hd : ∀ k, μ[d k | 𝒢 k] =ᵐ[μ] 0) (he : ∀ k, μ[e k | 𝒢 k] =ᵐ[μ] 0) :
    Martingale
      (fun n => runningSum d n * runningSum e n - runningSum (stepCovariance μ 𝒢 d e) n)
      𝒢 μ := by
  have hcA (k : ℕ) : StronglyMeasurable[𝒢 (k + 1)] (stepCovariance μ 𝒢 d e k) :=
    stronglyMeasurable_condExp.mono (𝒢.mono k.le_succ)
  have hcint (k : ℕ) : Integrable (stepCovariance μ 𝒢 d e k) μ := integrable_condExp
  refine martingale_of_condExp_sub_eq_zero_nat
    (fun k => (((adapted_runningSum hdA) k).mul ((adapted_runningSum heA) k)).sub
      ((adapted_runningSum hcA) k))
    (fun k => (integrable_mul_of_memLp_two (memLp_runningSum hd₂ k)
      (memLp_runningSum he₂ k)).sub (integrable_runningSum hcint k)) ?_
  intro k
  have hsplit :
      (runningSum d (k + 1) * runningSum e (k + 1) -
          runningSum (stepCovariance μ 𝒢 d e) (k + 1)) -
        (runningSum d k * runningSum e k - runningSum (stepCovariance μ 𝒢 d e) k) =
      runningSum d k * e k + runningSum e k * d k +
        (d k * e k - μ[d k * e k | 𝒢 k]) := by
    simp only [runningSum_succ, stepCovariance]
    ring
  rw [hsplit]
  exact condExp_product_increment ((adapted_runningSum hdA) k)
    ((adapted_runningSum heA) k) (memLp_runningSum hd₂ k) (memLp_runningSum he₂ k)
    (hd₂ k) (he₂ k) (hd k) (he k)

/-- Terminal cross-isometry for centered increments on a time grid. -/
theorem runningSum_cross_isometry {d e : ℕ → Ω → ℝ}
    (hdA : ∀ k, StronglyMeasurable[𝒢 (k + 1)] (d k))
    (heA : ∀ k, StronglyMeasurable[𝒢 (k + 1)] (e k))
    (hd₂ : ∀ k, MemLp (d k) 2 μ) (he₂ : ∀ k, MemLp (e k) 2 μ)
    (hd : ∀ k, μ[d k | 𝒢 k] =ᵐ[μ] 0) (he : ∀ k, μ[e k | 𝒢 k] =ᵐ[μ] 0) (n : ℕ) :
    (∫ ω, runningSum d n ω * runningSum e n ω ∂μ) =
      ∫ ω, runningSum (stepCovariance μ 𝒢 d e) n ω ∂μ := by
  have hm := compensated_running_product_martingale hdA heA hd₂ he₂ hd he
  have h := hm.setIntegral_eq (Nat.zero_le n) (MeasurableSet.univ : MeasurableSet[𝒢 0] Set.univ)
  simp only [runningSum_zero, Pi.zero_apply, zero_mul, sub_zero, Measure.restrict_univ,
    integral_zero, Pi.sub_apply, Pi.mul_apply] at h
  have hp : Integrable (fun ω => runningSum d n ω * runningSum e n ω) μ :=
    integrable_mul_of_memLp_two (memLp_runningSum hd₂ n) (memLp_runningSum he₂ n)
  have hcint : Integrable (runningSum (stepCovariance μ 𝒢 d e) n) μ :=
    integrable_runningSum (fun _ => integrable_condExp) n
  rw [integral_sub hp hcint] at h
  exact sub_eq_zero.mp h.symm

/-- A predictable weight can be pulled out of the conditional mean. -/
theorem centered_predictable_increment {a d : Ω → ℝ} {k : ℕ}
    (ha : StronglyMeasurable[𝒢 k] a) (haTop : MemLp a ⊤ μ) (hd₂ : MemLp d 2 μ)
    (hd : μ[d | 𝒢 k] =ᵐ[μ] 0) : μ[a * d | 𝒢 k] =ᵐ[μ] 0 := by
  have had₂ : MemLp (a * d) 2 μ := haTop.mul hd₂
  have hpull := condExp_mul_of_stronglyMeasurable_left ha
    (had₂.integrable (by norm_num)) (hd₂.integrable (by norm_num))
  filter_upwards [hpull, hd] with ω h hzero
  simp [h, Pi.mul_apply, hzero]

omit [IsFiniteMeasure μ] in
/-- Two predictable weights multiply the conditional covariance. -/
theorem predictable_increment_covariance {a b d e : Ω → ℝ} {k : ℕ}
    (ha : StronglyMeasurable[𝒢 k] a) (hb : StronglyMeasurable[𝒢 k] b)
    (haTop : MemLp a ⊤ μ) (hbTop : MemLp b ⊤ μ)
    (hd₂ : MemLp d 2 μ) (he₂ : MemLp e 2 μ) :
    μ[(a * d) * (b * e) | 𝒢 k] =ᵐ[μ] (a * b) * μ[d * e | 𝒢 k] := by
  have hde : MemLp (d * e) 1 μ := hd₂.mul he₂
  have hcoe : MemLp (a * b) ⊤ μ := haTop.mul hbTop
  have hprod : MemLp ((a * b) * (d * e)) 1 μ := hcoe.mul hde
  rw [show (a * d) * (b * e) = (a * b) * (d * e) by ring]
  exact condExp_mul_of_stronglyMeasurable_left (ha.mul hb)
    (memLp_one_iff_integrable.mp hprod) (memLp_one_iff_integrable.mp hde)

end FiniteMeasure

/-- If the square of a real process is a martingale and starts at zero,
the process vanishes almost surely at each later fixed time. -/
theorem zero_of_square_martingale {ι : Type*} [Preorder ι] [IsFiniteMeasure μ]
    {𝒢 : Filtration ι m} {X : ι → Ω → ℝ} {s t : ι}
    (h : Martingale (fun u ω => X u ω ^ 2) 𝒢 μ) (hst : s ≤ t)
    (hs : X s =ᵐ[μ] 0) : X t =ᵐ[μ] 0 := by
  have he := h.setIntegral_eq hst (MeasurableSet.univ : MeasurableSet[𝒢 s] Set.univ)
  simp only [Measure.restrict_univ] at he
  have hsint : (∫ ω, X s ω ^ 2 ∂μ) = 0 := by
    have heq : (fun ω => X s ω ^ 2) =ᵐ[μ] 0 := by
      filter_upwards [hs] with ω hω
      simp [hω]
    simpa using integral_congr_ae heq
  have hzero := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall (fun ω => sq_nonneg (X t ω))) (h.integrable t)).mp
    (he.symm.trans hsint)
  filter_upwards [hzero] with ω hω
  simpa using hω

/-- Equality almost surely at each time in a countable dense set implies
indistinguishability if both sample paths are almost surely continuous. -/
theorem indistinguishable_of_ae_eq_on_dense {ι : Type*} [TopologicalSpace ι]
    {D : Set ι} (hD : D.Countable) (hdense : Dense D) {X Y : ι → Ω → ℝ}
    (hX : ∀ᵐ ω ∂μ, Continuous (fun t => X t ω))
    (hY : ∀ᵐ ω ∂μ, Continuous (fun t => Y t ω))
    (heq : ∀ t ∈ D, X t =ᵐ[μ] Y t) :
    ∀ᵐ ω ∂μ, ∀ t, X t ω = Y t ω := by
  have : Countable D := hD.to_subtype
  have ha : ∀ᵐ ω ∂μ, ∀ t : D, X (t : ι) ω = Y (t : ι) ω :=
    ae_all_iff.2 (fun t => heq t t.property)
  filter_upwards [hX, hY, ha] with ω hcX hcY h
  intro t
  have hc : IsClosed {u | X u ω = Y u ω} := isClosed_eq hcX hcY
  have hi : D ⊆ {u | X u ω = Y u ω} := fun u hu => h ⟨u, hu⟩
  exact (closure_minimal hi hc) (hdense t)

/-- Centering an increment of a martingale works for any ordered time set. -/
theorem conditional_mean_martingale_increment {ι : Type*} [Preorder ι]
    {𝒢 : Filtration ι m} {X : ι → Ω → ℝ}
    (h : Martingale X 𝒢 μ) {s t : ι} (hst : s ≤ t) :
    μ[X t - X s | 𝒢 s] =ᵐ[μ] 0 := by
  have hdiff := condExp_sub (h.integrable t) (h.integrable s) (𝒢 s)
  filter_upwards [hdiff, h.condExp_ae_eq hst, h.condExp_ae_eq (le_refl s)]
    with ω hω htω hsω
  simp [hω, Pi.sub_apply, htω, hsω]

/-- The compensated-product martingale property identifies conditional
covariances of increments without using an Itô formula. In the application
C is the bracket candidate, so X * Y - C is the process tested in the
martingale problem. -/
theorem conditional_covariance_of_compensated_product
    {ι : Type*} [Preorder ι] [IsFiniteMeasure μ] {𝒢 : Filtration ι m} {X Y C : ι → Ω → ℝ}
    (hX : Martingale X 𝒢 μ) (hY : Martingale Y 𝒢 μ)
    (hXY : Martingale (fun t => X t * Y t - C t) 𝒢 μ)
    (hX₂ : ∀ t, MemLp (X t) 2 μ) (hY₂ : ∀ t, MemLp (Y t) 2 μ)
    {s t : ι} (hst : s ≤ t) :
    μ[(X t - X s) * (Y t - Y s) | 𝒢 s] =ᵐ[μ] μ[C t - C s | 𝒢 s] := by
  let d := X t - X s
  let e := Y t - Y s
  let P := fun u => X u * Y u - C u
  have hd := conditional_mean_martingale_increment hX hst
  have he := conditional_mean_martingale_increment hY hst
  have hP := conditional_mean_martingale_increment hXY hst
  have hd₂ : MemLp d 2 μ := (hX₂ t).sub (hX₂ s)
  have he₂ : MemLp e 2 μ := (hY₂ t).sub (hY₂ s)
  have hde := integrable_mul_of_memLp_two hd₂ he₂
  have hc (u : ι) : Integrable (C u) μ := by
    have hh := (integrable_mul_of_memLp_two (hX₂ u) (hY₂ u)).sub (hXY.integrable u)
    simpa only [sub_sub_cancel] using hh
  have hxe := integrable_mul_of_memLp_two (hX₂ s) he₂
  have hyd := integrable_mul_of_memLp_two (hY₂ s) hd₂
  have hxpull := condExp_mul_of_stronglyMeasurable_left (hX.stronglyMeasurable s)
    hxe (he₂.integrable (by norm_num))
  have hypull := condExp_mul_of_stronglyMeasurable_left (hY.stronglyMeasurable s)
    hyd (hd₂.integrable (by norm_num))
  have hPdiff : Integrable (P t - P s) μ := (hXY.integrable t).sub (hXY.integrable s)
  have hsplit : d * e - (C t - C s) = (P t - P s) - X s * e - Y s * d := by
    dsimp [d, e, P]
    ring
  have h₁ := condExp_sub hde ((hc t).sub (hc s)) (𝒢 s)
  rw [hsplit] at h₁
  have h₂ := condExp_sub (hPdiff.sub hxe) hyd (𝒢 s)
  have h₃ := condExp_sub hPdiff hxe (𝒢 s)
  filter_upwards [h₁, h₂, h₃, hd, he, hP, hxpull, hypull] with ω
    h₁ω h₂ω h₃ω hdω heω hPω hxω hyω
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.zero_apply] at *
  change μ[d * e | 𝒢 s] ω = μ[C t - C s | 𝒢 s] ω
  change μ[d | 𝒢 s] ω = 0 at hdω
  change μ[e | 𝒢 s] ω = 0 at heω
  change μ[P t - P s | 𝒢 s] ω = 0 at hPω
  rw [h₂ω, h₃ω, hPω, hxω, hyω, hdω, heω] at h₁ω
  linarith

/-- Sample a filtration along a deterministic nondecreasing grid. -/
def gridFiltration {ι : Type*} [Preorder ι] (𝒢 : Filtration ι m)
    (grid : ℕ →o ι) : Filtration ℕ m :=
  ⟨fun n => 𝒢 (grid n), fun _ _ h => 𝒢.mono (grid.monotone h), fun n => 𝒢.le (grid n)⟩

/-- The simple stochastic integral for predictable coefficients on a
deterministic time grid. -/
def gridIntegral {ι : Type*} [Preorder ι] (grid : ℕ →o ι)
    (weight : ℕ → Ω → ℝ) (X : ι → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  runningSum (fun k => weight k * (X (grid (k + 1)) - X (grid k))) n

/-- Simple stochastic integration preserves the martingale property. -/
theorem grid_integral_martingale {ι : Type*} [Preorder ι] [IsFiniteMeasure μ]
    {𝒢 : Filtration ι m} (grid : ℕ →o ι) {X : ι → Ω → ℝ}
    (hX : Martingale X 𝒢 μ) (hX₂ : ∀ t, MemLp (X t) 2 μ)
    {a : ℕ → Ω → ℝ} (ha : ∀ k, StronglyMeasurable[𝒢 (grid k)] (a k))
    (haTop : ∀ k, MemLp (a k) ⊤ μ) :
    Martingale (gridIntegral grid a X) (gridFiltration 𝒢 grid) μ := by
  have hle (k : ℕ) : grid k ≤ grid (k + 1) := grid.monotone k.le_succ
  apply runningSum_martingale
  · intro k
    exact ((ha k).mono (𝒢.mono (hle k))).mul
      ((hX.stronglyMeasurable _).sub ((hX.stronglyMeasurable _).mono (𝒢.mono (hle k))))
  · intro k
    exact ((haTop k).mul ((hX₂ _).sub (hX₂ _)) :
      MemLp (a k * (X (grid (k + 1)) - X (grid k))) 2 μ).integrable (by norm_num)
  · intro k
    exact centered_predictable_increment (𝒢 := gridFiltration 𝒢 grid) (k := k)
      (ha k) (haTop k) ((hX₂ _).sub (hX₂ _))
      (conditional_mean_martingale_increment hX (hle k))

/-- Cross-isometry on a deterministic grid, expressed using the increment
of a supplied bracket candidate. This is an identity about the actual
random variables defined by the grid sums, and the hypothesis on C is the
compensated-product martingale property. -/
theorem grid_integral_cross_isometry {ι : Type*} [Preorder ι] [IsFiniteMeasure μ]
    {𝒢 : Filtration ι m} (grid : ℕ →o ι) {X Y C : ι → Ω → ℝ}
    (hX : Martingale X 𝒢 μ) (hY : Martingale Y 𝒢 μ)
    (hXY : Martingale (fun t => X t * Y t - C t) 𝒢 μ)
    (hX₂ : ∀ t, MemLp (X t) 2 μ) (hY₂ : ∀ t, MemLp (Y t) 2 μ)
    {a b : ℕ → Ω → ℝ}
    (ha : ∀ k, StronglyMeasurable[𝒢 (grid k)] (a k))
    (hb : ∀ k, StronglyMeasurable[𝒢 (grid k)] (b k))
    (haTop : ∀ k, MemLp (a k) ⊤ μ) (hbTop : ∀ k, MemLp (b k) ⊤ μ) (n : ℕ) :
    (∫ ω, gridIntegral grid a X n ω * gridIntegral grid b Y n ω ∂μ) =
      ∑ k ∈ Finset.range n, ∫ ω, a k ω * b k ω *
        (C (grid (k + 1)) ω - C (grid k) ω) ∂μ := by
  let 𝒢' := gridFiltration 𝒢 grid
  let d := fun k => X (grid (k + 1)) - X (grid k)
  let e := fun k => Y (grid (k + 1)) - Y (grid k)
  let da := fun k => a k * d k
  let eb := fun k => b k * e k
  have hle (k : ℕ) : grid k ≤ grid (k + 1) := grid.monotone k.le_succ
  have hd₂ (k : ℕ) : MemLp (d k) 2 μ := (hX₂ _).sub (hX₂ _)
  have he₂ (k : ℕ) : MemLp (e k) 2 μ := (hY₂ _).sub (hY₂ _)
  have hda₂ (k : ℕ) : MemLp (da k) 2 μ := (haTop k).mul (hd₂ k)
  have heb₂ (k : ℕ) : MemLp (eb k) 2 μ := (hbTop k).mul (he₂ k)
  have hdaA (k : ℕ) : StronglyMeasurable[𝒢' (k + 1)] (da k) :=
    ((ha k).mono (𝒢.mono (hle k))).mul
      ((hX.stronglyMeasurable _).sub ((hX.stronglyMeasurable _).mono (𝒢.mono (hle k))))
  have hebA (k : ℕ) : StronglyMeasurable[𝒢' (k + 1)] (eb k) :=
    ((hb k).mono (𝒢.mono (hle k))).mul
      ((hY.stronglyMeasurable _).sub ((hY.stronglyMeasurable _).mono (𝒢.mono (hle k))))
  have hda (k : ℕ) : μ[da k | 𝒢' k] =ᵐ[μ] 0 :=
    centered_predictable_increment (𝒢 := 𝒢') (k := k) (ha k) (haTop k) (hd₂ k)
      (conditional_mean_martingale_increment hX (hle k))
  have heb (k : ℕ) : μ[eb k | 𝒢' k] =ᵐ[μ] 0 :=
    centered_predictable_increment (𝒢 := 𝒢') (k := k) (hb k) (hbTop k) (he₂ k)
      (conditional_mean_martingale_increment hY (hle k))
  have hc (u : ι) : Integrable (C u) μ := by
    have hh := (integrable_mul_of_memLp_two (hX₂ u) (hY₂ u)).sub (hXY.integrable u)
    simpa only [sub_sub_cancel] using hh
  change (∫ ω, runningSum da n ω * runningSum eb n ω ∂μ) = _
  rw [runningSum_cross_isometry hdaA hebA hda₂ heb₂ hda heb n]
  simp only [runningSum, Finset.sum_apply]
  have hstep (k : ℕ) : Integrable (stepCovariance μ 𝒢' da eb k) μ := integrable_condExp
  rw [integral_finsetSum (Finset.range n) (fun k _ => hstep k)]
  apply Finset.sum_congr rfl
  intro k _
  let c := C (grid (k + 1)) - C (grid k)
  have hcint : Integrable c μ := (hc _).sub (hc _)
  have hcLp : MemLp c 1 μ := memLp_one_iff_integrable.mpr hcint
  have habTop : MemLp (a k * b k) ⊤ μ := (haTop k).mul (hbTop k)
  have hweightC : Integrable ((a k * b k) * c) μ :=
    memLp_one_iff_integrable.mp (habTop.mul hcLp)
  have hweight := predictable_increment_covariance (𝒢 := 𝒢') (k := k)
    (ha k) (hb k) (haTop k) (hbTop k) (hd₂ k) (he₂ k)
  have hcov : μ[d k * e k | 𝒢' k] =ᵐ[μ] μ[c | 𝒢' k] :=
    conditional_covariance_of_compensated_product hX hY hXY hX₂ hY₂ (hle k)
  have hpull := condExp_mul_of_stronglyMeasurable_left ((ha k).mul (hb k)) hweightC hcint
  have hall : stepCovariance μ 𝒢' da eb k =ᵐ[μ] μ[(a k * b k) * c | 𝒢' k] :=
    hweight.trans ((EventuallyEq.rfl.mul hcov).trans hpull.symm)
  exact (integral_congr_ae hall).trans (integral_condExp (𝒢'.le k))

/-- Set-integral characterization of a martingale on an arbitrary ordered
time set. The tests are all events measurable at the earlier time. -/
theorem martingale_of_past_set_integrals {ι : Type*} [Preorder ι] [IsFiniteMeasure μ]
    {𝒢 : Filtration ι m} {X : ι → Ω → ℝ}
    (had : StronglyAdapted 𝒢 X) (hint : ∀ t, Integrable (X t) μ)
    (htest : ∀ s t, s ≤ t → ∀ A, MeasurableSet[𝒢 s] A →
      (∫ ω in A, X s ω ∂μ) = ∫ ω in A, X t ω ∂μ) :
    Martingale X 𝒢 μ := by
  refine ⟨had, fun s t hst => ?_⟩
  exact (ae_eq_condExp_of_forall_setIntegral_eq (𝒢.le s) (hint t)
    (fun _ _ _ => (hint s).integrableOn)
    (fun A hA _ => htest s t hst A hA) (had s).aestronglyMeasurable).symm

/-- The martingale property is closed under L¹ convergence at each time
on a fixed filtered probability space, provided the limit is adapted. -/
theorem martingale_of_timewise_L1_limits
    {ι : Type*} [Preorder ι] [IsFiniteMeasure μ]
    {𝒢 : Filtration ι m} {X : ι → Ω → ℝ} {Xn : ℕ → ι → Ω → ℝ}
    (had : StronglyAdapted 𝒢 X) (hint : ∀ t, Integrable (X t) μ)
    (hm : ∀ n, Martingale (Xn n) 𝒢 μ)
    (hconv : ∀ t, Tendsto (fun n => eLpNorm (Xn n t - X t) 1 μ) atTop (nhds 0)) :
    Martingale X 𝒢 μ := by
  refine martingale_of_past_set_integrals had hint ?_
  intro s t hst A hA
  have hs := tendsto_setIntegral_of_L1' (X s)
    (Eventually.of_forall (fun n => (hm n).integrable s)) (hconv s) A
  have ht := tendsto_setIntegral_of_L1' (X t)
    (Eventually.of_forall (fun n => (hm n).integrable t)) (hconv t) A
  have heq : (fun n => ∫ ω in A, Xn n s ω ∂μ) =
      (fun n => ∫ ω in A, Xn n t ω ∂μ) :=
    funext (fun n => (hm n).setIntegral_eq hst hA)
  rw [heq] at hs
  exact tendsto_nhds_unique hs ht

/-- Localized versions of the zero-square condition suffice, when the
localized values eventually cover the original process at each fixed
time. This is the last zero-bracket argument after identifying a common
driver, with the localization hypotheses explicit. -/
theorem zero_of_localized_square_martingales {ι : Type*} [Preorder ι] [OrderBot ι]
    [TopologicalSpace ι] [IsFiniteMeasure μ]
    {𝒢 : Filtration ι m} {X : ι → Ω → ℝ} {stopped : ℕ → ι → Ω → ℝ}
    {D : Set ι} (hD : D.Countable) (hdense : Dense D)
    (hcts : ∀ᵐ ω ∂μ, Continuous (fun t => X t ω))
    (hm : ∀ n, Martingale (fun t ω => stopped n t ω ^ 2) 𝒢 μ)
    (hstart : ∀ n, stopped n ⊥ =ᵐ[μ] 0)
    (hcover : ∀ t ∈ D, ∀ᵐ ω ∂μ, ∃ n, stopped n t ω = X t ω) :
    ∀ᵐ ω ∂μ, ∀ t, X t ω = 0 := by
  refine indistinguishable_of_ae_eq_on_dense hD hdense hcts
    (Eventually.of_forall (fun _ => continuous_const : ∀ ω : Ω,
      Continuous (fun _ : ι => (0 : ℝ)))) ?_
  intro t ht
  have hz : ∀ᵐ ω ∂μ, ∀ n, stopped n t ω = 0 := by
    rw [ae_all_iff]
    intro n
    exact zero_of_square_martingale (hm n) (bot_le : ⊥ ≤ t) (hstart n)
  filter_upwards [hcover t ht, hz] with ω hω hzero
  obtain ⟨n, hn⟩ := hω
  exact hn.symm.trans (hzero n)

/-- Itô isometry for simple predictable integrands when the compensated
square is X² minus the deterministic time clock. In particular this is
the formula needed on a Brownian time grid once its square martingale
has been established. -/
theorem grid_integral_ito_isometry {ι : Type*} [Preorder ι] [IsFiniteMeasure μ]
    {𝒢 : Filtration ι m} (grid : ℕ →o ι) (clock : ι → ℝ) {X : ι → Ω → ℝ}
    (hX : Martingale X 𝒢 μ)
    (hQ : Martingale (fun t ω => X t ω ^ 2 - clock t) 𝒢 μ)
    (hX₂ : ∀ t, MemLp (X t) 2 μ)
    {a : ℕ → Ω → ℝ}
    (ha : ∀ k, StronglyMeasurable[𝒢 (grid k)] (a k))
    (haTop : ∀ k, MemLp (a k) ⊤ μ) (n : ℕ) :
    (∫ ω, gridIntegral grid a X n ω ^ 2 ∂μ) =
      ∑ k ∈ Finset.range n, (clock (grid (k + 1)) - clock (grid k)) *
        ∫ ω, (a k ω)^2 ∂μ := by
  let C : ι → Ω → ℝ := fun t _ => clock t
  have hQ' : Martingale (fun t => X t * X t - C t) 𝒢 μ := by
    simpa only [C, Pi.sub_def, Pi.mul_def, pow_two] using hQ
  have h := grid_integral_cross_isometry grid hX hX hQ' hX₂ hX₂
    ha ha haTop haTop n
  simp only [C, ← pow_two] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_mul_const, mul_comm]

/-- The grid running sum adds one weighted increment at each step. -/
theorem gridIntegral_succ {ι : Type*} [Preorder ι] (grid : ℕ →o ι)
    (a : ℕ → Ω → ℝ) (X : ι → Ω → ℝ) (n : ℕ) :
    gridIntegral grid a X (n + 1) = gridIntegral grid a X n +
      a n * (X (grid (n + 1)) - X (grid n)) :=
  runningSum_succ _ _

/-- Take the even vertices of a fine grid. Consecutive coarse
intervals are each the union of two consecutive fine intervals. -/
def evenGrid {ι : Type*} [Preorder ι] (grid : ℕ →o ι) : ℕ →o ι :=
  ⟨fun n => grid (2 * n), fun _ _ hab => grid.monotone (Nat.mul_le_mul_left 2 hab)⟩

private theorem evenGrid_apply {ι : Type*} [Preorder ι] (grid : ℕ →o ι) (n : ℕ) :
    evenGrid grid n = grid (2 * n) := rfl

/-- Refining every coarse interval into two pieces and repeating the
predictable weight does not change the integral. The identity is pathwise
and needs no assumption on the law of the driver. -/
theorem grid_integral_invariant_under_doubling {ι : Type*} [Preorder ι]
    (grid : ℕ →o ι) (a : ℕ → Ω → ℝ) (X : ι → Ω → ℝ) (n : ℕ) :
    gridIntegral grid (fun k => a (k / 2)) X (2 * n) =
      gridIntegral (evenGrid grid) a X n := by
  induction n with
  | zero => simp [gridIntegral]
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      gridIntegral_succ, gridIntegral_succ, ih, gridIntegral_succ]
    simp only [evenGrid_apply,
      show (2 * n) / 2 = n by omega,
      show (2 * n + 1) / 2 = n by omega,
      show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
    ring

/-- Difference of two simple integrals on one grid. Together with
refinement invariance, this reduces mean-square comparison of repeated
dyadic refinements to one grid isometry. -/
theorem grid_integral_sub_weights {ι : Type*} [Preorder ι] (grid : ℕ →o ι)
    (a b : ℕ → Ω → ℝ) (X : ι → Ω → ℝ) (n : ℕ) :
    gridIntegral grid (fun k => a k - b k) X n =
      gridIntegral grid a X n - gridIntegral grid b X n := by
  induction n with
  | zero => simp [gridIntegral]
  | succ n ih =>
    simp only [gridIntegral_succ, ih]
    ring

private theorem eLpNorm_mul_two_to_one {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    eLpNorm (f * g) 1 μ ≤ eLpNorm f 2 μ * eLpNorm g 2 μ :=
  eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
    (f := g) (φ := f) hf.aestronglyMeasurable hg.aestronglyMeasurable

/-- Products of two L²-convergent sequences converge in L¹. This is
needed to pass the compensated-product martingale tests to an integral
defined as a mean-square limit. -/
theorem product_L1_limit_of_L2_limits {f g : Ω → ℝ} {fn gn : ℕ → Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hfn : ∀ n, MemLp (fn n) 2 μ) (hgn : ∀ n, MemLp (gn n) 2 μ)
    (hx : Tendsto (fun n => eLpNorm (fn n - f) 2 μ) atTop (nhds 0))
    (hy : Tendsto (fun n => eLpNorm (gn n - g) 2 μ) atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm (fn n * gn n - f * g) 1 μ) atTop (nhds 0) := by
  let A := fun n => eLpNorm (fn n - f) 2 μ
  let B := fun n => eLpNorm (gn n - g) 2 μ
  have hmon (n : ℕ) :
      eLpNorm (fn n * gn n - f * g) 1 μ ≤
        A n * B n + A n * eLpNorm g 2 μ + eLpNorm f 2 μ * B n := by
    have hsplit : fn n * gn n - f * g =
        (fn n - f) * (gn n - g) + (fn n - f) * g + f * (gn n - g) := by ring
    rw [hsplit]
    refine (eLpNorm_add_le le_rfl).trans ?_
    exact add_le_add
      ((eLpNorm_add_le le_rfl).trans (add_le_add
        (eLpNorm_mul_two_to_one ((hfn n).sub hf) ((hgn n).sub hg))
        (eLpNorm_mul_two_to_one ((hfn n).sub hf) hg)))
      (eLpNorm_mul_two_to_one hf ((hgn n).sub hg))
  have hxy : Tendsto (fun n => A n * B n) atTop (nhds 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul hx (Or.inr ENNReal.zero_ne_top)
      hy (Or.inr ENNReal.zero_ne_top)
  have hxg : Tendsto (fun n => A n * eLpNorm g 2 μ) atTop (nhds 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const hx (Or.inr hg.eLpNorm_ne_top)
  have hfy : Tendsto (fun n => eLpNorm f 2 μ * B n) atTop (nhds 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hy (Or.inr hf.eLpNorm_ne_top)
  have hbound : Tendsto
      (fun n => A n * B n + A n * eLpNorm g 2 μ + eLpNorm f 2 μ * B n) atTop (nhds 0) := by
    simpa only [add_zero] using (hxy.add hxg).add hfy
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun _ => zero_le) hmon

/-- A compensated-product martingale limit on one filtered space.
The martingales must be given on the same filtration. The weak-convergence
argument on different spaces in the manuscript is an additional step. -/
theorem compensated_product_martingale_of_limits {ι : Type*} [Preorder ι]
    [IsFiniteMeasure μ] {𝒢 : Filtration ι m}
    {X Y C : ι → Ω → ℝ} {Xn Yn Cn : ℕ → ι → Ω → ℝ}
    (hadX : StronglyAdapted 𝒢 X) (hadY : StronglyAdapted 𝒢 Y) (hadC : StronglyAdapted 𝒢 C)
    (hX₂ : ∀ t, MemLp (X t) 2 μ) (hY₂ : ∀ t, MemLp (Y t) 2 μ)
    (hXn₂ : ∀ n t, MemLp (Xn n t) 2 μ) (hYn₂ : ∀ n t, MemLp (Yn n t) 2 μ)
    (hC : ∀ t, Integrable (C t) μ) (_hCn : ∀ n t, Integrable (Cn n t) μ)
    (hm : ∀ n, Martingale (fun t => Xn n t * Yn n t - Cn n t) 𝒢 μ)
    (hx : ∀ t, Tendsto (fun n => eLpNorm (Xn n t - X t) 2 μ) atTop (nhds 0))
    (hy : ∀ t, Tendsto (fun n => eLpNorm (Yn n t - Y t) 2 μ) atTop (nhds 0))
    (hc : ∀ t, Tendsto (fun n => eLpNorm (Cn n t - C t) 1 μ) atTop (nhds 0)) :
    Martingale (fun t => X t * Y t - C t) 𝒢 μ := by
  refine martingale_of_timewise_L1_limits
    (fun t => ((hadX t).mul (hadY t)).sub (hadC t))
    (fun t => (integrable_mul_of_memLp_two (hX₂ t) (hY₂ t)).sub (hC t)) hm ?_
  intro t
  have hprod := product_L1_limit_of_L2_limits (hX₂ t) (hY₂ t)
    (fun n => hXn₂ n t) (fun n => hYn₂ n t) (hx t) (hy t)
  have hbound : Tendsto (fun n =>
      eLpNorm (Xn n t * Yn n t - X t * Y t) 1 μ +
        eLpNorm (Cn n t - C t) 1 μ) atTop (nhds 0) := by
    simpa only [add_zero] using hprod.add (hc t)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun _ => zero_le) (fun n => ?_)
  have hsplit : (Xn n t * Yn n t - Cn n t) - (X t * Y t - C t) =
      (Xn n t * Yn n t - X t * Y t) + -(Cn n t - C t) := by ring
  rw [hsplit]
  simpa only [eLpNorm_neg] using
    (eLpNorm_add_le (μ := μ) (f := Xn n t * Yn n t - X t * Y t)
      (g := -(Cn n t - C t)) (show (1 : ENNReal) ≤ 1 from le_rfl))

end RoughHeston

#print axioms RoughHeston.runningSum_martingale
#print axioms RoughHeston.compensated_running_product_martingale
#print axioms RoughHeston.runningSum_cross_isometry
#print axioms RoughHeston.centered_predictable_increment
#print axioms RoughHeston.predictable_increment_covariance
#print axioms RoughHeston.zero_of_square_martingale
#print axioms RoughHeston.indistinguishable_of_ae_eq_on_dense

#print axioms RoughHeston.conditional_mean_martingale_increment
#print axioms RoughHeston.conditional_covariance_of_compensated_product
#print axioms RoughHeston.grid_integral_martingale
#print axioms RoughHeston.grid_integral_cross_isometry
#print axioms RoughHeston.martingale_of_past_set_integrals
#print axioms RoughHeston.martingale_of_timewise_L1_limits
#print axioms RoughHeston.zero_of_localized_square_martingales
#print axioms RoughHeston.grid_integral_ito_isometry
#print axioms RoughHeston.grid_integral_invariant_under_doubling
#print axioms RoughHeston.grid_integral_sub_weights
#print axioms RoughHeston.product_L1_limit_of_L2_limits
#print axioms RoughHeston.compensated_product_martingale_of_limits
