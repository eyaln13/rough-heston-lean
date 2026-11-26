import StochasticCompletion
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
Stochastic sums as processes on the original filtration, with all their
increments stopped at the observation time. Conditional expectation of
the terminal integral identifies the timewise mean-square limit.
-/

open MeasureTheory Filter Set
open scoped BigOperators MeasureTheory ProbabilityTheory Topology NNReal ENNReal

namespace RoughHeston

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

section SimpleIntegral

variable [LinearOrder ι]

/-- One simple predictable integral, observed at time `t`. -/
def stochasticStep (u v : ι) (a : Ω → ℝ) (X : ι → Ω → ℝ)
    (t : ι) : Ω → ℝ :=
  a * (X (min t v) - X (min t u))

@[simp] theorem stochasticStep_before {u v t : ι} (ht : t ≤ u) (huv : u ≤ v)
    (a : Ω → ℝ) (X : ι → Ω → ℝ) : stochasticStep u v a X t = 0 := by
  simp [stochasticStep, min_eq_left ht, min_eq_left (ht.trans huv)]

@[simp] theorem stochasticStep_after {u v t : ι} (hvt : v ≤ t) (huv : u ≤ v)
    (a : Ω → ℝ) (X : ι → Ω → ℝ) :
    stochasticStep u v a X t = a * (X v - X u) := by
  simp [stochasticStep, min_eq_right hvt, min_eq_right (huv.trans hvt)]

theorem stochasticStep_memLp_two {u v : ι} {a : Ω → ℝ} {X : ι → Ω → ℝ}
    (hX₂ : ∀ t, MemLp (X t) 2 μ) (haTop : MemLp a ⊤ μ) (t : ι) :
    MemLp (stochasticStep u v a X t) 2 μ := by
  exact haTop.mul ((hX₂ (min t v)).sub (hX₂ (min t u)))

private theorem setIntegral_weighted_increment_zero [IsFiniteMeasure μ]
    {𝒢 : Filtration ι m} {X : ι → Ω → ℝ} {a : Ω → ℝ} {s t : ι}
    (hX : Martingale X 𝒢 μ) (hst : s ≤ t) (ha : StronglyMeasurable[𝒢 s] a)
    (hint : Integrable (a * (X t - X s)) μ)
    {A : Set Ω} (hA : MeasurableSet[𝒢 s] A) :
    (∫ ω in A, (a * (X t - X s)) ω ∂μ) = 0 := by
  let d := X t - X s
  have hce := condExp_mul_of_stronglyMeasurable_left ha
    hint ((hX.integrable t).sub (hX.integrable s))
  have hz : μ[a * d | 𝒢 s] =ᵐ[μ] (0 : Ω → ℝ) := by
    filter_upwards [hce, conditional_mean_martingale_increment hX hst] with ω h₁ h₂
    change μ[a * d | 𝒢 s] ω = (a * μ[d | 𝒢 s]) ω at h₁
    change μ[d | 𝒢 s] ω = 0 at h₂
    rw [h₁, Pi.mul_apply, h₂, mul_zero, Pi.zero_apply]
  rw [← setIntegral_condExp (𝒢.le s) hint hA]
  exact (integral_congr_ae (ae_restrict_of_ae hz)).trans (by simp)

/-- A single predictable weight gives a martingale whenever its products
with the driver's increments are integrable. -/
theorem stochasticStep_martingale_of_integrable [IsFiniteMeasure μ]
    {𝒢 : Filtration ι m} {X : ι → Ω → ℝ} {a : Ω → ℝ} {u v : ι}
    (huv : u ≤ v) (hX : Martingale X 𝒢 μ) (ha : StronglyMeasurable[𝒢 u] a)
    (hint : ∀ s t, Integrable (a * (X t - X s)) μ) :
    Martingale (stochasticStep u v a X) 𝒢 μ := by
  refine martingale_of_past_set_integrals ?_ (fun _ => hint _ _) ?_
  · intro t
    rcases le_total t u with htu | hut
    · rw [stochasticStep_before htu huv]
      exact stronglyMeasurable_zero
    · exact (ha.mono (𝒢.mono hut)).mul
        (((hX.stronglyMeasurable _).mono (𝒢.mono (min_le_left t v))).sub
          ((hX.stronglyMeasurable _).mono (𝒢.mono (min_le_left t u))))
  · intro s t hst A hA
    by_cases htu : t ≤ u
    · rw [stochasticStep_before (hst.trans htu) huv, stochasticStep_before htu huv]
    have hut : u ≤ t := (le_of_not_ge htu)
    by_cases hsu : s ≤ u
    · rw [stochasticStep_before hsu huv, stochasticStep, min_eq_right hut]
      simpa using (setIntegral_weighted_increment_zero hX (le_min hut huv)
        ha (hint _ _) (𝒢.mono hsu A hA)).symm
    have hus : u ≤ s := le_of_not_ge hsu
    by_cases hvs : v ≤ s
    · rw [stochasticStep_after hvs huv, stochasticStep_after (hvs.trans hst) huv]
    have hsv : s ≤ v := le_of_not_ge hvs
    have hi (r : ι) : Integrable (stochasticStep u v a X r) μ := hint _ _
    apply sub_eq_zero.mp
    rw [← integral_sub (hi s).integrableOn (hi t).integrableOn]
    have hdiff : (fun ω => stochasticStep u v a X s ω - stochasticStep u v a X t ω) =
        fun ω => -(a * (X (min t v) - X s)) ω := by
      ext ω
      simp only [stochasticStep, min_eq_left hsv, min_eq_right hus, min_eq_right hut,
        Pi.mul_apply, Pi.sub_apply]
      ring
    rw [hdiff, integral_neg, setIntegral_weighted_increment_zero hX (le_min hst hsv)
      (ha.mono (𝒢.mono hus)) (hint _ _) hA, neg_zero]

/-- A bounded predictable weight gives a martingale against a
square-integrable driver. -/
theorem stochasticStep_martingale [IsFiniteMeasure μ]
    {𝒢 : Filtration ι m} {X : ι → Ω → ℝ} {a : Ω → ℝ} {u v : ι}
    (huv : u ≤ v) (hX : Martingale X 𝒢 μ) (hX₂ : ∀ t, MemLp (X t) 2 μ)
    (ha : StronglyMeasurable[𝒢 u] a) (haTop : MemLp a ⊤ μ) :
    Martingale (stochasticStep u v a X) 𝒢 μ :=
  stochasticStep_martingale_of_integrable huv hX ha (fun s t =>
    (haTop.mul ((hX₂ t).sub (hX₂ s)) : MemLp (a * (X t - X s)) 2 μ).integrable (by norm_num))

/-- The stochastic sum with each increment stopped at the observation time. -/
def gridIntegralProcess (grid : ℕ →o ι) (a : ℕ → Ω → ℝ)
    (X : ι → Ω → ℝ) (n : ℕ) : ι → Ω → ℝ :=
  ∑ k ∈ Finset.range n, stochasticStep (grid k) (grid (k + 1)) (a k) X

@[simp] theorem gridIntegralProcess_zero (grid : ℕ →o ι)
    (a : ℕ → Ω → ℝ) (X : ι → Ω → ℝ) : gridIntegralProcess grid a X 0 = 0 := by
  simp [gridIntegralProcess]

theorem gridIntegralProcess_succ (grid : ℕ →o ι) (a : ℕ → Ω → ℝ)
    (X : ι → Ω → ℝ) (n : ℕ) :
    gridIntegralProcess grid a X (n + 1) =
      gridIntegralProcess grid a X n + stochasticStep (grid n) (grid (n + 1)) (a n) X := by
  simp [gridIntegralProcess, Finset.sum_range_succ]

theorem gridIntegralProcess_terminal (grid : ℕ →o ι) (a : ℕ → Ω → ℝ)
    (X : ι → Ω → ℝ) (n : ℕ) {T : ι} (hT : grid n ≤ T) :
    gridIntegralProcess grid a X n T = gridIntegral grid a X n := by
  unfold gridIntegralProcess gridIntegral runningSum
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  exact stochasticStep_after
    ((grid.monotone (Finset.mem_range.mp hk)).trans hT) (grid.monotone k.le_succ) _ _

theorem gridIntegralProcess_martingale [IsFiniteMeasure μ]
    {𝒢 : Filtration ι m} (grid : ℕ →o ι) {X : ι → Ω → ℝ}
    (hX : Martingale X 𝒢 μ) (hX₂ : ∀ t, MemLp (X t) 2 μ)
    {a : ℕ → Ω → ℝ} (ha : ∀ k, StronglyMeasurable[𝒢 (grid k)] (a k))
    (haTop : ∀ k, MemLp (a k) ⊤ μ) (n : ℕ) :
    Martingale (gridIntegralProcess grid a X n) 𝒢 μ := by
  induction n with
  | zero => simpa using martingale_zero ℝ 𝒢 μ
  | succ n ih =>
      rw [gridIntegralProcess_succ]
      exact ih.add (stochasticStep_martingale (grid.monotone n.le_succ)
        hX hX₂ (ha n) (haTop n))

theorem gridIntegralProcess_memLp_two (grid : ℕ →o ι) {X : ι → Ω → ℝ}
    (hX₂ : ∀ t, MemLp (X t) 2 μ) {a : ℕ → Ω → ℝ}
    (haTop : ∀ k, MemLp (a k) ⊤ μ) (n : ℕ) (t : ι) :
    MemLp (gridIntegralProcess grid a X n t) 2 μ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [gridIntegralProcess_succ, Pi.add_apply]
      exact ih.add (stochasticStep_memLp_two hX₂ (haTop n) t)

theorem gridIntegralProcess_continuous [TopologicalSpace ι] [OrderClosedTopology ι]
    (grid : ℕ →o ι) (a : ℕ → Ω → ℝ) {X : ι → Ω → ℝ}
    (n : ℕ) {ω : Ω} (hX : Continuous (fun t => X t ω)) :
    Continuous (fun t => gridIntegralProcess grid a X n t ω) := by
  induction n with
  | zero => simpa using (continuous_const : Continuous (fun _ : ι => (0 : ℝ)))
  | succ n ih =>
      simp only [gridIntegralProcess_succ, Pi.add_apply, stochasticStep, Pi.mul_apply,
        Pi.sub_apply]
      exact ih.add (continuous_const.mul
        ((hX.comp (continuous_id.min continuous_const)).sub
          (hX.comp (continuous_id.min continuous_const))))


/-- L² convergence at the terminal time propagates to every earlier
time by contraction of conditional expectation. The limiting process
is an actual adapted martingale on the same filtered space. -/
theorem martingale_limit_of_terminal_L2 [IsFiniteMeasure μ]
    {𝒢 : Filtration ι m} {Jn : ℕ → ι → Ω → ℝ} {T : ι} {I : Lp ℝ 2 μ}
    (hm : ∀ n, Martingale (Jn n) 𝒢 μ)
    (h₂ : ∀ n, MemLp (Jn n T) 2 μ)
    (hI : Tendsto (fun n => (h₂ n).toLp (Jn n T)) atTop (𝓝 I)) :
    let J : ι → Ω → ℝ := fun t => μ[(I : Ω → ℝ) | 𝒢 t]
    Martingale J 𝒢 μ ∧ (∀ t, MemLp (J t) 2 μ) ∧
      ∀ t ≤ T, Tendsto (fun n => eLpNorm (Jn n t - J t) 2 μ) atTop (𝓝 0) := by
  let J : ι → Ω → ℝ := fun t => μ[(I : Ω → ℝ) | 𝒢 t]
  have hI₂ := Lp.memLp I
  refine ⟨martingale_condExp _ 𝒢 μ, fun t => hI₂.condExp (by norm_num), fun t ht => ?_⟩
  have htend : Tendsto (fun n => eLpNorm (Jn n T - (I : Ω → ℝ)) 2 μ) atTop (𝓝 0) := by
    have hd := (continuous_edist.tendsto (I, I)).comp (hI.prodMk_nhds tendsto_const_nhds)
    have he (n : ℕ) : edist ((h₂ n).toLp (Jn n T)) I =
        eLpNorm (Jn n T - (I : Ω → ℝ)) 2 μ := calc
      _ = edist ((h₂ n).toLp (Jn n T)) (hI₂.toLp (I : Ω → ℝ)) :=
        congrArg _ (Lp.toLp_coeFn I hI₂).symm
      _ = _ := Lp.edist_toLp_toLp _ _ _ _
    simpa only [Function.comp_def, edist_self, he] using hd
  have hle (n : ℕ) :
      eLpNorm (Jn n t - J t) 2 μ ≤ eLpNorm (Jn n T - (I : Ω → ℝ)) 2 μ := by
    have heq := condExp_sub ((hm n).integrable T) (hI₂.integrable (by norm_num)) (𝒢 t)
    have hdiff : μ[Jn n T - (I : Ω → ℝ) | 𝒢 t] =ᵐ[μ] Jn n t - J t :=
      heq.trans (((hm n).condExp_ae_eq ht).sub EventuallyEq.rfl)
    rw [← eLpNorm_congr_ae hdiff]
    exact eLpNorm_condExp_le_eLpNorm _ (by norm_num)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htend
    (fun _ => zero_le) hle

/-- The terminal dyadic integral extends to an adapted square-integrable
martingale, with the same stochastic sums converging at every earlier time. -/
theorem dyadic_integral_martingale_of_terminal_limit [IsFiniteMeasure μ]
    {𝒢 : Filtration ι m} (G : NestedDyadicGrids ι) {T : ι}
    {X : ι → Ω → ℝ} {a : ℕ → ℕ → Ω → ℝ} {I : Lp ℝ 2 μ}
    (hX : Martingale X 𝒢 μ) (hX₂ : ∀ t, MemLp (X t) 2 μ)
    (hT : ∀ j, G.grid j (2 ^ j) ≤ T)
    (ha : ∀ j k, StronglyMeasurable[𝒢 (G.grid j k)] (a j k))
    (haTop : ∀ j k, MemLp (a j k) ⊤ μ)
    (hI : Tendsto (fun j => dyadicTerminalLp G j hX₂ (haTop j)) atTop (𝓝 I)) :
    let J : ι → Ω → ℝ := fun t => μ[(I : Ω → ℝ) | 𝒢 t]
    Martingale J 𝒢 μ ∧ (∀ t, MemLp (J t) 2 μ) ∧
      ∀ t ≤ T, Tendsto (fun j => eLpNorm
        (gridIntegralProcess (G.grid j) (a j) X (2 ^ j) t - J t) 2 μ) atTop (𝓝 0) := by
  let Jn := fun j => gridIntegralProcess (G.grid j) (a j) X (2 ^ j)
  have hm (j : ℕ) : Martingale (Jn j) 𝒢 μ :=
    gridIntegralProcess_martingale (G.grid j) hX hX₂ (ha j) (haTop j) (2 ^ j)
  have h₂ (j : ℕ) : MemLp (Jn j T) 2 μ :=
    gridIntegralProcess_memLp_two (G.grid j) hX₂ (haTop j) (2 ^ j) T
  refine martingale_limit_of_terminal_L2 hm h₂ ?_
  convert hI using 1
  funext j
  exact (MemLp.toLp_eq_toLp_iff _ _).2 (EventuallyEq.of_eq
    (gridIntegralProcess_terminal (G.grid j) (a j) X (2 ^ j) (hT j)))


/-- The countable-time Doob bound, with any countable set of observation
times before a fixed terminal time. No regularity of the sample paths
is needed for this bound. -/
theorem countable_martingale_maximal_ineq [IsFiniteMeasure μ]
    {𝒢 : Filtration ι m} {M : ι → Ω → ℝ} (hM : Martingale M 𝒢 μ)
    {T : ι} (times : ℕ → ι) (htimes : ∀ k, times k ≤ T) (ε : ℝ≥0) :
    (ε : ENNReal) * μ (⋃ k, {ω | (ε : ℝ) ≤ |M (times k) ω|}) ≤
      ENNReal.ofReal (∫ ω, |M T ω| ∂μ) := by
  classical
  let A (n : ℕ) := ⋃ k ∈ Finset.range n, {ω | (ε : ℝ) ≤ |M (times k) ω|}
  have hAmono : Monotone A := by
    intro n l hnl
    apply iUnion₂_mono'
    intro k hk
    exact ⟨k, Finset.mem_range.mpr ((Finset.mem_range.mp hk).trans_le hnl), le_rfl⟩
  have hcov : (⋃ n, A n) = ⋃ k, {ω | (ε : ℝ) ≤ |M (times k) ω|} := by
    ext ω
    simp only [A, Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_range]
    exact ⟨fun ⟨_, k, _, hk⟩ => ⟨k, hk⟩, fun ⟨k, hk⟩ => ⟨k + 1, k, k.lt_succ_self, hk⟩⟩
  rw [← hcov, hAmono.measure_iUnion, ENNReal.mul_iSup]
  apply iSup_le
  intro n
  let s := (Finset.range n).image times
  have hs (u : ι) (hu : u ∈ s) : u ≤ T := by
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hu
    exact htimes k
  let g (k : ℕ) : ι := if hk : k < s.card then s.orderEmbOfFin rfl ⟨k, hk⟩ else T
  have hg : Monotone g := by
    intro i j hij
    by_cases hj : j < s.card
    · have hi := hij.trans_lt hj
      simp only [g, dite_eq_left hi, dite_eq_left hj]
      exact (s.orderEmbOfFin rfl).monotone hij
    · rw [show g j = T by simp [g, hj]]
      by_cases hi : i < s.card
      · simpa [g, hi] using hs _ (s.orderEmbOfFin_mem rfl ⟨i, hi⟩)
      · simp [g, hi]
  have hgT : g s.card = T := by simp [g]
  let grid : ℕ →o ι := ⟨g, hg⟩
  let F : ℕ → Ω → ℝ := fun k => M (grid k)
  have hF : Martingale F (gridFiltration 𝒢 grid) μ :=
    ⟨fun k => hM.stronglyAdapted _, fun i j hij => hM.condExp_ae_eq (grid.monotone hij)⟩
  have habs : Submartingale (fun k ω => |F k ω|) (gridFiltration 𝒢 grid) μ := by
    have heq : (fun k ω => |F k ω|) = F ⊔ -F := by
      funext k ω
      change |F k ω| = max (F k ω) (-F k ω)
      exact abs_eq_max_neg
    rw [heq]
    exact hF.submartingale.sup hF.neg.submartingale
  let E := {ω | (ε : ℝ) ≤ (Finset.range (s.card + 1)).sup' Finset.nonempty_range_add_one
    (fun k => |F k ω|)}
  have hAE : A n ⊆ E := by
    intro ω hω
    simp only [A, Set.mem_iUnion, Set.mem_ofPred_eq] at hω
    obtain ⟨k, hk, hω⟩ := hω
    have hsk : times k ∈ s := Finset.mem_image_of_mem times hk
    have hrange : times k ∈ Set.range (s.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hsk
    obtain ⟨i, hi⟩ := hrange
    have hi' : (i : ℕ) ∈ Finset.range (s.card + 1) :=
      Finset.mem_range.mpr (i.isLt.trans s.card.lt_succ_self)
    have hgi : g i = times k := by simpa [g, i.isLt] using hi
    change (ε : ℝ) ≤ _
    refine (Finset.le_sup'_iff _).2 ⟨i, hi', ?_⟩
    simpa [F, grid, hgi] using hω
  calc
    (ε : ENNReal) * μ (A n) ≤ (ε : ENNReal) * μ E :=
      mul_le_mul_right (measure_mono hAE) _
    _ ≤ ENNReal.ofReal (∫ ω in E, |F s.card ω| ∂μ) := by
      exact maximal_ineq habs (fun _ _ => abs_nonneg _) s.card
    _ ≤ ENNReal.ofReal (∫ ω, |M T ω| ∂μ) := by
      apply ENNReal.ofReal_le_ofReal
      have hterm : F s.card = M T := congrArg M hgT
      rw [hterm]
      exact setIntegral_le_integral (hM.integrable T).abs
        (Eventually.of_forall fun _ => abs_nonneg _)


/-- Almost sure uniform Cauchy convergence from geometrically summable
terminal increments. Doob's inequality is applied on a countable dense
set, and path continuity extends the resulting bound to the interval. -/
theorem ae_uniformCauchySeqOn_of_terminal_increment_bounds
    [TopologicalSpace ι] [IsFiniteMeasure μ]
    {𝒢 : Filtration ι m} {T : ι} {M : ℕ → ι → Ω → ℝ}
    (hm : ∀ n, Martingale (M n) 𝒢 μ)
    (hc : ∀ᵐ ω ∂μ, ∀ n, ContinuousOn (fun t => M n t ω) (Iic T))
    (times : ℕ → ι) (htimes : ∀ k, times k ≤ T)
    (hdense : Iic T ⊆ closure (range times))
    (hbound : ∀ n, (∫ ω, |M (n + 1) T ω - M n T ω| ∂μ) ≤ ((2 : ℝ)⁻¹ ^ n) ^ 2) :
    ∀ᵐ ω ∂μ, UniformCauchySeqOn (fun n t => M n t ω) atTop (Iic T) := by
  let ε (n : ℕ) : ℝ≥0 := (2 : ℝ≥0)⁻¹ ^ n
  have hε (n : ℕ) : ε n ≠ 0 := by positivity
  let A (n : ℕ) := ⋃ k, {ω | (ε n : ℝ) ≤ |M (n + 1) (times k) ω - M n (times k) ω|}
  have hA (n : ℕ) : μ (A n) ≤ (ε n : ENNReal) := by
    have h := countable_martingale_maximal_ineq ((hm (n + 1)).sub (hm n))
      times htimes (ε n)
    have h' : ENNReal.ofReal (∫ ω, |M (n + 1) T ω - M n T ω| ∂μ) ≤
        (ε n : ENNReal) * (ε n : ENNReal) := by
      have hp : (ε n : ℝ) = (2 : ℝ)⁻¹ ^ n := by simp [ε]
      have hb := ENNReal.ofReal_le_ofReal (hbound n)
      rwa [← hp, pow_two, ENNReal.ofReal_mul (ε n).coe_nonneg, ENNReal.ofReal_coe_nnreal] at hb
    exact (ENNReal.mul_le_mul_iff_right (by simpa using hε n) ENNReal.coe_ne_top).mp (h.trans h')
  have hsum : (∑' n, μ (A n)) ≠ ∞ := by
    have hle := ENNReal.tsum_le_tsum hA
    have hsum : (∑' n, (ε n : ENNReal)) = (1 - (2 : ENNReal)⁻¹)⁻¹ := by
      simpa only [ε, ENNReal.coe_pow, ENNReal.coe_inv_two] using
        ENNReal.tsum_geometric ((2 : ENNReal)⁻¹)
    rw [hsum] at hle
    exact ne_top_of_le_ne_top (by norm_num) hle
  filter_upwards [hc, ae_eventually_notMem hsum] with ω hcω hω
  obtain ⟨N, hN⟩ := eventually_atTop.mp hω
  have hgap (n : ℕ) (hn : N ≤ n) (t : ι) (ht : t ∈ Iic T) :
      dist (M n t ω) (M (n + 1) t ω) ≤ (2 : ℝ)⁻¹ ^ n := by
    let S := {u | dist (M n u ω) (M (n + 1) u ω) ≤ (2 : ℝ)⁻¹ ^ n}
    have hS : IsClosed ((Subtype.val : Iic T → ι) ⁻¹' S) :=
      isClosed_le ((continuousOn_iff_continuous_domRestrict.mp (hcω n)).dist
        (continuousOn_iff_continuous_domRestrict.mp (hcω (n + 1))))
        continuous_const
    have htimes' (k : ℕ) : times k ∈ S := by
      have hk : ¬ (ε n : ℝ) ≤ |M (n + 1) (times k) ω - M n (times k) ω| := by
        intro h
        apply hN n hn
        exact mem_iUnion.mpr ⟨k, h⟩
      simpa [S, Real.dist_eq, abs_sub_comm, ε] using (lt_of_not_ge hk).le
    let D := fun k => (⟨times k, htimes k⟩ : Iic T)
    have hD : DenseRange D := by
      intro u
      rw [closure_subtype, ← Set.range_comp]
      exact hdense u.property
    exact (closure_minimal (by rintro _ ⟨k, rfl⟩; exact htimes' k) hS) (hD ⟨t, ht⟩)
  rw [Metric.uniformCauchySeqOn_iff]
  intro δ hδ
  have hz : Tendsto (fun n : ℕ => 2 * (2 : ℝ)⁻¹ ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (2 : ℝ)⁻¹) (by norm_num))
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hz.eventually_lt_const hδ)
  refine ⟨max J N, fun a ha b hb t ht => ?_⟩
  have hdist (a b : ℕ) (ha : max J N ≤ a) (hab : a ≤ b) :
      dist (M a t ω) (M b t ω) < δ := by
    refine (dist_le_Ico_sum_of_dist_le hab (fun {n} hn _ =>
      hgap n ((le_max_right J N).trans (ha.trans hn)) t ht)).trans_lt ?_
    have hle : (∑ n ∈ Finset.Ico a b, (2 : ℝ)⁻¹ ^ n) ≤
        ∑' n, if a ≤ n then (2 : ℝ)⁻¹ ^ n else 0 := by
      have hsum := (summable_geometric_of_lt_one (by norm_num : 0 ≤ (2 : ℝ)⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ < 1)).indicator (Ici a)
      have hS := hsum.sum_le_tsum (Finset.Ico a b)
        (fun i _ => Set.indicator_nonneg (fun _ _ => by positivity) _)
      simp only [Set.indicator_apply, Set.mem_Ici] at hS
      refine le_trans (le_of_eq ?_) hS
      apply Finset.sum_congr rfl
      intro i hi
      exact (ite_eq_left (Finset.mem_Ico.mp hi).1).symm
    rw [tsum_geometric_inv_two_ge] at hle
    exact hle.trans_lt (hJ a ((le_max_left J N).trans ha))
  rcases le_total a b with hab | hba
  · exact hdist a b ha hab
  · rw [dist_comm]
    exact hdist b a hb hba


private theorem exists_fast_terminal_subsequence [IsProbabilityMeasure μ]
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hg : Integrable g μ)
    (hlim : Tendsto (fun n => eLpNorm (f n - g) 2 μ) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧ ∀ n,
      (∫ ω, |f (φ (n + 1)) ω - f (φ n) ω| ∂μ) ≤ ((2 : ℝ)⁻¹ ^ n) ^ 2 := by
  have hL1 : Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
      (fun n => eLpNorm_le_eLpNorm_of_exponent_le (by norm_num))
  have he (n : ℕ) : eLpNorm (f n - g) 1 μ =
      ENNReal.ofReal (∫ ω, |f n ω - g ω| ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm ((hf n).sub hg).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hf n).sub hg)]
    simp only [Pi.sub_apply, Real.norm_eq_abs]
  have hL1' : Tendsto (fun n => ∫ ω, |f n ω - g ω| ∂μ) atTop (𝓝 0) := by
    have ht := (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ∞)).comp hL1
    simpa only [Function.comp_def, he, ENNReal.toReal_zero,
      ENNReal.toReal_ofReal (integral_nonneg fun _ => abs_nonneg _)] using ht
  have hfast (k : ℕ) : ∃ N : ℕ, ∀ n ≥ N,
      (∫ ω, |f n ω - g ω| ∂μ) < ((2 : ℝ)⁻¹ ^ k) ^ 2 / 2 :=
    eventually_atTop.mp (hL1'.eventually_lt_const (by positivity))
  choose N hN using hfast
  let φ := fun k => max k (N k)
  refine ⟨φ, tendsto_atTop.2 (fun n => eventually_atTop.2
    ⟨n, fun k hnk => hnk.trans (le_max_left k (N k))⟩), fun n => ?_⟩
  have h₁ := hN n (φ n) (le_max_right n (N n))
  have h₂ := hN (n + 1) (φ (n + 1)) (le_max_right (n + 1) (N (n + 1)))
  have hle :
      (∫ ω, |f (φ (n + 1)) ω - f (φ n) ω| ∂μ) ≤
        (∫ ω, |f (φ (n + 1)) ω - g ω| ∂μ) + (∫ ω, |f (φ n) ω - g ω| ∂μ) := by
    change (∫ ω, |(f (φ (n + 1)) - f (φ n)) ω| ∂μ) ≤
      (∫ ω, |(f (φ (n + 1)) - g) ω| ∂μ) + (∫ ω, |(f (φ n) - g) ω| ∂μ)
    rw [← integral_add ((hf (φ (n + 1))).sub hg).abs ((hf (φ n)).sub hg).abs]
    apply integral_mono ((hf _).sub (hf _)).abs (((hf _).sub hg).abs.add ((hf _).sub hg).abs)
    intro ω
    simpa only [Pi.add_apply, Pi.sub_apply, abs_sub_comm (g ω) (f (φ n) ω)] using
      abs_sub_le (f (φ (n + 1)) ω) (g ω) (f (φ n) ω)
  have hpow : ((2 : ℝ)⁻¹ ^ (n + 1)) ^ 2 ≤ ((2 : ℝ)⁻¹ ^ n) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    rw [pow_succ]
    exact mul_le_of_le_one_right (by positivity) (by norm_num)
  linarith

/-- A timewise L² limit of continuous martingales is a martingale with an
almost surely continuous modification on the observation interval. A
subsequence converges uniformly on the entire interval almost surely. -/
theorem continuous_martingale_version_of_L2_limits [TopologicalSpace ι]
    [IsProbabilityMeasure μ] {𝒢 : Filtration ι m} {T : ι}
    {M : ℕ → ι → Ω → ℝ} {J : ι → Ω → ℝ}
    (hm : ∀ n, Martingale (M n) 𝒢 μ) (hJ : Martingale J 𝒢 μ)
    (hc : ∀ᵐ ω ∂μ, ∀ n, ContinuousOn (fun t => M n t ω) (Iic T))
    (times : ℕ → ι) (htimes : ∀ k, times k ≤ T)
    (hdense : Iic T ⊆ closure (range times))
    (hconv : ∀ t ≤ T, Tendsto (fun n => eLpNorm (M n t - J t) 2 μ) atTop (𝓝 0)) :
    ∃ Jc : ι → Ω → ℝ, Martingale Jc 𝒢 μ ∧ (∀ t, Jc t =ᵐ[μ] J t) ∧
      (∀ᵐ ω ∂μ, ContinuousOn (fun t => Jc t ω) (Iic T)) ∧
      ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
        ∀ᵐ ω ∂μ, TendstoUniformlyOn (fun n t => M (φ n) t ω) (fun t => Jc t ω)
          atTop (Iic T) := by
  obtain ⟨φ, hφ, hbound⟩ :=
    exists_fast_terminal_subsequence (fun n => (hm n).integrable T)
      (hJ.integrable T) (hconv T le_rfl)
  let Jc (t : ι) (ω : Ω) : ℝ :=
    if t ≤ T then limUnder atTop (fun n => M (φ n) t ω) else J t ω
  have hJcad : StronglyAdapted 𝒢 Jc := by
    intro t
    by_cases ht : t ≤ T
    · let : MeasurableSpace Ω := 𝒢 t
      simpa only [Jc, ite_eq_left ht] using
        (StronglyMeasurable.limUnder (l := atTop) (fun n => (hm (φ n)).stronglyMeasurable t))
    · simpa only [Jc, ite_eq_right ht] using hJ.stronglyMeasurable t
  have hae := ae_uniformCauchySeqOn_of_terminal_increment_bounds
    (fun n => hm (φ n)) (hc.mono (fun _ hω n => hω (φ n))) times htimes hdense hbound
  have hunif : ∀ᵐ ω ∂μ, TendstoUniformlyOn (fun n t => M (φ n) t ω) (fun t => Jc t ω)
      atTop (Iic T) := by
    filter_upwards [hae] with ω hω
    apply hω.tendstoUniformlyOn_of_tendsto
    intro t ht
    rw [show Jc t ω = limUnder atTop (fun n => M (φ n) t ω) by
      exact ite_eq_left (show t ≤ T from ht)]
    apply tendsto_nhds_limUnder
    apply cauchySeq_tendsto_of_complete
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp hω ε hε
    exact ⟨N, fun n hn j hj => hN n hn j hj t ht⟩
  have hversion (t : ι) : Jc t =ᵐ[μ] J t := by
    by_cases ht : t ≤ T
    · have hf (n : ℕ) : AEStronglyMeasurable (M n t) μ :=
        (((hm n).stronglyAdapted t).mono (𝒢.le t)).aestronglyMeasurable
      have hprob := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) (hconv t ht)
      have hae' : ∀ᵐ ω ∂μ, Tendsto (fun n => M (φ n) t ω) atTop (𝓝 (Jc t ω)) :=
        hunif.mono (fun _ hω => hω.tendsto_at ht)
      exact tendstoInMeasure_ae_unique
        (tendstoInMeasure_of_tendsto_ae (fun n => hf (φ n)) hae') (hprob.comp hφ)
    · simp [Jc, ht]
  refine ⟨Jc, ⟨hJcad, ?_⟩, hversion, ?_, φ, hφ, hunif⟩
  · intro s t hst
    exact (condExp_congr_ae (hversion t)).trans ((hJ.condExp_ae_eq hst).trans (hversion s).symm)
  · filter_upwards [hunif, hc] with ω hω hcω
    exact hω.continuousOn (Eventually.of_forall fun n => hcω (φ n)).frequently

end SimpleIntegral

/-- Continuous stochastic integral on a bounded time interval for an
adapted bounded integrand with almost surely continuous paths, against
a continuous square-integrable martingale with integrable compensator. -/
theorem exists_continuous_integral_of_bounded_continuous_paths
    [IsProbabilityMeasure μ] {𝒢 : Filtration ℝ≥0 m} (T : ℝ≥0)
    {X C H : ℝ≥0 → Ω → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hX : Martingale X 𝒢 μ) (hX₂ : ∀ t, MemLp (X t) 2 μ)
    (hXcts : ∀ᵐ ω ∂μ, Continuous (fun t => X t ω))
    (hC : Martingale (fun t => X t * X t - C t) 𝒢 μ)
    (hCint : ∀ t, Integrable (C t) μ) (hCmon : ∀ s t, s ≤ t → C s ≤ᵐ[μ] C t)
    (hH : StronglyAdapted 𝒢 H) (hHtop : ∀ t, MemLp (H t) ⊤ μ)
    (hcts : ∀ᵐ ω ∂μ, ContinuousOn (fun t => H t ω) (Icc 0 T))
    (hbounded : ∀ᵐ ω ∂μ, ∀ t ≤ T, |H t ω| ≤ B) :
    let G := uniformDyadicGrids T
    let Jn := fun n => gridIntegralProcess (G.grid n) (fun k => H (G.grid n k)) X (2 ^ n)
    ∃ J : ℝ≥0 → Ω → ℝ, Martingale J 𝒢 μ ∧ (∀ t, MemLp (J t) 2 μ) ∧
      (∀ᵐ ω ∂μ, ContinuousOn (fun t => J t ω) (Iic T)) ∧
      (∀ t ≤ T, Tendsto (fun n => eLpNorm (Jn n t - J t) 2 μ) atTop (𝓝 0)) ∧
      ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
        ∀ᵐ ω ∂μ, TendstoUniformlyOn (fun n t => Jn (φ n) t ω)
          (fun t => J t ω) atTop (Iic T) := by
  let G := uniformDyadicGrids T
  let a := fun n k => H (G.grid n k)
  let Jn := fun n => gridIntegralProcess (G.grid n) (a n) X (2 ^ n)
  obtain ⟨I, hI, _⟩ := exists_unique_integral_of_bounded_continuous_paths T
    hB hX hX₂ hC hCint hCmon hH hHtop hcts hbounded
  obtain ⟨hJ, hJ₂, hconv⟩ := dyadic_integral_martingale_of_terminal_limit G (T := T) hX hX₂
    (fun j => by simp [G]) (fun j k => hH (G.grid j k))
    (fun j k => hHtop (G.grid j k)) hI
  have hJn (n : ℕ) : Martingale (Jn n) 𝒢 μ :=
    gridIntegralProcess_martingale (G.grid n) hX hX₂ (fun k => hH _) (fun k => hHtop _) _
  have hJncts : ∀ᵐ ω ∂μ, ∀ n, ContinuousOn (fun t => Jn n t ω) (Iic T) :=
    hXcts.mono (fun _ hω n =>
      (gridIntegralProcess_continuous (G.grid n) (a n) (2 ^ n) hω).continuousOn)
  let : Nonempty (Iic T) := ⟨⟨0, Set.mem_Iic.mpr (zero_le : 0 ≤ T)⟩⟩
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Iic T)
  obtain ⟨times, hD⟩ := hDc.exists_eq_range hDd.nonempty
  let times' := fun k => (times k : ℝ≥0)
  have ht' (k : ℕ) : times' k ≤ T := (times k).property
  have hd' : Iic T ⊆ closure (range times') := by
    intro t ht
    have hmem := hDd (⟨t, ht⟩ : Iic T)
    rwa [hD, closure_subtype, ← Set.range_comp] at hmem
  obtain ⟨J, hJm, hJver, hJcts, φ, hφ, huni⟩ :=
    continuous_martingale_version_of_L2_limits hJn hJ hJncts times' ht' hd' hconv
  refine ⟨J, hJm, (fun t => (memLp_congr_ae (hJver t)).2 (hJ₂ t)), hJcts, ?_, φ, hφ, huni⟩
  intro t ht
  refine (hconv t ht).congr' (Eventually.of_forall fun n => ?_)
  exact eLpNorm_congr_ae (EventuallyEq.rfl.sub (hJver t).symm)

end RoughHeston

#print axioms RoughHeston.stochasticStep_martingale
#print axioms RoughHeston.gridIntegralProcess_martingale
#print axioms RoughHeston.gridIntegralProcess_terminal
#print axioms RoughHeston.gridIntegralProcess_continuous

#print axioms RoughHeston.martingale_limit_of_terminal_L2
#print axioms RoughHeston.dyadic_integral_martingale_of_terminal_limit
#print axioms RoughHeston.countable_martingale_maximal_ineq
#print axioms RoughHeston.ae_uniformCauchySeqOn_of_terminal_increment_bounds
#print axioms RoughHeston.continuous_martingale_version_of_L2_limits
#print axioms RoughHeston.exists_continuous_integral_of_bounded_continuous_paths
