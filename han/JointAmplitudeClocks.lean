import AffineContinuousEnergyClock
import RankOneCompensators

open MeasureTheory ProbabilityTheory Filter Set
open scoped MeasureTheory ProbabilityTheory Topology NNReal ENNReal Interval

namespace RoughHeston

open SHEStochastic GirsanovPort

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} {T : ℝ≥0} {W a N : ℝ≥0 → Ω → ℝ}

/-- Pathwise primitive of a time process, frozen at the terminal time. -/
noncomputable def stoppedAmplitudePrimitive (T : ℝ≥0) (f : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ s in (0 : ℝ)..((min t T : ℝ≥0) : ℝ), f s.toNNReal ω

theorem stoppedAmplitudePrimitive_adapted {f : ℝ≥0 → Ω → ℝ}
    (hf : StronglyAdapted F f) (hc : ∀ ω, Continuous (fun t => f t ω)) :
    StronglyAdapted F (stoppedAmplitudePrimitive T f) := fun t => by
  have h := (weighted_time_primitive_stronglyMeasurable hf hc
    (d := fun _ => 1) measurable_const (min t T)).mono (F.mono (min_le_left t T))
  change StronglyMeasurable[F t] (fun ω => ∫ s in (0 : ℝ)..((min t T : ℝ≥0) : ℝ), f s.toNNReal ω)
  simpa only [one_mul] using h

theorem stoppedAmplitudePrimitive_continuous {f : ℝ≥0 → Ω → ℝ}
    (hc : ∀ ω, Continuous (fun t => f t ω)) (ω : Ω) :
    Continuous (fun t => stoppedAmplitudePrimitive T f t ω) := by
  have h := (hc ω).comp continuous_real_toNNReal
  exact (intervalIntegral.continuous_primitive (fun x y => h.intervalIntegrable x y) 0).comp
    (NNReal.continuous_coe.comp (continuous_id.min continuous_const))

@[simp] theorem stoppedAmplitudePrimitive_zero {f : ℝ≥0 → Ω → ℝ} :
    stoppedAmplitudePrimitive T f 0 = 0 := by
  funext ω
  change (∫ s in (0 : ℝ)..((min 0 T : ℝ≥0) : ℝ), f s.toNNReal ω) = 0
  simp only [min_eq_left zero_le, NNReal.coe_zero, intervalIntegral.integral_same]

/-- A continuous nonnegative row has a nondecreasing bracket clock. -/
theorem stoppedAmplitudePrimitive_monotone {f : ℝ≥0 → Ω → ℝ}
    (hc : ∀ ω, Continuous (fun t => f t ω)) (hf : ∀ t ω, 0 ≤ f t ω) (ω : Ω) :
    Monotone (fun t => stoppedAmplitudePrimitive T f t ω) := by
  intro s t hst
  let u : ℝ := (min s T : ℝ≥0)
  let v : ℝ := (min t T : ℝ≥0)
  have huv : u ≤ v := NNReal.coe_le_coe.mpr (min_le_min_right T hst)
  have h : Continuous (fun r : ℝ => f r.toNNReal ω) :=
    (hc ω).comp continuous_real_toNNReal
  change (∫ r in (0 : ℝ)..u, f r.toNNReal ω) ≤ ∫ r in (0 : ℝ)..v, f r.toNNReal ω
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (h.intervalIntegrable 0 u) (h.intervalIntegrable u v)]
  exact le_add_of_nonneg_right (intervalIntegral.integral_nonneg_of_forall huv (fun _ => hf _ _))

omit [IsProbabilityMeasure μ] in
private theorem primitive_clipped_power_bounds
    (haa : StronglyAdapted F a) (hac : ∀ ω, Continuous (fun t => a t ω))
    (ha : ∀ t ω, 0 ≤ a t ω) (p : ℕ)
    (hT : Integrable (stoppedAmplitudePrimitive T (fun t ω => a t ω ^ p) T) μ) :
    let A (n : ℕ) := stoppedAmplitudePrimitive T (fun t ω => min (a t ω) (n : ℝ) ^ p)
    let B := stoppedAmplitudePrimitive T (fun t ω => a t ω ^ p)
    (∀ t, Integrable (B t) μ) ∧ (∀ n t, Integrable (A n t) μ) ∧
      ∀ t, Tendsto (fun n => eLpNorm (A n t - B t) 1 μ) atTop (𝓝 0) := by
  let A (n : ℕ) := stoppedAmplitudePrimitive T (fun t ω => min (a t ω) (n : ℝ) ^ p)
  let B := stoppedAmplitudePrimitive T (fun t ω => a t ω ^ p)
  let c (t : ℝ≥0) := ((min t T : ℝ≥0) : ℝ)
  have hc (t : ℝ≥0) : 0 ≤ c t := (min t T).coe_nonneg
  have hct (t : ℝ≥0) : c t ≤ (T : ℝ) := NNReal.coe_le_coe.mpr (min_le_right _ _)
  have hcA (n : ℕ) (ω : Ω) : Continuous (fun t => min (a t ω) (n : ℝ) ^ p) :=
    ((hac ω).min continuous_const).pow p
  have hAA (n : ℕ) : StronglyAdapted F (A n) := by
    apply stoppedAmplitudePrimitive_adapted _ (hcA n)
    intro t
    let : MeasurableSpace Ω := F t
    exact (((haa t).measurable.min measurable_const).stronglyMeasurable).pow p
  have hBA : StronglyAdapted F B := stoppedAmplitudePrimitive_adapted
    (fun t => (haa t).pow p) (fun ω => (hac ω).pow p)
  have hA0 (n : ℕ) (t : ℝ≥0) (ω : Ω) : 0 ≤ A n t ω :=
    intervalIntegral.integral_nonneg_of_forall (hc t) (fun _ =>
      pow_nonneg (le_min (ha _ _) (Nat.cast_nonneg n)) p)
  have hAB (n : ℕ) (t : ℝ≥0) (ω : Ω) : A n t ω ≤ B t ω :=
    intervalIntegral.integral_mono_on (hc t)
      (((hcA n ω).comp continuous_real_toNNReal).intervalIntegrable _ _)
      (((hac ω).pow p |>.comp continuous_real_toNNReal).intervalIntegrable _ _)
      (fun s _ => pow_le_pow_left₀ (le_min (ha s.toNNReal ω) (Nat.cast_nonneg n)) (min_le_left _ _) _)
  have hBT (t : ℝ≥0) (ω : Ω) : B t ω ≤ B T ω := by
    have hf : Continuous (fun s : ℝ => a s.toNNReal ω ^ p) :=
      ((hac ω).comp continuous_real_toNNReal).pow p
    change (∫ s in (0:ℝ)..c t, a s.toNNReal ω ^ p) ≤ ∫ s in (0:ℝ)..c T, a s.toNNReal ω ^ p
    have he : c T = (T : ℝ) := by simp [c]
    rw [he, ← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable 0 (c t)) (hf.intervalIntegrable (c t) T)]
    exact le_add_of_nonneg_right
      (intervalIntegral.integral_nonneg_of_forall (hct t) (fun _ => pow_nonneg (ha _ _) _))
  have hBi (t : ℝ≥0) : Integrable (B t) μ := hT.mono'
    (((hBA t).mono (F.le t)).aestronglyMeasurable)
    (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg ((hA0 0 t ω).trans (hAB 0 t ω))]
      exact hBT t ω)
  have hAi (n : ℕ) (t : ℝ≥0) : Integrable (A n t) μ := (hBi t).mono'
    (((hAA n t).mono (F.le t)).aestronglyMeasurable)
    (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (hA0 n t ω)]
      exact hAB n t ω)
  refine ⟨hBi, hAi, fun t => ?_⟩
  have hb (n : ℕ) : ∀ᵐ ω ∂μ, ‖(A n t - B t) ω‖ ≤ B T ω := ae_of_all _ fun ω => by
    rw [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (hAB n t ω))]
    linarith [hA0 n t ω, hBT t ω]
  have hpoint : ∀ᵐ ω ∂μ, Tendsto (fun n => ‖(A n t - B t) ω‖) atTop (𝓝 ((0 : Ω → ℝ) ω)) := by
    refine ae_of_all _ fun ω => ?_
    obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image
      ((hac ω).continuousOn (s := Icc (0 : ℝ≥0) T))
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(tendsto_atTop.mp tendsto_natCast_atTop_atTop) M] with n hn
    have he : A n t ω = B t ω := by
      unfold A B stoppedAmplitudePrimitive
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le (hc t)]
      intro s hs
      have hsT : s.toNNReal ≤ T := NNReal.coe_le_coe.mp (by
        rw [Real.coe_toNNReal _ hs.1]
        exact hs.2.trans (hct t))
      change min (a s.toNNReal ω) (n : ℝ) ^ p = a s.toNNReal ω ^ p
      rw [min_eq_left ((hM (mem_image_of_mem _ ⟨zero_le, hsT⟩)).trans hn)]
    simp only [Pi.zero_apply, Pi.sub_apply, he, sub_self, norm_zero]
  have hi := tendsto_integral_of_dominated_convergence (B T)
    (fun n => ((hAi n t).sub (hBi t)).norm.aestronglyMeasurable) hT
    (fun n => by simpa only [norm_norm] using hb n) hpoint
  have he (n : ℕ) : eLpNorm (A n t - B t) 1 μ =
      ENNReal.ofReal (∫ ω, ‖(A n t - B t) ω‖ ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm ((hAi n t).sub (hBi t)).aestronglyMeasurable,
      ofReal_integral_norm_eq_lintegral_enorm ((hAi n t).sub (hBi t))]
  simpa only [Function.comp_def, ← he, Pi.zero_apply, integral_zero, ENNReal.ofReal_zero]
    using (ENNReal.continuous_ofReal.tendsto _).comp hi

omit [IsProbabilityMeasure μ] in
private theorem gridIntegralProcess_one_ae (hW0 : W 0 =ᵐ[μ] 0)
    (j : ℕ) (t : ℝ≥0) (ht : t ≤ T) :
    gridIntegralProcess ((uniformDyadicGrids T).grid j) (fun _ _ => 1) W (2 ^ j) t =ᵐ[μ] W t := by
  let g := (uniformDyadicGrids T).grid j
  have hs (n : ℕ) :
      ∑ k ∈ Finset.range n, stochasticStep (g k) (g (k+1)) (fun _ => 1) W t =
        W (min t (g n)) - W (min t (g 0)) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [stochasticStep, ← Pi.one_def, one_mul]
      abel
  unfold gridIntegralProcess
  rw [Finset.sum_apply]
  change (∑ k ∈ Finset.range (2^j), stochasticStep (g k) (g (k+1)) (fun _ => 1) W t)
    =ᵐ[μ] W t
  rw [hs, show g (2^j) = T from uniform_dyadic_terminal_vertex T j,
    show g 0 = 0 from uniform_dyadic_first_vertex T j, min_eq_left ht, min_eq_right zero_le]
  exact (EventuallyEq.rfl.sub hW0).trans (Eventually.of_forall fun ω => sub_zero (W t ω))

/-- The same amplitude cutoff integral has its actual square bracket and
mixed compensator with the driving martingale. -/
theorem amplitudeCutoff_actual_clocks
    (hW : Martingale W F μ) (hW₂ : ∀ t, MemLp (W t) 2 μ)
    (hW0 : W 0 =ᵐ[μ] 0) (hWf : ∀ t, W t = W (min t T))
    (hClock : Martingale (fun t ω => W t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) F μ)
    (hN : Martingale N F μ) (hN₂ : ∀ t, MemLp (N t) 2 μ)
    (hNf : ∀ t, N t = N (min t T)) (hCut : HasAmplitudeCutoffIntegral F μ T W N a)
    (haa : StronglyAdapted F a) (hap : IsStronglyPredictable F a)
    (hac : ∀ ω, Continuous (fun t => a t ω)) (ha : ∀ t ω, 0 ≤ a t ω)
    (ha₂ : MemLp (Function.uncurry a) 2 (jointPredictableMeasure F μ T)) :
    (∀ t, Integrable (stoppedAmplitudePrimitive T (fun s ω => a s ω ^ 2) t) μ) ∧
    Martingale (fun t => N t * N t - stoppedAmplitudePrimitive T (fun s ω => a s ω ^ 2) t) F μ ∧
    Martingale (fun t => N t * W t - stoppedAmplitudePrimitive T a t) F μ := by
  let C (t : ℝ≥0) (_ : Ω) : ℝ := (min t T : ℝ≥0)
  have hC : Martingale (fun t => W t * W t - C t) F μ := by
    change Martingale (fun t ω => W t ω * W t ω - ((min t T : ℝ≥0) : ℝ)) F μ
    simpa only [pow_two] using hClock
  have hCeq (t : ℝ≥0) (ht : t ≤ T) :
      C t =ᵐ[μ] fun _ => ∫ _s in (0:ℝ)..(t:ℝ), (1:ℝ) :=
    ae_of_all _ fun ω => by
      change ((min t T : ℝ≥0) : ℝ) = _
      rw [min_eq_left ht]
      simp
  have hD : ∀ᵐ ω ∂μ, IntervalIntegrable (fun _s : ℝ => (1:ℝ)) volume 0 T :=
    ae_of_all _ fun _ => intervalIntegrable_const
  have hDi : Integrable (fun _ : Ω => ∫ _s in (0:ℝ)..(T:ℝ), |(1:ℝ)|) μ := integrable_const _
  obtain ⟨J, hJ, hJ₂, hJl, hNlim⟩ := hCut
  let K (n : ℕ) (t : ℝ≥0) := J n (min t T)
  let clip (n : ℕ) (t : ℝ≥0) (ω : Ω) := min (a t ω) (n : ℝ)
  have hK (n : ℕ) : Martingale (K n) F μ := martingale_freeze_at (hJ n) T
  have hK₂ (n : ℕ) (t : ℝ≥0) : MemLp (K n t) 2 μ := hJ₂ n _
  have hKl (n : ℕ) (t : ℝ≥0) (ht : t ≤ T) :
      Tendsto (fun j => eLpNorm (gridIntegralProcess ((uniformDyadicGrids T).grid j)
        (fun k => clip n ((uniformDyadicGrids T).grid j k)) W (2 ^ j) t - K n t) 2 μ)
        atTop (𝓝 0) := by
    simpa only [K, min_eq_left ht] using hJl n t ht
  have hKlim (t : ℝ≥0) : Tendsto (fun n => eLpNorm (K n t - N t) 2 μ) atTop (𝓝 0) := by
    simpa only [K, min_assoc, min_self, ← hNf t] using hNlim (min t T)
  have hca (n : ℕ) : StronglyAdapted F (clip n) := fun t => by
    let : MeasurableSpace Ω := F t
    exact ((haa t).measurable.min measurable_const).stronglyMeasurable
  have hccts (n : ℕ) (ω : Ω) : Continuous (fun t => clip n t ω) :=
    (hac ω).min continuous_const
  have hcbd (n : ℕ) (t : ℝ≥0) (ω : Ω) : |clip n t ω| ≤ (n : ℝ) :=
    (abs_of_nonneg (le_min (ha t ω) (Nat.cast_nonneg n))).trans_le (min_le_right _ _)
  have hctop (n : ℕ) (t : ℝ≥0) : MemLp (clip n t) ⊤ μ :=
    memLp_top_of_bound (((hca n t).mono (F.le t)).aestronglyMeasurable) n
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hcbd n t ω)
  have hlW (t : ℝ≥0) (ht : t ≤ T) :
      Tendsto (fun j => eLpNorm (gridIntegralProcess ((uniformDyadicGrids T).grid j)
        (fun _ _ => 1) W (2 ^ j) t - W t) 2 μ) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr (fun j => ?_)
    have he := (gridIntegralProcess_one_ae (T := T) hW0 j t ht).sub
      (EventuallyEq.rfl : W t =ᵐ[μ] W t)
    rw [eLpNorm_congr_ae he, sub_self, eLpNorm_zero]
  let u := ha₂.toLp (Function.uncurry a)
  have hEi : Integrable (stoppedAmplitudePrimitive T (fun s ω => a s ω ^ 2) T) μ := by
    change Integrable (fun ω => ∫ s in (0 : ℝ)..((min T T : ℝ≥0) : ℝ), a s.toNNReal ω ^ 2) μ
    rw [min_self]
    exact (NativeEnergy.integrable (NativeTimeCut.prior T u)).congr
        (affineEnergyClock_prior_eq u hap ha₂.coeFn_toLp (le_rfl : T ≤ T))
  have hMi : Integrable (stoppedAmplitudePrimitive T a T) μ := by
    have hs : Integrable (fun ω => ∫ s in (0 : ℝ)..(T : ℝ), a s.toNNReal ω ^ 2) μ := by
      have he : stoppedAmplitudePrimitive T (fun s ω => a s ω ^ 2) T =
          (fun ω => ∫ s in (0 : ℝ)..(T : ℝ), a s.toNNReal ω ^ 2) := by
        funext ω
        change (∫ s in (0 : ℝ)..((min T T : ℝ≥0) : ℝ), a s.toNNReal ω ^ 2) = _
        rw [min_self]
      rwa [he] at hEi
    change Integrable (fun ω => ∫ s in (0 : ℝ)..((min T T : ℝ≥0) : ℝ), a s.toNNReal ω) μ
    rw [min_self]
    have hi := amplitude_mass_integrable_of_energy haa (ae_of_all _ fun ω => (hac ω).continuousOn) hs
    refine hi.congr (ae_of_all _ fun ω => ?_)
    apply intervalIntegral.integral_congr
    intro s _
    exact abs_of_nonneg (ha _ _)
  obtain ⟨hEi', hEci, hEl⟩ := primitive_clipped_power_bounds haa hac ha 2 hEi
  obtain ⟨hMi', hMci, hMl⟩ := primitive_clipped_power_bounds haa hac ha 1 (by simpa using hMi)
  let E := stoppedAmplitudePrimitive T (fun s ω => a s ω ^ 2)
  let Ec (n : ℕ) := stoppedAmplitudePrimitive T (fun s ω => clip n s ω ^ 2)
  let M := stoppedAmplitudePrimitive T a
  let Mc (n : ℕ) := stoppedAmplitudePrimitive T (clip n)
  have hE := stoppedAmplitudePrimitive_adapted (T := T) (fun t => (haa t).pow 2)
    (fun ω => (hac ω).pow 2)
  have hM := stoppedAmplitudePrimitive_adapted (T := T) haa hac
  have hEc (n : ℕ) : Martingale (fun t => K n t * K n t - Ec n t) F μ := by
    obtain ⟨Cw, hCw, hm⟩ := continuous_integrals_compensated_product T (mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) (Nat.cast_nonneg n))
      hW hW hC hW₂ hW₂ (hca n) (hca n) (hctop n) (hctop n)
      (hK n).stronglyAdapted (hK n).stronglyAdapted (hK₂ n) (hK₂ n)
      hCeq (ae_of_all _ fun ω => ((hccts n ω).mul (hccts n ω)).continuousOn)
      (ae_of_all _ fun ω t _ => by
        rw [abs_mul]
        exact mul_le_mul (hcbd n t ω) (hcbd n t ω) (abs_nonneg _) (Nat.cast_nonneg n))
      hD (ae_of_all _ fun ω => by
        simp only [mul_one]
        have hc : Continuous (fun s : ℝ => clip n s.toNNReal ω * clip n s.toNNReal ω) :=
          ((hccts n ω).comp continuous_real_toNNReal).mul ((hccts n ω).comp continuous_real_toNNReal)
        exact hc.intervalIntegrable 0 T) hDi (hKl n) (hKl n)
    have had := stoppedAmplitudePrimitive_adapted (T := T) (fun t => (hca n t).pow 2)
      (fun ω => (hccts n ω).pow 2)
    have hs (t : ℝ≥0) : K n (min t T) = K n t := by simp [K]
    refine ⟨fun t => (((hK n).stronglyAdapted t).mul ((hK n).stronglyAdapted t)).sub (had t), ?_⟩
    have he (t : ℝ≥0) :
        K n (min t T) * K n (min t T) - Cw t =ᵐ[μ] K n t * K n t - Ec n t := by
      rw [hs]
      refine EventuallyEq.rfl.sub ?_
      change Cw t =ᵐ[μ] fun ω => ∫ s in (0 : ℝ)..((min t T : ℝ≥0) : ℝ), clip n s.toNNReal ω ^ 2
      simpa only [pow_two, mul_one] using hCw t
    intro s t hst
    exact (condExp_congr_ae (he t).symm).trans ((hm.condExp_ae_eq hst).trans (he s))
  have hMc (n : ℕ) : Martingale (fun t => K n t * W t - Mc n t) F μ := by
    obtain ⟨Cw, hCw, hm⟩ := continuous_integrals_compensated_product T (Nat.cast_nonneg n)
      hW hW hC hW₂ hW₂ (hca n) (fun _ => stronglyMeasurable_const) (hctop n)
      (fun _ => memLp_const (1:ℝ))
      (hK n).stronglyAdapted hW.stronglyAdapted (hK₂ n) hW₂
      hCeq (ae_of_all _ fun ω => by simpa only [mul_one] using (hccts n ω).continuousOn)
      (ae_of_all _ fun ω t _ => by simpa only [mul_one] using hcbd n t ω)
      hD (ae_of_all _ fun ω => by
        simp only [mul_one]
        have hc : Continuous (fun s : ℝ => clip n s.toNNReal ω) :=
          (hccts n ω).comp continuous_real_toNNReal
        exact hc.intervalIntegrable 0 T)
      hDi (hKl n) hlW
    have had := stoppedAmplitudePrimitive_adapted (T := T) (hca n) (hccts n)
    have hs (t : ℝ≥0) : K n (min t T) = K n t := by simp [K]
    refine ⟨fun t => (((hK n).stronglyAdapted t).mul (hW.stronglyAdapted t)).sub (had t), ?_⟩
    have he (t : ℝ≥0) :
        K n (min t T) * W (min t T) - Cw t =ᵐ[μ] K n t * W t - Mc n t := by
      rw [hs, ← hWf t]
      refine EventuallyEq.rfl.sub ?_
      change Cw t =ᵐ[μ] fun ω => ∫ s in (0 : ℝ)..((min t T : ℝ≥0) : ℝ), clip n s.toNNReal ω
      simpa only [mul_one] using hCw t
    intro s t hst
    exact (condExp_congr_ae (he t).symm).trans ((hm.condExp_ae_eq hst).trans (he s))
  refine ⟨hEi', ?_, ?_⟩
  · exact compensated_product_martingale_of_limits hN.stronglyAdapted hN.stronglyAdapted hE
      hN₂ hN₂ hK₂ hK₂ hEi' hEci hEc hKlim hKlim hEl
  · apply compensated_product_martingale_of_limits hN.stronglyAdapted hW.stronglyAdapted hM
      hN₂ hW₂ hK₂ (fun _ => hW₂) (by simpa [M] using hMi')
      (by simpa only [Mc, clip, pow_one] using hMci) hMc hKlim
      (fun _ => by simpa only [sub_self, eLpNorm_zero] using tendsto_const_nhds)
    simpa only [M, Mc, clip, pow_one] using hMl

end RoughHeston

#print axioms RoughHeston.stoppedAmplitudePrimitive_adapted
#print axioms RoughHeston.stoppedAmplitudePrimitive_continuous
#print axioms RoughHeston.stoppedAmplitudePrimitive_monotone
#print axioms RoughHeston.amplitudeCutoff_actual_clocks
