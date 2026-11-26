import FixedHestonHorizon
import HestonFubiniKernel
import SHEStochastic.NativeTimeCut

open MeasureTheory ProbabilityTheory Filter Set
open scoped MeasureTheory ProbabilityTheory Topology NNReal ENNReal

namespace RoughHeston

open SHEStochastic

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} {T : ℝ≥0} {W a : ℝ≥0 → Ω → ℝ}

/-- The ordinary past restriction is the fixed-horizon amplitude section. -/
theorem jointAmplitudeSectionLp_eq_prior (t : ℝ≥0)
    (ha₂ : MemLp (Function.uncurry a) 2 (jointPredictableMeasure F μ T)) :
    jointAmplitudeSectionLp t ha₂ = NativeTimeCut.prior t (ha₂.toLp (Function.uncurry a)) := by
  apply Lp.ext
  filter_upwards [jointAmplitudeSectionLp_ae t ha₂,
    NativeTimeCut.prior_ae t (ha₂.toLp (Function.uncurry a)), ha₂.coeFn_toLp,
    ae_fst_mem_Ioo_jointPredictableMeasure (𝒢 := F) (μ := μ) T] with p hs hp ha ht
  erw [hs, hp, ha]
  by_cases h : p.1 ≤ t
  · simp [Set.indicator, h, not_lt.mpr, ht.1]
  · simp [Set.indicator, h, lt_of_not_ge]

/-- Nonnegative continuous amplitudes of finite predictable energy have
a continuous square-integrable martingale integral in the supplied
filtration. Both the actual past section and the dyadic cutoff
specification identify the same process. -/
theorem exists_continuous_joint_amplitude_integral
    (hW : Martingale W F μ) (hW₂ : ∀ t, MemLp (W t) 2 μ)
    (hWc : ∀ᵐ ω ∂μ, Continuous (fun t => W t ω))
    (hClock : Martingale (fun t ω => W t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) F μ)
    (haa : StronglyAdapted F a) (hap : IsStronglyPredictable F a)
    (hac : ∀ ω, Continuous (fun t => a t ω)) (ha : ∀ t ω, 0 ≤ a t ω)
    (ha₂ : MemLp (Function.uncurry a) 2 (jointPredictableMeasure F μ T)) :
    ∃ N : ℝ≥0 → Ω → ℝ, Martingale N F μ ∧ (∀ t, MemLp (N t) 2 μ) ∧
      (∀ᵐ ω ∂μ, Continuous (fun t => N t ω)) ∧ (N 0 =ᵐ[μ] 0) ∧
      (∀ t, N t = N (min t T)) ∧ HasAmplitudeCutoffIntegral F μ T W N a ∧
      ∀ t ≤ T, N t =ᵐ[μ] (jointItoIntegralCLM T hW₂
        (NativeTimeCut.prior t (ha₂.toLp (Function.uncurry a))) : Ω → ℝ) := by
  let A (n : ℕ) (s : ℝ≥0) (ω : Ω) := min (a s ω) (n : ℝ)
  have hAa (n : ℕ) : StronglyAdapted F (A n) := fun s => by
    let : MeasurableSpace Ω := F s
    exact ((haa s).measurable.min measurable_const).stronglyMeasurable
  have hAp (n : ℕ) : IsStronglyPredictable F (A n) := by
    let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    exact (hap.measurable.min measurable_const).stronglyMeasurable
  have hAc (n : ℕ) (ω : Ω) : Continuous (fun t => A n t ω) :=
    (hac ω).min continuous_const
  have hAb (n : ℕ) (s : ℝ≥0) (ω : Ω) : ‖A n s ω‖ ≤ (n : ℝ) :=
    (Real.norm_of_nonneg (le_min (ha s ω) (Nat.cast_nonneg n))).trans_le (min_le_right _ _)
  have hAt (n : ℕ) (s : ℝ≥0) : MemLp (A n s) ⊤ μ :=
    memLp_top_of_bound (((hAa n s).mono (F.le s)).aestronglyMeasurable) n
      (ae_of_all _ (hAb n s))
  let C (t : ℝ≥0) (_ : Ω) : ℝ := (min t T : ℝ≥0)
  have hC : Martingale (fun t => W t * W t - C t) F μ := by
    change Martingale (fun t ω => W t ω * W t ω - ((min t T : ℝ≥0) : ℝ)) F μ
    simpa only [pow_two] using hClock
  have hCm (s t : ℝ≥0) (hst : s ≤ t) : C s ≤ᵐ[μ] C t :=
    ae_of_all _ fun _ => NNReal.coe_le_coe.mpr (min_le_min hst le_rfl)
  have hJex (n : ℕ) := exists_continuous_integral_of_bounded_continuous_paths
    T (Nat.cast_nonneg n) hW hW₂ hWc hC (fun _ => integrable_const _) hCm (hAa n)
    (hAt n) (ae_of_all _ fun ω => (hAc n ω).continuousOn)
    (ae_of_all _ fun ω t _ => hAb n t ω)
  choose K hK hK₂ hKc hKl using hJex
  let J (n : ℕ) (t : ℝ≥0) := K n (min t T)
  have hJ (n : ℕ) : Martingale (J n) F μ := martingale_freeze_at (hK n) T
  have hJ₂ (n : ℕ) (t : ℝ≥0) : MemLp (J n t) 2 μ := hK₂ n _
  have hJl (n : ℕ) (t : ℝ≥0) (ht : t ≤ T) :
      Tendsto (fun j => eLpNorm (gridIntegralProcess ((uniformDyadicGrids T).grid j)
        (fun k => A n ((uniformDyadicGrids T).grid j k)) W (2 ^ j) t - J n t) 2 μ)
        atTop (𝓝 0) := by
    simpa only [J, min_eq_left ht] using (hKl n).1 t ht
  have hJc : ∀ᵐ ω ∂μ, ∀ n, ContinuousOn (fun t => J n t ω) (Iic T) := by
    filter_upwards [ae_all_iff.mpr hKc] with ω hω
    intro n
    exact ((hω n).comp_continuous (continuous_id.min continuous_const)
      (fun t => Set.mem_Iic.mpr (min_le_right t T))).continuousOn
  have hA₂ (n : ℕ) : MemLp (Function.uncurry (A n)) 2 (jointPredictableMeasure F μ T) :=
    MemLp.of_bound (hAp n).aestronglyMeasurable n (ae_of_all _ fun p => hAb n p.1 p.2)
  let I := jointItoIntegralCLM (𝒢 := F) T hW₂
  let u := ha₂.toLp (Function.uncurry a)
  let un (n : ℕ) := (hA₂ n).toLp (Function.uncurry (A n))
  have hul : Tendsto un atTop (𝓝 u) := by
    refine tendsto_iff_edist_tendsto_0.mpr ?_
    simp_rw [un, u, Lp.edist_toLp_toLp]
    apply tendsto_eLpNorm_two_dominated ha₂
      (fun n => ((hAp n).sub hap).aestronglyMeasurable)
    · intro n
      exact ae_of_all _ fun p => by
        change ‖A n p.1 p.2 - a p.1 p.2‖ ≤ ‖a p.1 p.2‖
        rw [Real.norm_of_nonneg (ha p.1 p.2), Real.norm_eq_abs,
          abs_of_nonpos (sub_nonpos.mpr (min_le_left _ _))]
        linarith [le_min (ha p.1 p.2) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    · exact ae_of_all _ fun p => by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [(tendsto_atTop.mp tendsto_natCast_atTop_atTop) (a p.1 p.2)] with n hn
        change (0 : ℝ) = min (a p.1 p.2) (n : ℝ) - a p.1 p.2
        rw [min_eq_left hn, sub_self]
  have hJrep (n : ℕ) : J n T =ᵐ[μ] (I (un n) : Ω → ℝ) :=
    ae_eq_of_same_L2_limit (hJl n T le_rfl)
      (jointItoIntegralCLM_stopped_dyadic le_rfl hW hW₂ hClock (hAa n) (hAp n)
        (ae_of_all _ fun ω => (hAc n ω).continuousOn) (hAb n) (hA₂ n))
  have hIlim : Tendsto (fun n => (hJ₂ n T).toLp (J n T)) atTop (𝓝 (I u)) := by
    have he (n : ℕ) : (hJ₂ n T).toLp (J n T) = I (un n) :=
      Lp.ext ((hJ₂ n T).coeFn_toLp.trans (hJrep n))
    rw [show (fun n => (hJ₂ n T).toLp (J n T)) = ((⇑I) ∘ un) from funext he]
    exact (I.continuous.tendsto u).comp hul
  obtain ⟨hL, hL₂, hLl⟩ := martingale_limit_of_terminal_L2 hJ (fun n => hJ₂ n T) hIlim
  let : Nonempty (Iic T) := ⟨⟨0, Set.mem_Iic.mpr zero_le⟩⟩
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Iic T)
  obtain ⟨times, hD⟩ := hDc.exists_eq_range hDd.nonempty
  let times' := fun k => (times k : ℝ≥0)
  have ht' (k : ℕ) : times' k ≤ T := (times k).property
  have hd' : Iic T ⊆ closure (range times') := by
    intro t ht
    have hm := hDd (⟨t, ht⟩ : Iic T)
    rwa [hD, closure_subtype, ← Set.range_comp] at hm
  obtain ⟨Y, hY, hYver, hYc, _⟩ :=
    continuous_martingale_version_of_L2_limits hJ hL hJc times' ht' hd' hLl
  let N (t : ℝ≥0) := Y (min t T)
  have hNf (t : ℝ≥0) : N t = N (min t T) := by simp only [N, min_assoc, min_self]
  have hNlim (t : ℝ≥0) : Tendsto (fun n => eLpNorm (J n t - N (min t T)) 2 μ) atTop (𝓝 0) := by
    refine (hLl (min t T) (min_le_right _ _)).congr (fun n => ?_)
    simp only [N, J, min_assoc, min_self]
    exact eLpNorm_congr_ae (EventuallyEq.rfl.sub (hYver (min t T)).symm)
  have hCut : HasAmplitudeCutoffIntegral F μ T W N a :=
    ⟨J, hJ, hJ₂, hJl, hNlim⟩
  have hNzero : N 0 =ᵐ[μ] 0 := by
    have hp := hCut.ae_eq_jointIto_fixed_horizon (u := 0) (zero_le : 0 ≤ T)
      hW hW₂ hClock haa hap (ae_of_all _ fun ω => (hac ω).continuousOn) ha ha₂
    have hz : jointAmplitudeSectionLp 0 ha₂ = 0 := by
      apply Lp.ext
      filter_upwards [jointAmplitudeSectionLp_ae 0 ha₂, Lp.coeFn_zero ℝ 2 (jointPredictableMeasure F μ T)] with p h₁ h₂
      simp only [h₁, h₂, Ioc_self, empty_prod, indicator_empty, Pi.zero_apply]
    rw [hz, map_zero] at hp
    exact hp.trans (Lp.coeFn_zero ℝ 2 μ)
  refine ⟨N, martingale_freeze_at hY T, fun t => (memLp_congr_ae (hYver _)).mpr (hL₂ _),
    ?_, hNzero, hNf, hCut, ?_⟩
  · filter_upwards [hYc] with ω hω
    exact hω.comp_continuous (continuous_id.min continuous_const)
      (fun t => Set.mem_Iic.mpr (min_le_right t T))
  · intro t ht
    rw [← jointAmplitudeSectionLp_eq_prior t ha₂]
    exact hCut.ae_eq_jointIto_fixed_horizon ht hW hW₂ hClock haa hap
      (ae_of_all _ fun ω => (hac ω).continuousOn) ha ha₂

end RoughHeston

#print axioms RoughHeston.jointAmplitudeSectionLp_eq_prior
#print axioms RoughHeston.exists_continuous_joint_amplitude_integral
