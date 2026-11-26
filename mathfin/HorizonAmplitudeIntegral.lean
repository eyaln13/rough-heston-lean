import RankOneCompensators
import ClippedDyadicIntegral
import JointHestonConvolution

open MeasureTheory ProbabilityTheory Filter Set
open scoped MeasureTheory ProbabilityTheory Topology NNReal ENNReal

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℝ≥0 m} {B M a : ℝ≥0 → Ω → ℝ}

private theorem gridIntegralProcess_freeze_driver (grid : ℕ →o ℝ≥0)
    (W : ℕ → Ω → ℝ) (n : ℕ) (t : ℝ≥0) :
    gridIntegralProcess grid W (fun s => B (min s t)) n t =
      gridIntegralProcess grid W B n t := by
  funext ω
  unfold gridIntegralProcess
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  simp only [stochasticStep, Pi.mul_apply, Pi.sub_apply,
    min_eq_left (min_le_left t (grid (k + 1))), min_eq_left (min_le_left t (grid k))]

/-- The amplitude representation obtained from the common driver agrees,
at each earlier observation time, with the Itô map built on that shorter
horizon. -/
theorem HasAmplitudeCutoffIntegral.ae_eq_jointItoAt [IsFiniteMeasure μ]
    {T t : ℝ≥0} (htT : t ≤ T) (h : HasAmplitudeCutoffIntegral 𝒢 μ T B M a)
    (hB : Martingale B 𝒢 μ) (hB₂ : ∀ s, MemLp (B s) 2 μ)
    (hclock : Martingale (fun s ω => B s ω ^ 2 - ((min s T : ℝ≥0) : ℝ)) 𝒢 μ)
    (haa : StronglyAdapted 𝒢 a)
    (hasm : StronglyMeasurable[𝒢.predictable] (Function.uncurry a))
    (hac : ∀ᵐ ω ∂μ, ContinuousOn (fun s => a s ω) (Icc 0 t))
    (ha : ∀ s ω, 0 ≤ a s ω)
    (ha₂ : MemLp (Function.uncurry a) 2 (jointPredictableMeasure 𝒢 μ t)) :
    let hB₂t (s : ℝ≥0) := hB₂ (min s t)
    M t =ᵐ[μ] (jointItoIntegralCLM (𝒢 := 𝒢) t hB₂t
      (ha₂.toLp (Function.uncurry a)) : Ω → ℝ) := by
  dsimp only
  let Bt (s : ℝ≥0) := B (min s t)
  let hB₂t (s : ℝ≥0) : MemLp (Bt s) 2 μ := hB₂ (min s t)
  let I := jointItoIntegralCLM (𝒢 := 𝒢) t hB₂t
  let H (n : ℕ) (s : ℝ≥0) (ω : Ω) := min (a s ω) (n : ℝ)
  have hHa (n : ℕ) : StronglyAdapted 𝒢 (H n) := by
    intro s
    let : MeasurableSpace Ω := 𝒢 s
    exact ((haa s).measurable.min measurable_const).stronglyMeasurable
  have hHsm (n : ℕ) : StronglyMeasurable[𝒢.predictable] (Function.uncurry (H n)) := by
    let : MeasurableSpace (ℝ≥0 × Ω) := 𝒢.predictable
    exact (hasm.measurable.min measurable_const).stronglyMeasurable
  have hHcts (n : ℕ) : ∀ᵐ ω ∂μ, ContinuousOn (fun s => H n s ω) (Icc 0 t) := by
    filter_upwards [hac] with ω hω
    exact continuous_min.comp_continuousOn (hω.prodMk continuousOn_const)
  have hHbd (n : ℕ) (s : ℝ≥0) (ω : Ω) : ‖H n s ω‖ ≤ (n : ℝ) :=
    (Real.norm_of_nonneg (le_min (ha s ω) (Nat.cast_nonneg n))).trans_le (min_le_right _ _)
  have hH₂ (n : ℕ) : MemLp (Function.uncurry (H n)) 2 (jointPredictableMeasure 𝒢 μ t) :=
    MemLp.of_bound (hHsm n).aestronglyMeasurable (n : ℝ)
      (Eventually.of_forall fun z => hHbd n z.1 z.2)
  let A := ha₂.toLp (Function.uncurry a)
  let Aclip (n : ℕ) := (hH₂ n).toLp (Function.uncurry (H n))
  have hBtm : Martingale Bt 𝒢 μ := martingale_freeze_at hB t
  have hBtclock : Martingale (fun s ω => Bt s ω ^ 2 - ((min s t : ℝ≥0) : ℝ)) 𝒢 μ := by
    simpa only [Bt, min_assoc, min_eq_left htT] using martingale_freeze_at hclock t
  obtain ⟨J, _, _, hJl, hMlim⟩ := h
  have hJrep (n : ℕ) : J n t =ᵐ[μ] (I (Aclip n) : Ω → ℝ) := by
    apply ae_eq_of_same_L2_limit (hJl n t htT)
    have hcut := jointItoIntegralCLM_stopped_dyadic htT hBtm hB₂t hBtclock
      (hHa n) (hHsm n) (hHcts n) (hHbd n) (hH₂ n)
    refine hcut.congr (fun j => ?_)
    rw [show gridIntegralProcess ((uniformDyadicGrids T).grid j)
        (fun k => H n ((uniformDyadicGrids T).grid j k)) Bt (2 ^ j) t =
      gridIntegralProcess ((uniformDyadicGrids T).grid j)
        (fun k => H n ((uniformDyadicGrids T).grid j k)) B (2 ^ j) t from
          gridIntegralProcess_freeze_driver _ _ _ _]
  have hdist (n : ℕ) : edist (Aclip n) A =
      eLpNorm (Function.uncurry (H n) - Function.uncurry a) 2 (jointPredictableMeasure 𝒢 μ t) :=
    Lp.edist_toLp_toLp _ _ _ _
  have hl : Tendsto Aclip atTop (𝓝 A) := by
    refine tendsto_iff_edist_tendsto_0.mpr ?_
    simp_rw [hdist]
    apply tendsto_eLpNorm_two_dominated ha₂
      (fun n => ((hHsm n).sub hasm).aestronglyMeasurable)
    · intro n
      exact Eventually.of_forall fun z => by
        change ‖min (a z.1 z.2) (n : ℝ) - a z.1 z.2‖ ≤ ‖a z.1 z.2‖
        rw [Real.norm_of_nonneg (ha z.1 z.2), Real.norm_eq_abs,
          abs_of_nonpos (sub_nonpos.mpr (min_le_left _ _))]
        linarith [le_min (ha z.1 z.2) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    · exact Eventually.of_forall fun z => by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [(tendsto_atTop.mp tendsto_natCast_atTop_atTop) (a z.1 z.2)] with n hn
        change (0 : ℝ) = min (a z.1 z.2) (n : ℝ) - a z.1 z.2
        rw [min_eq_left hn, sub_self]
  have hI : Tendsto (fun n => eLpNorm ((I (Aclip n) : Ω → ℝ) - (I A : Ω → ℝ)) 2 μ)
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Lp.edist_def] using
      tendsto_iff_edist_tendsto_0.mp ((I.continuous.tendsto A).comp hl)
  have hM' : Tendsto (fun n => eLpNorm (J n t - M t) 2 μ) atTop (𝓝 0) := by
    simpa only [min_eq_left htT] using hMlim t
  exact ae_eq_of_same_L2_limit hM' (hI.congr (fun n => eLpNorm_congr_ae ((hJrep n).symm.sub EventuallyEq.rfl)))

end RoughHeston

#print axioms RoughHeston.HasAmplitudeCutoffIntegral.ae_eq_jointItoAt
