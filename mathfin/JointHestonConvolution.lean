import JointDyadicIntegral
import JointHestonCutoffPath

open MeasureTheory ProbabilityTheory Filter Set
open scoped MeasureTheory ProbabilityTheory Topology NNReal ENNReal

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℝ≥0 m} {V B : ℝ≥0 → Ω → ℝ}

/-- The predictable Itô integral of the full Heston weight satisfies
the two successive dyadic and cutoff limits in the variance theorem. -/
theorem isHestonConvolutionAt_jointIto [IsFiniteMeasure μ] {α : ℝ}
    (hα : 1 / 2 < α) (hα' : α ≤ 1) (t : ℝ≥0)
    (hB : Martingale B 𝒢 μ) (hB₂ : ∀ s, MemLp (B s) 2 μ)
    (hclock : Martingale (fun s ω => B s ω ^ 2 - ((min s t : ℝ≥0) : ℝ)) 𝒢 μ)
    (hVp : IsStronglyPredictable 𝒢 V) (hVa : StronglyAdapted 𝒢 V)
    (hVc : ∀ᵐ ω ∂μ, ContinuousOn (fun s => V s ω) (Icc 0 t))
    (hVnonneg : ∀ s ω, 0 ≤ V s ω)
    (hVint : ∀ s, Integrable (V s) μ) {C : ℝ}
    (hmean : ∀ s, (∫ ω, V s ω ∂μ) ≤ C) :
    let hw := heston_convolution_weight_memLp_two_joint hα t hVp hVnonneg hVint hmean
    IsHestonConvolutionAt μ α t B V
      (jointItoIntegralCLM t hB₂ (hw.toLp (Function.uncurry (hestonConvolutionWeight α t V))) :
        Ω → ℝ) := by
  dsimp only
  let I := jointItoIntegralCLM (𝒢 := 𝒢) t hB₂
  let H := Function.uncurry (hestonConvolutionWeight α t V)
  let hw := heston_convolution_weight_memLp_two_joint hα t hVp hVnonneg hVint hmean
  let w := hw.toLp H
  have hpos : 0 < α := lt_trans (by norm_num) hα
  let Hcut (n : ℕ) := hestonCutoffWeight α t V n
  let hwcut (n : ℕ) := heston_cutoff_weight_memLp_two_joint (μ := μ) hpos hα' t hVp n
  let wcut (n : ℕ) := (hwcut n).toLp (Function.uncurry (Hcut n))
  refine ⟨Lp.memLp (I w), fun n => (I (wcut n) : Ω → ℝ), fun n => ?_, ?_⟩
  · refine ⟨Lp.memLp (I (wcut n)), ?_⟩
    exact jointItoIntegralCLM_dyadic t hB hB₂ hclock
      (heston_cutoffWeight_stronglyAdapted hVa α t n)
      (heston_cutoffWeight_predictable α t hVp n)
      (heston_cutoffWeight_ae_continuousOn α t n hVc)
      (heston_cutoffWeight_bound hpos hα' t V n) (hwcut n)
  · have hdist (n : ℕ) : edist (wcut n) w = eLpNorm
        (fun z : ℝ≥0 × Ω => Hcut n z.1 z.2 - hestonConvolutionWeight α t V z.1 z.2)
        2 (jointPredictableMeasure 𝒢 μ t) :=
      Lp.edist_toLp_toLp _ _ _ _
    have hwlim : Tendsto wcut atTop (𝓝 w) := tendsto_iff_edist_tendsto_0.mpr (by
      simpa only [hdist, Hcut] using heston_cutoff_weight_L2_joint_of_uniform_mean
        hα hα' t hVp hVnonneg hVint hmean)
    have hIlim := (I.continuous.tendsto w).comp hwlim
    change Tendsto (fun n => eLpNorm ((I (wcut n) : Ω → ℝ) - (I w : Ω → ℝ))
      2 μ) atTop (𝓝 0)
    simpa only [Function.comp_apply, Lp.edist_def] using tendsto_iff_edist_tendsto_0.mp hIlim

theorem ae_eq_of_same_L2_limit {F : ℕ → Ω → ℝ} {x y : Ω → ℝ}
    (hx : Tendsto (fun n => eLpNorm (F n - x) 2 μ) atTop (𝓝 0))
    (hy : Tendsto (fun n => eLpNorm (F n - y) 2 μ) atTop (𝓝 0)) : x =ᵐ[μ] y := by
  have htriangle (n : ℕ) : eLpNorm (x - y) 2 μ ≤
      eLpNorm (F n - x) 2 μ + eLpNorm (F n - y) 2 μ := by
    rw [show x - y = -(F n - x) + (F n - y) by abel]
    simpa only [eLpNorm_neg] using
      (eLpNorm_add_le (μ := μ) (p := 2) (f := -(F n - x)) (g := F n - y) (by norm_num))
  have hlim : Tendsto (fun n => eLpNorm (F n - x) 2 μ + eLpNorm (F n - y) 2 μ)
      atTop (𝓝 0) := by simpa only [zero_add] using hx.add hy
  have hzero : eLpNorm (x - y) 2 μ = 0 :=
    le_antisymm (le_of_tendsto_of_tendsto' tendsto_const_nhds hlim htriangle) zero_le
  have h := (eLpNorm_eq_zero_iff (by norm_num : (2 : ENNReal) ≠ 0)).1 hzero
  exact h.mono (fun _ hw => sub_eq_zero.mp hw)

/-- The dyadic-cutoff specification determines the stochastic
convolution up to almost sure equality at the specified time. -/
theorem IsHestonConvolutionAt.ae_unique {α : ℝ} {t : ℝ≥0} {z z' : Ω → ℝ}
    (h : IsHestonConvolutionAt μ α t B V z)
    (h' : IsHestonConvolutionAt μ α t B V z') : z =ᵐ[μ] z' := by
  obtain ⟨_, J, hJ, hj⟩ := h
  obtain ⟨_, J', hJ', hj'⟩ := h'
  have he (n : ℕ) : J n =ᵐ[μ] J' n := ae_eq_of_same_L2_limit (hJ n).2 (hJ' n).2
  exact ae_eq_of_same_L2_limit hj
    (hj'.congr fun n => eLpNorm_congr_ae ((he n).symm.sub EventuallyEq.rfl))

/-- The definition agrees for timewise almost surely equal drivers. -/
theorem IsHestonConvolutionAt.congr_driver {α : ℝ} {t : ℝ≥0} {B' : ℝ≥0 → Ω → ℝ}
    {z : Ω → ℝ} (h : IsHestonConvolutionAt μ α t B V z)
    (he : ∀ s, B s =ᵐ[μ] B' s) : IsHestonConvolutionAt μ α t B' V z := by
  obtain ⟨hz, J, hJ, hj⟩ := h
  refine ⟨hz, J, fun n => ⟨(hJ n).1, (hJ n).2.congr (fun j => ?_)⟩, hj⟩
  let G := uniformDyadicGrids t
  let A := fun k => hestonCutoffWeight α t V n (G.grid j k)
  have htimes : ∀ᵐ ω ∂μ, ∀ k, B (G.grid j k) ω = B' (G.grid j k) ω :=
    ae_all_iff.mpr fun k => he (G.grid j k)
  have hsum : dyadicTerminal G j A B =ᵐ[μ] dyadicTerminal G j A B' := by
    filter_upwards [htimes] with ω hω
    simp only [dyadicTerminal, gridIntegral, runningSum, Finset.sum_apply,
      Pi.mul_apply, Pi.sub_apply, hω]
  exact eLpNorm_congr_ae (hsum.sub EventuallyEq.rfl)

end RoughHeston

#print axioms RoughHeston.isHestonConvolutionAt_jointIto

#print axioms RoughHeston.IsHestonConvolutionAt.ae_unique
#print axioms RoughHeston.IsHestonConvolutionAt.congr_driver

#print axioms RoughHeston.ae_eq_of_same_L2_limit
