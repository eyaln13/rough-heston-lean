import AffinePointCompatibleRows
import AffinePointPreterminal
import AffineTiltedDrift
import Mathlib.Topology.Order.LeftRight

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston.GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} {T : ℝ≥0} {M Y C : ℝ≥0 → Ω → ℝ}

set_option maxHeartbeats 1600000 in
/-- All preterminal observations of the point density on the original
variance paths have the stated conditional expectation and fit together
continuously with the actual terminal payoff. -/
theorem affine_point_density_path_of_inverse
    {α κ σ q : ℝ} (hα : 0 < α) (hα' : α < 1) (hT : 0 < T) (hq : 0 ≤ q)
    {w j : ℝ → ℝ}
    (hw : AffineRiccatiTestOn α κ (σ^2/2) q (T:ℝ) w (fun _ => 0))
    (hj : AffineInputOn (T:ℝ) j)
    (hM : Martingale M F μ) (hM₂ : ∀ t, MemLp (M t) 2 μ)
    (hMc : ∀ ω, Continuous (fun t => M t ω)) (hM₀ : M 0 =ᵐ[μ] 0)
    (hY : StronglyAdapted F Y) (hYc : ∀ ω, Continuous (fun t => Y t ω))
    (hY₀ : ∀ t ω, 0 ≤ Y t ω) {Y₀ : ℝ} (hstart : ∀ ω, Y 0 ω ≤ Y₀)
    (hMC : Martingale (fun t => M t*M t-C t) F μ)
    (hCi : ∀ t, Integrable (C t) μ)
    (hCmon : ∀ s t, s ≤ t → C s ≤ᵐ[μ] C t)
    (hClock : ∀ t ≤ T, C t =ᵐ[μ] fun ω => ∫ r in (0:ℝ)..(t:ℝ), σ^2*Y r.toNNReal ω)
    (hInv : ∀ᵐ ω ∂μ, ∀ r ∈ Ioc (0:ℝ) (T:ℝ),
      M r.toNNReal ω = volterraConvolution (fractionalL α) (fun u => Y u.toNNReal ω) r +
        ∫ u in Ioc (0:ℝ) r, κ*Y u.toNNReal ω-j u) :
    let c := volterraConvolution w j T
    let a (t : ℝ≥0) (ω : Ω) := σ * Real.sqrt (Y t ω)
    let D := affinePointDensityPath T w c q M a Y
    StronglyAdapted F D ∧
      (∀ᵐ ω ∂μ, Continuous (fun t => D t ω)) ∧
      (∀ t, ∀ᵐ ω ∂μ, ‖D t ω‖ ≤ Real.exp c) ∧
      (∀ h < T, Martingale (affinePreterminalDensity T h w M (fun t ω => a t ω ^ 2)) F μ ∧
        ∀ r, ∀ᵐ ω ∂μ, ‖affinePreterminalDensity T h w M (fun t ω => a t ω ^ 2) r ω‖ ≤ Real.exp c) ∧
      ∀ t < T, μ[(fun ω => Real.exp (c-q*Y T ω)) | F t] =ᵐ[μ] D t := by
  let c := volterraConvolution w j T
  let a (t : ℝ≥0) (ω : Ω) := σ * Real.sqrt (Y t ω)
  let b (t : ℝ≥0) (ω : Ω) := σ^2 * Y t ω
  let E (h : ℝ≥0) := affinePreterminalDensity T h w M b
  let D := affinePointDensityPath T w c q M a Y
  have hEqB : (fun t ω => a t ω ^ 2) = b := by
    funext t ω
    simp only [a,b,mul_pow,Real.sq_sqrt (hY₀ _ _)]
  have he' : (fun t ω => (2*(σ^2/2))*Y t ω) = b := by funext t ω; dsimp [b]; ring
  have hb (t : ℝ≥0) (ω : Ω) : 0 ≤ b t ω := mul_nonneg (sq_nonneg _) (hY₀ _ _)
  have hba : StronglyAdapted F b := fun t => (hY t).const_mul _
  have hbc (ω : Ω) : Continuous (fun t => b t ω) := continuous_const.mul (hYc ω)
  have hbstart (ω : Ω) : b 0 ω ≤ σ^2*Y₀ := mul_le_mul_of_nonneg_left (hstart ω) (sq_nonneg _)
  have hCe : ∀ t ≤ T, C t =ᵐ[μ]
      fun ω => ∫ r in (0:ℝ)..(t:ℝ), (2*(σ^2/2))*Y r.toNNReal ω := by
    intro t ht
    have hTwo : 2 * (σ^2/2) = σ^2 := by ring
    simpa only [hTwo] using hClock t ht
  have hNorm (h : ℝ≥0) (hh : h < T) (r : ℝ≥0) :
      ∀ᵐ ω ∂μ, ‖E h r ω‖ ≤ Real.exp c := by
    have h := (heston_point_preterminal_conditional_density hα hα' (by positivity) hh hw hj
      hM hM₂ hMc hM₀ hY hYc hY₀ hstart hMC hCi hCmon hCe hInv r).2
    simpa only [E,c,he'] using h
  have hPr (h : ℝ≥0) (hh : h < T) : Martingale (E h) F μ :=
    affinePreterminalDensity_martingale_of_bound hh hw.solution_smooth hM hM₂ hMc hMC hCi hCmon
      (fun t ht => hClock t (ht.trans hh.le)) hba hbc hb hbstart (Real.exp_pos _).le (hNorm h hh)
  have hDpre (t : ℝ≥0) (ht : t<T) (ω : Ω) : D t ω = E t t ω := by
    simp only [D,affinePointDensityPath,ite_eq_left ht,E,hEqB]
  have hDval (t : ℝ≥0) (ht : T≤t) (ω : Ω) : D t ω = Real.exp (c-q*Y T ω) := by
    simp only [D,affinePointDensityPath,ite_eq_right (not_lt_of_ge ht)]
  have hDa : StronglyAdapted F D := by
    intro t
    by_cases ht : t<T
    · have he : D t = E t t := funext (hDpre t ht)
      rw [he]
      exact (hPr t ht).stronglyAdapted t
    · have he := funext (hDval t (le_of_not_gt ht))
      rw [he]
      apply Real.continuous_exp.comp_stronglyMeasurable
      exact stronglyMeasurable_const.sub (((hY T).mono (F.mono (le_of_not_gt ht))).const_mul q)
  have hDbd (t : ℝ≥0) : ∀ᵐ ω ∂μ, ‖D t ω‖ ≤ Real.exp c := by
    by_cases ht : t<T
    · simpa only [hDpre t ht] using hNorm t ht t
    · exact ae_of_all _ fun ω => by
        rw [hDval t (le_of_not_gt ht), Real.norm_of_nonneg (Real.exp_pos _).le]
        exact Real.exp_le_exp.mpr (sub_le_self _ (mul_nonneg hq (hY₀ _ _)))
  have hDlaw (t : ℝ≥0) (ht : t<T) : μ[(fun ω => Real.exp (c-q*Y T ω)) | F t] =ᵐ[μ] D t := by
    have he := (heston_point_preterminal_conditional_density hα hα' (by positivity) ht hw hj
      hM hM₂ hMc hM₀ hY hYc hY₀ hstart hMC hCi hCmon hCe hInv t).1
    have hE : μ[(fun ω => Real.exp (c-q*Y T ω)) | F t] =ᵐ[μ] E t t := by
      simpa only [c,min_self,he',E] using he
    exact hE.trans (ae_of_all _ fun ω => (hDpre t ht ω).symm)
  have hDleft : ∀ᵐ ω ∂μ, Tendsto (fun t => D t ω) (𝓝[<] T) (𝓝 (D T ω)) := by
    filter_upwards [hM₀,hInv] with ω h₀ hI
    let y (r : ℝ) := Y r.toNNReal ω
    have hYreal : Continuous y := (hYc ω).comp continuous_real_toNNReal
    have he (t : ℝ≥0) (ht : t<T) :
        D t ω = Real.exp (c - affineFuturePayoff α w j y T t) := by
      have h := affinePreterminalDensity_eq_exp_payoffs hα hα' ht hw hj ω (hYc ω) h₀ hI t
      simpa only [hDpre t ht,E,he', min_self,affinePastPayoff,zero_mul,integral_zero,zero_add,y,c] using h
    have hc : Tendsto (fun r : ℝ≥0 => (r:ℝ)) (𝓝[<] T) (𝓝[<] (T:ℝ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact NNReal.continuous_coe.continuousAt.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact NNReal.coe_lt_coe.mpr (show r<T from hr)
    have hf := (affine_pathwise_payoffs_left_limit hα hα' (NNReal.coe_pos.mpr hT)
      hw hj hYreal).comp hc
    have hf' : Tendsto (fun t : ℝ≥0 => affineFuturePayoff α w j y T t)
        (𝓝[<] T) (𝓝 (q*Y T ω)) := by
      simpa only [Function.comp_def,affinePastPayoff,zero_mul,integral_zero,zero_add,add_zero,y,
        Real.toNNReal_coe] using hf
    rw [hDval T le_rfl]
    refine ((Real.continuous_exp.tendsto (c-q*Y T ω)).comp (hf'.const_sub c)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (he t (show t<T from ht)).symm
  have hDc : ∀ᵐ ω ∂μ, Continuous (fun t => D t ω) := by
    filter_upwards [hDleft] with ω hL
    rw [continuous_iff_continuousAt]
    intro t
    rcases lt_trichotomy t T with h | h | h
    · obtain ⟨s,hts,hsT⟩ := exists_between h
      have hDloc : (fun t => D t ω) =ᶠ[𝓝 t] fun t => E s t ω := by
        filter_upwards [Iio_mem_nhds hts] with r hr
        have hr' : r < s := hr
        have hm := affinePreterminalDensity_consistent T s r w M b ω
        rw [min_eq_left hr'.le] at hm
        exact (hDpre r (hr'.trans hsT) ω).trans hm.symm
      have hEc : Continuous (fun t => E s t ω) :=
        Real.continuous_exp.comp ((affinePreterminalVarianceMartingale_continuous s
          (sub_pos.mpr (NNReal.coe_lt_coe.mpr hsT)) hw.solution_smooth hMc ω).neg.sub
            ((affinePreterminalCompensator_continuous hsT
              (fun x hx => (hw.solution_smooth x hx).continuousAt.continuousWithinAt) hbc ω).div_const 2))
      exact hEc.continuousAt.congr_of_eventuallyEq hDloc
    · subst t
      rw [continuousAt_iff_continuous_left'_right']
      refine ⟨hL,?_⟩
      unfold ContinuousWithinAt
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact (hDval T le_rfl ω).trans (hDval r (le_of_lt (show T<r from hr)) ω).symm
    · have he : (fun t => D t ω) =ᶠ[𝓝 t] fun _ => Real.exp (c-q*Y T ω) := by
        filter_upwards [Ioi_mem_nhds h] with r hr
        exact hDval r (le_of_lt (show T<r from hr)) ω
      exact continuousAt_const.congr_of_eventuallyEq he
  refine ⟨hDa,hDc,hDbd,?_,hDlaw⟩
  intro h hh
  change Martingale (affinePreterminalDensity T h w M (fun t ω => a t ω ^ 2)) F μ ∧
    ∀ r, ∀ᵐ ω ∂μ, ‖affinePreterminalDensity T h w M (fun t ω => a t ω ^ 2) r ω‖ ≤ Real.exp c
  rw [hEqB]
  exact ⟨hPr h hh,hNorm h hh⟩

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.affine_point_density_path_of_inverse
