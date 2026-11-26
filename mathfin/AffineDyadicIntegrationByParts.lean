import ClippedDyadicGrid
import EulerDyadicEndpointConvergence
import AffineWeightedBracket
import Mathlib.Analysis.Calculus.FDeriv.Measurable

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal Interval BigOperators

namespace RoughHeston

private theorem affine_ceiling_on_grid_cell {H t : ℝ≥0} (ht : t ≤ H)
    {n k : ℕ} (hr : t ∈ Ioc ((uniformDyadicGrids H).grid n k)
      ((uniformDyadicGrids H).grid n (k+1))) :
    eulerDyadicCeiling H n t = k+1 := by
  apply le_antisymm
  · unfold eulerDyadicCeiling
    exact Nat.find_min' _ (by simpa only [min_eq_left ht] using hr.2)
  · apply Nat.succ_le_of_lt
    by_contra! h
    have hb := ((uniformDyadicGrids H).grid n).monotone h
    exact (not_le_of_gt hr.1) ((min_eq_left ht ▸ eulerDyadicCeiling_spec H n t).trans hb)

/-- Dyadic stochastic sums of a continuously differentiable
deterministic weight converge pathwise to integration by parts on
every clipped horizon. -/
theorem tendsto_affine_dyadic_integration_by_parts
    {H t : ℝ≥0} (ht : t ≤ H) {g d : ℝ → ℝ} {X : ℝ≥0 → ℝ}
    (hX : Continuous X) (hdm : Measurable d) (hdc : ContinuousOn d (Icc 0 (t:ℝ)))
    (hDer : ∀ x ∈ Icc (0:ℝ) t, HasDerivAt g (d x) x) :
    Tendsto (fun n => gridIntegralProcess ((uniformDyadicGrids H).grid n)
      (fun k (_ : Unit) => g ((uniformDyadicGrids H).grid n k))
      (fun u (_ : Unit) => X u) (2^n) t ()) atTop
      (𝓝 (g t*X t-g 0*X 0 - ∫ r in (0:ℝ)..(t:ℝ), d r*X r.toNNReal)) := by
  let P := uniformDyadicGrids H
  let G (n : ℕ) := clippedDyadicGrid H t n
  let S (n : ℕ) (r : ℝ) := X (min (P.grid n (eulerDyadicCeiling H n r.toNNReal)) t)
  have hSm (n : ℕ) : Measurable (S n) := by
    have hC : Measurable (eulerDyadicCeiling H n) := (eulerDyadicCeiling_monotone H n).measurable
    have hG : Measurable (P.grid n : ℕ → ℝ≥0) := measurable_of_countable _
    exact hX.measurable.comp (((hG.comp (hC.comp continuous_real_toNNReal.measurable)).min measurable_const))
  let ν := volume.restrict (Ioc (0:ℝ) (t:ℝ))
  obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image (K := Icc (0:ℝ≥0) t) hX.norm.continuousOn
  obtain ⟨C,hC⟩ := isCompact_Icc.bddAbove_image hdc.norm
  let B' := max B 0
  let C' := max C 0
  have hB₀ : 0 ≤ B' := le_max_right _ _
  have hC₀ : 0 ≤ C' := le_max_right _ _
  have hDom (n : ℕ) : ∀ᵐ r ∂ν, ‖d r*S n r‖ ≤ C'*B' := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hs : min (P.grid n (eulerDyadicCeiling H n r.toNNReal)) t ∈ Icc 0 t :=
      ⟨zero_le,min_le_right _ _⟩
    have hS : ‖S n r‖ ≤ B' := (hB ⟨_,hs,rfl⟩).trans (le_max_left _ _)
    have hd : ‖d r‖ ≤ C' := (hC ⟨r,Ioc_subset_Icc_self hr,rfl⟩).trans (le_max_left _ _)
    rw [norm_mul]
    exact mul_le_mul hd hS (norm_nonneg _) hC₀
  have hIntegrable (n : ℕ) : Integrable (fun r => d r*S n r) ν :=
    (integrable_const (C'*B')).mono' (hdm.mul (hSm n)).aestronglyMeasurable (hDom n)
  have hPoint : ∀ᵐ r ∂ν, Tendsto (fun n => d r*S n r) atTop (𝓝 (d r*X r.toNNReal)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr₀ : 0 ≤ r := hr.1.le
    have hrt : r.toNNReal ≤ t := by
      exact NNReal.coe_le_coe.mp (by simpa only [Real.coe_toNNReal r hr₀] using hr.2)
    have hrH := hrt.trans ht
    have hL := tendsto_eulerDyadicCeiling_time H r.toNNReal
    rw [min_eq_left hrH] at hL
    have hmin := hL.min (tendsto_const_nhds (x := t))
    have hXm := (hX.tendsto (min r.toNNReal t)).comp hmin
    simpa only [S,Function.comp_apply,min_eq_left hrt] using hXm.const_mul (d r)
  have hIntLim := tendsto_integral_of_dominated_convergence (μ := ν) (fun _ => C'*B')
    (fun n => (hIntegrable n).aestronglyMeasurable) (integrable_const _) hDom hPoint
  have hStepCell (n k : ℕ) (r : ℝ) (hr : r ∈ Ioc (G n k:ℝ) (G n (k+1):ℝ)) :
      S n r = X (G n (k+1)) := by
    have hr₀ : 0 ≤ r := (NNReal.coe_nonneg (G n k)).trans hr.1.le
    have hrG : r.toNNReal ∈ Ioc (G n k) (G n (k+1)) := by
      constructor
      · exact NNReal.coe_lt_coe.mp (by simpa only [Real.coe_toNNReal r hr₀] using hr.1)
      · exact NNReal.coe_le_coe.mp (by simpa only [Real.coe_toNNReal r hr₀] using hr.2)
    have hrt : r.toNNReal ≤ t := hrG.2.trans (min_le_right _ _)
    have hCeil := affine_ceiling_on_grid_cell (hrt.trans ht)
      ((mem_Ioc_clippedDyadicGrid_iff hrt n k).mp hrG)
    simp only [S,hCeil,G,P,clippedDyadicGrid_apply]
  have hCellInt (n k : ℕ) :
      (∫ r in (G n k:ℝ)..(G n (k+1):ℝ), d r*S n r) =
        (g (G n (k+1))-g (G n k))*X (G n (k+1)) := by
    have hGle : (G n k : ℝ) ≤ G n (k+1) := by exact_mod_cast (G n).monotone k.le_succ
    rw [intervalIntegral.integral_of_le hGle]
    have he : EqOn (fun r => d r*S n r) (fun r => d r*X (G n (k+1)))
      (Ioc (G n k:ℝ) (G n (k+1):ℝ)) := by
      intro r hr
      change d r*S n r = d r*X (G n (k+1))
      rw [hStepCell n k r hr]
    rw [setIntegral_congr_fun measurableSet_Ioc he,integral_mul_const,← intervalIntegral.integral_of_le hGle]
    congr 1
    have hU : uIcc (G n k:ℝ) (G n (k+1):ℝ) ⊆ Icc 0 (t:ℝ) := by
      rw [uIcc_of_le hGle]
      exact Icc_subset_Icc (NNReal.coe_nonneg _) (NNReal.coe_le_coe.mpr (min_le_right _ _))
    have hdI : IntervalIntegrable d volume (G n k:ℝ) (G n (k+1):ℝ) :=
      (hdc.intervalIntegrable_of_Icc (NNReal.coe_nonneg t)).mono_set
        (by simpa only [uIcc_of_le (NNReal.coe_nonneg t)] using hU)
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r hr => hDer r (hU hr)) hdI
  have hStepsInt (n : ℕ) :
      (∫ r,d r*S n r ∂ν) =
        ∑ k ∈ Finset.range (2^n), (g (G n (k+1))-g (G n k))*X (G n (k+1)) := by
    have hI : ∀ k < 2^n, IntervalIntegrable (fun r => d r*S n r) volume (G n k:ℝ) (G n (k+1):ℝ) := by
      intro k _
      have hle : (G n k:ℝ) ≤ G n (k+1) := by exact_mod_cast (G n).monotone k.le_succ
      apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mpr
      have h : IntegrableOn (fun r => d r*S n r) (Ioc 0 (t:ℝ)) := hIntegrable n
      exact h.mono_set (Ioc_subset_Ioc (NNReal.coe_nonneg _)
        (NNReal.coe_le_coe.mpr (min_le_right _ _)))
    have hsum := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k => (G n k:ℝ)) hI
    change (∑ k ∈ Finset.range (2^n), ∫ r in (G n k:ℝ)..(G n (k+1):ℝ), d r*S n r) =
      ∫ r in (G n 0:ℝ)..(G n (2^n):ℝ), d r*S n r at hsum
    rw [show G n 0=0 from clippedDyadicGrid_first_vertex H t n,
      show G n (2^n)=t from clippedDyadicGrid_terminal_vertex ht n,NNReal.coe_zero,
      intervalIntegral.integral_of_le (NNReal.coe_nonneg t)] at hsum
    rw [← hsum]
    exact Finset.sum_congr rfl fun k _ => hCellInt n k
  have hExact (n : ℕ) : gridIntegralProcess (P.grid n) (fun k (_ : Unit) => g (P.grid n k))
      (fun u (_ : Unit) => X u) (2^n) t () =
      g t*X t-g 0*X 0 - (∫ r,d r*S n r ∂ν) := by
    rw [← gridIntegral_clippedDyadicGrid_eq_stopped H t n (fun u (_ : Unit) => g u)
      (fun u (_ : Unit) => X u),hStepsInt]
    unfold gridIntegral runningSum
    rw [Finset.sum_apply]
    let F (k : ℕ) := g (G n k)*X (G n k)
    have htel : ∑ k ∈ Finset.range (2^n), (F (k+1)-F k) = g t*X t-g 0*X 0 := by
      rw [Finset.sum_range_sub]
      dsimp [F]
      rw [show G n 0=0 from clippedDyadicGrid_first_vertex H t n,
        show G n (2^n)=t from clippedDyadicGrid_terminal_vertex ht n,NNReal.coe_zero]
    rw [← htel,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    change g (G n k)*(X (G n (k+1))-X (G n k)) =
      F (k+1)-F k- (g (G n (k+1))-g (G n k))*X (G n (k+1))
    dsimp [F]
    ring
  rw [← intervalIntegral.integral_of_le (NNReal.coe_nonneg t)] at hIntLim
  exact (hIntLim.const_sub (g t*X t-g 0*X 0)).congr (fun n => (hExact n).symm)

/-- The constructed variance-martingale integral is the pathwise
integration-by-parts expression at each preterminal observation time. -/
theorem affine_weighted_integral_eq_by_parts
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} {M J : ℝ≥0 → Ω → ℝ} {w : ℝ → ℝ} {d : ℝ}
    {H t : ℝ≥0} (hd : 0 < d) (ht : t ≤ H)
    (hw : ∀ s > 0, ContDiffAt ℝ 1 w s) (hM : Martingale M 𝒢 μ)
    (hM₂ : ∀ u, MemLp (M u) 2 μ)
    (hMc : ∀ᵐ ω ∂μ, Continuous (fun u => M u ω))
    (hJ : Tendsto (fun n => eLpNorm
      (gridIntegralProcess ((uniformDyadicGrids H).grid n)
        (fun k _ => affinePreterminalWeight w d H ((uniformDyadicGrids H).grid n k))
        M (2^n) t-J t) 2 μ) atTop (𝓝 0)) :
    J t =ᵐ[μ] fun ω => w (d+(H:ℝ)-(t:ℝ))*M t ω-w (d+(H:ℝ))*M 0 ω +
      ∫ r in (0:ℝ)..(t:ℝ), deriv w (d+(H:ℝ)-r)*M r.toNNReal ω := by
  let P := uniformDyadicGrids H
  let W := affinePreterminalWeight w d H
  let g (r : ℝ) := w (d+(H:ℝ)-r)
  let p (r : ℝ) := -deriv w (d+(H:ℝ)-r)
  let F (n : ℕ) := gridIntegralProcess (P.grid n) (fun k _ => W (P.grid n k)) M (2^n) t
  let Y (ω : Ω) := w (d+(H:ℝ)-(t:ℝ))*M t ω-w (d+(H:ℝ))*M 0 ω +
    ∫ r in (0:ℝ)..(t:ℝ), deriv w (d+(H:ℝ)-r)*M r.toNNReal ω
  have hpm : Measurable p := ((measurable_deriv w).comp (measurable_const.sub measurable_id)).neg
  have hPos (r : ℝ) (hr : r ∈ Icc 0 (t:ℝ)) : 0 < d+(H:ℝ)-r := by
    have htH := NNReal.coe_le_coe.mpr ht
    linarith [hr.2]
  have hpc : ContinuousOn p (Icc 0 (t:ℝ)) := by
    have hWc : ContDiffOn ℝ 1 w (Ioi 0) := fun s hs => (hw s hs).contDiffWithinAt
    exact ((hWc.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).comp
      (continuous_const.sub continuous_id).continuousOn hPos).neg
  have hDer (r : ℝ) (hr : r ∈ Icc (0:ℝ) t) : HasDerivAt g (p r) r := by
    have hh := ((hw _ (hPos r hr)).differentiableAt one_ne_zero).hasDerivAt
    have he := hh.comp r ((hasDerivAt_id r).const_sub (d+(H:ℝ)))
    change HasDerivAt g (deriv w (d+(H:ℝ)-r)* -1) r at he
    simpa only [p,mul_neg,mul_one] using he
  have hFa : ∀ n, AEStronglyMeasurable (F n) μ := by
    intro n
    have hm := gridIntegralProcess_martingale (P.grid n) hM hM₂
      (fun k => stronglyMeasurable_const (b := W (P.grid n k)))
      (fun k => memLp_const (W (P.grid n k))) (2^n)
    exact (hm.integrable t).aestronglyMeasurable
  have hPath : ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω) atTop (𝓝 (Y ω)) := by
    filter_upwards [hMc] with ω hω
    have hh := tendsto_affine_dyadic_integration_by_parts (X := fun s => M s ω) ht hω hpm hpc hDer
    have hYL : g (t:ℝ)*M t ω-g 0*M 0 ω -
        (∫ r in (0:ℝ)..(t:ℝ), p r*M r.toNNReal ω) = Y ω := by
      unfold p Y g
      simp only [sub_zero,neg_mul,intervalIntegral.integral_neg,sub_neg_eq_add]
    rw [hYL] at hh
    refine hh.congr (fun n => ?_)
    unfold F gridIntegralProcess
    rw [Finset.sum_apply]
    have hEq (k : ℕ) (hk : k ∈ Finset.range (2^n)) : W (P.grid n k) = g (P.grid n k) := by
      have hle : P.grid n k ≤ H := ((P.grid n).monotone (Finset.mem_range.mp hk).le).trans_eq
        (uniform_dyadic_terminal_vertex H n)
      simp [W,affinePreterminalWeight,g,min_eq_left hle]
      congr 1
      ring
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro k hk
    change g (P.grid n k)*(M (min t (P.grid n (k+1))) ω-M (min t (P.grid n k)) ω) =
      W (P.grid n k)*(M (min t (P.grid n (k+1))) ω-M (min t (P.grid n k)) ω)
    rw [hEq k hk]
  exact tendstoInMeasure_ae_unique
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hJ)
    (tendstoInMeasure_of_tendsto_ae hFa hPath)

#print axioms tendsto_affine_dyadic_integration_by_parts
#print axioms affine_weighted_integral_eq_by_parts

end RoughHeston
