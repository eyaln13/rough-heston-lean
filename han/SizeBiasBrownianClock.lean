import SizeBiasGirsanov
import FiniteBrownianGridRate
import GridQuadraticDrift
import StochasticCompletion
import FiniteHorizonLevy
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import MathFin.Probability.Brownian.Ito.ItoIntegralProcessLocalMartingaleGeneral

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} {H : ℝ≥0} {B Z g : ℝ≥0 → Ω → ℝ} {ε : ℝ}

local instance clockTimeMeasureFinite (t : ℝ≥0) : IsFiniteMeasure (hestonTimeMeasure t) := by
  rw [hestonTimeMeasure_eq_horizon]
  infer_instance

private noncomputable def shiftedDyadicGrid (s t : ℝ≥0) (j : ℕ) : ℕ →o ℝ≥0 :=
  ⟨fun k => s + (uniformDyadicGrids (t - s)).grid j k,
   fun _ _ h => add_le_add_right (((uniformDyadicGrids (t - s)).grid j).monotone h) s⟩

private theorem shiftedDyadicGrid_first (s t : ℝ≥0) (j : ℕ) :
    shiftedDyadicGrid s t j 0 = s := by
  change s + (uniformDyadicGrids (t - s)).grid j 0 = s
  rw [uniform_dyadic_first_vertex, add_zero]

private theorem shiftedDyadicGrid_last {s t : ℝ≥0} (hst : s ≤ t) (j : ℕ) :
    shiftedDyadicGrid s t j (2 ^ j) = t := by
  change s + (uniformDyadicGrids (t - s)).grid j (2 ^ j) = t
  rw [uniform_dyadic_terminal_vertex, add_tsub_cancel_of_le hst]

private theorem shiftedDyadicGrid_gap (s t : ℝ≥0) (j k : ℕ) :
    (shiftedDyadicGrid s t j (k + 1) : ℝ) - (shiftedDyadicGrid s t j k : ℝ) =
      ((t - s : ℝ≥0) : ℝ) / (2 : ℝ) ^ j := by
  change ((s + ((k + 1 : ℕ) : ℝ≥0) * (t - s) / 2 ^ j : ℝ≥0) : ℝ) -
    ((s + (k : ℝ≥0) * (t - s) / 2 ^ j : ℝ≥0) : ℝ) = _
  push_cast
  ring

omit [IsProbabilityMeasure μ] in
private theorem sizeBiased_frozenBrownian_memLp (hB : MathFinBridge.BrownianOn μ F H B)
    (hε : 0 < ε) (hZ : Measurable (Z H)) (hZ₀ : ∀ᵐ ω ∂μ, 0 ≤ Z H ω)
    (hZ₂ : MemLp (Z H) 2 μ) (t : ℝ≥0) :
    MemLp (B (min t H)) 2 (sizeBiasedLaw μ (Z H) ε) := by
  let Q := sizeBiasedLaw μ (Z H) ε
  let r := min t H
  have hmeas (u : ℝ≥0) : Measurable (B u) := (hB.adapted u).mono (F.le u) |>.measurable
  have hinc : HasLaw (B r - B 0) (gaussianReal 0 (r - 0)) μ :=
    ⟨((hmeas r).sub (hmeas 0)).aemeasurable, hB.normal_increment 0 r zero_le (min_le_right _ _)⟩
  have hinc₄ : MemLp (B r - B 0) 4 μ := hinc.memLp (memLp_id_gaussianReal 4)
  have heq : B r - B 0 =ᵐ[μ] B r := hB.zero_at_start.mono fun ω hω => by
    change B r ω - B 0 ω = B r ω
    rw [show B 0 ω = 0 from hω, sub_zero]
  have h₄ : MemLp (B r) 4 μ := hinc₄.ae_eq heq
  have : ENNReal.HolderTriple 4 4 2 := ⟨by
    have htwo : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have htop : (2 : ℝ≥0∞) ≠ ∞ := ENNReal.ofNat_ne_top
    rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num,
      ENNReal.mul_inv (Or.inl htwo) (Or.inl htop), ← two_mul, ← mul_assoc,
      ENNReal.mul_inv_cancel htwo htop, one_mul]⟩
  have hprod₄ : MemLp (fun ω => B r ω * B r ω) 2 μ := h₄.mul h₄
  have hsq : MemLp (fun ω => B r ω ^ 2) 2 μ := by simpa only [pow_two] using hprod₄
  have hprod : Integrable (fun ω => B r ω ^ 2 * Z H ω) μ := hsq.integrable_mul hZ₂
  apply (memLp_two_iff_integrable_sq (hmeas r).aestronglyMeasurable).2
  unfold sizeBiasedLaw
  apply (integrable_withDensity_iff_integrable_smul' (hZ.div_const ε).ennreal_ofReal
    (ae_of_all μ fun _ => ENNReal.ofReal_lt_top)).2
  apply (hprod.div_const ε).congr
  filter_upwards [hZ₀] with ω hw
  rw [ENNReal.toReal_ofReal (div_nonneg hw hε.le), smul_eq_mul]
  ring

private theorem timePrimitive_frozen_memLp {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hg : IsStronglyPredictable F g)
    (hg₂ : Integrable (fun p : ℝ≥0 × Ω => g p.1 p.2 ^ 2) ((hestonTimeMeasure H).prod Q))
    (t : ℝ≥0) :
    MemLp (fun ω => ∫ r, g r ω ∂hestonTimeMeasure (min t H)) 2 Q := by
  let u := min t H
  let D (ω : Ω) := ∫ r, g r ω ∂hestonTimeMeasure u
  have hm : Measurable D := ((stronglyAdapted_timePrimitive hg u).mono (F.le u)).measurable
  have hi : Integrable (fun ω => (u : ℝ) * ∫ r, g r ω ^ 2 ∂hestonTimeMeasure H) Q :=
    hg₂.integral_prod_right.const_mul _
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2
  refine hi.mono' (hm.pow_const 2).aestronglyMeasurable ?_
  filter_upwards [hg₂.prod_left_ae] with ω hω
  let grid : ℕ →o ℝ≥0 := ⟨fun k => if k = 0 then 0 else u, by
    intro a b hab
    by_cases ha : a = 0
    · simp [ha]
    · have hb : b ≠ 0 := fun hb => ha (Nat.eq_zero_of_le_zero (hb ▸ hab))
      simp [ha, hb]⟩
  have hgmeas : AEStronglyMeasurable (fun r => g r ω) (hestonTimeMeasure H) :=
    ((hg.mono F.predictable_le_prod).comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hgrid : grid 1 ≤ H := min_le_right _ _
  have hgrid₀ : grid 0 = 0 := rfl
  have hgrid₁ : grid 1 = u := rfl
  have h := physicalDrift_gridQuadraticSum_mesh_bound hgmeas hω grid 1 hgrid u.2 (by
    intro k hk
    have hk' : k = 0 := by simpa using hk
    simp [hk', hgrid₀, hgrid₁])
  have hzero : hestonTimeMeasure 0 = 0 := by
    rw [hestonTimeMeasure_eq_horizon, MathFin.ItoIntegralCLM.timeMeasureHorizon]
    simp
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (D ω))]
  simp only [Finset.sum_range_one, zero_add, hgrid₀, hgrid₁, hzero, integral_zero_measure, sub_zero] at h
  exact h

/-- Once the full-filtration martingale tilt has been established, square
integrability of the physical drift determines its Brownian clock under
the actual terminal-mass law. -/
theorem sizeBiasedShift_frozenClock (hB : MathFinBridge.BrownianOn μ F H B)
    (hε : 0 < ε) (hZ : Measurable (Z H)) (hZ₀ : ∀ᵐ ω ∂μ, 0 ≤ Z H ω)
    (hZ₂ : MemLp (Z H) 2 μ) (hg : IsStronglyPredictable F g)
    [IsProbabilityMeasure (sizeBiasedLaw μ (Z H) ε)]
    (hg₂ : Integrable (fun p : ℝ≥0 × Ω => g p.1 p.2 ^ 2)
      ((hestonTimeMeasure H).prod (sizeBiasedLaw μ (Z H) ε)))
    (hN : Martingale (fun t ω => B (min t H) ω -
      ∫ r, g r ω ∂hestonTimeMeasure (min t H)) F (sizeBiasedLaw μ (Z H) ε)) :
    Martingale (fun t ω => (B (min t H) ω - (∫ r, g r ω ∂hestonTimeMeasure (min t H))) ^ 2 -
      ((min t H : ℝ≥0) : ℝ)) F (sizeBiasedLaw μ (Z H) ε) := by
  let Q := sizeBiasedLaw μ (Z H) ε
  let B' (t : ℝ≥0) := B (min t H)
  let D (t : ℝ≥0) (ω : Ω) := ∫ r, g r ω ∂hestonTimeMeasure (min t H)
  let N (t : ℝ≥0) (ω : Ω) := B' t ω - D t ω
  have : IsProbabilityMeasure Q := inferInstanceAs (IsProbabilityMeasure (sizeBiasedLaw μ (Z H) ε))
  have hB' (t : ℝ≥0) : MemLp (B' t) 2 Q := sizeBiased_frozenBrownian_memLp hB hε hZ hZ₀ hZ₂ t
  have hD (t : ℝ≥0) : MemLp (D t) 2 Q := timePrimitive_frozen_memLp hg hg₂ t
  have hN₂ (t : ℝ≥0) : MemLp (N t) 2 Q := (hB' t).sub (hD t)
  suffices hclock : Martingale (fun t ω => N (min t H) ω ^ 2 - ((min t H : ℝ≥0) : ℝ)) F Q by
    simpa only [N, B', D, min_assoc, min_self] using hclock
  apply frozen_clock_of_gridQuadraticSum_L1 hN hN₂
  intro s t hst ht
  let grid := shiftedDyadicGrid s t
  let n (j : ℕ) := 2 ^ j
  let δ (j : ℕ) : ℝ := ((t - s : ℝ≥0) : ℝ) / (2 : ℝ) ^ j
  let v : ℝ := (t : ℝ) - (s : ℝ)
  have hδ₀ (j : ℕ) : 0 ≤ δ j := by dsimp [δ]; positivity
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
      (show 0 ≤ (2 : ℝ)⁻¹ by norm_num) (show (2 : ℝ)⁻¹ < 1 by norm_num)
    simpa only [δ, div_eq_mul_inv, inv_pow, mul_zero] using
      (tendsto_const_nhds (x := ((t - s : ℝ≥0) : ℝ))).mul hp
  have hlast (j : ℕ) : grid j (n j) = t := shiftedDyadicGrid_last hst j
  have hfirst (j : ℕ) : grid j 0 = s := shiftedDyadicGrid_first s t j
  have hvertex (j k : ℕ) (hk : k ≤ n j) : grid j k ≤ H :=
    ((grid j).monotone hk).trans ((hlast j).le.trans ht)
  have hincr (j : ℕ) :
      (∑ k ∈ Finset.range (n j), 2 * ((grid j (k + 1) : ℝ) - (grid j k : ℝ)) ^ 2) =
        2 * δ j * v := by
    calc
      _ = ∑ k ∈ Finset.range (n j), (2 * δ j) * ((grid j (k + 1) : ℝ) - (grid j k : ℝ)) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [shiftedDyadicGrid_gap]
        dsimp only [δ]
        ring
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_range_sub (fun k => (grid j k : ℝ)), hlast, hfirst]
  have hBgrid (j : ℕ) : gridQuadraticSum (grid j) B' (n j) = gridQuadraticSum (grid j) B (n j) := by
    funext ω
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    simp [B', min_eq_left (hvertex j _ (Nat.succ_le_of_lt hk')), min_eq_left (hvertex j _ hk'.le)]
  have hOldBound (j : ℕ) : (∫ ω, |gridQuadraticSum (grid j) B' (n j) ω - v| ∂Q) ≤
      Real.sqrt (∫ ω, Z H ω ^ 2 ∂μ) * Real.sqrt (2 * δ j * v) / ε := by
    rw [hBgrid]
    simpa only [hlast, hfirst, hincr, v] using
      sizeBiased_oldBrownian_gridQuadraticSum_L1_bound hB (grid j) (n j) (hvertex j _ le_rfl) hε hZ hZ₀ hZ₂
  have hOldRight : Tendsto (fun j => Real.sqrt (∫ ω, Z H ω ^ 2 ∂μ) *
      Real.sqrt (2 * δ j * v) / ε) atTop (𝓝 0) := by
    have hδ' : Tendsto (fun j => 2 * δ j * v) atTop (𝓝 0) := by
      simpa only [mul_zero, zero_mul] using (hδ.const_mul 2).mul_const v
    have hsqrt : Tendsto (fun j => Real.sqrt (2 * δ j * v)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp hδ'
    simpa only [mul_zero, zero_div] using (hsqrt.const_mul (Real.sqrt (∫ ω, Z H ω ^ 2 ∂μ))).div_const ε
  have hOld : Tendsto (fun j => ∫ ω, |gridQuadraticSum (grid j) B' (n j) ω - v| ∂Q) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hOldRight
      (fun _ => integral_nonneg fun _ => abs_nonneg _) hOldBound
  let e (ω : Ω) := ∫ r, g r ω ^ 2 ∂hestonTimeMeasure H
  have hei : Integrable e Q := hg₂.integral_prod_right
  have hDriftBound (j : ℕ) : (∫ ω, gridQuadraticSum (grid j) D (n j) ω ∂Q) ≤
      δ j * ∫ ω, e ω ∂Q := by
    rw [← integral_const_mul]
    apply integral_mono_ae (integrable_gridQuadraticSum_of_memLp hD _ _) (hei.const_mul _)
    filter_upwards [hg₂.prod_left_ae] with ω hω
    have hgmeas : AEStronglyMeasurable (fun r => g r ω) (hestonTimeMeasure H) :=
      ((hg.mono F.predictable_le_prod).comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    have h := physicalDrift_gridQuadraticSum_mesh_bound hgmeas hω (grid j) (n j) (hvertex j _ le_rfl)
      (hδ₀ j) (fun k _ => (shiftedDyadicGrid_gap s t j k).le)
    refine le_trans ?_ h
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    simp [D, min_eq_left (hvertex j _ (Nat.succ_le_of_lt hk')), min_eq_left (hvertex j _ hk'.le)]
  have hDrift : Tendsto (fun j => ∫ ω, gridQuadraticSum (grid j) D (n j) ω ∂Q) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun _ => integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) hDriftBound
    simpa only [zero_mul] using hδ.mul_const (∫ ω, e ω ∂Q)
  exact ⟨grid, n, hfirst, hlast, gridQuadraticSum_sub_L1_tendsto hB' hD grid n v hOld hDrift⟩

private theorem continuous_frozen_timePrimitive {f : ℝ≥0 → ℝ} (hf : Measurable f)
    (hi : Integrable f (hestonTimeMeasure H)) :
    Continuous (fun t : ℝ≥0 => ∫ r, f r ∂hestonTimeMeasure (min t H)) := by
  let v (s : ℝ) := f s.toNNReal
  have hm : Measurable v := hf.comp continuous_real_toNNReal.measurable
  have hiOpen : IntegrableOn v (Ioo (0 : ℝ) (H : ℝ)) :=
    hi.comp_aemeasurable continuous_real_toNNReal.measurable.aemeasurable
  have hEq : volume.restrict (Ioo (0 : ℝ) (H : ℝ)) = volume.restrict (Icc 0 (H : ℝ)) :=
    Measure.restrict_congr_set (Ioo_ae_eq_Ioc.trans Ioc_ae_eq_Icc)
  have hiClosed : IntegrableOn v (Icc (0 : ℝ) (H : ℝ)) := by
    rwa [IntegrableOn, ← hEq]
  have hmain := (intervalIntegral.continuousOn_primitive hiClosed).comp_continuous
    (NNReal.continuous_coe.comp (continuous_id.min continuous_const))
    (fun t : ℝ≥0 => show ((min t H : ℝ≥0) : ℝ) ∈ Icc 0 (H : ℝ) from
      ⟨(min t H).2, by exact_mod_cast min_le_right t H⟩)
  apply hmain.congr
  intro t
  change (∫ r in Ioc (0 : ℝ) (min t H : ℝ≥0), v r) = ∫ r, f r ∂hestonTimeMeasure (min t H)
  rw [hestonTimeMeasure, integral_map continuous_real_toNNReal.measurable.aemeasurable
    hf.aestronglyMeasurable, integral_Ioc_eq_integral_Ioo]

/-- The square-energy condition turns the focal mass-tilted driver into a
Brownian motion on the original filtration equipped with its Q-null sets.
The formula holds simultaneously over the finite horizon. -/
private theorem sizeBiasedShift_brownianOn_of_clock {G : Filtration ℝ≥0 m}
    (hB : MathFinBridge.BrownianOn μ F H B) (hg : IsStronglyPredictable F g)
    [IsProbabilityMeasure (sizeBiasedLaw μ (Z H) ε)]
    (hNull : ∀ A : Set Ω, MeasurableSet A → sizeBiasedLaw μ (Z H) ε A = 0 → MeasurableSet[G 0] A)
    (hg₂ : Integrable (fun p : ℝ≥0 × Ω => g p.1 p.2 ^ 2)
      ((hestonTimeMeasure H).prod (sizeBiasedLaw μ (Z H) ε)))
    (hN : Martingale (fun t ω => B (min t H) ω -
      ∫ r, g r ω ∂hestonTimeMeasure (min t H)) G (sizeBiasedLaw μ (Z H) ε))
    (hClock : Martingale (fun t ω => (B (min t H) ω - (∫ r, g r ω ∂hestonTimeMeasure (min t H))) ^ 2 -
      ((min t H : ℝ≥0) : ℝ)) G (sizeBiasedLaw μ (Z H) ε)) :
    let Q := sizeBiasedLaw μ (Z H) ε
    ∃ W : ℝ≥0 → Ω → ℝ, MathFinBridge.BrownianOn Q G H W ∧
      ∀ᵐ ω ∂Q, ∀ t ≤ H, W t ω = B t ω - ∫ r, g r ω ∂hestonTimeMeasure t := by
  let Q := sizeBiasedLaw μ (Z H) ε
  let N (t : ℝ≥0) (ω : Ω) := B (min t H) ω - ∫ r, g r ω ∂hestonTimeMeasure (min t H)
  have hac : Q ≪ μ := withDensity_absolutelyContinuous μ _
  have hgmeas (ω : Ω) : Measurable (fun r => g r ω) :=
    ((hg.mono F.predictable_le_prod).comp_measurable (measurable_id.prodMk measurable_const)).measurable
  have hNcts : ∀ᵐ ω ∂Q, Continuous (fun t => N t ω) := by
    filter_upwards [hac.ae_le hB.continuous_paths, hg₂.prod_left_ae] with ω hb hi
    have hg₁ := ((memLp_two_iff_integrable_sq (hgmeas ω).aestronglyMeasurable).2 hi).integrable one_le_two
    have hb' := hb.comp_continuous (continuous_id.min continuous_const)
      (fun t : ℝ≥0 => show min t H ∈ Icc 0 H from ⟨zero_le, min_le_right _ _⟩)
    exact hb'.sub (continuous_frozen_timePrimitive (hgmeas ω) hg₁)
  have hN₀ : N 0 =ᵐ[Q] 0 := by
    have hz : hestonTimeMeasure 0 = 0 := by
      rw [hestonTimeMeasure_eq_horizon, MathFin.ItoIntegralCLM.timeMeasureHorizon]
      simp
    filter_upwards [hac.ae_le hB.zero_at_start] with ω hw
    simpa only [N, min_eq_left (show (0 : ℝ≥0) ≤ H from zero_le), hz, integral_zero_measure, sub_zero] using hw
  obtain ⟨W, hW, heW⟩ := MathFinBridge.brownianOn_modification_of_measurable_nulls hNull hN hClock hNcts hN₀
  have hWcts : ∀ᵐ ω ∂Q, Continuous (fun t : ℝ≥0 => W (min t H) ω) :=
    hW.continuous_paths.mono fun ω hw => hw.comp_continuous (continuous_id.min continuous_const)
      (fun t : ℝ≥0 => show min t H ∈ Icc 0 H from ⟨zero_le, min_le_right _ _⟩)
  obtain ⟨S, hS, hdS⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have hsame : ∀ᵐ ω ∂Q, ∀ t, W (min t H) ω = N t ω := by
    apply indistinguishable_of_ae_eq_on_dense hS hdS hWcts hNcts
    intro t _
    simpa only [N, min_assoc, min_self] using heW (min t H)
  refine ⟨W, hW, hsame.mono fun ω hw t ht => ?_⟩
  simpa only [N, min_eq_left ht] using hw t

/-- The martingale tilt has a Brownian modification on the same
filtration when that filtration already contains the new null sets. -/
theorem sizeBiasedShift_brownianOn (hB : MathFinBridge.BrownianOn μ F H B)
    (hε : 0 < ε) (hZ : Measurable (Z H)) (hZ₀ : ∀ᵐ ω ∂μ, 0 ≤ Z H ω)
    (hZ₂ : MemLp (Z H) 2 μ) (hg : IsStronglyPredictable F g)
    [IsProbabilityMeasure (sizeBiasedLaw μ (Z H) ε)]
    (hNull : ∀ A : Set Ω, MeasurableSet A → sizeBiasedLaw μ (Z H) ε A = 0 → MeasurableSet[F 0] A)
    (hg₂ : Integrable (fun p : ℝ≥0 × Ω => g p.1 p.2 ^ 2)
      ((hestonTimeMeasure H).prod (sizeBiasedLaw μ (Z H) ε)))
    (hN : Martingale (fun t ω => B (min t H) ω -
      ∫ r, g r ω ∂hestonTimeMeasure (min t H)) F (sizeBiasedLaw μ (Z H) ε)) :
    let Q := sizeBiasedLaw μ (Z H) ε
    ∃ W : ℝ≥0 → Ω → ℝ, MathFinBridge.BrownianOn Q F H W ∧
      ∀ᵐ ω ∂Q, ∀ t ≤ H, W t ω = B t ω - ∫ r, g r ω ∂hestonTimeMeasure t :=
  sizeBiasedShift_brownianOn_of_clock hB hg hNull hg₂ hN
    (sizeBiasedShift_frozenClock hB hε hZ hZ₀ hZ₂ hg hg₂ hN)

open MathFin.ItoLocalMartingale (nullAugmentation nullsAlg condExp_sup_nulls)

/-- The Brownian conclusion is available in the filtration obtained by
adjoining the Q-null ambient sets, even when the original completion
only knew the old law's null sets. -/
theorem sizeBiasedShift_brownianOn_nullAugmentation (hB : MathFinBridge.BrownianOn μ F H B)
    (hε : 0 < ε) (hZ : Measurable (Z H)) (hZ₀ : ∀ᵐ ω ∂μ, 0 ≤ Z H ω)
    (hZ₂ : MemLp (Z H) 2 μ) (hg : IsStronglyPredictable F g)
    [IsProbabilityMeasure (sizeBiasedLaw μ (Z H) ε)]
    (hg₂ : Integrable (fun p : ℝ≥0 × Ω => g p.1 p.2 ^ 2)
      ((hestonTimeMeasure H).prod (sizeBiasedLaw μ (Z H) ε)))
    (hN : Martingale (fun t ω => B (min t H) ω -
      ∫ r, g r ω ∂hestonTimeMeasure (min t H)) F (sizeBiasedLaw μ (Z H) ε)) :
    let Q := sizeBiasedLaw μ (Z H) ε
    let G := nullAugmentation F Q
    ∃ W : ℝ≥0 → Ω → ℝ, MathFinBridge.BrownianOn Q G H W ∧
      ∀ᵐ ω ∂Q, ∀ t ≤ H, W t ω = B t ω - ∫ r, g r ω ∂hestonTimeMeasure t := by
  let Q := sizeBiasedLaw μ (Z H) ε
  let G := nullAugmentation F Q
  have hNull (A : Set Ω) (hA : MeasurableSet A) (hA₀ : Q A = 0) : MeasurableSet[G 0] A :=
    (show nullsAlg _ Q ≤ G 0 from le_sup_right) A (MeasurableSpace.measurableSet_generateFrom ⟨hA, hA₀⟩)
  have aug {X : ℝ≥0 → Ω → ℝ} (hX : Martingale X F Q) : Martingale X G Q := by
    refine ⟨fun t => (hX.stronglyAdapted t).mono le_sup_left, fun s t hst => ?_⟩
    exact (condExp_sup_nulls (F.le s) (hX.integrable t)).trans (hX.condExp_ae_eq hst)
  exact sizeBiasedShift_brownianOn_of_clock hB hg hNull hg₂ (aug hN)
    (aug (sizeBiasedShift_frozenClock hB hε hZ hZ₀ hZ₂ hg hg₂ hN))

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.sizeBiasedShift_frozenClock
#print axioms RoughHeston.GirsanovPort.sizeBiasedShift_brownianOn
#print axioms RoughHeston.GirsanovPort.sizeBiasedShift_brownianOn_nullAugmentation
