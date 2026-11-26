import EntropySmoothExtension
import GridItoPowerLimit
import StochasticCovariation

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {F : Filtration ℝ≥0 m} {Z C : ℝ≥0 → Ω → ℝ} {H : ℝ≥0}

private theorem stronglyAdapted_gridStieltjes
    (hZ : StronglyAdapted F Z) (hC : StronglyAdapted F C) (grid : ℕ →o ℝ≥0) (n : ℕ) :
    StronglyAdapted F (gridIntegralProcess grid (fun k => Z (grid k)) C n) := by
  intro t
  have hStep (k : ℕ) : StronglyMeasurable[F t]
      (stochasticStep (grid k) (grid (k + 1)) (Z (grid k)) C t) := by
    by_cases h : t ≤ grid k
    · rw [stochasticStep_before h (grid.monotone (Nat.le_succ k))]
      exact stronglyMeasurable_zero
    · exact ((hZ _).mono (F.mono (le_of_not_ge h))).mul
        (((hC _).mono (F.mono (min_le_left t _))).sub ((hC _).mono (F.mono (min_le_left t _))))
  have h := Finset.stronglyMeasurable_fun_sum (Finset.range n) (fun k _ => hStep k)
  convert h using 1
  funext ω
  simp only [gridIntegralProcess, Finset.sum_apply]

/-- The regularized entropy identity for the bracket density of a bounded
nonnegative continuous martingale in the supplied filtration. -/
theorem boundedMartingale_regularizedEntropy_identity
    (hZ : Martingale Z F μ) (hC : Martingale (fun t => Z t * Z t - C t) F μ)
    (hCmono : ∀ s t, s ≤ t → C s ≤ᵐ[μ] C t)
    {K : ℝ} (hBound : ∀ t, ∀ᵐ ω ∂μ, ‖Z t ω‖ ≤ K)
    (hNonneg : ∀ t, ∀ᵐ ω ∂μ, 0 ≤ Z t ω)
    (hcts : ∀ᵐ ω ∂μ, ContinuousOn (fun t => Z t ω) (Icc 0 H))
    {d : ℝ → Ω → ℝ}
    (hDensity : ∀ t ≤ H, C t =ᵐ[μ] fun ω => ∫ r in 0..(t : ℝ), d r ω)
    (hInt : ∀ᵐ ω ∂μ, IntervalIntegrable (fun r => d r ω) volume 0 (H : ℝ))
    (hMass : Integrable (fun ω => ∫ r in 0..(H : ℝ), |d r ω|) μ)
    {η : ℝ} (hη : 0 < η) :
    (∫ ω, regularizedEntropy η (Z H ω) - regularizedEntropy η (Z 0 ω) ∂μ) =
      (1 / 2 : ℝ) * ∫ ω, (∫ r in 0..(H : ℝ),
        extendedEntropySecond η (Z r.toNNReal ω) * d r ω) ∂μ := by
  let W (t : ℝ≥0) (ω : Ω) := extendedEntropySecond η (Z t ω)
  have hWc := extendedEntropySecond_continuous hη
  have hWb (t : ℝ≥0) (ω : Ω) : |W t ω| ≤ η⁻¹ := by
    dsimp [W, extendedEntropySecond]
    have hp : 0 < max (Z t ω) 0 + η := add_pos_of_nonneg_of_pos (le_max_right _ _) hη
    rw [abs_of_nonneg (inv_nonneg.mpr hp.le)]
    exact inv_anti₀ hη (le_add_of_nonneg_left (le_max_right _ _))
  have hwAdapt : StronglyAdapted F W := fun t => hWc.comp_stronglyMeasurable (hZ.stronglyMeasurable t)
  have hCAdapt := adapted_compensator_of_compensated_product hZ.stronglyAdapted hZ.stronglyAdapted hC
  have hWpath : ∀ᵐ ω ∂μ, ContinuousOn (fun (t : ℝ≥0) => W t ω) (Icc 0 H) :=
    hcts.mono fun ω hw => hWc.comp_continuousOn hw
  have hwD : ∀ᵐ ω ∂μ, IntervalIntegrable (fun r => W r.toNNReal ω * d r ω) volume 0 (H : ℝ) := by
    filter_upwards [hWpath, hInt] with ω hw hi
    have hT : (0 : ℝ) ≤ (H : ℝ) := H.2
    have hi' := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 hi
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2
    let v (r : ℝ) := W r.toNNReal ω
    have hcont : ContinuousOn v (Icc (0 : ℝ) (H : ℝ)) :=
      hw.comp continuous_real_toNNReal.continuousOn (fun r hr =>
        ⟨zero_le, by
          have he : (r.toNNReal : ℝ) = r := Real.coe_toNNReal _ hr.1
          have hle : (r.toNNReal : ℝ) ≤ (H : ℝ) := he.trans_le hr.2
          exact_mod_cast hle⟩)
    have hmeas : AEStronglyMeasurable v (volume.restrict (Ioc (0 : ℝ) (H : ℝ))) :=
      hcont.aestronglyMeasurable measurableSet_Icc |>.mono_measure
        (Measure.restrict_mono_set volume Ioc_subset_Icc_self)
    refine (hi'.abs.const_mul η⁻¹).mono' (hmeas.mul hi'.aestronglyMeasurable) ?_
    exact ae_of_all _ fun r => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hWb _ _) (abs_nonneg _)
  let G := uniformDyadicGrids H
  let Cn := fun (j : ℕ) => gridIntegralProcess (G.grid j) (fun k => W (G.grid j k)) C (2 ^ j)
  obtain ⟨Cw, _, hCwi, hCni, hCw, hCnv⟩ :=
    dyadic_compensator_density_L1 (𝒢 := F) (W := W) H (inv_nonneg.mpr hη.le) hDensity hWpath
      (ae_of_all _ fun ω t _ => hWb t ω) hInt hwD hMass
      (fun j => stronglyAdapted_gridStieltjes hwAdapt hCAdapt (G.grid j) (2 ^ j))
  have hcon := tendsto_setIntegral_of_L1' (Cw H)
    (Eventually.of_forall fun j => hCni j H) (hCnv H) Set.univ
  simp only [Measure.restrict_univ] at hcon
  have he_Cn (j : ℕ) :
      (∫ ω, Cn j H ω ∂μ) = ∑ k ∈ Finset.range (2 ^ j),
        ∫ ω, W (G.grid j k) ω * (C (G.grid j (k + 1)) ω - C (G.grid j k) ω) ∂μ := by
    have hH : G.grid j (2 ^ j) = H := uniform_dyadic_terminal_vertex H j
    have hCint (t : ℝ≥0) : Integrable (C t) μ := by
      have h₂ : MemLp (Z t) 2 μ := MemLp.of_bound
        (((hZ.stronglyMeasurable t).mono (F.le t)).aestronglyMeasurable) K (hBound t)
      have hsq : Integrable (Z t * Z t) μ := h₂.integrable_mul h₂
      simpa only [sub_sub_cancel] using hsq.sub (hC.integrable t)
    have hWtop (t : ℝ≥0) : MemLp (W t) ⊤ μ :=
      memLp_top_of_bound (((hwAdapt t).mono (F.le t)).aestronglyMeasurable) _ (ae_of_all _ fun ω => by
        simpa only [Real.norm_eq_abs] using hWb t ω)
    have hsum (k : ℕ) : Integrable (fun ω => W (G.grid j k) ω *
        (C (G.grid j (k + 1)) ω - C (G.grid j k) ω)) μ :=
      memLp_one_iff_integrable.1 ((hWtop _).mul
        (memLp_one_iff_integrable.2 ((hCint _).sub (hCint _))))
    rw [← integral_finsetSum _ (fun k _ => hsum k)]
    apply integral_congr_ae
    apply ae_of_all
    intro ω
    simp only [Cn, gridIntegralProcess, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro k hk
    have hu := (G.grid j).monotone (Nat.le_succ k)
    have hv := ((G.grid j).monotone (Nat.succ_le_of_lt (Finset.mem_range.mp hk))).trans_eq hH
    rw [stochasticStep_after hv hu]
    rfl
  have hCon' := hcon.const_mul (1 / 2 : ℝ)
  change Tendsto (fun j => (1 / 2 : ℝ) * ∫ ω, Cn j H ω ∂μ) atTop
    (𝓝 ((1 / 2 : ℝ) * ∫ ω, Cw H ω ∂μ)) at hCon'
  simp only [he_Cn] at hCon'
  have hIto := tendsto_expected_dyadic_ito_compensator_sum H hZ hC hCmono hBound hcts
    (extendedEntropy_hasDerivAt hη) (extendedEntropyFirst_hasDerivAt hη) hWc
    (extendedEntropySecond_lipschitz hη).lipschitzOnWith
  have he := tendsto_nhds_unique hIto hCon'
  have heq := hCw H
  simp only [min_self] at heq
  change (∫ ω, regularizedEntropy η (Z H ω) - regularizedEntropy η (Z 0 ω) ∂μ) =
    (1 / 2 : ℝ) * ∫ ω, (∫ r in 0..(H : ℝ), W r.toNNReal ω * d r ω) ∂μ
  rw [← integral_congr_ae heq]
  rw [← he]
  apply integral_congr_ae
  filter_upwards [hNonneg H, hNonneg 0] with ω hH h0
  rw [extendedEntropy_eq hη hH, extendedEntropy_eq hη h0]

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.boundedMartingale_regularizedEntropy_identity
