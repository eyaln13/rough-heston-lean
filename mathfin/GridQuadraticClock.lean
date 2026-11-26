import MartingalePowerMoment

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {F : Filtration ℝ≥0 m} {N : ℝ≥0 → Ω → ℝ}

private theorem grid_self_integral_martingale (grid : ℕ →o ℝ≥0)
    (hN : Martingale N F μ) (hN₂ : ∀ t, MemLp (N t) 2 μ) :
    Martingale (gridIntegral grid (fun k => N (grid k)) N) (gridFiltration F grid) μ := by
  have hle (k : ℕ) : grid k ≤ grid (k + 1) := grid.monotone k.le_succ
  have hi (k : ℕ) : Integrable (N (grid k) * (N (grid (k + 1)) - N (grid k))) μ :=
    (hN₂ (grid k)).integrable_mul ((hN₂ (grid (k + 1))).sub (hN₂ (grid k)))
  apply runningSum_martingale
  · intro k
    exact ((hN.stronglyAdapted _).mono (F.mono (hle k))).mul
      ((hN.stronglyAdapted _).sub ((hN.stronglyAdapted _).mono (F.mono (hle k))))
  · exact hi
  · intro k
    have h := condExp_mul_of_stronglyMeasurable_left (hN.stronglyAdapted (grid k))
      (hi k) ((hN.integrable (grid (k + 1))).sub (hN.integrable (grid k)))
    filter_upwards [h, conditional_mean_martingale_increment hN (hle k)] with ω hω hzero
    change μ[N (grid k) * (N (grid (k + 1)) - N (grid k)) | F (grid k)] ω = 0
    rw [hω, Pi.mul_apply, hzero, Pi.zero_apply, mul_zero]

private theorem integral_gridQuadraticSum_eq_square_difference (grid : ℕ →o ℝ≥0) (n : ℕ)
    (hN : Martingale N F μ) (hN₂ : ∀ t, MemLp (N t) 2 μ)
    {E : Set Ω} (hE : MeasurableSet[F (grid 0)] E) :
    (∫ ω in E, gridQuadraticSum grid N n ω ∂μ) =
      (∫ ω in E, N (grid n) ω ^ 2 ∂μ) - ∫ ω in E, N (grid 0) ω ^ 2 ∂μ := by
  let G := gridIntegral grid (fun k => N (grid k)) N
  have hG := grid_self_integral_martingale grid hN hN₂
  have hInt : (∫ ω in E, G n ω ∂μ) = 0 := by
    have he := hG.setIntegral_eq (Nat.zero_le n) hE
    change (∫ ω in E, G 0 ω ∂μ) = (∫ ω in E, G n ω ∂μ) at he
    rw [← he]
    simp [G, gridIntegral, runningSum]
  have hpt : gridQuadraticSum grid N n =
      fun ω => N (grid n) ω ^ 2 - N (grid 0) ω ^ 2 - 2 * G n ω :=
    funext (gridQuadraticSum_eq_square_sub_integral grid N n)
  have hlast : Integrable (fun ω => N (grid n) ω ^ 2) μ := (hN₂ _).integrable_sq
  have hfirst : Integrable (fun ω => N (grid 0) ω ^ 2) μ := (hN₂ _).integrable_sq
  have hd : Integrable (fun ω => N (grid n) ω ^ 2 - N (grid 0) ω ^ 2) μ := hlast.sub hfirst
  have hGi : Integrable (fun ω => 2 * G n ω) μ := (hG.integrable n).const_mul 2
  rw [hpt, integral_sub hd.integrableOn hGi.integrableOn, integral_sub hlast.integrableOn hfirst.integrableOn,
    integral_const_mul, hInt, mul_zero, sub_zero]

/-- An L¹ limit of squared grid increments identifies the clock of a
square-integrable martingale on the original filtration. No independence
or Gaussian law under that measure is assumed. -/
theorem frozen_clock_of_gridQuadraticSum_L1 {H : ℝ≥0}
    (hN : Martingale N F μ) (hN₂ : ∀ t, MemLp (N t) 2 μ)
    (hgrid : ∀ s t : ℝ≥0, s ≤ t → t ≤ H →
      ∃ (grid : ℕ → (ℕ →o ℝ≥0)) (n : ℕ → ℕ),
        (∀ j, grid j 0 = s) ∧ (∀ j, grid j (n j) = t) ∧
        Tendsto (fun j => eLpNorm (gridQuadraticSum (grid j) N (n j) -
          fun _ => (t : ℝ) - (s : ℝ)) 1 μ) atTop (𝓝 0)) :
    Martingale (fun t ω => N (min t H) ω ^ 2 - ((min t H : ℝ≥0) : ℝ)) F μ := by
  refine martingale_of_past_set_integrals (fun t => ?_) (fun t => ?_) ?_
  · exact (((hN.stronglyAdapted (min t H)).mono (F.mono (min_le_left t H))).pow 2).sub
      stronglyMeasurable_const
  · exact (hN₂ (min t H)).integrable_sq.sub (integrable_const _)
  · intro s t hst E hE
    by_cases hs : s ≤ H
    · let t' := min t H
      have ht' : t' ≤ H := min_le_right _ _
      obtain ⟨grid, n, hsGrid, htGrid, hlim⟩ := hgrid s t' (le_min hst hs) ht'
      have hi (j : ℕ) : Integrable (gridQuadraticSum (grid j) N (n j)) μ :=
        integrable_finsetSum _ fun k _ => ((hN₂ _).sub (hN₂ _)).integrable_sq
      have hEq (j : ℕ) :
          (∫ ω in E, gridQuadraticSum (grid j) N (n j) ω ∂μ) =
            (∫ ω in E, N t' ω ^ 2 ∂μ) - ∫ ω in E, N s ω ^ 2 ∂μ := by
        have he : MeasurableSet[F (grid j 0)] E := by rw [hsGrid j]; exact hE
        simpa only [hsGrid j, htGrid j] using
          integral_gridQuadraticSum_eq_square_difference (grid j) (n j) hN hN₂ he
      have hlim' := tendsto_setIntegral_of_L1' _ (Eventually.of_forall hi) hlim E
      simp only [hEq, setIntegral_const, smul_eq_mul] at hlim'
      have hclock := tendsto_nhds_unique tendsto_const_nhds hlim'
      rw [min_eq_left hs, integral_sub (hN₂ s).integrable_sq.integrableOn (integrable_const _),
        integral_sub (hN₂ t').integrable_sq.integrableOn (integrable_const _), setIntegral_const,
        setIntegral_const, smul_eq_mul, smul_eq_mul]
      linarith
    · have hsH := le_of_not_ge hs
      simp only [min_eq_right hsH, min_eq_right (hsH.trans hst)]

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.frozen_clock_of_gridQuadraticSum_L1
