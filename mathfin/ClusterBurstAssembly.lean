import ClusterBurstScaling
import ClusterBurstDeterministicBounds

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Interval

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The exact first-moment identities and the old-law fourth moment give
a uniform size-biased burst for the rectangular-pulse cluster. -/
theorem rectangularPulse_cluster_burst
    {U Z : Ω → ℝ} {α ε d r σ A C₄ : ℝ} {R m : ℝ → ℝ}
    (hα : 1/2 < α) (hα' : α ≤ 1) (hε : 0 < ε) (hd : 0 < d) (hdr : d ≤ r / 8)
    (hεd : ε = d ^ α) (hσ : 0 < σ) (hA : 0 ≤ A) (hC₄ : 0 < C₄)
    (hR : Measurable R)
    (hComp : ∀ u ∈ Ioc (0 : ℝ) r, fractionalK α u / 2 ≤ R u ∧ R u ≤ 2 * fractionalK α u)
    (hm : ∀ s ∈ Ioc (0 : ℝ) r, 0 ≤ m s)
    (hMean : ∀ s ∈ Icc (r/4) (r/2), m s = volterraConvolution R (rectangularPulseRate ε d) s)
    (hCovInt : IntegrableOn (fun s => R (r-s) * m s) (Ioc (0 : ℝ) r))
    (hmInt : IntegrableOn m (Ioc (0 : ℝ) r))
    (hmUp : ∀ s ∈ Ioc (0 : ℝ) r, m s ≤ A * ε * fractionalK α s)
    (hU : Measurable U) (hU₀ : ∀ ω, 0 ≤ U ω) (hU₄ : MemLp U 4 P)
    (hZ : Measurable Z) (hZ₀ : ∀ᵐ ω ∂P, 0 ≤ Z ω) (hZ₂ : MemLp Z 2 P)
    [IsProbabilityMeasure (sizeBiasedLaw P Z ε)]
    (hEU :
      (∫ ω, U ω ∂sizeBiasedLaw P Z ε) =
        m r + (σ ^ 2 / ε) * ∫ s in Ioc (0 : ℝ) r, R (r-s) * m s)
    (hEZ :
      (∫ ω, Z ω ∂sizeBiasedLaw P Z ε) =
        ε + (σ ^ 2 / ε) * ∫ s in Ioc (0 : ℝ) r, m s)
    (hFour : (∫ ω, U ω ^ 4 ∂P) ≤ ε * C₄ * (r ^ (2 * α - 1)) ^ 4 / (r ^ α)) :
    let Q := sizeBiasedLaw P Z ε
    let a := σ ^ 2 / (16 * (Real.Gamma α) ^ 2)
    let z := 1 + σ ^ 2 * A / (Real.Gamma α * α)
    let c := Real.sqrt (C₄ * z)
    a ^ 2 / (8 * c) ≤ Q.real {ω |
      (a / 2) * r ^ (2 * α - 1) ≤ U ω ∧ Z ω ≤ (8 * c * (z+1) / a ^ 2) * r ^ α} := by
  let Q := sizeBiasedLaw P Z ε
  let a := σ ^ 2 / (16 * (Real.Gamma α) ^ 2)
  let z := 1 + σ ^ 2 * A / (Real.Gamma α * α)
  have hr : 0 < r := by linarith
  have hαp : 0 < α := by linarith
  have hΓ := Real.Gamma_pos_of_pos hαp
  have ha : 0 < a := by dsimp [a]; positivity
  have hz : 0 < z := by dsimp [z]; positivity
  have hSU : 0 < r ^ (2 * α - 1) := Real.rpow_pos_of_pos hr _
  have hSZ : 0 < r ^ α := Real.rpow_pos_of_pos hr _
  have hQEU : a * r ^ (2 * α - 1) ≤ ∫ ω, U ω ∂Q := by
    have h := pulse_covariance_middle_lower hαp hα' hε hd hdr hR hComp hm hMean hCovInt
    have hn : 0 ≤ σ ^ 2 / ε := div_nonneg (sq_nonneg _) hε.le
    have hmr : 0 ≤ m r := hm _ ⟨hr, le_rfl⟩
    rw [hEU]
    calc
      _ = (σ ^ 2 / ε) * ((ε / (16 * (Real.Gamma α)^2)) * r ^ (2 * α - 1)) := by
        dsimp [a]
        field_simp
      _ ≤ (σ ^ 2 / ε) * ∫ s in Ioc (0 : ℝ) r, R (r - s) * m s := mul_le_mul_of_nonneg_left h hn
      _ ≤ _ := le_add_of_nonneg_left hmr
  have hQEZ : (∫ ω, Z ω ∂Q) ≤ z * r ^ α := by
    have hδ : ε ≤ r ^ α := hεd.trans_le (Real.rpow_le_rpow hd.le (by linarith) hαp.le)
    have hg := pulse_mean_integral_upper hαp hr.le hmInt hmUp
    have hs := mul_le_mul_of_nonneg_left hg (div_nonneg (sq_nonneg σ) hε.le)
    rw [hEZ]
    calc
      _ ≤ r ^ α + (σ ^ 2 / ε) * ((A * ε) * (r ^ α / (Real.Gamma α * α))) := add_le_add hδ hs
      _ = _ := by dsimp [z]; field_simp
  have hPSq : (∫ ω, Z ω ^ 2 ∂P) ≤ ε * z * r ^ α := by
    rw [integral_sizeBiasedLaw_eq hε hZ hZ₀] at hQEZ
    have he : (fun ω => Z ω * Z ω) = fun ω => Z ω ^ 2 := funext fun _ => (pow_two _).symm
    rw [he] at hQEZ
    have h := (div_le_iff₀ hε).1 hQEZ
    exact h.trans_eq (by ring)
  exact scaled_sizeBiased_cluster_burst_of_old_moments hε ha hC₄ hz hSU hSZ hU hU₀ hU₄
    hZ hZ₀ hZ₂ hQEU hQEZ hPSq hFour

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.rectangularPulse_cluster_burst
