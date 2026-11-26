import StoppedClusterEnvelope
import PositiveClusterMass
import LocalizedGridBDG

/-! A pulse with positive input immediately after birth cannot have an
identically zero variance history on an initial interval. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 m} [F.IsComplete P] [F.IsRightContinuous]

/-- Optional stopping at the first positive variance. Until that stop the
inverse equation makes the martingale equal to the negative of the
accumulated deterministic pulse input. -/
theorem pulse_activates_before {d : ℝ≥0} (hd : 0 < d) {ε α κ : ℝ} (hε : 0 < ε)
    {M U : ℝ≥0 → Ω → ℝ} (hm : Martingale M F P) (hp : IsStronglyPredictable F U)
    (hmc : ∀ ω, Continuous (fun s => M s ω)) (hm₀ : M 0 =ᵐ[P] 0)
    (huc : ∀ ω, Continuous (fun s => U s ω)) (hu₀ : ∀ ω, U 0 ω = 0)
    (hn : ∀ s ≤ d, ∀ ω, 0 ≤ U s ω)
    (hinv : ∀ᵐ ω ∂P, ∀ t ≤ d, M t ω =
      volterraConvolution (fractionalL α) (fun s => U s.toNNReal ω) t +
      κ * (∫ s in Ioc (0 : ℝ) t, U s.toNNReal ω) - ε / (d : ℝ) * (t : ℝ)) :
    ∀ᵐ ω ∂P, ∃ s ∈ Ioo (0 : ℝ≥0) d, 0 < U s ω := by
  let τ := envelopeStop d 0 U
  have ht := envelopeStop_isStoppingTime P d 0 hp
  let S := stoppedProcess M (fun ω => (τ ω : WithTop ℝ≥0))
  have hS : Martingale S F P := hm.stoppedProcess (fun ω => (hmc ω).isRightContinuous) ht
  have hv : S d =ᵐ[P] fun ω => -(ε / (d:ℝ) * (τ ω : ℝ)) := by
    filter_upwards [hinv] with ω he
    have hτ : τ ω ≤ d := envelopeStop_le d 0 U ω
    have hz (s : ℝ) (hs : s ∈ Ioc (0:ℝ) (τ ω)) : U s.toNNReal ω = 0 := by
      have hsτ : s.toNNReal ≤ τ ω := Real.toNNReal_le_iff_le_coe.mpr hs.2
      exact le_antisymm (le_threshold_through_envelopeStop ω (huc ω).continuousOn
        (hu₀ ω).le _ hsτ) (hn _ (hsτ.trans hτ) ω)
    have hJ : (∫ s in Ioc (0 : ℝ) (τ ω), U s.toNNReal ω) = 0 := by
      exact setIntegral_eq_zero_of_forall_eq_zero hz
    have hL : volterraConvolution (fractionalL α) (fun s => U s.toNNReal ω) (τ ω) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro s hs
      exact mul_eq_zero_of_right _ (hz s hs)
    change stoppedProcess M (fun ω => (τ ω : WithTop ℝ≥0)) d ω = _
    rw [stoppedProcess_of_eq_coe (τ := fun x => (τ x : WithTop ℝ≥0)) (ω := ω) d (rfl : (τ ω : WithTop ℝ≥0) = τ ω),
      min_eq_right hτ, he (τ ω) hτ, hJ, hL]
    ring
  have hi := (hS.integrable d).neg
  have hzero : S 0 =ᵐ[P] 0 := by
    filter_upwards [hm₀] with ω h
    exact (stoppedProcess_eq_of_le (show ((0:ℝ≥0) : WithTop ℝ≥0) ≤ _ from bot_le)).trans h
  have hmean := hS.setIntegral_eq (zero_le : (0:ℝ≥0) ≤ d) (s := univ) MeasurableSet.univ
  simp only [setIntegral_univ, integral_congr_ae hzero] at hmean
  have hnon : 0 ≤ᵐ[P] -S d := hv.mono fun ω he => by
    change 0 ≤ -S d ω
    rw [he, neg_neg]
    positivity
  have he := (integral_eq_zero_iff_of_nonneg_ae hnon hi).mp (by
    change (∫ ω, -S d ω ∂P) = 0
    rw [integral_neg, ← hmean]
    simp)
  filter_upwards [hv, he] with ω hvω heω
  change -S d ω = 0 at heω
  rw [hvω,neg_neg] at heω
  have hd' : 0 < (d:ℝ) := hd
  have hz : (τ ω:ℝ) = 0 := (mul_eq_zero.mp heω).resolve_left (div_pos hε hd').ne'
  have hτ : τ ω = 0 := NNReal.coe_eq_zero.mp hz
  obtain ⟨s,hs,hu⟩ := (envelopeStop_lt_horizon_iff d 0 U ω).mp (show τ ω < d by rw [hτ]; exact hd)
  refine ⟨s, ⟨lt_of_le_of_ne zero_le ?_,hs⟩,hu⟩
  rintro rfl
  simp [hu₀ ω] at hu

/-- Strict positivity simultaneously at every age of the focal density
martingale for the rectangular pulse, including after immigration ends. -/
theorem focal_mass_positive_of_rectangular_inverse {d H : ℝ≥0} (hd : 0 < d) (hdH : d ≤ H)
    {ε α κ : ℝ} (hε : 0 < ε) (hα : α < 1) (hκ : 0 ≤ κ)
    {M U : ℝ≥0 → Ω → ℝ} (hm : Martingale M F P) (hp : IsStronglyPredictable F U)
    (hmc : ∀ ω, Continuous (fun s => M s ω)) (hm₀ : M 0 =ᵐ[P] 0)
    (huc : ∀ ω, Continuous (fun s => U s ω)) (hu₀ : ∀ ω, U 0 ω = 0)
    (hn : ∀ s ≤ H, ∀ ω, 0 ≤ U s ω)
    (hinv : ∀ᵐ ω ∂P, ∀ t ≤ H, M t ω =
      volterraConvolution (fractionalL α) (fun s => U s.toNNReal ω) t +
      κ * (∫ s in Ioc (0 : ℝ) t, U s.toNNReal ω) - ε / (d : ℝ) * min (t : ℝ) d) :
    ∀ᵐ ω ∂P, ∀ t ≤ H, 0 < ε + M t ω := by
  have hpos := pulse_activates_before hd hε hm hp hmc hm₀ huc hu₀
    (fun t ht => hn t (ht.trans hdH)) (hinv.mono fun ω he t ht => by
      simpa [min_eq_left (show (t : ℝ) ≤ d from ht)] using he t (ht.trans hdH))
  have hcap : ε / (d:ℝ) * (d:ℝ) = ε := div_mul_cancel₀ _ (show 0 < (d:ℝ) from hd).ne'
  have hrate : 0 < ε / (d:ℝ) := div_pos hε hd
  filter_upwards [hinv,hpos] with ω he hv
  obtain ⟨s,hs,hU⟩ := hv
  have hadd := pulsed_cluster_mass_pos (κ := κ) (r := (H:ℝ)) (d := (d:ℝ))
    (A := fun v => ε / (d:ℝ) * min v (d:ℝ)) hα hκ ((huc ω).comp continuous_real_toNNReal)
    (fun v hv => hn v.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hv.2) ω)
    (fun v _ => hcap ▸ mul_le_mul_of_nonneg_left (min_le_right v (d:ℝ)) hrate.le)
    (fun v hv => by rw [min_eq_left hv.2.le]; exact (mul_lt_mul_of_pos_left hv.2 hrate).trans_eq hcap)
    ⟨(s:ℝ), ⟨hs.1,hs.2⟩, by simpa using hU⟩
  intro t ht
  have h := hadd (t:ℝ) ⟨t.coe_nonneg,ht⟩
  rw [he t ht]
  simp only [Function.comp_def] at h
  linarith only [h]

#print axioms focal_mass_positive_of_rectangular_inverse

#print axioms pulse_activates_before

end RoughHeston
