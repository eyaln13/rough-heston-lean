import AffineLocalExponential
import StochasticFoundation
import Mathlib.Topology.Order.IsLUB

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace RoughHeston

/-- Uniformly bounded preterminal martingales extend to the terminal
time by a continuous version and dominated convergence. -/
theorem affine_martingale_of_bounded_preterminal_of_left_limit {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝒢 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {D : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {C : ℝ} (hT : 0 < T)
    (had : StronglyAdapted 𝒢 D)
    (_hC : 0 ≤ C) (hB : ∀ t < T, ∀ᵐ ω ∂μ, ‖D t ω‖ ≤ C)
    (hleft : ∀ᵐ ω ∂μ, Tendsto (fun t => D t ω) (𝓝[<] T) (𝓝 (D T ω)))
    (hM : ∀ t < T, Martingale (fun s => D (min s t)) 𝒢 μ) :
    Martingale (fun s => D (min s T)) 𝒢 μ := by
  obtain ⟨u,hm,hu,hlim⟩ := exists_seq_strictMono_tendsto' hT
  have hDlim : ∀ᵐ ω ∂μ, Tendsto (fun n => D (u n) ω) atTop (𝓝 (D T ω)) := by
    filter_upwards [hleft] with ω hω
    have huWithin : Tendsto u atTop (𝓝[<] T) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hlim
        (Eventually.of_forall fun n => (hu n).2)
    exact hω.comp huWithin
  have hBT : ∀ᵐ ω ∂μ, ‖D T ω‖ ≤ C := by
    filter_upwards [hDlim,ae_all_iff.mpr (fun n => hB (u n) (hu n).2)] with ω hl hb
    exact le_of_tendsto hl.norm (Eventually.of_forall hb)
  have hBa (t : ℝ≥0) (ht : t ≤ T) : ∀ᵐ ω ∂μ, ‖D t ω‖ ≤ C := by
    rcases lt_or_eq_of_le ht with hlt | he
    · exact hB t hlt
    · simpa only [he] using hBT
  have hAd' : StronglyAdapted 𝒢 (fun s => D (min s T)) :=
    fun s => (had (min s T)).mono (𝒢.mono (min_le_left _ _))
  have hInt (s : ℝ≥0) : Integrable (D (min s T)) μ :=
    (integrable_const C).mono' ((hAd' s).mono (𝒢.le s)).aestronglyMeasurable
      (hBa _ (min_le_right _ _))
  refine martingale_of_past_set_integrals hAd' hInt ?_
  intro s t hst A hA
  by_cases htT : t < T
  · have hsT : s < T := hst.trans_lt htT
    simpa only [min_eq_left hst, min_self, min_eq_left hsT.le, min_eq_left htT.le] using
      (hM t htT).setIntegral_eq hst hA
  have hTt : T ≤ t := le_of_not_gt htT
  by_cases hsT : s < T
  · rw [min_eq_left hsT.le,min_eq_right hTt]
    let ν := μ.restrict A
    have hDCT := tendsto_integral_of_dominated_convergence (μ := ν) (fun _ : Ω => C)
      (fun n => ((had (u n)).mono (𝒢.le (u n))).aestronglyMeasurable)
      (integrable_const C)
      (fun n => ae_mono Measure.restrict_le_self (hB (u n) (hu n).2))
      (ae_mono Measure.restrict_le_self hDlim)
    have hNear := hlim.eventually (Ioi_mem_nhds hsT)
    have hEq : (fun n => ∫ ω,D (u n) ω ∂ν) =ᶠ[atTop]
        fun _ => ∫ ω,D s ω ∂ν := by
      filter_upwards [hNear] with n hn
      have hsu : s ≤ u n := (show s<u n from hn).le
      simpa only [min_eq_left hsu,min_self] using ((hM (u n) (hu n).2).setIntegral_eq hsu hA).symm
    exact tendsto_nhds_unique (tendsto_const_nhds.congr' hEq.symm) hDCT
  · rw [min_eq_right (le_of_not_gt hsT),min_eq_right hTt]

/-- A continuous version supplies the left limit needed by the
bounded preterminal martingale limit. -/
theorem affine_martingale_of_bounded_preterminal {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝒢 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {D : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {C : ℝ} (hT : 0 < T)
    (had : StronglyAdapted 𝒢 D)
    (_hC : 0 ≤ C) (hB : ∀ t < T, ∀ᵐ ω ∂μ, ‖D t ω‖ ≤ C)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => D t ω) (Icc 0 T))
    (hM : ∀ t < T, Martingale (fun s => D (min s t)) 𝒢 μ) :
    Martingale (fun s => D (min s T)) 𝒢 μ := by
  refine affine_martingale_of_bounded_preterminal_of_left_limit hT had _hC hB ?_ hM
  filter_upwards [hc] with ω hω
  have hNH : 𝓝[<] T ≤ 𝓝[Icc (0:ℝ≥0) T] T := by
    refine le_inf nhdsWithin_le_nhds (le_principal_iff.mpr ?_)
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ⟨zero_le,(show t<T from ht).le⟩
  have he := hω T ⟨zero_le,le_rfl⟩
  change Tendsto (fun t => D t ω) (𝓝[Icc (0:ℝ≥0) T] T) (𝓝 (D T ω)) at he
  exact he.mono_left hNH

/-- Terminal and preterminal affine exponent identities give the
conditional transform once the bounded preterminal martingales have
been constructed in the ambient filtration. -/
theorem conditional_affine_laplace_of_preterminal_martingales {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝒢 : Filtration ℝ≥0 m} {D : ℝ≥0 → Ω → ℝ}
    {s T : ℝ≥0} (hs : s < T) {payoff future : Ω → ℝ} (c : ℝ)
    (had : StronglyAdapted 𝒢 D)
    (hB : ∀ t < T, ∀ᵐ ω ∂μ, ‖D t ω‖ ≤ Real.exp c)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => D t ω) (Icc 0 T))
    (hM : ∀ t < T, Martingale (fun r => D (min r t)) 𝒢 μ)
    (hTerm : D T =ᵐ[μ] fun ω => Real.exp (c-payoff ω))
    (hFuture : D s =ᵐ[μ] fun ω => Real.exp (c-future ω)) :
    μ[(fun ω => Real.exp (-payoff ω)) | 𝒢 s] =ᵐ[μ] fun ω => Real.exp (-future ω) := by
  let _ : MeasurableSpace Ω := m
  have hM' := affine_martingale_of_bounded_preterminal (zero_le.trans_lt hs) had (Real.exp_pos c).le hB hc hM
  have hPay : (fun ω => Real.exp (-payoff ω)) =ᵐ[μ] Real.exp (-c) • D T := by
    filter_upwards [hTerm] with ω hω
    rw [Pi.smul_apply,smul_eq_mul,hω,← Real.exp_add]
    congr 1
    ring
  have hCE := hM'.condExp_ae_eq hs.le
  simp only [min_self,min_eq_left hs.le] at hCE
  refine ((condExp_congr_ae hPay).trans (condExp_smul (Real.exp (-c)) (D T) (𝒢 s))).trans ?_
  filter_upwards [hCE,hFuture] with ω hE hω
  rw [Pi.smul_apply,smul_eq_mul,hE,hω,← Real.exp_add]
  congr 1
  ring

#print axioms affine_martingale_of_bounded_preterminal_of_left_limit
#print axioms affine_martingale_of_bounded_preterminal
#print axioms conditional_affine_laplace_of_preterminal_martingales

end RoughHeston
