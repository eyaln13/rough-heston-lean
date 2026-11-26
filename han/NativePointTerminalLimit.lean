import BridgeScalarNative
import SHEStochastic.NativeTimeCut
import JointDyadicIntegral
import HestonFubiniKernel

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston.GirsanovPort

open SHEStochastic

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} {H : ℝ≥0} {B M : ℝ≥0 → Ω → ℝ}

local notation "ν" => jointPredictableMeasure F μ H

/-- Causal predictable L² rows lose no terminal energy at the last
singleton when the deterministic preterminal times increase to H. -/
theorem native_prior_tendsto_at_horizon (u : Lp ℝ 2 ν)
    {t : ℕ → ℝ≥0} (hlim : Tendsto t atTop (𝓝 H)) :
    Tendsto (fun n => NativeTimeCut.prior (t n) u) atTop (𝓝 u) := by
  let a (n : ℕ) : Lp ℝ 2 ν := NativeTimeCut.prior (t n) u
  let d (n : ℕ) (p : ℝ≥0 × Ω) := a n p - u p
  have hd : Tendsto (fun n => eLpNorm (d n) 2 ν) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_two_dominated (Lp.memLp u)
    · intro n
      exact (Lp.stronglyMeasurable (a n)).aestronglyMeasurable.sub (Lp.stronglyMeasurable u).aestronglyMeasurable
    · intro n
      filter_upwards [NativeTimeCut.prior_ae (t n) u] with p hp
      change ‖(NativeTimeCut.prior (t n) u) p - u p‖ ≤ ‖u p‖
      rw [hp]
      change ‖(if t n < p.1 then 0 else u p) - u p‖ ≤ ‖u p‖
      by_cases ht : t n < p.1 <;> simp [ht]
    · filter_upwards [ae_fst_mem_Ioo_jointPredictableMeasure (𝒢 := F) (μ := μ) H,
        ae_all_iff.mpr (fun n => NativeTimeCut.prior_ae (t n) u)] with p hp hu
      have h : ∀ᶠ n in atTop, p.1 < t n := hlim.eventually (Ioi_mem_nhds hp.2)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [h] with n hn
      change (0 : ℝ) = (NativeTimeCut.prior (t n) u) p - u p
      rw [hu n, ite_eq_right (not_lt_of_ge hn.le)]
      change (0 : ℝ) = u p - u p
      rw [sub_self]
  apply tendsto_iff_edist_tendsto_0.mpr
  exact hd.congr (fun n => (Lp.edist_def (a n) u).symm)

/-- Continuous preterminal affine representatives with the same
underlying predictable row extend to the terminal payoff in joint L². -/
theorem terminal_joint_repr_of_preterminal_prefix
    (hB₂ : ∀ t, MemLp (B t) 2 μ) (hM : StronglyAdapted F M)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (u : Lp ℝ 2 ν)
    (hpre : ∀ t < H, M t =ᵐ[μ] jointItoIntegralCLM H hB₂ (NativeTimeCut.prior t u))
    {t : ℕ → ℝ≥0} (ht : ∀ n, t n < H) (hlim : Tendsto t atTop (𝓝 H)) :
    M H =ᵐ[μ] jointItoIntegralCLM H hB₂ u := by
  have hmeas (n : ℕ) : AEStronglyMeasurable (M (t n)) μ :=
    ((hM (t n)).mono (F.le _)).aestronglyMeasurable
  have hMlim : TendstoInMeasure μ (fun n => M (t n)) atTop (M H) :=
    tendstoInMeasure_of_tendsto_ae hmeas <| hc.mono fun ω hω => (hω.tendsto H).comp hlim
  let J := jointItoIntegralCLM (𝒢 := F) H hB₂
  have hIlp : Tendsto (fun n => J (NativeTimeCut.prior (t n) u)) atTop (𝓝 (J u)) :=
    (J.continuous.tendsto u).comp (native_prior_tendsto_at_horizon u hlim)
  have hIlim := tendstoInMeasure_of_tendsto_Lp hIlp
  exact tendstoInMeasure_ae_unique hMlim (hIlim.congr_left fun n => (hpre _ (ht n)).symm)

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.native_prior_tendsto_at_horizon
#print axioms RoughHeston.GirsanovPort.terminal_joint_repr_of_preterminal_prefix
