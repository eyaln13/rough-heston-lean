import PreterminalAffineNoiseRepresentation
import NativeVarianceAmplitude
import NativeShortHorizon
import NativePointTerminalLimit

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston.GirsanovPort

open SHEStochastic SHE SHE.PredictableL2

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} {T : ℝ≥0} {B M a Y : ℝ≥0 → Ω → ℝ}

local notation "ν" => jointPredictableMeasure F μ T

noncomputable def affinePointDensityPath {Ω : Type*} (T : ℝ≥0) (w : ℝ → ℝ) (c q : ℝ)
    (M a Y : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if t < T then affinePreterminalDensity T t w M (fun u x => a u x ^ 2) t ω
    else Real.exp (c - q * Y T ω)

theorem affinePreterminalDensity_consistent {Ω : Type*}
    (T H t : ℝ≥0) (w : ℝ → ℝ) (M a : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    affinePreterminalDensity T H w M a t ω =
      affinePreterminalDensity T (min t H) w M a (min t H) ω := by
  unfold affinePreterminalDensity
  rw [affinePreterminalVarianceMartingale_consistent]
  congr 2
  simp only [affinePreterminalCompensator_eq, min_self]

set_option maxHeartbeats 1600000 in
/-- The preterminal values of the actual point test use successive
prefixes of one full-horizon joint row. -/
theorem affine_point_compatible_prefix_of_joint_prefix
    (P : FiniteScalarIto.Family F μ T Unit)
    (hB₂ : ∀ t, MemLp (B t) 2 μ) (hB : Martingale B F μ)
    (hBclock : Martingale (fun t ω => B t ω^2 - ((min t T : ℝ≥0) : ℝ)) F μ)
    (hAgree : ∀ t ≤ T, P.W () t =ᵐ[μ] B t)
    (ha : IsStronglyPredictable F a)
    (hac : ∀ ω, Continuous (fun t => a t ω))
    (ha₀ : ∀ t ω, 0 ≤ a t ω) (ha₂ : MemLp (Function.uncurry a) 2 ν)
    (hMPrefix : ∀ r ≤ T, M r =ᵐ[μ] jointItoIntegralCLM T hB₂ (jointAmplitudeSectionLp r ha₂))
    (hM : Martingale M F μ) (hM₂ : ∀ s, MemLp (M s) 2 μ)
    (hMc : ∀ ω, Continuous (fun t => M t ω))
    {w : ℝ → ℝ} (hw : ∀ s > 0, ContDiffAt ℝ 1 w s) {c q K : ℝ} (hK : 0 ≤ K)
    (hD : ∀ t < T, Martingale (affinePreterminalDensity T t w M (fun t ω => a t ω ^ 2)) F μ ∧
      ∀ r, ∀ᵐ ω ∂μ, ‖affinePreterminalDensity T t w M (fun t ω => a t ω ^ 2) r ω‖ ≤ K)
    (u : Lp ℝ 2 ν)
    (hu : ⇑u =ᵐ[ν] fun p => min K (affinePointDensityPath T w c q M a Y p.1 p.2) *
      (-(w ((T : ℝ)-(p.1 : ℝ)) * a p.1 p.2))) :
    ∀ t < T, (fun ω => affinePointDensityPath T w c q M a Y t ω - 1) =ᵐ[μ]
      jointItoIntegralCLM T hB₂ (NativeTimeCut.prior t u) := by
  let D := affinePointDensityPath T w c q M a Y
  let f (p : ℝ≥0 × Ω) := min K (D p.1 p.2) * (-(w ((T : ℝ)-(p.1 : ℝ)) * a p.1 p.2))
  intro t ht
  let B' (r : ℝ≥0) := B (min r t)
  let hB₂' (r : ℝ≥0) : MemLp (B' r) 2 μ := hB₂ (min r t)
  let P' := truncateScalarNativeFamily P ht.le
  have hB' : Martingale B' F μ := martingale_freeze_at hB t
  have hBc' : Martingale (fun r ω => B' r ω ^ 2 - ((min r t : ℝ≥0) : ℝ)) F μ := by
    simpa only [B', min_assoc, min_eq_left ht.le] using martingale_freeze_at hBclock t
  have hAgree' (r : ℝ≥0) (hr : r ≤ t) : P'.W () r =ᵐ[μ] B' r := by
    change P.W () r =ᵐ[μ] B (min r t)
    rw [min_eq_left hr]
    exact hAgree r (hr.trans ht.le)
  have ha₂' : MemLp (Function.uncurry a) 2 (jointPredictableMeasure F μ t) := by
    rw [jointPredictableMeasure_eq_restrict F μ ht.le]
    exact ha₂.restrict _
  have hMp (r : ℝ≥0) (hr : r ≤ t) : M r =ᵐ[μ]
      (jointItoIntegralCLM t hB₂' (jointAmplitudeSectionLp r ha₂') : Ω → ℝ) := by
    have hN := hMPrefix r (hr.trans ht.le)
    let g := (Ioc (0 : ℝ≥0) r ×ˢ (univ : Set Ω)).indicator (Function.uncurry a)
    have hz (p : ℝ≥0 × Ω) (hp : t < p.1) : g p = 0 := by
      apply indicator_of_notMem
      exact fun h => hp.not_ge (h.1.2.trans hr)
    have he := jointIto_short_horizon_eq_of_supported_row ht.le hB₂ hB hBclock hz
      (jointAmplitudeSectionLp_ae r ha₂') (jointAmplitudeSectionLp_ae r ha₂)
    rw [he]
    exact hN
  obtain ⟨A, hAa, hArep⟩ := native_amplitude_of_joint_prefix P' hB₂' hB' hBc' hAgree' ha₂' hMp
  obtain ⟨R, hR, hDrep⟩ := affine_preterminal_density_representation P' hB₂' hB' hBc' hAgree' A
    ha hac hAa hM hM₂ hMc hArep ht hw hK (hD t ht).1 (hD t ht).2
  have hRf : ⇑R =ᵐ[jointPredictableMeasure F μ t] f := by
    filter_upwards [hR, ae_mem_joint_timeBand F μ t] with p hp hband
    have hpT : p.1 < T := hband.1.2.trans_lt ht
    have he : affinePreterminalDensity T t w M (fun r ω => a r ω ^ 2) p.1 p.2 = D p.1 p.2 := by
      rw [affinePreterminalDensity_consistent, min_eq_left hband.1.2]
      simp only [D, affinePointDensityPath, ite_eq_left hpT]
    have hw' : affinePreterminalWeight w ((T : ℝ)-(t : ℝ)) t p.1 = w ((T : ℝ)-(p.1 : ℝ)) := by
      simp only [affinePreterminalWeight, min_eq_left hband.1.2]
      congr 1
      ring
    change R p = f p
    rw [hp,he,hw']
  have hI := jointIto_short_horizon_eq_prior ht.le hB₂ hB hBclock hRf hu
  filter_upwards [hDrep] with ω hω
  change D t ω - 1 = _
  have hDt : D t ω = affinePreterminalDensity T t w M (fun r ω => a r ω ^ 2) t ω := by
    simp only [D, affinePointDensityPath, ite_eq_left ht]
  rw [hDt, hω, hI, add_sub_cancel_left]

set_option maxHeartbeats 900000 in
theorem affine_point_compatible_prefix
    (P : FiniteScalarIto.Family F μ T Unit)
    (hB₂ : ∀ t, MemLp (B t) 2 μ) (hB : Martingale B F μ)
    (hBclock : Martingale (fun t ω => B t ω^2 - ((min t T : ℝ≥0) : ℝ)) F μ)
    (hAgree : ∀ t ≤ T, P.W () t =ᵐ[μ] B t)
    (ha : IsStronglyPredictable F a) (haa : StronglyAdapted F a)
    (hac : ∀ ω, Continuous (fun t => a t ω))
    (ha₀ : ∀ t ω, 0 ≤ a t ω) (ha₂ : MemLp (Function.uncurry a) 2 ν)
    (hCut : HasAmplitudeCutoffIntegral F μ T B M a)
    (hM : Martingale M F μ) (hM₂ : ∀ s, MemLp (M s) 2 μ)
    (hMc : ∀ ω, Continuous (fun t => M t ω))
    {w : ℝ → ℝ} (hw : ∀ s > 0, ContDiffAt ℝ 1 w s) {c q K : ℝ} (hK : 0 ≤ K)
    (hD : ∀ t < T, Martingale (affinePreterminalDensity T t w M (fun t ω => a t ω ^ 2)) F μ ∧
      ∀ r, ∀ᵐ ω ∂μ, ‖affinePreterminalDensity T t w M (fun t ω => a t ω ^ 2) r ω‖ ≤ K)
    (u : Lp ℝ 2 ν)
    (hu : ⇑u =ᵐ[ν] fun p => min K (affinePointDensityPath T w c q M a Y p.1 p.2) *
      (-(w ((T : ℝ)-(p.1 : ℝ)) * a p.1 p.2))) :
    ∀ t < T, (fun ω => affinePointDensityPath T w c q M a Y t ω - 1) =ᵐ[μ]
      jointItoIntegralCLM T hB₂ (NativeTimeCut.prior t u) := by
  apply affine_point_compatible_prefix_of_joint_prefix P hB₂ hB hBclock hAgree ha hac ha₀ ha₂
    ?_ hM hM₂ hMc hw hK hD u hu
  intro r hr
  exact hCut.ae_eq_jointIto_fixed_horizon hr hB hB₂ hBclock haa ha
    (ae_of_all _ fun ω => (hac ω).continuousOn) ha₀ ha₂

/-- A continuous point-density path with its calculated preterminal
representatives has the full terminal stochastic integral. -/
theorem affine_point_prefices_include_terminal
    (hB₂ : ∀ t, MemLp (B t) 2 μ) {D : ℝ≥0 → Ω → ℝ}
    (hD : StronglyAdapted F D) (hc : ∀ᵐ ω ∂μ, Continuous (fun t => D t ω))
    (u : Lp ℝ 2 ν)
    (hPre : ∀ t < T, (fun ω => D t ω - 1) =ᵐ[μ]
      jointItoIntegralCLM T hB₂ (NativeTimeCut.prior t u))
    {t : ℕ → ℝ≥0} (ht : ∀ n, t n < T) (hlim : Tendsto t atTop (𝓝 T)) :
    (fun ω => D T ω - 1) =ᵐ[μ] jointItoIntegralCLM T hB₂ u :=
  terminal_joint_repr_of_preterminal_prefix hB₂
    (fun q => (hD q).sub stronglyMeasurable_const)
    (hc.mono fun _ hω => hω.sub continuous_const) u hPre ht hlim

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.affine_point_compatible_prefix
#print axioms RoughHeston.GirsanovPort.affine_point_compatible_prefix_of_joint_prefix
#print axioms RoughHeston.GirsanovPort.affine_point_prefices_include_terminal
