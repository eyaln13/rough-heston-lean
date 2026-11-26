import HestonKernelFamilyMeasurable
import HorizonAmplitudeIntegral
import JointHorizonExtension

open MeasureTheory ProbabilityTheory Filter Set
open scoped MeasureTheory ProbabilityTheory Topology NNReal ENNReal

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℝ≥0 m} {V B M a : ℝ≥0 → Ω → ℝ} {u T : ℝ≥0}

/-- The convolution at `u` only uses the driver through `u`. -/
theorem IsHestonConvolutionAt.congr_driver_on {α : ℝ} {B' : ℝ≥0 → Ω → ℝ} {z : Ω → ℝ}
    (h : IsHestonConvolutionAt μ α u B V z) (he : ∀ s ≤ u, B s =ᵐ[μ] B' s) :
    IsHestonConvolutionAt μ α u B' V z := by
  obtain ⟨hz, J, hJ, hj⟩ := h
  refine ⟨hz, J, fun n => ⟨(hJ n).1, (hJ n).2.congr (fun j => ?_)⟩, hj⟩
  let G := uniformDyadicGrids u
  let A := fun k => hestonCutoffWeight α u V n (G.grid j k)
  have htimes : ∀ᵐ ω ∂μ, ∀ k ≤ 2 ^ j, B (G.grid j k) ω = B' (G.grid j k) ω := by
    refine ae_all_iff.mpr fun k => ?_
    by_cases hk : k ≤ 2 ^ j
    · have hs : G.grid j k ≤ u := (G.grid j).monotone hk |>.trans_eq
        (uniform_dyadic_terminal_vertex u j)
      exact (he _ hs).mono fun _ hω _ => hω
    · exact Eventually.of_forall fun _ h => False.elim (hk h)
  have hsum : dyadicTerminal G j A B =ᵐ[μ] dyadicTerminal G j A B' := by
    filter_upwards [htimes] with ω hω
    simp only [dyadicTerminal, gridIntegral, runningSum, Finset.sum_apply,
      Pi.mul_apply, Pi.sub_apply]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hsucc := Nat.succ_le_of_lt (Finset.mem_range.mp hk)
    rw [hω (k + 1) hsucc, hω k ((Nat.le_succ k).trans hsucc)]
  exact eLpNorm_congr_ae (hsum.sub EventuallyEq.rfl)

variable [IsFiniteMeasure μ]

/-- The fixed-horizon predictable section is the zero extension of the section on `[0,u]`. -/
theorem jointBandExtend_hestonKernelFamilyLp {α : ℝ} (u : Icc (0 : ℝ≥0) T)
    (hα : 1 / 2 < α) (hVp : IsStronglyPredictable 𝒢 V)
    (hVnonneg : ∀ s ω, 0 ≤ V s ω) (hVint : ∀ s, Integrable (V s) μ)
    {C : ℝ} (hmean : ∀ s, (∫ ω, V s ω ∂μ) ≤ C) :
    let w := Function.uncurry (hestonConvolutionWeight α u V)
    let hw := heston_convolution_weight_memLp_two_joint hα u hVp hVnonneg hVint hmean
    jointBandExtend 𝒢 μ u.property.2 (hw.toLp w) =
      hestonKernelFamilyLp hα hVp hVnonneg hVint hmean u := by
  dsimp only
  apply Lp.ext
  refine (jointBandExtend_toLp_ae_eq 𝒢 μ u.property.2 ?_ _).trans
    (hestonKernelFamilyLp_ae hα hVp hVnonneg hVint hmean u).symm
  intro z hz
  have h : ¬ 0 < ((u : ℝ≥0) : ℝ) - (z.1 : ℝ) :=
    not_lt.mpr (sub_nonpos.mpr (NNReal.coe_le_coe.mpr (le_of_lt hz)))
  simp [Function.uncurry, hestonConvolutionWeight, hestonKernel, h]

/-- The fixed-horizon Itô map computes the same stochastic convolution
as the square-mean dyadic and cutoff limits at the observation time. -/
theorem isHestonConvolutionAt_jointIto_fixed_horizon {α : ℝ} (u : Icc (0 : ℝ≥0) T)
    (hα : 1 / 2 < α) (hα' : α ≤ 1)
    (hB : Martingale B 𝒢 μ) (hB₂ : ∀ s, MemLp (B s) 2 μ)
    (hclock : Martingale (fun s ω => B s ω ^ 2 - ((min s T : ℝ≥0) : ℝ)) 𝒢 μ)
    (hVp : IsStronglyPredictable 𝒢 V) (hVa : StronglyAdapted 𝒢 V)
    (hVc : ∀ᵐ ω ∂μ, ContinuousOn (fun s => V s ω) (Icc 0 (u : ℝ≥0)))
    (hVnonneg : ∀ s ω, 0 ≤ V s ω) (hVint : ∀ s, Integrable (V s) μ)
    {C : ℝ} (hmean : ∀ s, (∫ ω, V s ω ∂μ) ≤ C) :
    IsHestonConvolutionAt μ α u B V
      (jointItoIntegralCLM T hB₂ (hestonKernelFamilyLp hα hVp hVnonneg hVint hmean u) : Ω → ℝ) := by
  let Bu (s : ℝ≥0) := B (min s u)
  let hBu₂ (s : ℝ≥0) : MemLp (Bu s) 2 μ := hB₂ (min s u)
  have hBu : Martingale Bu 𝒢 μ := martingale_freeze_at hB u
  have hclock_u : Martingale (fun s ω => Bu s ω ^ 2 - ((min s (u : ℝ≥0) : ℝ≥0) : ℝ)) 𝒢 μ := by
    simpa only [Bu, min_assoc, min_eq_left u.property.2] using martingale_freeze_at hclock (u : ℝ≥0)
  have hshort := isHestonConvolutionAt_jointIto hα hα' u hBu hBu₂ hclock_u
    hVp hVa hVc hVnonneg hVint hmean
  dsimp only at hshort
  rw [jointItoIntegralCLM_cross_horizon 𝒢 μ u.property.2 hB₂ hB hclock,
    jointBandExtend_hestonKernelFamilyLp u hα hVp hVnonneg hVint hmean] at hshort
  exact hshort.congr_driver_on fun s hs => Eventually.of_forall fun ω =>
    congrFun (congrArg B (min_eq_left hs)) ω

/-- Any short-horizon dyadic convolution agrees almost surely with the fixed-horizon integral. -/
theorem IsHestonConvolutionAt.ae_eq_jointIto_fixed_horizon {α : ℝ} (u : Icc (0 : ℝ≥0) T)
    {z : Ω → ℝ} (h : IsHestonConvolutionAt μ α u B V z)
    (hα : 1 / 2 < α) (hα' : α ≤ 1)
    (hB : Martingale B 𝒢 μ) (hB₂ : ∀ s, MemLp (B s) 2 μ)
    (hclock : Martingale (fun s ω => B s ω ^ 2 - ((min s T : ℝ≥0) : ℝ)) 𝒢 μ)
    (hVp : IsStronglyPredictable 𝒢 V) (hVa : StronglyAdapted 𝒢 V)
    (hVc : ∀ᵐ ω ∂μ, ContinuousOn (fun s => V s ω) (Icc 0 (u : ℝ≥0)))
    (hVnonneg : ∀ s ω, 0 ≤ V s ω) (hVint : ∀ s, Integrable (V s) μ)
    {C : ℝ} (hmean : ∀ s, (∫ ω, V s ω ∂μ) ≤ C) :
    z =ᵐ[μ] (jointItoIntegralCLM T hB₂ (hestonKernelFamilyLp hα hVp hVnonneg hVint hmean u) : Ω → ℝ) :=
  h.ae_unique (isHestonConvolutionAt_jointIto_fixed_horizon u hα hα' hB hB₂ hclock
    hVp hVa hVc hVnonneg hVint hmean)

/-- A stopped amplitude section viewed in the fixed predictable space. -/
noncomputable def jointAmplitudeSectionLp (u : ℝ≥0)
    (ha₂ : MemLp (Function.uncurry a) 2 (jointPredictableMeasure 𝒢 μ T)) :
    Lp ℝ 2 (jointPredictableMeasure 𝒢 μ T) :=
  (ha₂.indicator (measurableSet_joint_timeBand 𝒢 u).nullMeasurableSet).toLp
    ((Ioc (0 : ℝ≥0) u ×ˢ (univ : Set Ω)).indicator (Function.uncurry a))

omit [IsFiniteMeasure μ] in
theorem jointAmplitudeSectionLp_ae (u : ℝ≥0)
    (ha₂ : MemLp (Function.uncurry a) 2 (jointPredictableMeasure 𝒢 μ T)) :
    ⇑(jointAmplitudeSectionLp u ha₂) =ᵐ[jointPredictableMeasure 𝒢 μ T]
      (Ioc (0 : ℝ≥0) u ×ˢ (univ : Set Ω)).indicator (Function.uncurry a) :=
  (ha₂.indicator (measurableSet_joint_timeBand 𝒢 u).nullMeasurableSet).coeFn_toLp

/-- The recovered amplitude martingale is the fixed-horizon Itô
integral of the amplitude stopped at the observation time. -/
theorem HasAmplitudeCutoffIntegral.ae_eq_jointIto_fixed_horizon
    (hu : u ≤ T) (h : HasAmplitudeCutoffIntegral 𝒢 μ T B M a)
    (hB : Martingale B 𝒢 μ) (hB₂ : ∀ s, MemLp (B s) 2 μ)
    (hclock : Martingale (fun s ω => B s ω ^ 2 - ((min s T : ℝ≥0) : ℝ)) 𝒢 μ)
    (haa : StronglyAdapted 𝒢 a)
    (hasm : StronglyMeasurable[𝒢.predictable] (Function.uncurry a))
    (hac : ∀ᵐ ω ∂μ, ContinuousOn (fun s => a s ω) (Icc 0 u))
    (ha : ∀ s ω, 0 ≤ a s ω)
    (ha₂ : MemLp (Function.uncurry a) 2 (jointPredictableMeasure 𝒢 μ T)) :
    M u =ᵐ[μ] (jointItoIntegralCLM T hB₂ (jointAmplitudeSectionLp u ha₂) : Ω → ℝ) := by
  have hau : MemLp (Function.uncurry a) 2 (jointPredictableMeasure 𝒢 μ u) := by
    rw [jointPredictableMeasure_eq_restrict 𝒢 μ hu]
    exact ha₂.restrict _
  have hshort := h.ae_eq_jointItoAt hu hB hB₂ hclock haa hasm hac ha hau
  dsimp only at hshort
  rw [jointItoIntegralCLM_cross_horizon 𝒢 μ hu hB₂ hB hclock] at hshort
  have heq : jointBandExtend 𝒢 μ hu (hau.toLp (Function.uncurry a)) = jointAmplitudeSectionLp u ha₂ :=
    Lp.ext ((jointBandExtend_coeFn 𝒢 μ hu (hau.toLp (Function.uncurry a))).trans
      ((joint_timeBand_indicator_ae_eq 𝒢 μ hu hau.coeFn_toLp).trans
        (jointAmplitudeSectionLp_ae u ha₂).symm))
  simpa only [heq] using hshort

end RoughHeston

#print axioms RoughHeston.IsHestonConvolutionAt.congr_driver_on
#print axioms RoughHeston.jointBandExtend_hestonKernelFamilyLp
#print axioms RoughHeston.isHestonConvolutionAt_jointIto_fixed_horizon
#print axioms RoughHeston.jointAmplitudeSectionLp_ae
#print axioms RoughHeston.HasAmplitudeCutoffIntegral.ae_eq_jointIto_fixed_horizon

#print axioms RoughHeston.IsHestonConvolutionAt.ae_eq_jointIto_fixed_horizon
