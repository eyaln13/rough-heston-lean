import BoundedNativeExpEnergyRepresentation
import StoppedExponentialEnergy
import JointAffineStopAfterBirth
import SHEStochastic.NativeExponentialMartingale

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston.GirsanovPort

open SHEStochastic SHE SHE.PredictableL2

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} [Approximable F μ] {H : ℝ≥0} {B N : ℝ≥0 → Ω → ℝ}

local notation "ν" => jointPredictableMeasure F μ H

/-- The explicit exponential of a Brownian integral and its energy. -/
noncomputable def jointStochasticExponential (N g : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (N t ω - affineEnergyClock g t ω / 2)

omit [IsProbabilityMeasure μ] [Approximable F μ] in
theorem jointStochasticExponential_adapted {g : ℝ≥0 → Ω → ℝ}
    (hN : StronglyAdapted F N) (hg : StronglyAdapted F g) (hgc : ∀ ω, Continuous (fun t => g t ω)) :
    StronglyAdapted F (jointStochasticExponential N g) := by
  intro t
  exact Real.continuous_exp.comp_stronglyMeasurable
    ((hN t).sub ((affineEnergyClock_stronglyAdapted hg hgc t).div stronglyMeasurable_const))

omit m [IsProbabilityMeasure μ] [Approximable F μ] in
theorem jointStochasticExponential_continuous {g : ℝ≥0 → Ω → ℝ}
    (hNc : ∀ ω, Continuous (fun t => N t ω)) (hgc : ∀ ω, Continuous (fun t => g t ω)) (ω : Ω) :
    Continuous (fun t => jointStochasticExponential N g t ω) :=
  Real.continuous_exp.comp ((hNc ω).sub ((affineEnergyClock_continuous hgc ω).div_const 2))

omit [Approximable F μ] in
private theorem prior_horizon_eq (u : Lp ℝ 2 ν) : NativeTimeCut.prior H u = u := by
  apply Lp.ext
  filter_upwards [NativeTimeCut.prior_ae H u,
    ae_fst_mem_Ioo_jointPredictableMeasure (𝒢:=F) (μ:=μ) H] with p hp hmem
  rw [hp, ite_eq_right (not_lt_of_ge hmem.2.le)]

set_option maxHeartbeats 1300000 in
/-- Terminal integral identity for the actual stochastic exponential
stopped at a bounded-energy stopping time. All integrals use the same
Brownian driver and the supplied filtration. -/
theorem stopped_joint_stochastic_exponential
    (P : FiniteScalarIto.Family F μ H Unit)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hB₂ : ∀ t, MemLp (B t) 2 μ) (hB : Martingale B F μ)
    (hBclock : Martingale (fun t ω => B t ω ^ 2 - ((min t H : ℝ≥0) : ℝ)) F μ)
    (hAgree : ∀ t ≤ H, P.W () t =ᵐ[μ] B t)
    (hN : StronglyAdapted F N) (hNc : ∀ ω, Continuous (fun t => N t ω))
    {g : ℝ≥0 → Ω → ℝ} (hg : IsStronglyPredictable F g) (hgc : ∀ ω, Continuous (fun t => g t ω))
    (u : Lp ℝ 2 ν) (hu : ⇑u =ᵐ[ν] Function.uncurry g)
    (hRep : ∀ t, N t =ᵐ[μ] jointItoIntegralCLM H hB₂ (NativeTimeCut.prior t u))
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτH : ∀ ω, τ ω ≤ H) {K E : ℝ} (hK : 0 ≤ K) (hE : 0 ≤ E)
    (hbd : ∀ ω t, t ≤ τ ω → |jointStochasticExponential N g t ω| ≤ K)
    (hCap : ∀ ω, affineEnergyClock g (τ ω) ω ≤ E) :
    ∃ r : Lp ℝ 2 ν, (⇑r =ᵐ[ν] fun p =>
      controlThrough (fun t ω => jointStochasticExponential N g t ω * g t ω) τ p.1 p.2) ∧
      (fun ω => jointStochasticExponential N g (τ ω) ω) =ᵐ[μ]
        (fun ω => 1 + jointItoIntegralCLM H hB₂ r ω) := by
  let g' := controlThrough g τ
  have hg' : IsStronglyPredictable F g' := controlThrough_predictable hτ hg
  have hvLp : MemLp (Function.uncurry g') 2 ν := by
    refine (Lp.memLp u).mono hg'.aestronglyMeasurable ?_
    filter_upwards [hu] with p hp
    change ‖controlThrough g τ p.1 p.2‖ ≤ ‖u p‖
    change u p = g p.1 p.2 at hp
    rw [hp]
    by_cases h : p.1 ≤ τ p.2 <;> simp [controlThrough, h]
  let v := hvLp.toLp (Function.uncurry g')
  have hv : ⇑v =ᵐ[ν] Function.uncurry g' := hvLp.coeFn_toLp
  let D (t : ℝ≥0) (ω : Ω) := jointStochasticExponential N g (min t (τ ω)) ω
  have hDform (t : ℝ≥0) (ω : Ω) : D t ω =
      Real.exp (N (min t (τ ω)) ω - affineEnergyClock g' t ω / 2) := by
    simp only [D,jointStochasticExponential,g',affineEnergyClock_controlThrough]
  have hDa : StronglyAdapted F D := by
    have h := ((jointStochasticExponential_adapted hN hg.stronglyAdapted hgc).isStronglyProgressive_of_continuous
      (jointStochasticExponential_continuous hNc hgc)).stronglyAdapted_stoppedProcess hτ
    intro t
    convert h t using 2
    funext ω
    simp only [stoppedProcess, D, ← WithTop.coe_min, WithTop.untopA_eq_untop WithTop.coe_ne_top,
      WithTop.untop_coe]
  have hDc (ω : Ω) : Continuous (fun t => D t ω) :=
    (jointStochasticExponential_continuous hNc hgc ω).comp (continuous_id.min continuous_const)
  have hD : IsStronglyPredictable F D := hDa.isStronglyPredictable_of_leftContinuous (fun ω _ => (hDc ω).continuousWithinAt)
  have hDbd (t : ℝ≥0) (ω : Ω) : ‖D t ω‖ ≤ K := hbd ω _ (min_le_right _ _)
  have hNStop (t : ℝ≥0) : (fun ω => N (min t (τ ω)) ω) =ᵐ[μ]
      jointItoIntegralCLM H hB₂ (NativeTimeCut.prior t v) := by
    have hstop : IsStoppingTime F (fun ω => (min t (τ ω) : WithTop ℝ≥0)) := by
      simpa only [WithTop.coe_min] using (isStoppingTime_const F t).min hτ
    apply jointIto_random_stop_of_prefix P hnull hB₂ hB hBclock hAgree hN (ae_of_all _ hNc) u
      (NativeTimeCut.prior t v) hRep hstop (fun ω => (min_le_right _ _).trans (hτH ω))
    filter_upwards [NativeTimeCut.prior_ae t v, hv, hu] with p hp h₂ h₃
    change v p = controlThrough g τ p.1 p.2 at h₂
    change u p = g p.1 p.2 at h₃
    rw [hp,h₂,h₃]
    simp only [controlThrough, le_min_iff]
    by_cases h : p.1 ≤ t <;> simp [h, not_lt.mpr, lt_of_not_ge]
  have hDnative (t : ℝ≥0) (ht : t ≤ H) : D t =ᵐ[μ]
      NativeExponential.density P scalarHilbertBasis 1 (NativeTimeCut.prior t v) := by
    have he := scalarNativeIntegral_eq_joint P.toCoordinates hB₂ hB hBclock hAgree (NativeTimeCut.prior t v)
    filter_upwards [hNStop t, affineEnergyClock_prior_eq v hg' hv ht] with ω h₁ h₂
    rw [hDform, h₁]
    change _ = Real.exp (1 * FiniteCylindricalIto.rawIntegral P.toCoordinates scalarHilbertBasis
        (NativeTimeCut.prior t v) ω - 1^2 * NativeEnergy.energy (NativeTimeCut.prior t v) ω / 2)
    rw [he,h₂]
    simp
  have hEnergy : ∀ᵐ ω ∂μ, NativeEnergy.energy v ω ≤ E := by
    filter_upwards [affineEnergyClock_prior_eq v hg' hv (le_refl H)] with ω hw
    dsimp only [g'] at hw
    rw [prior_horizon_eq, affineEnergyClock_controlThrough, min_eq_right (hτH ω)] at hw
    rw [hw]
    exact hCap ω
  have hEnd : D H =ᵐ[μ] NativeExponential.density P scalarHilbertBasis 1 v := by
    simpa only [prior_horizon_eq] using hDnative H le_rfl
  have hMean : (∫ ω, D H ω ∂μ) = 1 := by
    rw [integral_congr_ae hEnd]
    exact (NativeBoundedExponential.bounded_energy P scalarHilbertBasis 1 v E hE hEnergy).2.1
  have hCond (t : ℝ≥0) (ht : t ≤ H) : μ[D H | F t] =ᵐ[μ] D t :=
    (condExp_congr_ae hEnd).trans ((NativeExponentialMartingale.conditional_at_time
      P scalarHilbertBasis 1 t ht v E hE hEnergy).trans (hDnative t ht).symm)
  have hA := affineEnergyClock_controlThrough_stronglyAdapted hg'
  have hAc (ω : Ω) : Continuous (fun t => affineEnergyClock g' t ω) := by
    simp_rw [g',affineEnergyClock_controlThrough]
    exact (affineEnergyClock_continuous hgc ω).comp (continuous_id.min continuous_const)
  have hAm : Measurable (Function.uncurry (affineEnergyClock g')) :=
    measurable_uncurry_of_continuous_of_measurable hAc (fun t => ((hA t).mono (F.le t)).measurable)
  have hGm : Measurable (fun p : ℝ≥0 × Ω => Real.exp (affineEnergyClock g' p.1 p.2) * (g' p.1 p.2)^2) :=
    hAm.exp.mul (((hg'.mono F.predictable_le_prod).measurable).pow_const 2)
  have hGad (t : ℝ≥0) : StronglyMeasurable[F t]
      (fun ω => Real.exp (affineEnergyClock g' t ω) * (g' t ω)^2) :=
    (Real.continuous_exp.comp_stronglyMeasurable (hA t)).mul ((hg'.stronglyAdapted t).pow 2)
  have hGω := ae_of_all μ (affineEnergyClock_exp_identity_controlThrough hgc hτH)
  obtain ⟨r,hr,he⟩ := bounded_native_exp_joint_representation_of_energy_identity P hB₂ hB hBclock hAgree
    v hg' hGad hGm hGω hv hD hK hDbd hDnative hMean hCond
  refine ⟨r, hr.trans (ae_of_all _ fun p => ?_), ?_⟩
  · by_cases hp : p.1 ≤ τ p.2
    · simp [D,g',controlThrough,hp]
    · simp [g',controlThrough,hp]
  · simpa only [D, show ∀ ω, min H (τ ω) = τ ω from fun ω => min_eq_right (hτH ω)] using he

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.stopped_joint_stochastic_exponential
