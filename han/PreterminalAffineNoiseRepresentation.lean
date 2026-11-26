import NativeWeightedAffinePrefix
import AffineNativeContinuousRepresentation
import HestonConditionalAffine
import SHEStochastic.FilteredStoppedIto

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston.GirsanovPort

open SHEStochastic SHE SHE.PredictableL2

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} {T H : ℝ≥0} {B M a : ℝ≥0 → Ω → ℝ}

local notation "ν" => jointPredictableMeasure F μ H

set_option maxHeartbeats 1500000 in
/-- The actual bounded affine preterminal density has the joint
Brownian representation with the original variance amplitude. -/
theorem affine_preterminal_density_representation
    (P : FiniteScalarIto.Family F μ H Unit)
    (hB₂ : ∀ t, MemLp (B t) 2 μ) (hB : Martingale B F μ)
    (hBclock : Martingale (fun t ω => B t ω^2 - ((min t H : ℝ≥0) : ℝ)) F μ)
    (hAgree : ∀ t ≤ H, P.W () t =ᵐ[μ] B t)
    (A : Process (E := ℝ) F μ H)
    (ha : IsStronglyPredictable F a) (hac : ∀ ω, Continuous (fun t => a t ω))
    (hAa : ⇑A =ᵐ[energyMeasure μ H] Function.uncurry a)
    (hM : Martingale M F μ) (hM₂ : ∀ s, MemLp (M s) 2 μ)
    (hMc : ∀ ω, Continuous (fun t => M t ω))
    (hRep : ∀ t ≤ H, M t =ᵐ[μ] ⇑((FiniteCylindricalIto.terminalIto P.toCoordinates scalarHilbertBasis).integral
      (StoppedItoInputs.stop F μ H t A)))
    (hHT : H < T) {w : ℝ → ℝ} (hw : ∀ s > 0, ContDiffAt ℝ 1 w s)
    {K : ℝ} (hK : 0 ≤ K)
    (hDmart : Martingale (affinePreterminalDensity T H w M (fun t ω => a t ω ^ 2)) F μ)
    (hDbd : ∀ t, ∀ᵐ ω ∂μ, ‖affinePreterminalDensity T H w M (fun t ω => a t ω ^ 2) t ω‖ ≤ K) :
    let W := affinePreterminalWeight w ((T : ℝ)-(H : ℝ)) H
    let D := affinePreterminalDensity T H w M (fun t ω => a t ω ^ 2)
    ∃ v : Lp ℝ 2 ν,
      (⇑v =ᵐ[ν] fun p => min K (D p.1 p.2) * (-(W p.1 * a p.1 p.2))) ∧
      D H =ᵐ[μ] fun ω => 1 + jointItoIntegralCLM H hB₂ v ω := by
  let d := (T : ℝ) - (H : ℝ)
  let W := affinePreterminalWeight w d H
  let b (t : ℝ≥0) (ω : Ω) := a t ω ^ 2
  let D := affinePreterminalDensity T H w M b
  let Dc (t : ℝ≥0) (ω : Ω) := min K (D t ω)
  have hd : 0 < d := sub_pos.mpr (NNReal.coe_lt_coe.mpr hHT)
  have hWc : ContinuousOn w (Icc d (d+(H:ℝ))) := fun x hx =>
    (hw x (hd.trans_le hx.1)).continuousAt.continuousWithinAt
  let x (s : ℝ≥0) := d+((H:ℝ)-(min s H:ℝ≥0))
  have hx (s : ℝ≥0) : x s ∈ Icc d (d+(H:ℝ)) :=
    ⟨le_add_of_nonneg_right (sub_nonneg.mpr (NNReal.coe_le_coe.mpr (min_le_right _ _))),
      by dsimp [x]; linarith [NNReal.coe_nonneg (min s H)]⟩
  have hWx : Continuous W := hWc.comp_continuous
    (continuous_const.add (continuous_const.sub (NNReal.continuous_coe.comp
      (continuous_id.min continuous_const)))) hx
  obtain ⟨C,hC⟩ := isCompact_Icc.bddAbove_image hWc.norm
  let K' := max C 0
  have hK' : 0 ≤ K' := le_max_right _ _
  have hWbd (t : ℝ≥0) : ‖W t‖ ≤ K' :=
    (show ‖W t‖ ≤ C from hC ⟨x t,hx t,rfl⟩).trans (le_max_left _ _)
  have hν : ν = (energyMeasure μ H).trim F.predictable_le_prod :=
    (FilteredScalarIto.processMeasure_eq (𝓖 := F) (μ := μ) H
      (B := fun _ _ => (0 : ℝ)) (fun _ => measurable_const)).symm
  let Ap : Lp ℝ 2 ν := FiniteCylindricalIto.processTransport A
  have hAa' : ⇑A =ᵐ[ν] Function.uncurry a := by
    rw [hν]
    exact ae_eq_trim_of_measurable F.predictable_le_prod (Lp.stronglyMeasurable A).measurable
      ha.measurable hAa
  have hAp : ⇑Ap =ᵐ[ν] Function.uncurry a := (FiniteCylindricalIto.processTransport_ae A).trans hAa'
  let g (t : ℝ≥0) (ω : Ω) := -(W t * a t ω)
  have hgc (ω : Ω) : Continuous (fun t => g t ω) := (hWx.mul (hac ω)).neg
  have hg : IsStronglyPredictable F g :=
    ((hWx.measurable.comp (SHE.PredictableClock.time_measurable F)).stronglyMeasurable.mul ha).neg
  have hi : MemLp (Function.uncurry g) 2 ν := by
    refine ((Lp.memLp Ap).const_mul K').mono hg.aestronglyMeasurable ?_
    filter_upwards [hAp] with p hp
    change ‖-(W p.1 * a p.1 p.2)‖ ≤ ‖K' * Ap p‖
    change Ap p = a p.1 p.2 at hp
    rw [norm_neg, norm_mul, norm_mul, Real.norm_of_nonneg hK', hp]
    exact mul_le_mul_of_nonneg_right (hWbd _) (norm_nonneg _)
  let u := hi.toLp (Function.uncurry g)
  have hu : ⇑u =ᵐ[ν] Function.uncurry g := hi.coeFn_toLp
  have hN (t : ℝ≥0) (ht : t ≤ H) :
      (fun ω => -affinePreterminalVarianceMartingale H d w M t ω) =ᵐ[μ]
        jointItoIntegralCLM H hB₂ (NativeTimeCut.prior t u) := by
    obtain ⟨r,hr,hNr⟩ := native_weighted_affine_prefix P hB₂ hB hBclock hAgree A
      hM hM₂ (ae_of_all _ hMc) hRep hd hw t ht
    have hne : ∀ᵐ p ∂ν, p.1 ≠ t :=
      FilteredScalarIto.trim_ae_fst_ne (𝓖 := F) (μ := μ) H t
        (B := fun _ _ => (0 : ℝ)) (fun _ => measurable_const)
    have he : NativeTimeCut.prior t u = -r := by
      apply Lp.ext
      filter_upwards [NativeTimeCut.prior_ae t u,hu,hr,hAa',hne,Lp.coeFn_neg r] with
        p hp hg' hr' hA' hn hneg
      change (NativeTimeCut.prior t u) p = (-r) p
      rw [hp, hneg, Pi.neg_apply, hr']
      change (if t < p.1 then 0 else u p) = -(if p.1 < t then W p.1 * A p else 0)
      change u p = -(W p.1 * a p.1 p.2) at hg'
      change A p = a p.1 p.2 at hA'
      rw [hg', hA']
      rcases lt_or_gt_of_ne hn with h | h
      · simp [h, not_lt_of_ge h.le]
      · simp [h, not_lt_of_ge h.le]
    rw [he,map_neg]
    filter_upwards [hNr, Lp.coeFn_neg (jointItoIntegralCLM H hB₂ r)] with ω h₁ h₂
    rw [h₂, Pi.neg_apply, h₁]
  have hA (t : ℝ≥0) (ht : t ≤ H) (ω : Ω) :
      affinePreterminalCompensator T H w b t ω = affineEnergyClock g t ω := by
    rw [affinePreterminalCompensator_eq, min_eq_left ht, affineEnergyClock,
      intervalIntegral.integral_of_le t.coe_nonneg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    have hsH : s.toNNReal ≤ H := NNReal.coe_le_coe.mp
      (by simpa only [Real.coe_toNNReal s hs.1.le] using hs.2.trans (NNReal.coe_le_coe.mpr ht))
    have hW : W s.toNNReal = w ((T : ℝ)-s) := by
      simp only [W, affinePreterminalWeight, min_eq_left hsH, Real.coe_toNNReal s hs.1.le,d]
      congr 1
      ring
    change w ((T : ℝ)-s)^2 * b s.toNNReal ω = (g s.toNNReal ω)^2
    rw [show g s.toNNReal ω = -(W s.toNNReal * a s.toNNReal ω) from rfl, neg_sq, mul_pow, hW]
  have hDnative (t : ℝ≥0) (ht : t ≤ H) : D t =ᵐ[μ]
      NativeExponential.density P scalarHilbertBasis 1 (NativeTimeCut.prior t u) := by
    filter_upwards [hN t ht, affineEnergyClock_prior_eq u hg hu ht] with ω h₁ h₂
    have he := scalarNativeIntegral_eq_joint P.toCoordinates hB₂ hB hBclock hAgree
      (NativeTimeCut.prior t u)
    change Real.exp (-affinePreterminalVarianceMartingale H d w M t ω -
      affinePreterminalCompensator T H w b t ω / 2) =
      Real.exp (1 * FiniteCylindricalIto.rawIntegral P.toCoordinates scalarHilbertBasis (NativeTimeCut.prior t u) ω -
        1^2 * NativeEnergy.energy (NativeTimeCut.prior t u) ω/2)
    rw [he, h₂, hA t ht ω, one_mul, one_pow, one_mul]
    exact congrArg (fun x : ℝ => Real.exp (x - affineEnergyClock g t ω/2)) h₁
  have hD₀ (t : ℝ≥0) (ω : Ω) : 0 ≤ D t ω := (Real.exp_pos _).le
  have hDcl (t : ℝ≥0) : Dc t =ᵐ[μ] D t := by
    filter_upwards [hDbd t] with ω hω
    have hb : D t ω ≤ K := le_trans (le_abs_self _) hω
    exact min_eq_right hb
  have hDcont (ω : Ω) : Continuous (fun t => D t ω) :=
    Real.continuous_exp.comp ((affinePreterminalVarianceMartingale_continuous H hd hw hMc ω).neg.sub
      ((affinePreterminalCompensator_continuous hHT
        (fun x hx => (hw x hx).continuousAt.continuousWithinAt)
        (fun ω => (hac ω).pow 2) ω).div_const 2))
  have hDad : StronglyAdapted F Dc := fun t =>
    ((measurable_const.min (hDmart.stronglyAdapted t).measurable)).stronglyMeasurable
  have hDp : IsStronglyPredictable F Dc := hDad.isStronglyPredictable_of_leftContinuous
    (fun ω t => (continuous_const.min (hDcont ω)).continuousAt.continuousWithinAt)
  have hDCbound (t : ℝ≥0) (ω : Ω) : ‖Dc t ω‖ ≤ K := by
    rw [Real.norm_of_nonneg (le_min hK (hD₀ t ω))]
    exact min_le_left _ _
  have hDcm : Martingale Dc F μ := hDmart.congr hDad (fun t => (hDcl t).symm)
  have hCond (t : ℝ≥0) (ht : t ≤ H) : μ[Dc H | F t] =ᵐ[μ] Dc t :=
    hDcm.condExp_ae_eq ht
  have hDmean : (∫ ω, Dc H ω ∂μ) = 1 := by
    have h := (integral_condExp (F.le 0)).symm.trans
      (integral_congr_ae (hDcm.condExp_ae_eq (show (0 : ℝ≥0) ≤ H from zero_le)))
    rw [h, integral_congr_ae (hDcl 0)]
    have h0 : D 0 = (fun _ => (1 : ℝ)) := by
      funext ω
      simp [D, affinePreterminalDensity, affinePreterminalVarianceMartingale,
        affinePreterminalCompensator_eq]
    rw [h0]
    simp
  obtain ⟨v,hVr,hV⟩ := continuous_bounded_native_exp_joint_representation P hB₂ hB hBclock hAgree
    u hg hgc hu hDp hK hDCbound (fun t ht => (hDcl t).trans (hDnative t ht)) hDmean hCond
  exact ⟨v, hVr, (hDcl H).symm.trans hV⟩

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.affine_preterminal_density_representation
