import BridgeScalarNative
import AffineVariancePreterminal
import SHEStochastic.StochasticRiemannSums
import SHEStochastic.FiniteCylindricalLocality
import SHE.StoppedInputAlgebra

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston.GirsanovPort

open SHEStochastic SHE SHE.PredictableL2

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} {H : ℝ≥0} {B M : ℝ≥0 → Ω → ℝ}

local notation "ν" => jointPredictableMeasure F μ H

private theorem uniformDyadicGrid_eq_unifPart (H : ℝ≥0) (n k : ℕ) :
    MathFin.unifPart H (2^n) k = (uniformDyadicGrids H).grid n k := by
  change (k : ℝ≥0) / ((2^n : ℕ) : ℝ≥0) * H = (k : ℝ≥0) * H / (2^n : ℝ≥0)
  rw [Nat.cast_pow, Nat.cast_ofNat, div_mul_eq_mul_div]

set_option maxHeartbeats 1100000 in
/-- The affine weighted preterminal martingale is the exact joint
Itô integral of its weighted predictable amplitude, from ordinary
native Riemann sums and pathwise integration by parts. -/
theorem native_weighted_affine_prefix
    (P : FiniteScalarIto.Family F μ H Unit)
    (hB₂ : ∀ s, MemLp (B s) 2 μ) (hB : Martingale B F μ)
    (hClock : Martingale (fun s ω => B s ω ^ 2 - ((min s H : ℝ≥0) : ℝ)) F μ)
    (hAgree : ∀ s ≤ H, P.W () s =ᵐ[μ] B s)
    (A : Process (E := ℝ) F μ H)
    (hM : Martingale M F μ) (hM₂ : ∀ s, MemLp (M s) 2 μ)
    (hMc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hRep : ∀ t ≤ H, M t =ᵐ[μ] ⇑((FiniteCylindricalIto.terminalIto P.toCoordinates scalarHilbertBasis).integral
      (StoppedItoInputs.stop F μ H t A)))
    {w : ℝ → ℝ} {d : ℝ} (hd : 0 < d)
    (hw : ∀ s > 0, ContDiffAt ℝ 1 w s) (t : ℝ≥0) (ht : t ≤ H) :
    ∃ r : Lp ℝ 2 ν,
      (⇑r =ᵐ[ν] fun p => if p.1 < t then affinePreterminalWeight w d H p.1 * A p else 0) ∧
      affinePreterminalVarianceMartingale H d w M t =ᵐ[μ] jointItoIntegralCLM H hB₂ r := by
  let e := scalarHilbertBasis
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  let U := StoppedItoInputs.stop F μ H t A
  let W := affinePreterminalWeight w d H
  let G (s : ℝ≥0) (_ : Ω) := W s
  have hpre : ContinuousOn w (Icc d (d+(H:ℝ))) := fun s hs =>
    (hw s (hd.trans_le hs.1)).continuousAt.continuousWithinAt
  have hdom (s : ℝ≥0) : d+((H:ℝ)-(min s H:ℝ≥0)) ∈ Icc d (d+(H:ℝ)) :=
    ⟨le_add_of_nonneg_right (sub_nonneg.mpr (NNReal.coe_le_coe.mpr (min_le_right _ _))),
      by linarith [NNReal.coe_nonneg (min s H)]⟩
  have hW : Continuous W :=
    hpre.comp_continuous
      (continuous_const.add (continuous_const.sub (NNReal.continuous_coe.comp
        (continuous_id.min continuous_const)))) hdom
  obtain ⟨C,hC⟩ := isCompact_Icc.bddAbove_image hpre.norm
  let K := max C 0
  have hK : 0 ≤ K := le_max_right _ _
  have hWbd (s : ℝ≥0) : |W s| ≤ K :=
    (show ‖W s‖ ≤ C from hC ⟨_, hdom s, rfl⟩).trans (le_max_left _ _)
  have hG : StronglyMeasurable[F.predictable] (Function.uncurry G) :=
    (hW.measurable.comp (SHE.PredictableClock.time_measurable F)).stronglyMeasurable
  let V := PredictableMultiplier.process U (Function.uncurry G) hG K (fun p => hWbd p.1)
  let r : Lp ℝ 2 ν := FiniteCylindricalIto.processTransport V
  have hVt := PredictableMultiplier.process_ae U (Function.uncurry G) hG K (fun p => hWbd p.1)
  have hν : ν = (energyMeasure μ H).trim (predictable_le_product F) :=
    (FilteredScalarIto.processMeasure_eq (𝓖 := F) (μ := μ) H
      (B := fun _ _ => (0 : ℝ)) (fun _ => measurable_const)).symm
  have hV₀ : ⇑V =ᵐ[ν] fun p => if p.1 < t then W p.1 * A p else 0 := by
    have h1 : ⇑V =ᵐ[ν] fun p => W p.1 * U p := by
      rw [hν]
      apply ae_eq_trim_of_measurable (predictable_le_product F)
      · exact (Lp.stronglyMeasurable V).measurable
      · exact (hG.mul (Lp.stronglyMeasurable U)).measurable
      · exact hVt
    have h2 : ⇑U =ᵐ[ν] (StoppedItoInputs.before (Ω := Ω) t).indicator A := by
      rw [hν]
      exact ((Lp.memLp A).indicator (StoppedItoInputs.before_measurable F t).nullMeasurableSet).coeFn_toLp
    filter_upwards [h1,h2] with p hp hq
    rw [hp, hq]
    by_cases h : p.1 < t
    · rw [ite_eq_left h, indicator_of_mem]
      exact_mod_cast h
    · rw [ite_eq_right h, indicator_of_notMem, mul_zero]
      exact_mod_cast h
  refine ⟨r, (FiniteCylindricalIto.processTransport_ae V).trans hV₀, ?_⟩
  have hL := StochasticRiemannSums.tendstoInMeasure J (FiniteCylindricalIto.pastLocality P e)
    U G (fun _ => stronglyMeasurable_const) hG (ae_of_all _ fun _ => hW.continuousOn)
    K hK (fun s _ => hWbd s)
  let f (n : ℕ) := gridIntegralProcess ((uniformDyadicGrids H).grid n)
    (fun k (_ : Ω) => W ((uniformDyadicGrids H).grid n k)) M (2^n) t
  have hsum (n : ℕ) : StochasticRiemannSums.sum J U G (2^n) =ᵐ[μ] f n := by
    have hStep (k : ℕ) :
        ⇑(J.integral (StoppedItoInputs.stop F μ H (MathFin.unifPart H (2^n) k) U)) =ᵐ[μ]
          M (min t ((uniformDyadicGrids H).grid n k)) := by
      rw [uniformDyadicGrid_eq_unifPart]
      let q := (uniformDyadicGrids H).grid n k
      change ⇑(J.integral (StoppedItoInputs.stop F μ H (q : ℝ) U)) =ᵐ[μ] M (min t q)
      have he : StoppedItoInputs.stop F μ H (q : ℝ) U =
          StoppedItoInputs.stop F μ H ((min t q : ℝ≥0) : ℝ) A := by
        dsimp only [U]
        rw [StoppedInputAlgebra.stop_stop, NNReal.coe_min, min_comm]
      rw [he]
      exact (hRep (min t q) ((min_le_left _ _).trans ht)).symm
    filter_upwards [ae_all_iff.mpr hStep] with ω hω
    let S (k : ℕ) := G (MathFin.unifPart H (2^n) k) ω *
      (J.integral (StoppedItoInputs.stop F μ H (MathFin.unifPart H (2^n) (k+1)) U) ω -
        J.integral (StoppedItoInputs.stop F μ H (MathFin.unifPart H (2^n) k) U) ω)
    change (∑ k : Fin (2^n), S (k : ℕ)) = _
    rw [Fin.sum_univ_eq_sum_range S]
    unfold f gridIntegralProcess
    simp only [S, Finset.sum_apply, stochasticStep, Pi.mul_apply, Pi.sub_apply]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hω k,hω (k+1)]
    simp only [G, uniformDyadicGrid_eq_unifPart]
  have htend := TendstoInMeasure.congr_left hsum
    (hL.comp (tendsto_pow_atTop_atTop_of_one_lt (by decide : (1 : ℕ) < 2)))
  have hFa (n : ℕ) : AEStronglyMeasurable (f n) μ :=
    ((gridIntegralProcess_martingale ((uniformDyadicGrids H).grid n) hM hM₂
      (fun _ => stronglyMeasurable_const) (fun _ => memLp_const _) (2^n)).integrable t).aestronglyMeasurable
  have hPath : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop
      (𝓝 (affinePreterminalVarianceMartingale H d w M t ω)) := by
    let gp (r : ℝ) := w (d+(H:ℝ)-r)
    let p (r : ℝ) := -deriv w (d+(H:ℝ)-r)
    have hpm : Measurable p := ((measurable_deriv w).comp (measurable_const.sub measurable_id)).neg
    have hPos (r : ℝ) (hr : r ∈ Icc 0 (t:ℝ)) : 0 < d+(H:ℝ)-r := by
      have hh := NNReal.coe_le_coe.mpr ht
      linarith [hr.2]
    have hpc : ContinuousOn p (Icc 0 (t:ℝ)) := by
      have hWc : ContDiffOn ℝ 1 w (Ioi 0) := fun s hs => (hw s hs).contDiffWithinAt
      exact ((hWc.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).comp
        (continuous_const.sub continuous_id).continuousOn hPos).neg
    have hDer (r : ℝ) (hr : r ∈ Icc 0 (t:ℝ)) : HasDerivAt gp (p r) r := by
      have hh := ((hw _ (hPos r hr)).differentiableAt one_ne_zero).hasDerivAt
      have he := hh.comp r ((hasDerivAt_id r).const_sub (d+(H:ℝ)))
      change HasDerivAt gp (deriv w (d+(H:ℝ)-r)* -1) r at he
      simpa only [p,mul_neg,mul_one] using he
    filter_upwards [hMc] with ω hω
    have hh := tendsto_affine_dyadic_integration_by_parts (X := fun s => M s ω) ht hω hpm hpc hDer
    have he : gp t * M t ω - gp 0 * M 0 ω - ∫ y in (0:ℝ)..(t:ℝ), p y * M y.toNNReal ω =
      affinePreterminalVarianceMartingale H d w M t ω := by
      simp only [gp, p, affinePreterminalVarianceMartingale, min_eq_left ht, sub_zero,
        neg_mul, intervalIntegral.integral_neg, sub_neg_eq_add]
    rw [he] at hh
    apply hh.congr
    intro n
    simp only [f, gridIntegralProcess, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro k hk
    have hkH : (uniformDyadicGrids H).grid n k ≤ H :=
      (((uniformDyadicGrids H).grid n).monotone (Finset.mem_range.mp hk).le).trans_eq
        (uniform_dyadic_terminal_vertex H n)
    have hEq : W ((uniformDyadicGrids H).grid n k) = gp ((uniformDyadicGrids H).grid n k) := by
      simp only [W, affinePreterminalWeight, gp, min_eq_left hkH]
      congr 1
      ring
    rw [hEq]
    rfl
  have hrEq : J.integral V = jointItoIntegralCLM H hB₂ r :=
    scalarNativeIntegral_eq_joint P.toCoordinates hB₂ hB hClock hAgree r
  exact (tendstoInMeasure_ae_unique htend (tendstoInMeasure_of_tendsto_ae hFa hPath)).symm.trans
    (congrArg (fun z : Lp ℝ 2 μ => (z : Ω → ℝ)) hrEq).eventuallyEq

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.native_weighted_affine_prefix
