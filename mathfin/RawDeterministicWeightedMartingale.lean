import SmoothKernelStochasticCompensator
import CommonDriverLimit

/-! Continuous versions of deterministically weighted martingales on
the original filtration, with explicit bracket paths. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

set_option maxHeartbeats 900000

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω}
  {F : Filtration ℝ≥0 m}

/-- Integrating a continuous adapted process against a deterministic
continuous time weight gives an adapted process on the original filtration. -/
theorem stronglyAdapted_weighted_intervalIntegral
    {X : ℝ≥0 → Ω → ℝ} (hX : StronglyAdapted F X)
    (hXc : ∀ ω, Continuous (fun t => X t ω)) {g : ℝ → ℝ} (hg : Continuous g) :
    StronglyAdapted F (fun t ω => ∫ r in (0 : ℝ)..(t : ℝ), g r * X r.toNNReal ω) := by
  intro t
  let I (r : ℝ) (ω : Ω) := g r * X (min r.toNNReal t) ω
  have hIc (ω : Ω) : Continuous (fun r => I r ω) :=
    hg.mul ((hXc ω).comp (continuous_real_toNNReal.min continuous_const))
  let : MeasurableSpace Ω := F t
  have hIm (r : ℝ) : Measurable (I r) :=
    (stronglyMeasurable_const.mul ((hX (min r.toNNReal t)).mono (F.mono (min_le_right _ _)))).measurable
  have hm := (measurable_uncurry_of_continuous_of_measurable hIc hIm).stronglyMeasurable
  have h := hm.integral_prod_left' (μ := volume.restrict (Ioc (0 : ℝ) (t : ℝ)))
  have he : (fun ω => ∫ r in Ioc (0 : ℝ) (t : ℝ), I r ω) =
      (fun ω => ∫ r in (0 : ℝ)..(t : ℝ), g r * X r.toNNReal ω) := by
    funext ω
    rw [intervalIntegral.integral_of_le t.coe_nonneg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    have ht : r.toNNReal ≤ t := NNReal.coe_le_coe.mp
      ((Real.coe_toNNReal r hr.1.le).trans_le hr.2)
    simp [I, min_eq_left ht]
  change StronglyMeasurable (fun ω => ∫ r in Ioc (0 : ℝ) (t : ℝ), I r ω) at h
  rw [he] at h
  exact h

private theorem stronglyAdapted_freeze {X : ℝ≥0 → Ω → ℝ} (hX : StronglyAdapted F X) (H : ℝ≥0) :
    StronglyAdapted F (fun t => X (min t H)) :=
  fun t => (hX _).mono (F.mono (min_le_left _ _))

/-- Construct a continuous all-paths version of the weighted integral,
and identify its actual nondecreasing bracket on the original filtration. -/
theorem exists_raw_deterministic_weighted_martingale [IsProbabilityMeasure μ]
    (H : ℝ≥0) {M C D : ℝ≥0 → Ω → ℝ} {g d : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g) (hd : Continuous d) (hgd : ∀ s, HasDerivAt g (d s) s)
    (hM : Martingale M F μ) (hM₂ : ∀ t, MemLp (M t) 2 μ)
    (hMc : ∀ ω, Continuous (fun t => M t ω))
    (hMC : Martingale (fun t => M t * M t - C t) F μ)
    (hCi : ∀ t, Integrable (C t) μ) (hCmon : ∀ s t, s ≤ t → C s ≤ᵐ[μ] C t)
    (hC : ∀ t ≤ H, C t =ᵐ[μ] fun ω => ∫ r in (0 : ℝ)..(t : ℝ), D r.toNNReal ω)
    (hDa : StronglyAdapted F D) (hDc : ∀ ω, Continuous (fun t => D t ω))
    (hD₀ : ∀ t ω, 0 ≤ D t ω) :
    let Y (t : ℝ≥0) (ω : Ω) :=
      g (min t H : ℝ≥0) * M (min t H) ω - g 0 * M 0 ω -
        ∫ r in (0 : ℝ)..((min t H : ℝ≥0):ℝ), d r * M r.toNNReal ω
    let A (t : ℝ≥0) (ω : Ω) :=
      ∫ r in (0 : ℝ)..((min t H : ℝ≥0):ℝ), (g r)^2 * D r.toNNReal ω
    Martingale Y F μ ∧ (∀ t, MemLp (Y t) 2 μ) ∧
      (∀ ω, Continuous (fun t => Y t ω)) ∧ (∀ ω, Continuous (fun t => A t ω)) ∧
      (∀ ω, Monotone (fun t => A t ω)) ∧ (∀ ω, Y 0 ω = 0) ∧ (∀ ω, A 0 ω = 0) ∧
      Martingale (fun t => Y t * Y t - A t) F μ := by
  dsimp only
  let Y (t : ℝ≥0) (ω : Ω) :=
    g (min t H : ℝ≥0) * M (min t H) ω - g 0 * M 0 ω -
      ∫ r in (0 : ℝ)..((min t H : ℝ≥0):ℝ), d r * M r.toNNReal ω
  let A (t : ℝ≥0) (ω : Ω) :=
    ∫ r in (0 : ℝ)..((min t H : ℝ≥0):ℝ), (g r)^2 * D r.toNNReal ω
  let w (r : ℝ) := g (1+(H:ℝ)-r)
  have hw : ContDiff ℝ 1 w :=
    hg.comp (contDiff_const.sub contDiff_id)
  have hW (s : ℝ≥0) : affinePreterminalWeight w 1 H s = g (min s H : ℝ≥0) := by
    unfold affinePreterminalWeight w
    congr 1
    ring
  have hDcR (ω : Ω) : Continuous (fun r : ℝ => D r.toNNReal ω) :=
    (hDc ω).comp continuous_real_toNNReal
  have hWDc (ω : Ω) : Continuous (fun r : ℝ => (affinePreterminalWeight w 1 H r.toNNReal)^2 * D r.toNNReal ω) := by
    simp_rw [hW]
    exact ((hg.continuous.comp (NNReal.continuous_coe.comp
      (continuous_real_toNNReal.min continuous_const))).pow 2).mul (hDcR ω)
  have hDi : Integrable (fun ω => ∫ r in (0 : ℝ)..(H : ℝ), |D r.toNNReal ω|) μ := by
    refine (hCi H).congr ?_
    filter_upwards [hC H le_rfl] with ω hω
    rw [hω]
    simp only [abs_of_nonneg (hD₀ _ _)]
  obtain ⟨J, B, hJ, hJ₂, _, hJlim, hB, hJB⟩ :=
    exists_affine_preterminal_weighted_martingale (w := w) (d := (1:ℝ)) (by norm_num) H
      hw.continuous.continuousOn hM hM₂ (Eventually.of_forall hMc) hMC hCi hCmon hC
      (Eventually.of_forall fun ω => (hDcR ω).intervalIntegrable _ _)
      (Eventually.of_forall fun ω => (hWDc ω).intervalIntegrable _ _) hDi
  have hder (r : ℝ) : deriv w r = -d (1+(H:ℝ)-r) := by
    have h := (hgd (1+(H:ℝ)-r)).comp r ((hasDerivAt_id r).const_sub (1+(H:ℝ)))
    change HasDerivAt w (d (1+(H:ℝ)-r)*(-1)) r at h
    simpa only [mul_neg, mul_one] using h.deriv
  have hEqY (t : ℝ≥0) : J (min t H) =ᵐ[μ] Y t := by
    let u := min t H
    have hu : u ≤ H := min_le_right _ _
    refine (affine_weighted_integral_eq_by_parts (d := (1:ℝ)) (w := w) (by norm_num) hu
      (fun _ _ => hw.contDiffAt) hM hM₂ (Eventually.of_forall hMc) (hJlim u hu)).mono ?_
    intro ω hω
    rw [hω]
    have h1 : w (1+(H:ℝ)-(u:ℝ)) = g u := by unfold w; congr 1; ring
    have h0 : w (1+(H:ℝ)) = g 0 := by unfold w; congr 1; ring
    have h2 (r : ℝ) : deriv w (1+(H:ℝ)-r) = -d r := by rw [hder]; congr 2; ring
    simp only [Y, u, h1, h0, h2, neg_mul, intervalIntegral.integral_neg]
    ring
  have hEqA (t : ℝ≥0) : B t =ᵐ[μ] A t := by
    filter_upwards [hB t] with ω hω
    rw [hω]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le (NNReal.coe_nonneg (min t H))] at hr
    have hrH : r.toNNReal ≤ H := NNReal.coe_le_coe.mp
      ((Real.coe_toNNReal r hr.1).trans_le (hr.2.trans (NNReal.coe_le_coe.mpr (min_le_right _ _))))
    simp only [hW, min_eq_left hrH, Real.coe_toNNReal r hr.1]
  have hYa : StronglyAdapted F Y := by
    intro t
    let u := min t H
    have ha : StronglyMeasurable[F t] (fun ω => g (u : ℝ) * M u ω) :=
      stronglyMeasurable_const.mul ((hM.stronglyAdapted u).mono (F.mono (min_le_left _ _)))
    have hb : StronglyMeasurable[F t] (fun ω => g 0 * M 0 ω) :=
      stronglyMeasurable_const.mul ((hM.stronglyAdapted 0).mono (F.mono zero_le))
    have he : StronglyMeasurable[F t] (fun ω =>
        ∫ r in (0 : ℝ)..(u : ℝ), d r * M r.toNNReal ω) :=
      stronglyAdapted_freeze (stronglyAdapted_weighted_intervalIntegral hM.stronglyAdapted hMc hd) H t
    exact (ha.sub hb).sub he
  have hAa : StronglyAdapted F A :=
    stronglyAdapted_freeze (stronglyAdapted_weighted_intervalIntegral hDa hDc (hg.continuous.pow 2)) H
  have hY : Martingale Y F μ := (martingale_freeze_at hJ H).congr hYa hEqY
  have hAY : Martingale (fun t => Y t * Y t - A t) F μ :=
    hJB.congr (fun t => ((hYa t).mul (hYa t)).sub (hAa t))
      (fun t => ((hEqY t).mul (hEqY t)).sub (hEqA t))
  have hCont (f : ℝ → ℝ) (hf : Continuous f) :
      Continuous (fun t : ℝ≥0 => ∫ r in (0 : ℝ)..((min t H : ℝ≥0):ℝ), f r) :=
    (intervalIntegral.differentiable_integral_of_continuous (a := 0) hf).continuous.comp
      (NNReal.continuous_coe.comp (continuous_id.min continuous_const))
  have hAc (ω : Ω) : Continuous (fun t => A t ω) :=
    hCont _ ((hg.continuous.pow 2).mul (hDcR ω))
  have hYc (ω : Ω) : Continuous (fun t => Y t ω) :=
    (((hg.continuous.comp (NNReal.continuous_coe.comp (continuous_id.min continuous_const))).mul
      ((hMc ω).comp (continuous_id.min continuous_const))).sub continuous_const).sub
      (hCont _ (hd.mul ((hMc ω).comp continuous_real_toNNReal)))
  have hAmono (ω : Ω) : Monotone (fun t => A t ω) := by
    intro s t hst
    dsimp [A]
    simp_rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg _)]
    exact setIntegral_mono_set (((hg.continuous.pow 2).mul (hDcR ω)).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (Eventually.of_forall fun r => mul_nonneg (sq_nonneg _) (hD₀ _ _))
      (Ioc_subset_Ioc_right (NNReal.coe_le_coe.mpr (min_le_min_right H hst))).eventuallyLE
  exact ⟨hY, fun t => (hJ₂ _).ae_eq (hEqY t), hYc, hAc, hAmono,
    fun ω => by simp [Y], fun ω => by simp [A], hAY⟩

#print axioms RoughHeston.stronglyAdapted_weighted_intervalIntegral
#print axioms RoughHeston.exists_raw_deterministic_weighted_martingale

end RoughHeston
