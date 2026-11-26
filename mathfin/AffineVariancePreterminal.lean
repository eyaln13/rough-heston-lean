import AffineDyadicIntegrationByParts
import AffineStoppedBracket

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal Interval

namespace RoughHeston

theorem weighted_time_primitive_stronglyMeasurable
    {Ω : Type*} {m : MeasurableSpace Ω} {𝒢 : Filtration ℝ≥0 m}
    {X : ℝ≥0 → Ω → ℝ}
    (hX : StronglyAdapted 𝒢 X) (hc : ∀ ω, Continuous fun t => X t ω)
    {d : ℝ → ℝ} (hd : Measurable d) (t : ℝ≥0) :
    StronglyMeasurable[𝒢 t] (fun ω => ∫ s in (0:ℝ)..(t:ℝ), d s*X s.toNNReal ω) := by
  let _ : MeasurableSpace Ω := 𝒢 t
  let F (s : ℝ) (ω : Ω) := X (min s.toNNReal t) ω
  have hF : Measurable (Function.uncurry F) := measurable_uncurry_of_continuous_of_measurable
    (fun ω => (hc ω).comp (continuous_real_toNNReal.min continuous_const))
    (fun s => ((hX (min s.toNNReal t)).mono (𝒢.mono (min_le_right _ _))).measurable)
  have hProd : Measurable (fun p : Ω × ℝ => d p.2*F p.2 p.1) :=
    (hd.comp measurable_snd).mul (hF.comp measurable_swap)
  have hInt := hProd.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (0:ℝ) (t:ℝ)))
  convert hInt using 1
  funext ω
  rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r hr
  have hrt : r.toNNReal ≤ t := NNReal.coe_le_coe.mp
    (by simpa only [Real.coe_toNNReal r hr.1.le] using hr.2)
  dsimp [F]
  rw [min_eq_left hrt]

private theorem affine_martingale_stop_deterministic
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} {X : ℝ≥0 → Ω → ℝ} (hX : Martingale X 𝒢 μ) (H : ℝ≥0) :
    Martingale (fun t => X (min t H)) 𝒢 μ := by
  refine martingale_of_past_set_integrals
    (fun t => (hX.stronglyAdapted (min t H)).mono (𝒢.mono (min_le_left _ _)))
    (fun t => hX.integrable (min t H)) ?_
  intro s t hst A hA
  by_cases hs : s ≤ H
  · simpa only [min_eq_left hs] using (hX.setIntegral_eq (le_min hst hs) hA)
  · rw [min_eq_right (le_of_not_ge hs), min_eq_right ((le_of_not_ge hs).trans hst)]

/-- Pathwise representation of the deterministic Riccati-weighted
variance martingale stopped at a strictly preterminal horizon. -/
noncomputable def affinePreterminalVarianceMartingale {Ω : Type*}
    (H : ℝ≥0) (d : ℝ) (w : ℝ → ℝ) (M : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  w (d+(H:ℝ)-(min t H:ℝ≥0))*M (min t H) ω - w (d+(H:ℝ))*M 0 ω +
    ∫ r in (0:ℝ)..((min t H:ℝ≥0):ℝ),deriv w (d+(H:ℝ)-r)*M r.toNNReal ω

theorem affinePreterminalVarianceMartingale_continuous {Ω : Type*}
    {w : ℝ → ℝ} {d : ℝ} (H : ℝ≥0) (hd : 0 < d)
    (hw : ∀ s > 0, ContDiffAt ℝ 1 w s)
    {M : ℝ≥0 → Ω → ℝ} (hMc : ∀ ω, Continuous fun t => M t ω) (ω : Ω) :
    Continuous (fun t : ℝ≥0 => affinePreterminalVarianceMartingale H d w M t ω) := by
  let N := affinePreterminalVarianceMartingale H d w M
  let W := affinePreterminalWeight w d H
  let f (r : ℝ) := deriv w (d+(H:ℝ)-r)
  have hW : Continuous W := by
    have hWc : ContinuousOn w (Ioi 0) := fun t ht => (hw t ht).continuousAt.continuousWithinAt
    have hg : Continuous (fun t : ℝ≥0 => d+((H:ℝ)-(min t H:ℝ≥0))) :=
      continuous_const.add (continuous_const.sub (NNReal.continuous_coe.comp (continuous_id.min continuous_const)))
    exact hWc.comp_continuous hg (fun t =>
      add_pos_of_pos_of_nonneg hd (sub_nonneg.mpr (NNReal.coe_le_coe.mpr (min_le_right _ _))))
  have hTime : Continuous (fun t : ℝ≥0 => ((min t H:ℝ≥0):ℝ)) :=
    NNReal.continuous_coe.comp (continuous_id.min continuous_const)
  let F (r : ℝ) := deriv w (d+(H:ℝ)-min r (H:ℝ))*M r.toNNReal ω
  have hArg : Continuous (fun r : ℝ => d+(H:ℝ)-min r (H:ℝ)) :=
    continuous_const.sub (continuous_id.min continuous_const)
  have hWc : ContDiffOn ℝ 1 w (Ioi 0) := fun r hr => (hw r hr).contDiffWithinAt
  have hF : Continuous F := ((hWc.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).comp_continuous
    hArg (fun r => by
      change 0 < d+(H:ℝ)-min r (H:ℝ)
      linarith [min_le_right r (H:ℝ)])).mul ((hMc ω).comp continuous_real_toNNReal)
  have hPrim : Continuous (fun t : ℝ≥0 => ∫ r in (0:ℝ)..((min t H:ℝ≥0):ℝ), F r) :=
    (intervalIntegral.continuous_primitive (fun a b => hF.intervalIntegrable a b) 0).comp hTime
  have hIntEq (t : ℝ≥0) : (∫ r in (0:ℝ)..((min t H:ℝ≥0):ℝ),F r) =
      ∫ r in (0:ℝ)..((min t H:ℝ≥0):ℝ), f r*M r.toNNReal ω := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le (NNReal.coe_nonneg _)] at hr
    dsimp [F,f]
    rw [min_eq_left (hr.2.trans (NNReal.coe_le_coe.mpr (min_le_right t H)))]
  have hc : Continuous (fun t : ℝ≥0 => W t*M (min t H) ω-w (d+(H:ℝ))*M 0 ω+
       ∫ r in (0:ℝ)..((min t H:ℝ≥0):ℝ), F r) :=
    ((hW.mul ((hMc ω).comp (continuous_id.min continuous_const))).sub continuous_const).add hPrim
  convert hc using 1
  funext t
  rw [hIntEq t]
  have he : d+(H:ℝ)-(min t H:ℝ≥0) = d+((H:ℝ)-(min t H:ℝ≥0)) := by ring
  simp only [affinePreterminalVarianceMartingale,W,affinePreterminalWeight,he,f]

/-- The actual preterminal Riccati-weighted variance martingale, its
ordinary compensated square, and its stochastic exponential in the
ambient filtration. The original bracket rate may be unbounded. -/
theorem affine_preterminal_variance_exponential
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} {M C b : ℝ≥0 → Ω → ℝ}
    {w : ℝ → ℝ} {d : ℝ} (hd : 0 < d) (H : ℝ≥0)
    (hw : ∀ s > 0, ContDiffAt ℝ 1 w s)
    (hM : Martingale M 𝒢 μ) (hM₂ : ∀ t, MemLp (M t) 2 μ)
    (hMc : ∀ ω, Continuous fun t => M t ω)
    (hMC : Martingale (fun t => M t*M t-C t) 𝒢 μ)
    (hCi : ∀ t, Integrable (C t) μ)
    (hCmon : ∀ s t, s ≤ t → C s ≤ᵐ[μ] C t)
    (hC : ∀ t ≤ H, C t =ᵐ[μ] fun ω => ∫ r in (0:ℝ)..(t:ℝ), b r.toNNReal ω)
    (hbad : StronglyAdapted 𝒢 b) (hbc : ∀ ω, Continuous fun t => b t ω)
    (hb₀ : ∀ t ω, 0 ≤ b t ω) {L : ℝ} (hbStart : ∀ ω, b 0 ω ≤ L) :
    let N := affinePreterminalVarianceMartingale H d w M
    let B (t : ℝ≥0) (ω : Ω) := (affinePreterminalWeight w d H t)^2*b t ω
    let V := affineStoppedBracket H B
    Martingale N 𝒢 μ ∧ Martingale (fun t ω => N t ω^2-V t ω) 𝒢 μ ∧
      IsLocalMartingale (fun t ω => Real.exp (-N t ω-V t ω/2)) 𝒢 μ := by
  dsimp only
  let N := affinePreterminalVarianceMartingale H d w M
  let W := affinePreterminalWeight w d H
  let B (t : ℝ≥0) (ω : Ω) := (W t)^2*b t ω
  let V := affineStoppedBracket H B
  have hW : Continuous W := by
    have hWc : ContinuousOn w (Ioi 0) := fun t ht => (hw t ht).continuousAt.continuousWithinAt
    have hg : Continuous (fun t : ℝ≥0 => d+((H:ℝ)-(min t H:ℝ≥0))) :=
      continuous_const.add (continuous_const.sub (NNReal.continuous_coe.comp (continuous_id.min continuous_const)))
    exact hWc.comp_continuous hg (fun t =>
      add_pos_of_pos_of_nonneg hd (sub_nonneg.mpr (NNReal.coe_le_coe.mpr (min_le_right _ _))))
  have hbRealC (ω : Ω) : Continuous (fun r : ℝ => b r.toNNReal ω) :=
    (hbc ω).comp continuous_real_toNNReal
  have hD : ∀ᵐ ω ∂μ, IntervalIntegrable (fun r : ℝ => b r.toNNReal ω) volume (0:ℝ) H :=
    ae_of_all _ fun ω => (hbRealC ω).intervalIntegrable 0 H
  have hWB (ω : Ω) : Continuous (fun t => B t ω) := (hW.pow 2).mul (hbc ω)
  have hWBReal (ω : Ω) : Continuous (fun r : ℝ => B r.toNNReal ω) :=
    (hWB ω).comp continuous_real_toNNReal
  have hWD : ∀ᵐ ω ∂μ, IntervalIntegrable (fun r : ℝ => B r.toNNReal ω) volume (0:ℝ) H :=
    ae_of_all _ fun ω => (hWBReal ω).intervalIntegrable 0 H
  have hDi : Integrable (fun ω => ∫ r in (0:ℝ)..(H:ℝ), |b r.toNNReal ω|) μ := by
    refine (hCi H).congr ?_
    filter_upwards [hC H le_rfl] with ω hω
    rw [hω]
    apply intervalIntegral.integral_congr
    intro r _
    exact (abs_of_nonneg (hb₀ _ _)).symm
  obtain ⟨J,A,hJ,hJ₂,hJc,hJconv,hA,hComp⟩ :=
    exists_affine_preterminal_weighted_martingale hd H
      (fun t ht => (hw t ht).continuousAt.continuousWithinAt)
      hM hM₂ (ae_of_all _ hMc) hMC hCi hCmon hC hD hWD hDi
  let f (r : ℝ) := deriv w (d+(H:ℝ)-r)
  have hf : Measurable f := (measurable_deriv w).comp (measurable_const.sub measurable_id)
  have hNad : StronglyAdapted 𝒢 N := by
    intro t
    have hMt := (hM.stronglyAdapted (min t H)).mono (𝒢.mono (min_le_left _ _))
    have hM0 := (hM.stronglyAdapted 0).mono (𝒢.mono (show 0 ≤ t from zero_le))
    have hF := (weighted_time_primitive_stronglyMeasurable hM.stronglyAdapted hMc hf (min t H)).mono
      (𝒢.mono (min_le_left _ _))
    exact ((hMt.const_mul (w (d+(H:ℝ)-(min t H:ℝ≥0)))).sub
      (hM0.const_mul (w (d+(H:ℝ))))).add hF
  have hBad : StronglyAdapted 𝒢 B := fun t => (hbad t).const_mul ((W t)^2)
  have hVad : StronglyAdapted 𝒢 V := by
    intro t
    have h := weighted_time_primitive_stronglyMeasurable hBad hWB
      (d := fun _ => (1:ℝ)) measurable_const (min t H)
    have h' : StronglyMeasurable[𝒢 (min t H)] (V t) := by
      change StronglyMeasurable[𝒢 (min t H)]
        (fun ω => ∫ r in (0:ℝ)..((min t H:ℝ≥0):ℝ), B r.toNNReal ω)
      simpa only [one_mul] using h
    exact h'.mono (𝒢.mono (min_le_left _ _))
  have hPart (t : ℝ≥0) : J (min t H) =ᵐ[μ] N t :=
    affine_weighted_integral_eq_by_parts hd (min_le_right _ _) hw hM hM₂
      (ae_of_all _ hMc) (hJconv (min t H) (min_le_right _ _))
  have hNM : Martingale N 𝒢 μ :=
    (affine_martingale_stop_deterministic hJ H).congr hNad hPart
  have hCompN : Martingale (fun t ω => N t ω^2-V t ω) 𝒢 μ := by
    refine hComp.congr (fun t => ((hNad t).pow 2).sub (hVad t)) ?_
    intro t
    filter_upwards [hPart t,hA t] with ω hj ha
    change J (min t H) ω*J (min t H) ω-A t ω = N t ω^2-V t ω
    rw [hj,ha,pow_two]
    rfl
  have hTime : Continuous (fun t : ℝ≥0 => ((min t H:ℝ≥0):ℝ)) :=
    NNReal.continuous_coe.comp (continuous_id.min continuous_const)
  have hNcts (ω : Ω) : Continuous (fun t => N t ω) :=
    affinePreterminalVarianceMartingale_continuous H hd hw hMc ω
  have hVcts (ω : Ω) : Continuous (fun t => V t ω) :=
    (intervalIntegral.continuous_primitive (fun a b => (hWBReal ω).intervalIntegrable a b) 0).comp hTime
  have hN₀ (ω : Ω) : N 0 ω = 0 := by
    simp [N,affinePreterminalVarianceMartingale]
  refine ⟨hNM,hCompN,?_⟩
  exact affine_exp_isLocalMartingale_of_stopped_bracket H hNad hVad hBad hNcts hWB
    (Locally.of_prop ⟨hNM,fun ω => (hNcts ω).isCadlag⟩)
    (Locally.of_prop ⟨hCompN,fun ω => (((hNcts ω).pow 2).sub (hVcts ω)).isCadlag⟩)
    (fun t ω => mul_nonneg (sq_nonneg _) (hb₀ t ω)) (K := (W 0)^2*L)
    (fun ω => by
      change |N 0 ω|+(W 0)^2*b 0 ω ≤ (W 0)^2*L
      rw [hN₀,abs_zero,zero_add]
      exact mul_le_mul_of_nonneg_left (hbStart ω) (sq_nonneg _))

#print axioms affine_preterminal_variance_exponential

end RoughHeston
