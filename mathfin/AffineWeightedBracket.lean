import StochasticCovariation

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal Interval

namespace RoughHeston

/-- The backward Riccati weight, clamped at a strictly preterminal
time to keep it bounded and continuous. -/
noncomputable def affinePreterminalWeight (w : ℝ → ℝ) (d : ℝ) (H t : ℝ≥0) : ℝ :=
  w (d+((H:ℝ)-(min t H:ℝ≥0)))

/-- The actual dyadic stochastic integral of a preterminal Riccati
weight has the ordinary weighted square compensator. This construction
uses the given variance martingale and its compensator directly. -/
theorem exists_affine_preterminal_weighted_martingale
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} {M C : ℝ≥0 → Ω → ℝ} {D : ℝ → Ω → ℝ}
    {w : ℝ → ℝ} {d : ℝ} (hd : 0 < d) (H : ℝ≥0)
    (hw : ContinuousOn w (Ioi 0))
    (hM : Martingale M 𝒢 μ) (hM₂ : ∀ t, MemLp (M t) 2 μ)
    (hMc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hMC : Martingale (fun t => M t * M t-C t) 𝒢 μ)
    (hCi : ∀ t, Integrable (C t) μ) (hCmon : ∀ s t, s ≤ t → C s ≤ᵐ[μ] C t)
    (hC : ∀ t ≤ H, C t =ᵐ[μ] fun ω => ∫ r in (0:ℝ)..(t:ℝ), D r ω)
    (hD : ∀ᵐ ω ∂μ, IntervalIntegrable (fun r => D r ω) volume (0:ℝ) H)
    (hWD : ∀ᵐ ω ∂μ, IntervalIntegrable
      (fun r => (affinePreterminalWeight w d H r.toNNReal)^2*D r ω) volume (0:ℝ) H)
    (hDi : Integrable (fun ω => ∫ r in (0:ℝ)..(H:ℝ), |D r ω|) μ) :
    let W := affinePreterminalWeight w d H
    let P := uniformDyadicGrids H
    let Jn := fun n => gridIntegralProcess (P.grid n) (fun k _ => W (P.grid n k)) M (2^n)
    ∃ J B : ℝ≥0 → Ω → ℝ,
      Martingale J 𝒢 μ ∧ (∀ t, MemLp (J t) 2 μ) ∧
      (∀ᵐ ω ∂μ, ContinuousOn (fun t => J t ω) (Iic H)) ∧
      (∀ t ≤ H, Tendsto (fun n => eLpNorm (Jn n t-J t) 2 μ) atTop (𝓝 0)) ∧
      (∀ t, B t =ᵐ[μ] fun ω => ∫ r in (0:ℝ)..((min t H:ℝ≥0):ℝ), (W r.toNNReal)^2*D r ω) ∧
      Martingale (fun t => J (min t H)*J (min t H)-B t) 𝒢 μ := by
  dsimp only
  let W := affinePreterminalWeight w d H
  let g (t : ℝ≥0) := d+((H:ℝ)-(min t H:ℝ≥0))
  have hg : Continuous g :=
    continuous_const.add (continuous_const.sub (NNReal.continuous_coe.comp (continuous_id.min continuous_const)))
  have hgr (t : ℝ≥0) : g t ∈ Icc d (d+(H:ℝ)) := by
    dsimp [g]
    exact ⟨le_add_of_nonneg_right (sub_nonneg.mpr (NNReal.coe_le_coe.mpr (min_le_right t H))),
      add_le_add (le_refl d) (sub_le_self _ (NNReal.coe_nonneg _))⟩
  have hW : Continuous W := hw.comp_continuous hg (fun t => hd.trans_le (hgr t).1)
  have hwc : ContinuousOn w (Icc d (d+(H:ℝ))) :=
    hw.mono (fun _ hs => hd.trans_le hs.1)
  obtain ⟨F,hF⟩ := isCompact_Icc.bddAbove_image hwc.norm
  let L := max F 0
  have hL : 0 ≤ L := le_max_right _ _
  have hAbs (t : ℝ≥0) : |W t| ≤ L := by
    have he := hF ⟨g t,hgr t,rfl⟩
    have he' : |W t| ≤ F := by simpa only [W,affinePreterminalWeight,g,Real.norm_eq_abs] using he
    exact he'.trans (le_max_left _ _)
  let K (t : ℝ≥0) (_ : Ω) := W t
  have hK : StronglyAdapted 𝒢 K := fun _ => stronglyMeasurable_const
  have hKtop (t : ℝ≥0) : MemLp (K t) ⊤ μ := memLp_const _
  have hKc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => K t ω) (Icc 0 H) :=
    ae_of_all _ fun _ => hW.continuousOn
  have hKB : ∀ᵐ ω ∂μ, ∀ t ≤ H, |K t ω| ≤ L := ae_of_all _ fun _ t _ => hAbs t
  obtain ⟨J,hJ,hJ₂,hJc,hJconv,_⟩ := exists_continuous_integral_of_bounded_continuous_paths
    H hL hM hM₂ hMc hMC hCi hCmon hK hKtop hKc hKB
  have hKKc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => K t ω*K t ω) (Icc 0 H) :=
    ae_of_all _ fun _ => (hW.mul hW).continuousOn
  have hKKB : ∀ᵐ ω ∂μ, ∀ t ≤ H, |K t ω*K t ω| ≤ L^2 := by
    refine ae_of_all _ fun ω t _ => ?_
    rw [abs_mul,pow_two]
    exact mul_le_mul (hAbs t) (hAbs t) (abs_nonneg _) hL
  have hWD' : ∀ᵐ ω ∂μ, IntervalIntegrable
      (fun r => K r.toNNReal ω*K r.toNNReal ω*D r ω) volume (0:ℝ) H := by
    simpa only [K,W,pow_two] using hWD
  obtain ⟨B,hB,hJcomp⟩ := continuous_integrals_compensated_product H (sq_nonneg L)
    hM hM hMC hM₂ hM₂ hK hK hKtop hKtop hJ.stronglyAdapted hJ.stronglyAdapted hJ₂ hJ₂
    hC hKKc hKKB hD hWD' hDi hJconv hJconv
  exact ⟨J,B,hJ,hJ₂,hJc,hJconv,(by simpa only [K,W,pow_two] using hB),hJcomp⟩

#print axioms exists_affine_preterminal_weighted_martingale

end RoughHeston
