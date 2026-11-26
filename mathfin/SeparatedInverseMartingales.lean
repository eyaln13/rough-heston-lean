import DirectVarianceInversion
import IndependentCommonDriver

open MeasureTheory ProbabilityTheory Filter Set
open scoped MeasureTheory ProbabilityTheory Topology NNReal ENNReal

namespace RoughHeston

open MathFin.ItoLocalMartingale (nullAugmentation)

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℝ≥0 m} {T : ℝ≥0} {α v₀ κ θ σ : ℝ}

/-- Inverse equation data attached to one variance coordinate of the
limiting pair. The square and cross-compensators are specified jointly. -/
structure VarianceInverseMartingaleData (μ : Measure Ω) (𝒢 : Filtration ℝ≥0 m)
    (T : ℝ≥0) (α v₀ κ θ : ℝ) (V M : ℝ≥0 → Ω → ℝ) : Prop where
  adapted : StronglyAdapted 𝒢 V
  path_continuous : ∀ ω, Continuous (fun t => V t ω)
  nonnegative : ∀ t ω, 0 ≤ V t ω
  integrable : ∀ t, Integrable (V t) μ
  mean_bound : ∃ C : ℝ, ∀ t, (∫ ω, V t ω ∂μ) ≤ C
  lp_paths : ∃ f g : ℝ → Lp ℝ 2 μ,
    Continuous f ∧ Continuous g ∧
    (∀ s, ⇑(f s) =ᵐ[μ] fun ω => V s.toNNReal ω - v₀) ∧
    (∀ s, ⇑(g s) =ᵐ[μ] fun ω => κ * (θ - V s.toNNReal ω))
  martingale : Martingale M 𝒢 μ
  square_integrable : ∀ t, MemLp (M t) 2 μ
  martingale_continuous : ∀ᵐ ω ∂μ, ContinuousOn (fun t => M t ω) (Iic T)
  inverse_identity : ∀ t ≤ T,
    (fun ω => ∫ s in Ioc (0 : ℝ) (t : ℝ), fractionalL α ((t : ℝ) - s) *
      (V s.toNNReal ω - v₀)) =ᵐ[μ]
    (fun ω => (∫ s in Ioc (0 : ℝ) (t : ℝ), κ * (θ - V s.toNNReal ω)) + M t ω)

theorem VarianceInverseMartingaleData.martingale_zero
    {V M : ℝ≥0 → Ω → ℝ} (d : VarianceInverseMartingaleData μ 𝒢 T α v₀ κ θ V M) :
    M 0 =ᵐ[μ] 0 := by
  filter_upwards [d.inverse_identity 0 zero_le] with ω hω
  simpa only [NNReal.coe_zero, Ioc_self, Measure.restrict_empty, integral_zero_measure, zero_add,
    Pi.zero_apply] using hω.symm

/-- The inverse equations with rank-one covariances and positive separation
give two direct variance solutions on one space with one Brownian driver. -/
theorem separated_heston_of_inverse_martingales [IsProbabilityMeasure μ]
    (hT : 0 < T) (hα : 1 / 2 < α) (hα' : α < 1) (hσ : 0 < σ)
    {X Y M N Cmm Cmn Cnn : ℝ≥0 → Ω → ℝ}
    (dx : VarianceInverseMartingaleData μ 𝒢 T α v₀ κ θ X M)
    (dy : VarianceInverseMartingaleData μ 𝒢 T α v₀ κ θ Y N)
    (hmm : Martingale (fun t => M t * M t - Cmm t) 𝒢 μ)
    (hmn : Martingale (fun t => M t * N t - Cmn t) 𝒢 μ)
    (hnn : Martingale (fun t => N t * N t - Cnn t) 𝒢 μ)
    (hcmm : ∀ᵐ ω ∂μ, ∀ t ≤ T, Cmm t ω =
      ∫ s in (0 : ℝ)..(t : ℝ), (σ * Real.sqrt (X s.toNNReal ω)) ^ 2)
    (hcmn : ∀ᵐ ω ∂μ, ∀ t ≤ T, Cmn t ω =
      ∫ s in (0 : ℝ)..(t : ℝ), (σ * Real.sqrt (X s.toNNReal ω)) * (σ * Real.sqrt (Y s.toNNReal ω)))
    (hcnn : ∀ᵐ ω ∂μ, ∀ t ≤ T, Cnn t ω =
      ∫ s in (0 : ℝ)..(t : ℝ), (σ * Real.sqrt (Y s.toNNReal ω)) ^ 2)
    (hsep : 0 < μ {ω | ∃ t ≤ T, X t ω ≠ Y t ω}) :
    let P := μ.prod gaussianLimit
    let F := nullAugmentation (prodFiltration 𝒢 canonicalAuxiliaryFiltration) P
    let lift (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (z : Ω × (ℝ≥0 → ℝ)) := X t z.1
    ∃ B : ℝ≥0 → (Ω × (ℝ≥0 → ℝ)) → ℝ, IsBrownianOn P F T B ∧
      IsHestonVarianceSolution P F T α v₀ κ θ σ B (lift X) ∧
      IsHestonVarianceSolution P F T α v₀ κ θ σ B (lift Y) ∧
      0 < P {z | ∃ t ≤ T, lift X t z ≠ lift Y t z} := by
  dsimp only
  let P := μ.prod gaussianLimit
  let F := nullAugmentation (prodFiltration 𝒢 canonicalAuxiliaryFiltration) P
  let lift (V : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (z : Ω × (ℝ≥0 → ℝ)) := V t z.1
  let amp (V : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) := σ * Real.sqrt (V t ω)
  have hAmpAdapted {V : ℝ≥0 → Ω → ℝ} (hV : StronglyAdapted 𝒢 V) :
      StronglyAdapted 𝒢 (amp V) := fun t =>
    stronglyMeasurable_const.mul (hV t).measurable.sqrt.stronglyMeasurable
  have hAmpCont {V : ℝ≥0 → Ω → ℝ} (hV : ∀ ω, Continuous (fun t => V t ω)) :
      ∀ᵐ ω ∂μ, ContinuousOn (fun t => amp V t ω) (Icc 0 T) :=
    ae_of_all μ fun ω => (continuous_const.mul (Real.continuous_sqrt.comp (hV ω))).continuousOn
  have hAmpNonneg (V : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : 0 ≤ amp V t ω :=
    mul_nonneg hσ.le (Real.sqrt_nonneg _)
  obtain ⟨B, hB, hBm, hB₂, hBclock, hXcut, hYcut⟩ :=
    rank_one_pair_has_common_brownian_on_product_with_compensator T
      dx.martingale dy.martingale dx.square_integrable dy.square_integrable
      dx.martingale_continuous dy.martingale_continuous dx.martingale_zero dy.martingale_zero
      hmm hmn hnn (hAmpAdapted dx.adapted) (hAmpAdapted dy.adapted)
      (hAmpCont dx.path_continuous) (hAmpCont dy.path_continuous)
      (hAmpNonneg X) (hAmpNonneg Y) hcmm hcmn hcnn
  have hfst : MeasurePreserving (Prod.fst : Ω × (ℝ≥0 → ℝ) → Ω) P μ :=
    measurePreserving_fst
  have liftAdapted {V : ℝ≥0 → Ω → ℝ} (hV : StronglyAdapted 𝒢 V) :
      StronglyAdapted F (lift V) := fun t =>
    ((hV t).comp_measurable (@measurable_fst Ω (ℝ≥0 → ℝ) (𝒢 t)
      (canonicalAuxiliaryFiltration t))).mono le_sup_left
  have solve {V U : ℝ≥0 → Ω → ℝ}
      (d : VarianceInverseMartingaleData μ 𝒢 T α v₀ κ θ V U)
      (hcut : HasAmplitudeCutoffIntegral F P T B (lift U) (lift (amp V))) :
      IsHestonVarianceSolution P F T α v₀ κ θ σ B (lift V) := by
    have hVa := liftAdapted d.adapted
    have hVc (z : Ω × (ℝ≥0 → ℝ)) : Continuous (fun t => lift V t z) :=
      d.path_continuous z.1
    have hVp : IsStronglyPredictable F (lift V) :=
      hVa.isStronglyPredictable_of_leftContinuous (fun z _ => (hVc z).continuousWithinAt)
    have hVi (t : ℝ≥0) : Integrable (lift V t) P :=
      hfst.integrable_comp_of_integrable (d.integrable t)
    obtain ⟨C, hC⟩ := d.mean_bound
    have hmean (t : ℝ≥0) : (∫ z, lift V t z ∂P) ≤ C := by
      change (∫ z, V t z.1 ∂P) ≤ C
      rw [← integral_map hfst.measurable.aemeasurable
        (hfst.map_eq.symm ▸ (d.integrable t).aestronglyMeasurable), hfst.map_eq]
      exact hC t
    obtain ⟨f, g, hfc, hgc, hf, hg⟩ := d.lp_paths
    let e : Lp ℝ 2 μ →+ Lp ℝ 2 P := Lp.compMeasurePreserving (Prod.fst : Ω × (ℝ≥0 → ℝ) → Ω) hfst
    have he : Isometry (e : Lp ℝ 2 μ → Lp ℝ 2 P) := Lp.isometry_compMeasurePreserving hfst
    let f' (s : ℝ) := e (f s)
    let g' (s : ℝ) := e (g s)
    have hf' : Continuous f' := he.continuous.comp hfc
    have hg' : Continuous g' := he.continuous.comp hgc
    have hfRep (s : ℝ) : ⇑(f' s) =ᵐ[P] fun z => lift V s.toNNReal z - v₀ :=
      (Lp.coeFn_compMeasurePreserving (f s) hfst).trans
        (hfst.quasiMeasurePreserving.ae (hf s))
    have hgRep (s : ℝ) : ⇑(g' s) =ᵐ[P] fun z => κ * (θ - lift V s.toNNReal z) :=
      (Lp.coeFn_compMeasurePreserving (g s) hfst).trans
        (hfst.quasiMeasurePreserving.ae (hg s))
    have hnonneg (s : ℝ≥0) (z : Ω × (ℝ≥0 → ℝ)) : 0 ≤ lift V s z :=
      d.nonnegative s z.1
    have hcts : ∀ᵐ z ∂P, ContinuousOn (fun t => lift V t z) (Icc 0 T) :=
      ae_of_all P fun z => (hVc z).continuousOn
    have hinv := heston_L2_inverse_of_samplewise hα' hσ.le hB₂ hBm hBclock
      hVp hVa hcts hnonneg hVi hmean hf'.stronglyMeasurable hf'.continuousOn
      hg'.stronglyMeasurable hg'.continuousOn hfRep hgRep hcut
      (fun t ht => hfst.quasiMeasurePreserving.ae (d.inverse_identity t ht))
    exact isHestonVarianceSolution_of_L2_inverse hα hα' hT hσ.ne' hB₂ hBm hBclock
      hVp hVa hcts hnonneg hVi hmean hf'.stronglyMeasurable hf'.continuousOn
      hg'.stronglyMeasurable hg'.continuousOn hfRep hgRep hinv
  exact ⟨B, hB, solve dx hXcut, solve dy hYcut,
    (measure_separation_prod_fst (μ := μ) (ν := gaussianLimit) T X Y).symm ▸ hsep⟩

end RoughHeston

#print axioms RoughHeston.VarianceInverseMartingaleData.martingale_zero
#print axioms RoughHeston.separated_heston_of_inverse_martingales
