import IndependentCommonDriver
import PulsedCommonBrownianFocal

open MeasureTheory ProbabilityTheory Filter Set
open scoped MeasureTheory ProbabilityTheory NNReal

namespace RoughHeston

open MathFin.ItoLocalMartingale (nullAugmentation nullsAlg condExp_sup_nulls)

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

/-- The product enlargement preserves the mixed compensator between the
selected focal cluster and the same Brownian motion driving both aggregates. -/
theorem pulsed_pair_has_common_brownian_on_product_with_focal [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} (T : ℝ≥0)
    {M N Cmm Cmn Cnn a b : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M 𝒢 μ) (hN : Martingale N 𝒢 μ)
    (hM₂ : ∀ t, MemLp (M t) 2 μ) (hN₂ : ∀ t, MemLp (N t) 2 μ)
    (hMc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => M t ω) (Iic T))
    (hNc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => N t ω) (Iic T))
    (hM₀ : M 0 =ᵐ[μ] 0) (hN₀ : N 0 =ᵐ[μ] 0)
    (hmm : Martingale (fun t => M t * M t - Cmm t) 𝒢 μ)
    (hmn : Martingale (fun t => M t * N t - Cmn t) 𝒢 μ)
    (hnn : Martingale (fun t => N t * N t - Cnn t) 𝒢 μ)
    (haa : StronglyAdapted 𝒢 a) (hba : StronglyAdapted 𝒢 b)
    (hac : ∀ᵐ ω ∂μ, ContinuousOn (fun t => a t ω) (Icc 0 T))
    (hbc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => b t ω) (Icc 0 T))
    (ha : ∀ t ω, 0 ≤ a t ω) (hb : ∀ t ω, 0 ≤ b t ω)
    (hcmm : ∀ᵐ ω ∂μ, ∀ t ≤ T, Cmm t ω = ∫ s in (0 : ℝ)..(t : ℝ), a s.toNNReal ω ^ 2)
    (hcmn : ∀ᵐ ω ∂μ, ∀ t ≤ T, Cmn t ω =
      ∫ s in (0 : ℝ)..(t : ℝ), a s.toNNReal ω * b s.toNNReal ω)
    (hcnn : ∀ᵐ ω ∂μ, ∀ t ≤ T, Cnn t ω = ∫ s in (0 : ℝ)..(t : ℝ), b s.toNNReal ω ^ 2)
    {X Y U J Cx Cy : ℝ≥0 → Ω → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (haX : a = GirsanovPort.varianceAmplitude σ X) (hbY : b = GirsanovPort.varianceAmplitude σ Y)
    (hJ : Martingale J 𝒢 μ) (hJ₂ : ∀ t, MemLp (J t) 2 μ)
    (hJc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => J t ω) (Iic T)) (hJ₀ : J 0 =ᵐ[μ] 0)
    (hXJ : Martingale (fun t => M t * J t - Cx t) 𝒢 μ)
    (hYJ : Martingale (fun t => N t * J t - Cy t) 𝒢 μ)
    (hCx : ∀ᵐ ω ∂μ, ∀ t ≤ T, Cx t ω = ∫ s in (0 : ℝ)..(t : ℝ), σ ^ 2 * U s.toNNReal ω)
    (hCy : ∀ᵐ ω ∂μ, ∀ t ≤ T, Cy t ω = ∫ s in (0 : ℝ)..(t : ℝ),
      σ ^ 2 * U s.toNNReal ω * Real.sqrt (Y s.toNNReal ω) / Real.sqrt (X s.toNNReal ω))
    (hXm : Measurable (Function.uncurry X)) (hUm : Measurable (Function.uncurry U))
    (hXc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => X t ω) (Icc 0 T))
    (hYc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => Y t ω) (Icc 0 T))
    (hUc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => U t ω) (Icc 0 T))
    (hParts : ∀ᵐ ω ∂μ, ∀ t ≤ T, 0 ≤ U t ω ∧ U t ω ≤ X t ω) :
    let P := μ.prod gaussianLimit
    let F := nullAugmentation (prodFiltration 𝒢 canonicalAuxiliaryFiltration) P
    let lift (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (z : Ω × (ℝ≥0 → ℝ)) := X t z.1
    ∃ B Cf : ℝ≥0 → (Ω × (ℝ≥0 → ℝ)) → ℝ, MathFinBridge.BrownianOn P F T B ∧
      Martingale B F P ∧ (∀ t, MemLp (B t) 2 P) ∧
      Martingale (fun t ω => B t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) F P ∧
      HasAmplitudeCutoffIntegral F P T B (lift M) (lift a) ∧
      HasAmplitudeCutoffIntegral F P T B (lift N) (lift b) ∧
      Martingale (fun t => B t * (lift J) (min t T) - Cf t) F P ∧
      (∀ t≤T, Cf t =ᵐ[P] fun z => ∫ s in (0:ℝ)..(t:ℝ),
        GirsanovPort.focalBracketDensity σ (lift U) (lift X) s.toNNReal z) := by
  let P := μ.prod gaussianLimit
  let G := prodFiltration 𝒢 canonicalAuxiliaryFiltration
  let F := nullAugmentation G P
  let lift (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (z : Ω × (ℝ≥0 → ℝ)) := X t z.1
  let W (t : ℝ≥0) (z : Ω × (ℝ≥0 → ℝ)) := brownian (min t T) z.2
  have hle (t : ℝ≥0) : G t ≤ F t := le_sup_left
  have aug {X : ℝ≥0 → (Ω × (ℝ≥0 → ℝ)) → ℝ} (hX : Martingale X G P) :
      Martingale X F P := by
    refine ⟨fun t => (hX.stronglyAdapted t).mono (hle t), fun s t hst => ?_⟩
    exact (condExp_sup_nulls (G.le s) (hX.integrable t)).trans (hX.condExp_ae_eq hst)
  have liftM {X : ℝ≥0 → Ω → ℝ} (hX : Martingale X 𝒢 μ) :
      Martingale (lift X) F P :=
    aug (martingale_prod_fst (G := canonicalAuxiliaryFiltration) (ν := gaussianLimit) hX)
  have liftA {X : ℝ≥0 → Ω → ℝ} (hX : StronglyAdapted 𝒢 X) :
      StronglyAdapted F (lift X) :=
    fun t => ((hX t).comp_measurable (@measurable_fst Ω (ℝ≥0 → ℝ) (𝒢 t)
      (canonicalAuxiliaryFiltration t))).mono (hle t)
  have liftP {p : Ω → Prop} (hp : ∀ᵐ ω ∂μ, p ω) :
      ∀ᵐ z : Ω × (ℝ≥0 → ℝ) ∂P, p z.1 :=
    (measurePreserving_fst (μ := μ) (ν := gaussianLimit)).quasiMeasurePreserving.ae hp
  obtain ⟨hWm, hW₂, _, hWc, hWs⟩ := canonical_auxiliary_driver T
  have hw : Martingale W F P := aug (martingale_prod_snd (F := 𝒢) (μ := μ) hWm)
  have hws : Martingale (fun t z => W t z * W t z - ((min t T : ℝ≥0) : ℝ)) F P := by
    simpa only [pow_two] using aug (martingale_prod_snd (F := 𝒢) (μ := μ) hWs)
  have orthogonal {X : ℝ≥0 → Ω → ℝ} (hX : Martingale X 𝒢 μ) :
      Martingale (fun t => W t * lift X t) F P := by
    convert aug (martingale_prod_mul hX hWm) using 1
    ext t z
    exact mul_comm _ _
  have hsquare {X C : ℝ≥0 → Ω → ℝ} (hX : ∀ t, MemLp (X t) 2 μ)
      (hC : Martingale (fun t => X t * X t - C t) 𝒢 μ) :
      Integrable (C T) μ := by
    have hprod := ((hX T).mul (hX T) : MemLp (X T * X T) 1 μ).integrable le_rfl
    simpa only [sub_sub_cancel] using hprod.sub (hC.integrable T)
  have hae : Integrable (fun ω => ∫ s in (0 : ℝ)..(T : ℝ), a s.toNNReal ω ^ 2) μ :=
    (hsquare hM₂ hmm).congr (hcmm.mono fun ω hω => hω T le_rfl)
  have hbe : Integrable (fun ω => ∫ s in (0 : ℝ)..(T : ℝ), b s.toNNReal ω ^ 2) μ :=
    (hsquare hN₂ hnn).congr (hcnn.mono fun ω hω => hω T le_rfl)
  have ham := amplitude_mass_integrable_of_energy haa hac hae
  have hbm := amplitude_mass_integrable_of_energy hba hbc hbe
  have hnull (E : Set (Ω × (ℝ≥0 → ℝ))) (hE : MeasurableSet E) (h0 : P E = 0) :
      MeasurableSet[F 0] E :=
    (show nullsAlg _ P ≤ F 0 from le_sup_right) E
      (MeasurableSpace.measurableSet_generateFrom ⟨hE, h0⟩)
  apply GirsanovPort.pulsed_pair_has_common_brownian_with_focal (X := lift X) (Y := lift Y) (U := lift U)
    (J := lift J) (Cx := lift Cx) (Cy := lift Cy) T (liftM hM) (liftM hN) hw
      (fun t => (hM₂ t).comp_fst gaussianLimit) (fun t => (hN₂ t).comp_fst gaussianLimit)
      (fun t => (hW₂ t).comp_snd μ)
      (liftP hMc) (liftP hNc) (Eventually.of_forall fun z => hWc z.2)
      (liftP hM₀) (liftP hN₀) (liftM hmm) (liftM hmn) (liftM hnn)
      (orthogonal hM) (orthogonal hN) hws (liftA haa) (liftA hba) (liftP hac) (liftP hbc)
      (fun t z => ha t z.1) (fun t z => hb t z.1)
      (liftP hcmm) (liftP hcmn) (liftP hcnn) (ham.comp_fst gaussianLimit) (hbm.comp_fst gaussianLimit)
    hσ (by subst a; rfl) (by subst b; rfl) (liftM hJ) (fun t => (hJ₂ t).comp_fst gaussianLimit)
    (liftP hJc) (liftP hJ₀) (liftM hXJ) (liftM hYJ) (orthogonal hJ) (liftP hCx) (liftP hCy)
    (hXm.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
    (hUm.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
    (liftP hXc) (liftP hYc) (liftP hUc) (liftP hParts) hnull

#print axioms pulsed_pair_has_common_brownian_on_product_with_focal

end RoughHeston
