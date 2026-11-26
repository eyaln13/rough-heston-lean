import HestonWeightedFubini
import BanachHestonInversion

open MeasureTheory ProbabilityTheory Set Filter
open scoped MeasureTheory ProbabilityTheory NNReal ENNReal

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℝ≥0 m} {B V : ℝ≥0 → Ω → ℝ}

private theorem real_timeIntegral_stochastic_convolution [IsFiniteMeasure μ] {α : ℝ}
    (hα : 1/2 < α) (hα' : α ≤ 1) (t : ℝ≥0) (hB₂ : ∀ r, MemLp (B r) 2 μ)
    (hVp : IsStronglyPredictable 𝒢 V) (hVnonneg : ∀ s ω, 0 ≤ V s ω)
    (hVint : ∀ s, Integrable (V s) μ) {C : ℝ} (hmean : ∀ s, (∫ ω, V s ω ∂μ) ≤ C)
    {f : ℝ → ℝ} (hfm : Measurable f) :
    let S := fixedHestonConvolutionLp (T := t) hα hB₂ hVp hVnonneg hVint hmean
    (∫ u : ℝ≥0, f ((t : ℝ)-(u : ℝ)) • S (u : ℝ) ∂hestonTimeMeasure t) =
      volterraSmulConvolution f S (t : ℝ) := by
  dsimp only
  let S := fixedHestonConvolutionLp (T := t) hα hB₂ hVp hVnonneg hVint hmean
  have hc : Continuous S := fixedHestonConvolutionLp_continuous hα hα' hB₂ hVp hVnonneg hVint hmean
  have hm : StronglyMeasurable (fun u : ℝ≥0 => f ((t : ℝ)-(u : ℝ)) • S (u : ℝ)) :=
    (hfm.comp (measurable_const.sub measurable_subtype_coe)).stronglyMeasurable.smul
      (hc.stronglyMeasurable.comp_measurable measurable_subtype_coe)
  rw [hestonTimeMeasure, integral_map continuous_real_toNNReal.measurable.aemeasurable
    hm.aestronglyMeasurable, volterraSmulConvolution, ← restrict_Ioo_eq_restrict_Ioc]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  simp only [Real.coe_toNNReal u hu.1.le, S]

/-- The Riccati-kernel Itô integral expressed with the real-time
Volterra path used in the variance equation. -/
theorem heston_riccati_real_stochastic_term [IsFiniteMeasure μ] {α q : ℝ}
    (hα : 1/2 < α) (hα' : α ≤ 1) (t : ℝ≥0) (hB₂ : ∀ r, MemLp (B r) 2 μ)
    (hVp : IsStronglyPredictable 𝒢 V) (hVnonneg : ∀ s ω, 0 ≤ V s ω)
    (hVint : ∀ s, Integrable (V s) μ) {C : ℝ} (hmean : ∀ s, (∫ ω, V s ω ∂μ) ≤ C)
    {f w : ℝ → ℝ} (hfm : Measurable f) (hfi : IntegrableOn f (Ioc 0 (t : ℝ)))
    (hw : ∀ s ∈ Ioc 0 (t : ℝ), w s =
      q * fractionalK α s + volterraConvolution (fractionalK α) f s) :
    let I := jointItoIntegralCLM (𝒢 := 𝒢) t hB₂
    let S := fixedHestonConvolutionLp (T := t) hα hB₂ hVp hVnonneg hVint hmean
    ∃ W : Lp ℝ 2 (jointPredictableMeasure 𝒢 μ t),
      (⇑W =ᵐ[jointPredictableMeasure 𝒢 μ t] fun z =>
        w ((t : ℝ)-(z.1 : ℝ)) * Real.sqrt (V z.1 z.2)) ∧
      I W = q • S (t : ℝ) + volterraSmulConvolution f S (t : ℝ) := by
  dsimp only
  obtain ⟨W, hW, he⟩ := heston_riccati_stochastic_term hα hα' t hB₂
    hVp hVnonneg hVint hmean hfm hfi hw
  refine ⟨W, hW, ?_⟩
  rw [he, ← real_timeIntegral_stochastic_convolution hα hα' t hB₂ hVp hVnonneg hVint hmean hfm]
  have heq (u : ℝ≥0) : fixedHestonConvolutionLp (T := t) hα hB₂ hVp hVnonneg hVint hmean
      (u : ℝ) =
      jointItoIntegralCLM (𝒢 := 𝒢) t hB₂
        (hestonKernelFamilyLp hα hVp hVnonneg hVint hmean (hestonNNRealHorizonPoint t u)) := by
    unfold fixedHestonConvolutionLp
    congr 2
    apply Subtype.ext
    change min (u : ℝ).toNNReal t = min u t
    simp
  simp_rw [heq]


/-- The affine convolution identity in terminal L². Both sides use the
same finite-horizon Itô map. The deterministic integrability assumptions
specify the Fubini triangle and the weighted variance terms. -/
theorem heston_affineTransform_identity [IsFiniteMeasure μ] {α σ κ a q : ℝ}
    (hα : 1/2 < α) (hα' : α ≤ 1) (t : ℝ≥0) (ht : 0 < t) (hB₂ : ∀ r, MemLp (B r) 2 μ)
    (hVp : IsStronglyPredictable 𝒢 V) (hVnonneg : ∀ s ω, 0 ≤ V s ω)
    (hVint : ∀ s, Integrable (V s) μ) {C : ℝ} (hmean : ∀ s, (∫ ω, V s ω ∂μ) ≤ C)
    (g w : ℝ → ℝ) (v j : ℝ → Lp ℝ 2 μ) :
    let T := (t : ℝ)
    let ν := volume.restrict (Ioc 0 T)
    let K := fractionalK α
    let f := fun s => g s - κ*w s - a*w s^2
    let d := fun s => j s - κ • v s
    let S := fixedHestonConvolutionLp (T := t) hα hB₂ hVp hVnonneg hVint hmean
    let D := volterraSmulConvolution K d
    let I := jointItoIntegralCLM (𝒢 := 𝒢) t hB₂
    Measurable f → IntegrableOn f (Ioc 0 T) →
    (∀ s ∈ Ioc 0 T, w s = q*K s + volterraConvolution K f s) →
    (∀ s ∈ Ioc 0 T, v s = D s + σ • S s) →
    Integrable (fun z : ℝ × ℝ => (f (T-z.1)*K (z.1-z.2)) • d z.2) (ν.prod ν) →
    Integrable (fun s => K (T-s) • d s) ν →
    Integrable (fun s => volterraConvolution f K (T-s) • d s) ν →
    Integrable (fun s => f (T-s) • D s) ν →
    Integrable (fun s => f (T-s) • S s) ν →
    Integrable (fun s => w (T-s) • j s) ν →
    Integrable (fun s => w (T-s) • v s) ν →
    Integrable (fun s => (w (T-s))^2 • v s) ν →
    Integrable (fun s => g (T-s) • v s) ν →
    ∃ W : Lp ℝ 2 (jointPredictableMeasure 𝒢 μ t),
      (⇑W =ᵐ[jointPredictableMeasure 𝒢 μ t] fun z =>
        w (T-(z.1 : ℝ)) * Real.sqrt (V z.1 z.2)) ∧
      q • v T + volterraSmulConvolution g v T = volterraSmulConvolution w j T + σ • I W +
        a • volterraSmulConvolution (fun s => (w s)^2) v T := by
  dsimp only
  intro hfm hfi hw hv htri hKd hrd hfd hfS hwj hwv hw₂v hgv
  let T := (t : ℝ)
  let ν := volume.restrict (Ioc 0 T)
  let K := fractionalK α
  let f := fun s => g s - κ*w s - a*w s^2
  let d := fun s => j s - κ • v s
  let S := fixedHestonConvolutionLp (T := t) hα hB₂ hVp hVnonneg hVint hmean
  let D := volterraSmulConvolution K d
  let I := jointItoIntegralCLM (𝒢 := 𝒢) t hB₂
  obtain ⟨W, hW, hIto⟩ := heston_riccati_real_stochastic_term (q := q) hα hα' t hB₂
    hVp hVnonneg hVint hmean hfm hfi hw
  refine ⟨W, hW, ?_⟩
  change q • v T + volterraSmulConvolution g v T = volterraSmulConvolution w j T + σ • I W +
    a • volterraSmulConvolution (fun s => (w s)^2) v T
  change Integrable (fun s => K (T-s) • d s) ν at hKd
  change Integrable (fun s => volterraConvolution f K (T-s) • d s) ν at hrd
  change Integrable (fun s => f (T-s) • D s) ν at hfd
  change Integrable (fun s => f (T-s) • S s) ν at hfS
  change Integrable (fun s => w (T-s) • j s) ν at hwj
  change Integrable (fun s => w (T-s) • v s) ν at hwv
  change Integrable (fun s => (w (T-s))^2 • v s) ν at hw₂v
  change Integrable (fun s => g (T-s) • v s) ν at hgv
  have hK (x : ℝ) (hx : x ≤ 0) : K x = 0 := by simp [K, fractionalK, hx]
  have hAssoc : volterraSmulConvolution f D T =
      volterraSmulConvolution (volterraConvolution f K) d T :=
    volterra_smul_convolution_assoc hK htri
  have hDrift : q • D T + volterraSmulConvolution f D T = volterraSmulConvolution w d T := by
    rw [hAssoc]
    change q • (∫ s, K (T-s) • d s ∂ν) +
      (∫ s, volterraConvolution f K (T-s) • d s ∂ν) = _
    have hline := integral_add (hKd.smul q) hrd
    simp only [Pi.smul_apply] at hline
    rw [← integral_smul, ← hline]
    unfold volterraSmulConvolution
    change (∫ s in Ioc (0 : ℝ) T, _) = ∫ s in Ioc (0 : ℝ) T, _
    rw [← restrict_Ioo_eq_restrict_Ioc]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro s hs
    have hmem : T-s ∈ Ioc (0 : ℝ) T :=
      ⟨sub_pos.mpr hs.2, sub_le_self _ hs.1.le⟩
    simp_rw [smul_smul, ← add_smul]
    rw [hw _ hmem, volterraConvolution_comm_at hmem.1.le]
  have hvf : volterraSmulConvolution f v T =
      volterraSmulConvolution f D T + σ • volterraSmulConvolution f S T := by
    change (∫ s, f (T-s) • v s ∂ν) =
      (∫ s, f (T-s) • D s ∂ν) + σ • (∫ s, f (T-s) • S s ∂ν)
    have hline := integral_add hfd (hfS.smul σ)
    simp only [Pi.smul_apply] at hline
    rw [← integral_smul, ← hline]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    change f (T-s) • v s = f (T-s) • D s + σ • (f (T-s) • S s)
    rw [hv s hs, smul_add, smul_comm (f (T-s)) σ]
  have hwd : volterraSmulConvolution w d T =
      volterraSmulConvolution w j T - κ • volterraSmulConvolution w v T := by
    change (∫ s, w (T-s) • d s ∂ν) =
      (∫ s, w (T-s) • j s ∂ν) - κ • (∫ s, w (T-s) • v s ∂ν)
    have hline := integral_sub hwj (hwv.smul κ)
    simp only [Pi.smul_apply] at hline
    rw [← integral_smul, ← hline]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s _
    change w (T-s) • (j s - κ • v s) = w (T-s) • j s - κ • (w (T-s) • v s)
    rw [smul_sub, smul_comm (w (T-s)) κ]
  have hfv : volterraSmulConvolution f v T =
      volterraSmulConvolution g v T - κ • volterraSmulConvolution w v T -
        a • volterraSmulConvolution (fun s => (w s)^2) v T := by
    change (∫ s, f (T-s) • v s ∂ν) =
      (∫ s, g (T-s) • v s ∂ν) - κ • (∫ s, w (T-s) • v s ∂ν) -
        a • (∫ s, (w (T-s))^2 • v s ∂ν)
    have hfirst := integral_sub hgv (hwv.smul κ)
    have hsecond := integral_sub (hgv.sub (hwv.smul κ)) (hw₂v.smul a)
    simp only [Pi.sub_apply, Pi.smul_apply] at hfirst hsecond
    rw [← integral_smul, ← integral_smul, ← hfirst, ← hsecond]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s _
    change (g (T-s)-κ*w (T-s)-a*(w (T-s))^2) • v s =
      g (T-s) • v s - κ • (w (T-s) • v s) - a • ((w (T-s))^2 • v s)
    simp only [sub_smul, mul_smul]
  have hcomb : q • v T + volterraSmulConvolution f v T =
      volterraSmulConvolution w d T + σ • I W := by
    change I W = q • S T + volterraSmulConvolution f S T at hIto
    rw [hv T ⟨by exact_mod_cast ht, le_rfl⟩, hvf, ← hDrift, hIto]
    module
  rw [hfv, hwd] at hcomb
  have hh := congrArg (fun x : Lp ℝ 2 μ => x + κ • volterraSmulConvolution w v T +
    a • volterraSmulConvolution (fun s => (w s)^2) v T) hcomb
  convert hh using 1 <;> abel

end RoughHeston

#print axioms RoughHeston.heston_riccati_real_stochastic_term

#print axioms RoughHeston.heston_affineTransform_identity
