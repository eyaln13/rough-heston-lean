import CenteredCanonicalTightness

/-! The canonical approximation argument when only centered increment
bounds are uniform over the actual immigration mesh. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped MeasureTheory Topology NNReal ENNReal

namespace RoughHeston

variable {T : ℝ≥0} {α v₀ κ θ σ : ℝ}
  {Pn : ℕ → ProbabilityMeasure (CanonicalPath T (ℝ × ℝ))}

theorem regular_heston_of_centered_canonical_increment_moments
    (hT : 0 < T) (hα : 1 / 2 < α) (hα' : α < 1) (hσ : 0 < σ)
    {q β A : ℝ} (hq : 2 ≤ q) (hβ : 1 < β)
    {C : ENNReal} (hC : C ≠ ⊤)
    {bn : ℕ → CanonicalPath T (ℝ × ℝ)} {b : CanonicalPath T (ℝ × ℝ)}
    (hb : Tendsto bn atTop (𝓝 b))
    (hstart : ∀ n, ((Pn n).map (fun p => p-bn n) : Measure (CanonicalPath T (ℝ × ℝ)))
      {f | A < ‖f (canonicalEvalTime T 0)‖} = 0)
    (hinc : ∀ (n : ℕ) (s t : CanonicalPathTime T),
      (∫⁻ f : CanonicalPath T (ℝ × ℝ), edist (f s) (f t) ^ q ∂((Pn n).map (fun p => p-bn n) : Measure _)) ≤
        C * edist s t ^ β)
    (hNonneg : ∀ n, ∀ᵐ (p : CanonicalPath T (ℝ × ℝ)) ∂(Pn n : Measure _), ∀ t ≤ T,
      0 ≤ (canonicalPathEval T t p).1 ∧ 0 ≤ (canonicalPathEval T t p).2)
    {ℓ : ℝ} (hℓ : 0 < ℓ) {pstar : ENNReal} (hpstar : 0 < pstar)
    (hgap : ∀ n, pstar ≤ (Pn n : Measure _) {p | ℓ ≤ canonicalPairGap T p})
    {d e : ℕ → ℝ≥0 → ℝ} (hd : ∀ t, Tendsto (fun n => d n t) atTop (𝓝 0))
    (he : ∀ t, Tendsto (fun n => e n t) atTop (𝓝 0)) :
    let 𝒢 := canonicalPathNaturalFiltration (E := ℝ × ℝ) T
    let f := canonicalFirstVariance
    let k := canonicalSecondVariance
    let M := canonicalVarianceMartingale T α v₀ κ θ f
    let N := canonicalVarianceMartingale T α v₀ κ θ k
    let gmm := canonicalVarianceCovariance σ f f
    let gmn := canonicalVarianceCovariance σ f k
    let gnn := canonicalVarianceCovariance σ k k
    let Cmm := canonicalVarianceCompensator T gmm
    let Cmn := canonicalVarianceCompensator T gmn
    let Cnn := canonicalVarianceCompensator T gnn
    (∀ n, Martingale (fun t p => M t p + d n t) 𝒢 (Pn n : Measure _)) →
    (∀ n, Martingale (fun t p => N t p + e n t) 𝒢 (Pn n : Measure _)) →
    (∀ n, Martingale (fun t p => (M t p + d n t) * (M t p + d n t) - Cmm t p) 𝒢 (Pn n : Measure _)) →
    (∀ n, Martingale (fun t p => (M t p + d n t) * (N t p + e n t) - Cmn t p) 𝒢 (Pn n : Measure _)) →
    (∀ n, Martingale (fun t p => (N t p + e n t) * (N t p + e n t) - Cnn t p) 𝒢 (Pn n : Measure _)) →
    uniformCanonicalSecondMoment Pn M → uniformCanonicalSecondMoment Pn N →
    uniformCanonicalSecondMoment Pn (fun t p => M t p * M t p - Cmm t p) →
    uniformCanonicalSecondMoment Pn (fun t p => M t p * N t p - Cmn t p) →
    uniformCanonicalSecondMoment Pn (fun t p => N t p * N t p - Cnn t p) →
    RegularHestonPair T α v₀ κ θ σ := by
  intro 𝒢 f k M N gmm gmn gnn Cmm Cmn Cnn hMn hNn hmmn hmnn hnnn hM₂ hN₂ hMM₂ hMN₂ hNN₂
  obtain ⟨Q, φ, hφ, hweak, hpath⟩ := canonicalPairPath_subsequence_of_centered_increment_moments
    hT q β A hq hβ Pn C hC hb hstart hinc
  have hAtTop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hSecond {F : ℝ≥0 → CanonicalPath T (ℝ × ℝ) → ℝ}
      (h : uniformCanonicalSecondMoment Pn F) : uniformCanonicalSecondMoment (Pn ∘ φ) F := by
    intro t
    obtain ⟨C0, hC0⟩ := h t
    exact ⟨C0, fun n => hC0 (φ n)⟩
  exact regular_heston_of_canonical_approximations hT hα hα' hσ hweak hpath
    (fun n => hNonneg (φ n)) hℓ hpstar (fun n => hgap (φ n))
    (fun t => (hd t).comp hAtTop) (fun t => (he t).comp hAtTop)
    (fun n => hMn (φ n)) (fun n => hNn (φ n)) (fun n => hmmn (φ n))
    (fun n => hmnn (φ n)) (fun n => hnnn (φ n))
    (hSecond hM₂) (hSecond hN₂) (hSecond hMM₂) (hSecond hMN₂) (hSecond hNN₂)


theorem separated_heston_of_centered_canonical_increment_moments
    (hT : 0 < T) (hα : 1 / 2 < α) (hα' : α < 1) (hσ : 0 < σ)
    {q β A : ℝ} (hq : 2 ≤ q) (hβ : 1 < β)
    {C : ENNReal} (hC : C ≠ ⊤)
    {bn : ℕ → CanonicalPath T (ℝ × ℝ)} {b : CanonicalPath T (ℝ × ℝ)}
    (hb : Tendsto bn atTop (𝓝 b))
    (hstart : ∀ n, ((Pn n).map (fun p => p-bn n) : Measure (CanonicalPath T (ℝ × ℝ)))
      {f | A < ‖f (canonicalEvalTime T 0)‖} = 0)
    (hinc : ∀ (n : ℕ) (s t : CanonicalPathTime T),
      (∫⁻ f : CanonicalPath T (ℝ × ℝ), edist (f s) (f t) ^ q ∂((Pn n).map (fun p => p-bn n) : Measure _)) ≤
        C * edist s t ^ β)
    (hNonneg : ∀ n, ∀ᵐ (p : CanonicalPath T (ℝ × ℝ)) ∂(Pn n : Measure _), ∀ t ≤ T,
      0 ≤ (canonicalPathEval T t p).1 ∧ 0 ≤ (canonicalPathEval T t p).2)
    {ℓ : ℝ} (hℓ : 0 < ℓ) {pstar : ENNReal} (hpstar : 0 < pstar)
    (hgap : ∀ n, pstar ≤ (Pn n : Measure _) {p | ℓ ≤ canonicalPairGap T p})
    {d e : ℕ → ℝ≥0 → ℝ} (hd : ∀ t, Tendsto (fun n => d n t) atTop (𝓝 0))
    (he : ∀ t, Tendsto (fun n => e n t) atTop (𝓝 0)) :
    let 𝒢 := canonicalPathNaturalFiltration (E := ℝ × ℝ) T
    let f := canonicalFirstVariance
    let k := canonicalSecondVariance
    let M := canonicalVarianceMartingale T α v₀ κ θ f
    let N := canonicalVarianceMartingale T α v₀ κ θ k
    let gmm := canonicalVarianceCovariance σ f f
    let gmn := canonicalVarianceCovariance σ f k
    let gnn := canonicalVarianceCovariance σ k k
    let Cmm := canonicalVarianceCompensator T gmm
    let Cmn := canonicalVarianceCompensator T gmn
    let Cnn := canonicalVarianceCompensator T gnn
    (∀ n, Martingale (fun t p => M t p + d n t) 𝒢 (Pn n : Measure _)) →
    (∀ n, Martingale (fun t p => N t p + e n t) 𝒢 (Pn n : Measure _)) →
    (∀ n, Martingale (fun t p => (M t p + d n t) * (M t p + d n t) - Cmm t p) 𝒢 (Pn n : Measure _)) →
    (∀ n, Martingale (fun t p => (M t p + d n t) * (N t p + e n t) - Cmn t p) 𝒢 (Pn n : Measure _)) →
    (∀ n, Martingale (fun t p => (N t p + e n t) * (N t p + e n t) - Cnn t p) 𝒢 (Pn n : Measure _)) →
    uniformCanonicalSecondMoment Pn M → uniformCanonicalSecondMoment Pn N →
    uniformCanonicalSecondMoment Pn (fun t p => M t p * M t p - Cmm t p) →
    uniformCanonicalSecondMoment Pn (fun t p => M t p * N t p - Cmn t p) →
    uniformCanonicalSecondMoment Pn (fun t p => N t p * N t p - Cnn t p) →
    ∃ (Ω : Type) (m : MeasurableSpace Ω) (μ : @Measure Ω m)
      (F : Filtration ℝ≥0 m) (B X Y : ℝ≥0 → Ω → ℝ),
      IsProbabilityMeasure μ ∧ IsBrownianOn μ F T B ∧
        IsHestonVarianceSolution μ F T α v₀ κ θ σ B X ∧
        IsHestonVarianceSolution μ F T α v₀ κ θ σ B Y ∧
        0 < μ {p | ∃ t ≤ T, X t p ≠ Y t p} := by
  intro 𝒢 f k M N gmm gmn gnn Cmm Cmn Cnn hMn hNn hmmn hmnn hnnn hM₂ hN₂ hMM₂ hMN₂ hNN₂
  exact (regular_heston_of_centered_canonical_increment_moments (Pn:=Pn) (v₀:=v₀) (κ:=κ) (θ:=θ)
    hT hα hα' hσ (q:=q) (β:=β) (A:=A) (C:=C) (bn:=bn) (d:=d) (e:=e)
    hq hβ hC hb hstart hinc hNonneg hℓ hpstar hgap hd he hMn hNn hmmn hmnn hnnn hM₂ hN₂ hMM₂ hMN₂ hNN₂).variance

#print axioms RoughHeston.regular_heston_of_centered_canonical_increment_moments
#print axioms RoughHeston.separated_heston_of_centered_canonical_increment_moments

end RoughHeston
