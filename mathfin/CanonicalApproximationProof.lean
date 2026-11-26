import CanonicalSeparatedVariance
import CanonicalPathSupMoment

open MeasureTheory ProbabilityTheory Filter Set
open scoped MeasureTheory Topology NNReal ENNReal

namespace RoughHeston

variable {T : ℝ≥0} {α v₀ κ θ σ : ℝ}
  {Pn : ℕ → ProbabilityMeasure (CanonicalPath T (ℝ × ℝ))}
  {P : ProbabilityMeasure (CanonicalPath T (ℝ × ℝ))}

/-- Nonnegativity of both coordinates is preserved by weak convergence
in the uniform path topology. -/
theorem canonicalPair_ae_nonnegative_of_weak_limit
    (hweak : Tendsto Pn atTop (𝓝 P))
    (hp : ∀ n, ∀ᵐ (p : CanonicalPath T (ℝ × ℝ)) ∂(Pn n : Measure _), ∀ t ≤ T,
      0 ≤ (canonicalPathEval T t p).1 ∧ 0 ≤ (canonicalPathEval T t p).2) :
    ∀ᵐ (p : CanonicalPath T (ℝ × ℝ)) ∂(P : Measure _), ∀ t ≤ T,
      0 ≤ (canonicalPathEval T t p).1 ∧ 0 ≤ (canonicalPathEval T t p).2 := by
  let S : Set (CanonicalPath T (ℝ × ℝ)) :=
    {p | ∀ t ≤ T, 0 ≤ (canonicalPathEval T t p).1 ∧ 0 ≤ (canonicalPathEval T t p).2}
  have hS : IsClosed S := by
    have he : S = ⋂ t, ⋂ _ : t ≤ T,
        {p | 0 ≤ (canonicalPathEval T t p).1 ∧ 0 ≤ (canonicalPathEval T t p).2} := by
      ext p
      simp [S]
    rw [he]
    apply isClosed_iInter
    intro t
    apply isClosed_iInter
    intro _
    exact (isClosed_le continuous_const (continuous_canonicalPathEval T t).fst).inter
      (isClosed_le continuous_const (continuous_canonicalPathEval T t).snd)
  have hmeas := hS.measurableSet
  have hone (n : ℕ) : (Pn n : Measure _) S = 1 :=
    ((ae_mem_iff_measure_eq hmeas.nullMeasurableSet).1 (hp n)).trans measure_univ
  change ∀ᵐ (p : CanonicalPath T (ℝ × ℝ)) ∂(P : Measure _), p ∈ S
  apply (ae_mem_iff_measure_eq hmeas.nullMeasurableSet).2
  rw [measure_univ]
  apply le_antisymm ((measure_mono (subset_univ S)).trans_eq measure_univ)
  simpa only [hone, limsup_const] using ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hweak hS

/-- The uniform timewise L² bound used by the martingale tests. -/
def uniformCanonicalSecondMoment
    (Pn : ℕ → ProbabilityMeasure (CanonicalPath T (ℝ × ℝ)))
    (F : ℝ≥0 → CanonicalPath T (ℝ × ℝ) → ℝ) : Prop :=
  ∀ t, ∃ C : ℝ, ∀ n, MemLp (F t) 2 (Pn n : Measure _) ∧
    (∫ p, (F t p) ^ 2 ∂(Pn n : Measure _)) ≤ C

private theorem integral_norm_le_sqrt_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {f : Ω → ℝ} (hf : MemLp f 2 ν) :
    (∫ p, ‖f p‖ ∂ν) ≤ Real.sqrt (∫ p, (f p) ^ 2 ∂ν) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by rw [Real.holderConjugate_iff]; norm_num
  have h := integral_mul_norm_le_Lp_mul_Lq hpq
    (by simpa using hf : MemLp f (ENNReal.ofReal 2) ν)
    (memLp_const (1 : ℝ) : MemLp (fun _ => (1 : ℝ)) (ENNReal.ofReal 2) ν)
  have hn (x : ℝ) : ‖x‖ ^ (2 : ℝ) = x ^ 2 := by rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  simpa [hn, Real.sqrt_eq_rpow, one_div] using h

private theorem uniformCanonicalSecondMoment.integrable {F : ℝ≥0 → CanonicalPath T (ℝ × ℝ) → ℝ}
    (h : uniformCanonicalSecondMoment Pn F) (n : ℕ) (t : ℝ≥0) :
    Integrable (F t) (Pn n : Measure _) :=
  ((h t).choose_spec n).1.integrable one_le_two

private theorem uniformCanonicalSecondMoment.norm_mean_bound {F : ℝ≥0 → CanonicalPath T (ℝ × ℝ) → ℝ}
    (h : uniformCanonicalSecondMoment Pn F) (t : ℝ≥0) :
    ∃ C : ℝ, ∀ n, (∫ p, ‖F t p‖ ∂(Pn n : Measure _)) ≤ C := by
  obtain ⟨C, hC⟩ := h t
  exact ⟨Real.sqrt C, fun n => (integral_norm_le_sqrt_integral_sq (hC n).1).trans
    (Real.sqrt_le_sqrt (hC n).2)⟩

private theorem uniformCanonicalSecondMoment.limit_memLp {F : ℝ≥0 → CanonicalPath T (ℝ × ℝ) → ℝ}
    (h : uniformCanonicalSecondMoment Pn F) (hweak : Tendsto Pn atTop (𝓝 P))
    (hF : ∀ t, Continuous (F t)) (t : ℝ≥0) : MemLp (F t) 2 (P : Measure _) := by
  obtain ⟨C, hC⟩ := h t
  exact (weak_limit_memLp_two_and_sq_moment_bound hweak (hF t)
    (fun n => (hC n).1) (fun n => (hC n).2)).1

/-- The complete passage from converging canonical approximation laws
with consistent martingale tests and a uniform gap to the direct
variance theorem's witnesses. -/
theorem regular_heston_of_canonical_approximations
    (hT : 0 < T) (hα : 1 / 2 < α) (hα' : α < 1) (hσ : 0 < σ)
    (hweak : Tendsto Pn atTop (𝓝 P))
    (hpath : MemLp (fun p : CanonicalPath T (ℝ × ℝ) => ‖p‖) 2 (P : Measure _))
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
  have hNonneg' := canonicalPair_ae_nonnegative_of_weak_limit hweak hNonneg
  have hsep := canonicalPairDifferent_of_weak_limit hweak hℓ hpstar hgap
  have hM := canonicalVarianceMartingale_of_weak_limit hα' hweak f hd hMn hM₂
  have hN := canonicalVarianceMartingale_of_weak_limit hα' hweak k he hNn hN₂
  have hmm := canonicalVarianceCompensatedProduct_of_weak_limit hα' hweak f f gmm hd hd hmmn
    hM₂.integrable hM₂.integrable hM₂.norm_mean_bound hM₂.norm_mean_bound hMM₂
  have hmn := canonicalVarianceCompensatedProduct_of_weak_limit hα' hweak f k gmn hd he hmnn
    hM₂.integrable hN₂.integrable hM₂.norm_mean_bound hN₂.norm_mean_bound hMN₂
  have hnn := canonicalVarianceCompensatedProduct_of_weak_limit hα' hweak k k gnn he he hnnn
    hN₂.integrable hN₂.integrable hN₂.norm_mean_bound hN₂.norm_mean_bound hNN₂
  have hContinuous (c : C(ℝ × ℝ, ℝ)) (t : ℝ≥0) :
      Continuous (canonicalVarianceMartingale T α v₀ κ θ c t) :=
    (continuous_recoveredVarianceMartingale T hα' v₀ κ θ (min t T).prop).comp
      (ContinuousMap.continuous_postcomp c)
  exact regular_heston_of_canonical_martingales hT hα hα' hσ hpath hNonneg' hsep hM hN
    (hM₂.limit_memLp hweak (hContinuous f)) (hN₂.limit_memLp hweak (hContinuous k)) hmm hmn hnn

theorem separated_heston_of_canonical_approximations
    (hT : 0 < T) (hα : 1 / 2 < α) (hα' : α < 1) (hσ : 0 < σ)
    (hweak : Tendsto Pn atTop (𝓝 P))
    (hpath : MemLp (fun p : CanonicalPath T (ℝ × ℝ) => ‖p‖) 2 (P : Measure _))
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
  exact (regular_heston_of_canonical_approximations hT hα hα' hσ hweak hpath hNonneg hℓ hpstar hgap
    hd he hMn hNn hmmn hmnn hnnn hM₂ hN₂ hMM₂ hMN₂ hNN₂).variance

/-- A uniform increment moment estimate supplies the weak subsequence
and its square-integrable path bound. The remaining inputs concern the
martingale identities and separation estimates of the approximations. -/
theorem separated_heston_of_canonical_increment_moments
    (hT : 0 < T) (hα : 1 / 2 < α) (hα' : α < 1) (hσ : 0 < σ)
    {q β A : ℝ} (hq : 2 ≤ q) (hβ : 1 < β)
    {C : ENNReal} (hC : C ≠ ⊤)
    (hstart : ∀ n, (Pn n : Measure (CanonicalPath T (ℝ × ℝ)))
      {f | A < ‖f (canonicalEvalTime T 0)‖} = 0)
    (hinc : ∀ (n : ℕ) (s t : CanonicalPathTime T),
      (∫⁻ f : CanonicalPath T (ℝ × ℝ), edist (f s) (f t) ^ q ∂(Pn n : Measure _)) ≤
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
  obtain ⟨Q, φ, hφ, hweak⟩ := canonicalPairPath_subsequence_of_increment_moments
    hT q β A (by linarith) hβ Pn C hC hstart hinc
  obtain ⟨D, hD⟩ := uniform_canonicalPath_sup_sq_moment hT q β A hq hβ Pn C hC hstart hinc
  have hpath := (weak_limit_canonicalPath_sup_sq_moment hweak (fun n => hD.2 (φ n))).1
  have hAtTop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hSecond {F : ℝ≥0 → CanonicalPath T (ℝ × ℝ) → ℝ}
      (h : uniformCanonicalSecondMoment Pn F) : uniformCanonicalSecondMoment (Pn ∘ φ) F := by
    intro t
    obtain ⟨C0, hC0⟩ := h t
    exact ⟨C0, fun n => hC0 (φ n)⟩
  exact separated_heston_of_canonical_approximations hT hα hα' hσ hweak hpath
    (fun n => hNonneg (φ n)) hℓ hpstar (fun n => hgap (φ n))
    (fun t => (hd t).comp hAtTop) (fun t => (he t).comp hAtTop)
    (fun n => hMn (φ n)) (fun n => hNn (φ n)) (fun n => hmmn (φ n))
    (fun n => hmnn (φ n)) (fun n => hnnn (φ n))
    (hSecond hM₂) (hSecond hN₂) (hSecond hMM₂) (hSecond hMN₂) (hSecond hNN₂)

end RoughHeston

#print axioms RoughHeston.canonicalPair_ae_nonnegative_of_weak_limit
#print axioms RoughHeston.regular_heston_of_canonical_approximations
#print axioms RoughHeston.separated_heston_of_canonical_approximations

#print axioms RoughHeston.separated_heston_of_canonical_increment_moments
