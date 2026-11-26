import CorrelatedHestonVariancePair
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Gaussian.Basic

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston

private theorem measure_ext_of_real_projections {μ ν : Measure (ℝ × ℝ)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ L : (ℝ × ℝ) →L[ℝ] ℝ, μ.map L = ν.map L) : μ = ν := by
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_apply, charFunDual_apply]
  have he := congrArg (fun η : Measure ℝ => ∫ x, Complex.exp ((x : ℂ) * Complex.I) ∂η) (h L)
  rwa [integral_map L.continuous.measurable.aemeasurable (by fun_prop),
    integral_map L.continuous.measurable.aemeasurable (by fun_prop)] at he

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

private theorem map_restrict_eq_smul_of_indep {k : MeasurableSpace Ω}
    {g : Ω → ℝ} (hg : @Measurable Ω ℝ m _ g) (hi : @Indep Ω ((borel ℝ).comap g) k m μ)
    {A : Set Ω} (hA : MeasurableSet[k] A) :
    @Measure.map Ω ℝ m _ g (μ.restrict A) = μ A • @Measure.map Ω ℝ m _ g μ := by
  let : MeasurableSpace Ω := m
  ext E hE
  rw [Measure.map_apply hg hE, Measure.smul_apply, Measure.map_apply hg hE,
    Measure.restrict_apply (hg hE), smul_eq_mul, mul_comm (μ A)]
  exact (hi.indepSet_of_measurableSet ⟨E, hE, rfl⟩ hA).measure_inter_eq_mul

/-- Independence of all scalar projections of a measurable real pair from
a past sigma-algebra gives independence of the joint pair from that past. -/
theorem indep_pair_of_indep_projections [IsProbabilityMeasure μ] {k : MeasurableSpace Ω}
    (hk : k ≤ m) {D : Ω → ℝ × ℝ} (hD : @Measurable Ω (ℝ × ℝ) m _ D)
    (h : ∀ L : (ℝ × ℝ) →L[ℝ] ℝ, @Indep Ω ((borel ℝ).comap (L ∘ D)) k m μ) :
    @Indep Ω ((inferInstance : MeasurableSpace (ℝ × ℝ)).comap D) k m μ := by
  let : MeasurableSpace Ω := m
  apply (indep_iff_forall_indepSet μ).mpr
  intro U A hU hA
  obtain ⟨E, hE, rfl⟩ := hU
  have hAμ := hk A hA
  have hm := measure_ne_top μ A
  let : IsFiniteMeasure (μ A • μ.map D) := (μ.map D).smul_finite hm
  have he : (μ.restrict A).map D = μ A • μ.map D := by
    apply measure_ext_of_real_projections
    intro L
    rw [Measure.map_map L.continuous.measurable hD,
      Measure.map_smul _ L.continuous.measurable.aemeasurable,
      Measure.map_map L.continuous.measurable hD]
    exact map_restrict_eq_smul_of_indep (L.continuous.measurable.comp hD) (h L) hA
  have hEq := congrArg (fun η : Measure (ℝ × ℝ) => η E) he
  rw [Measure.map_apply hD hE, Measure.restrict_apply (hD hE),
    Measure.smul_apply, Measure.map_apply hD hE, smul_eq_mul, mul_comm (μ A)] at hEq
  exact (indepSet_iff_measure_inter_eq_mul (hD hE) hAμ μ).mpr hEq

private theorem real_pair_linear_projection (L : (ℝ × ℝ) →L[ℝ] ℝ) :
    ∃ a x y : ℝ, x ^ 2 + y ^ 2 = 1 ∧ ∀ p, L p = a * (x * p.1 + y * p.2) := by
  let p : ℝ × ℝ := (1, 0)
  let q : ℝ × ℝ := (0, 1)
  let x := L p
  let y := L q
  have hl (z : ℝ × ℝ) : L z = x * z.1 + y * z.2 := by
    have he : z = z.1 • p + z.2 • q := by ext <;> simp [p, q]
    conv_lhs => rw [he]
    simp only [map_add, map_smul, smul_eq_mul, x, y]
    ring
  let a := Real.sqrt (x^2 + y^2)
  have ha2 : a^2 = x^2 + y^2 := Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  by_cases ha : a = 0
  · have hsq : x^2 + y^2 = 0 := by rw [← ha2, ha]; norm_num
    have hx : x^2 = 0 := le_antisymm (by nlinarith [sq_nonneg y]) (sq_nonneg x)
    have hy : y^2 = 0 := le_antisymm (by nlinarith [sq_nonneg x]) (sq_nonneg y)
    refine ⟨0, 1, 0, by norm_num, fun z => ?_⟩
    rw [hl, sq_eq_zero_iff.mp hx, sq_eq_zero_iff.mp hy]
    ring
  · refine ⟨a, x/a, y/a, ?_, fun z => ?_⟩
    · rw [div_pow, div_pow, ← add_div, ← ha2, div_self (pow_ne_zero _ ha)]
    · rw [hl]
      field_simp

variable {F : Filtration ℝ≥0 m} {T : ℝ≥0} {B C : ℝ≥0 → Ω → ℝ}

/-- The same real Brownian projections give a Gaussian joint increment
which is independent of the entire past. This includes degenerate
linear transformations such as correlation one or minus one. -/
theorem jointly_gaussian_independent_increments_of_Brownian_projections [IsProbabilityMeasure μ]
    (hB : StronglyAdapted F B) (hC : StronglyAdapted F C)
    (hPr : ∀ x y : ℝ, x^2+y^2=1 →
      MathFinBridge.BrownianOn μ F T (fun t ω => x * B t ω + y * C t ω))
    {s t : ℝ≥0} (hst : s ≤ t) (ht : t ≤ T) :
    let D (ω : Ω) := (B t ω - B s ω, C t ω - C s ω)
    IsGaussian (μ.map D) ∧
      Indep ((inferInstance : MeasurableSpace (ℝ × ℝ)).comap D) (F s) μ := by
  intro D
  have hBm (u : ℝ≥0) : Measurable (B u) := ((hB u).mono (F.le u)).measurable
  have hCm (u : ℝ≥0) : Measurable (C u) := ((hC u).mono (F.le u)).measurable
  have hD : Measurable D := ((hBm t).sub (hBm s)).prodMk ((hCm t).sub (hCm s))
  have hp (L : (ℝ × ℝ) →L[ℝ] ℝ) :
      IsGaussian ((μ.map D).map L) ∧ Indep ((borel ℝ).comap (L ∘ D)) (F s) μ := by
    obtain ⟨a, x, y, hn, hl⟩ := real_pair_linear_projection L
    let e (ω : Ω) := (x * B t ω + y * C t ω) - (x * B s ω + y * C s ω)
    have he : L ∘ D = (fun z : ℝ => a * z) ∘ e := by
      funext ω
      simp only [Function.comp_apply, hl, D, e]
      ring
    have hem : Measurable e := ((hBm t).const_mul x |>.add ((hCm t).const_mul y)).sub
      (((hBm s).const_mul x).add ((hCm s).const_mul y))
    have ha : Measurable (fun z : ℝ => a * z) := measurable_id.const_mul a
    have hLaw : μ.map e = gaussianReal 0 (t - s) := (hPr x y hn).normal_increment s t hst ht
    constructor
    · rw [Measure.map_map L.continuous.measurable hD, he, ← Measure.map_map ha hem, hLaw]
      simp only [mul_comm a]
      rw [gaussianReal_map_mul_const]
      infer_instance
    · have hindep : @IndepFun Ω ℝ Ω m (borel ℝ) (F s) e id μ := by
        simpa only [IndepFun_iff_Indep, MeasurableSpace.comap_id] using
          (hPr x y hn).independent_of_past s t hst ht
      have hab : @Measurable ℝ ℝ (borel ℝ) (borel ℝ) (fun z => a * z) := by
        exact (continuous_const.mul continuous_id).borel_measurable
      have hi := hindep.comp (φ := fun z : ℝ => a * z) (ψ := id) hab
        (@measurable_id Ω (F s))
      rw [he]
      simpa only [IndepFun_iff_Indep, Function.id_comp, MeasurableSpace.comap_id] using hi
  exact ⟨isGaussian_of_isGaussian_map fun L => (hp L).1,
    indep_pair_of_indep_projections (F.le s) hD fun L => (hp L).2⟩


/-- The Gaussian increment law and independence of the joint past are
preserved by the stock-driver linear combination, including when its
covariance matrix is degenerate. -/
theorem jointly_gaussian_independent_increments_of_correlated_projections
    [IsProbabilityMeasure μ] (hB : StronglyAdapted F B) (hC : StronglyAdapted F C)
    (hPr : ∀ x y : ℝ, x^2+y^2=1 →
      MathFinBridge.BrownianOn μ F T (fun t ω => x * B t ω + y * C t ω))
    (ρ : ℝ) {s t : ℝ≥0} (hst : s ≤ t) (ht : t ≤ T) :
    let W (u : ℝ≥0) (ω : Ω) := ρ * B u ω + Real.sqrt (1 - ρ^2) * C u ω
    let D (ω : Ω) := (B t ω - B s ω, W t ω - W s ω)
    IsGaussian (μ.map D) ∧
      Indep ((inferInstance : MeasurableSpace (ℝ × ℝ)).comap D) (F s) μ := by
  intro W D
  let E (ω : Ω) := (B t ω - B s ω, C t ω - C s ω)
  let fst := ContinuousLinearMap.fst ℝ ℝ ℝ
  let snd := ContinuousLinearMap.snd ℝ ℝ ℝ
  let L := fst.prod (ρ • fst + Real.sqrt (1 - ρ^2) • snd)
  have he : D = L ∘ E := by
    funext ω
    apply Prod.ext
    · rfl
    · change (ρ * B t ω + Real.sqrt (1-ρ^2) * C t ω) -
        (ρ * B s ω + Real.sqrt (1-ρ^2) * C s ω) =
        ρ * (B t ω-B s ω) + Real.sqrt (1-ρ^2) * (C t ω-C s ω)
      ring
  have hBm (u : ℝ≥0) : Measurable (B u) := ((hB u).mono (F.le u)).measurable
  have hCm (u : ℝ≥0) : Measurable (C u) := ((hC u).mono (F.le u)).measurable
  have hE : Measurable E := ((hBm t).sub (hBm s)).prodMk ((hCm t).sub (hCm s))
  have hL : Measurable L := L.continuous.measurable
  obtain ⟨hG, hI⟩ := jointly_gaussian_independent_increments_of_Brownian_projections hB hC hPr hst ht
  have hG' : IsGaussian (μ.map E) := hG
  have hI' : Indep ((inferInstance : MeasurableSpace (ℝ × ℝ)).comap E) (F s) μ := hI
  rw [he]
  refine ⟨?_, indep_of_indep_of_le_left hI' ?_⟩
  · rw [← Measure.map_map hL hE]
    let _ : IsGaussian (μ.map E) := hG'
    infer_instance
  · rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hL.comap_le

#print axioms indep_pair_of_indep_projections
#print axioms jointly_gaussian_independent_increments_of_Brownian_projections
#print axioms jointly_gaussian_independent_increments_of_correlated_projections

end RoughHeston
