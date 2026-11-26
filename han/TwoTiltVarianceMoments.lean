import ActualStoppedAffineTransport
import MathFin.Probability.Analysis.FiniteMeasureCauchySchwarz

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace RoughHeston.GirsanovPort

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Hölder's inequality transfers uniformly bounded second moments
to uniformly bounded first moments under a square-integrable density. -/
theorem integral_le_under_square_density {D f : Ω → ℝ} (hDm : Measurable D)
    (hD₀ : ∀ᵐ ω ∂P, 0≤D ω) (hD₂ : MemLp D 2 P) (hf₂ : MemLp f 2 P) :
    let Q := P.withDensity (fun ω => ENNReal.ofReal (D ω))
    Integrable f Q ∧
      (∫ ω,f ω ∂Q) ≤ Real.sqrt (∫ ω,D ω^2 ∂P) * Real.sqrt (∫ ω,f ω^2 ∂P) := by
  let Q := P.withDensity (fun ω => ENNReal.ofReal (D ω))
  have hi : Integrable (fun ω => D ω*f ω) P := hD₂.integrable_mul hf₂
  have hEq : (fun ω => (ENNReal.ofReal (D ω)).toReal • f ω) =ᵐ[P] fun ω => D ω*f ω := by
    filter_upwards [hD₀] with ω hω
    simp only [ENNReal.toReal_ofReal hω,smul_eq_mul]
  have hf : Integrable f Q := by
    apply (integrable_withDensity_iff_integrable_smul' hDm.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).2
    exact hi.congr hEq.symm
  refine ⟨hf,?_⟩
  rw [integral_withDensity_eq_integral_toReal_smul hDm.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), integral_congr_ae hEq]
  exact (integral_mono hi hi.abs fun ω => le_abs_self (D ω*f ω)).trans
    (MathFin.integral_abs_mul_le_sqrt_mul_sqrt hD₂ hf₂)

/-- A fourth moment under the original law and two square-integrable
densities give every first-moment input used by the stopped point tests. -/
theorem uniform_necessary_moments_under_two_tilts [IsProbabilityMeasure P]
    {D₁ D₂ : Ω → ℝ} (hD₁m : Measurable D₁) (hD₂m : Measurable D₂)
    (hD₁₀ : ∀ᵐ ω ∂P, 0≤D₁ ω) (hD₁₂ : MemLp D₁ 2 P)
    {Q R : Measure Ω}
    (hQ : Q = P.withDensity (fun ω => ENNReal.ofReal (D₁ ω)))
    (hR : R = Q.withDensity (fun ω => ENNReal.ofReal (D₂ ω)))
    (hD₂₀ : ∀ᵐ ω ∂Q, 0≤D₂ ω) (hD₂₂ : MemLp D₂ 2 Q)
    {Y : ℝ≥0 → Ω → ℝ} (hY : ∀ t, Measurable (Y t))
    (hY₄ : ∀ t, Integrable (fun ω => Y t ω ^ 4) P) {K : ℝ}
    (hK : ∀ t, (∫ ω,Y t ω ^ 4 ∂P)≤K) :
    ∃ A₀ A₁ A₂ : ℝ,
      (∀ t, Integrable (Y t) P ∧ (∫ ω,Y t ω ∂P)≤A₀) ∧
      (∀ t, Integrable (Y t) Q ∧ (∫ ω,Y t ω ∂Q)≤A₁) ∧
      (∀ t, Integrable (Y t) R ∧ (∫ ω,Y t ω ∂R)≤A₂) := by
  have hY₂ (t : ℝ≥0) : MemLp (fun ω => Y t ω ^ 2) 2 P := by
    apply (memLp_two_iff_integrable_sq ((hY t).pow_const 2).aestronglyMeasurable).2
    simpa only [← pow_mul] using hY₄ t
  have hYi₂ (t : ℝ≥0) : Integrable (fun ω => Y t ω ^ 2) P := (hY₂ t).integrable one_le_two
  have hYP₂ (t : ℝ≥0) : MemLp (Y t) 2 P :=
    (memLp_two_iff_integrable_sq (hY t).aestronglyMeasurable).2 (hYi₂ t)
  have hb₂ (t : ℝ≥0) : (∫ ω,Y t ω ^ 2 ∂P) ≤ K+1 := by
    calc
      _ ≤ ∫ ω,Y t ω ^ 4+1 ∂P := integral_mono (hYi₂ t) ((hY₄ t).add (integrable_const 1))
        (fun ω => by nlinarith [sq_nonneg (Y t ω ^ 2-1)])
      _ ≤ _ := by rw [integral_add (hY₄ t) (integrable_const 1)]; simpa using hK t
  let J := Real.sqrt (∫ ω,D₁ ω ^ 2 ∂P)
  let KQ := J * Real.sqrt K
  have hQ₂ (t : ℝ≥0) : Integrable (fun ω => Y t ω ^ 2) Q ∧
      (∫ ω,Y t ω ^ 2 ∂Q) ≤ KQ := by
    have hp := integral_le_under_square_density hD₁m hD₁₀ hD₁₂ (hY₂ t)
    rw [hQ]
    refine ⟨hp.1,hp.2.trans ?_⟩
    change J * Real.sqrt (∫ ω,(Y t ω ^ 2)^2 ∂P) ≤ J * Real.sqrt K
    simp only [← pow_mul]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hK t)) (Real.sqrt_nonneg _)
  refine ⟨K+2,J*Real.sqrt (K+1),Real.sqrt (∫ ω,D₂ ω ^ 2 ∂Q)*Real.sqrt KQ,?_,?_,?_⟩
  · intro t
    refine ⟨(hYP₂ t).integrable one_le_two,?_⟩
    calc
      _ ≤ ∫ ω,Y t ω ^ 2+1 ∂P := integral_mono ((hYP₂ t).integrable one_le_two)
        ((hYi₂ t).add (integrable_const 1)) (fun ω => by nlinarith [sq_nonneg (Y t ω-1)])
      _ ≤ _ := by
        rw [integral_add (hYi₂ t) (integrable_const 1)]
        simp only [integral_const,probReal_univ,one_smul]
        linarith [hb₂ t]
  · intro t
    have hp := integral_le_under_square_density hD₁m hD₁₀ hD₁₂ (hYP₂ t)
    rw [hQ]
    exact ⟨hp.1,hp.2.trans <| mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hb₂ t)) (Real.sqrt_nonneg _)⟩
  · intro t
    have hm : MemLp (Y t) 2 Q :=
      (memLp_two_iff_integrable_sq (hY t).aestronglyMeasurable).2 (hQ₂ t).1
    have hp := integral_le_under_square_density hD₂m hD₂₀ hD₂₂ hm
    rw [hR]
    exact ⟨hp.1,hp.2.trans <| mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hQ₂ t).2) (Real.sqrt_nonneg _)⟩

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.integral_le_under_square_density
#print axioms RoughHeston.GirsanovPort.uniform_necessary_moments_under_two_tilts
