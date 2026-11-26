import BirthTraceMartingaleShift
import SizeBiasConditionedBirthExpectation
import TwoTiltVarianceMoments

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace RoughHeston.GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 m} {A : Set Ω} {b r : ℝ≥0}

local notation "G" => birthTraceFiltration F b A
local notation "μ" => birthTraceLaw P A

set_option maxHeartbeats 900000 in
/-- The birth-conditional old-law Laplace complement has the original
birth-event expectation after the actual size bias on the trace. -/
theorem point_test_trace_birth_sizeBias_le
    (hA : MeasurableSet[F b] A) (hPA : 0<P A)
    {Z : ℝ≥0 → A → ℝ} (hZ : Martingale Z G μ)
    (hZ₀ : ∀ t, ∀ᵐ ω ∂μ, 0≤Z t ω) {ε : ℝ} (hε : 0<ε)
    (hZb : Z 0 =ᵐ[μ] fun _ => ε)
    {Y : Ω → ℝ} (hY : Measurable Y) (hY₀ : ∀ ω, 0≤Y ω) {q : ℝ} (hq : 0≤q) :
    (∫ ω : A, 1-P[(fun x => Real.exp (-q*Y x))|F b] ω ∂sizeBiasedLaw μ (Z r) ε) ≤
      (boundaryConditionedMeasure P A).real {ω | 0<Y ω} := by
  let _ : IsProbabilityMeasure μ := birthTraceLaw_isProbability (F.le b A hA) hPA
  let g (ω : Ω) := 1-P[(fun x => Real.exp (-q*Y x))|F b] ω
  have hg : StronglyMeasurable[F b] g := stronglyMeasurable_const.sub stronglyMeasurable_condExp
  have hg' : StronglyMeasurable[G 0] (fun ω : A => g ω) := by
    have hgg : StronglyMeasurable[F (b+0)] g :=
      (congrArg (fun t => StronglyMeasurable[F t] g) (add_zero b)).mpr hg
    exact hgg.comp_measurable (Measurable.of_comap_le le_rfl)
  have hSub := birthTraceLaw_map (P:=P) (F.le b A hA)
  change (∫ ω : A,g ω ∂sizeBiasedLaw μ (Z r) ε)≤_
  rw [integral_sizeBiasedLaw_eq_at_birth hZ hε hZ₀ (zero_le : 0≤r) hZb hg']
  rw [←integral_map measurable_subtype_coe.aemeasurable (hg.mono (F.le b)).aestronglyMeasurable,hSub]
  let _ : IsProbabilityMeasure (boundaryConditionedMeasure P A) := boundaryConditionedMeasure_isProbability hPA
  have hc : Martingale (fun (_ : ℝ≥0) (_ : Ω) => (1:ℝ)) F (boundaryConditionedMeasure P A) :=
    martingale_const F (boundaryConditionedMeasure P A) 1
  have hb := point_test_conditioned_birth_sizeBias_le hA hPA (le_rfl : b≤b) hc
    (fun _ => ae_of_all _ fun _ => zero_le_one) (by norm_num : (0:ℝ)<1)
    EventuallyEq.rfl hY hY₀ hq
  simpa [sizeBiasedLaw,g] using hb

/-- Uniform physical fourth moments give uniform trace fourth moments.
The only constant is the inverse original birth probability. -/
theorem birthTrace_fourth_moment_bounded
    (hA : MeasurableSet[F b] A) (hPA : 0<P A)
    {Y : ℝ≥0 → Ω → ℝ} {K : ℝ}
    (hYm : ∀ t, Measurable (Y t))
    (hY₄ : ∀ t, Integrable (fun ω => Y t ω ^ 4) P)
    (hK : ∀ t, (∫ ω, Y t ω ^ 4 ∂P)≤K) :
    ∀ t, Integrable (fun ω : A => Y (b+t) ω ^ 4) μ ∧
      (∫ ω : A,Y (b+t) ω ^ 4 ∂μ)≤K/P.real A := by
  intro t
  let f (ω : Ω) := Y (b+t) ω ^ 4
  have hm : Measurable f := (hYm (b+t)).pow_const 4
  have hp : Integrable f P := hY₄ (b+t)
  have hf₂ : MemLp f 1 P := memLp_one_iff_integrable.mpr hp
  have hint := memLp_one_iff_integrable.mp (birthTrace_memLp hA hPA hf₂)
  refine ⟨hint,?_⟩
  change (∫ ω : A,f ω ∂μ) ≤ _
  rw [←integral_map measurable_subtype_coe.aemeasurable hm.aestronglyMeasurable,
    birthTraceLaw_map (F.le b A hA),integral_boundaryConditionedMeasure]
  exact div_le_div_of_nonneg_right
    ((setIntegral_le_integral hp (ae_of_all _ fun ω => by dsimp [f]; positivity)).trans (hK (b+t)))
    ENNReal.toReal_nonneg

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.point_test_trace_birth_sizeBias_le
#print axioms RoughHeston.GirsanovPort.birthTrace_fourth_moment_bounded
