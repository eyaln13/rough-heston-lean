import FocalDriftEnergy
import SizeBiasBrownianClock

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Interval Topology

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} {H : ℝ≥0} {B Z U X C : ℝ≥0 → Ω → ℝ} {ε σ : ℝ}

local instance focalTimeMeasureFinite (t : ℝ≥0) : IsFiniteMeasure (hestonTimeMeasure t) := by
  rw [hestonTimeMeasure_eq_horizon]
  infer_instance

private theorem mass_has_mean (hZ : Martingale Z F μ) (hStart : Z 0 =ᵐ[μ] fun _ => ε) (t : ℝ≥0) :
    (∫ ω, Z t ω ∂μ) = ε := by
  have he := hZ.setIntegral_eq (show (0 : ℝ≥0) ≤ t from zero_le)
    (MeasurableSet.univ : MeasurableSet[F 0] (univ : Set Ω))
  simp only [Measure.restrict_univ] at he
  rw [← he, integral_congr_ae hStart]
  simp

private theorem focalMass_integrable_physical (hZ : Martingale Z F μ)
    (hStart : Z 0 =ᵐ[μ] fun _ => ε) (hNonneg : ∀ t, ∀ᵐ ω ∂μ, 0 ≤ Z t ω)
    (hZm : Measurable (Function.uncurry Z)) :
    Integrable (Function.uncurry Z) ((hestonTimeMeasure H).prod μ) := by
  let θ := hestonTimeMeasure H
  refine ⟨hZm.aestronglyMeasurable, ?_⟩
  change (∫⁻ p, ‖Z p.1 p.2‖ₑ ∂θ.prod μ) < ∞
  rw [lintegral_prod (fun p : ℝ≥0 × Ω => ‖Z p.1 p.2‖ₑ) hZm.enorm.aemeasurable]
  have h (t : ℝ≥0) : (∫⁻ ω, ‖Z t ω‖ₑ ∂μ) = ENNReal.ofReal ε := by
    have he : (fun ω => ‖Z t ω‖ₑ) =ᵐ[μ] fun ω => ENNReal.ofReal (Z t ω) :=
      (hNonneg t).mono fun _ => Real.enorm_eq_ofReal
    rw [lintegral_congr_ae he, ← ofReal_integral_eq_lintegral_ofReal (hZ.integrable t) (hNonneg t), mass_has_mean hZ hStart]
  simp only [h, lintegral_const]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

private theorem focalDriverDrift_mul_mass {z u x σ : ℝ} (hz : z ≠ 0) :
    z * (σ * u / (z * Real.sqrt x)) = σ * u / Real.sqrt x := by
  by_cases hx : Real.sqrt x = 0
  · simp [hx]
  · field_simp

omit [IsProbabilityMeasure μ] in
private theorem finiteBrownianOn_time_memLp (hB : MathFinBridge.BrownianOn μ F H B)
    (t : ℝ≥0) (ht : t ≤ H) : MemLp (B t) 2 μ := by
  have hm (s : ℝ≥0) : Measurable (B s) := ((hB.adapted s).mono (F.le s)).measurable
  have hd : HasLaw (B t - B 0) (gaussianReal 0 (t - 0)) μ :=
    ⟨((hm t).sub (hm 0)).aemeasurable, hB.normal_increment 0 t zero_le ht⟩
  have hi : MemLp (B t - B 0) 2 μ := hd.memLp (memLp_id_gaussianReal 2)
  refine hi.ae_eq (hB.zero_at_start.mono ?_)
  intro ω hw
  change B t ω - B 0 ω = B t ω
  rw [show B 0 ω = 0 from hw, sub_zero]

/-- For the actual focal-cluster cross bracket, terminal mass bias
preserves the supplied usual filtration and changes the Brownian driver
by the stated drift. The square energy is derived from the old law. -/
theorem focalDriverDrift_sizeBiasedBrownian
    [F.IsComplete μ] [F.IsRightContinuous]
    (hB : MathFinBridge.BrownianOn μ F H B)
    (hZ : Martingale Z F μ) (hC : Martingale (fun t => Z t * Z t - C t) F μ)
    (hε : 0 < ε) (hStart : Z 0 =ᵐ[μ] fun _ => ε) (hZ₂ : MemLp (Z H) 2 μ)
    (hZcont : ∀ ω, Continuous (fun t => Z t ω))
    (hCcont : ∀ ω, Continuous (fun t => C t ω))
    (hPos : ∀ᵐ ω ∂μ, ∀ t ≤ H, 0 < Z t ω)
    (hNonneg : ∀ t, ∀ᵐ ω ∂μ, 0 ≤ Z t ω)
    (hMono : ∀ᵐ ω ∂μ, Monotone (fun t => C t ω))
    (hZpred : IsStronglyPredictable F Z) (hUpred : IsStronglyPredictable F U)
    (hXpred : IsStronglyPredictable F X)
    (hParts : ∀ᵐ ω ∂μ, ∀ t ≤ H, 0 ≤ U t ω ∧ U t ω ≤ X t ω)
    (hUι : Integrable (Function.uncurry U) ((hestonTimeMeasure H).prod μ))
    (hDensity : ∀ᵐ ω ∂μ, ∀ t ≤ H, C t ω =
      ∫ r in (0 : ℝ)..(t : ℝ), σ ^ 2 * U r.toNNReal ω)
    (hCross : Martingale (fun t ω => Z (min t H) ω * B (min t H) ω -
      ∫ r, σ * U r ω / Real.sqrt (X r ω) ∂hestonTimeMeasure (min t H)) F μ) :
    let Q := sizeBiasedLaw μ (Z H) ε
    let g := focalDriverDrift σ Z U X
    IsProbabilityMeasure Q ∧ Q ≪ μ ∧ μ ≪ Q ∧
      Integrable (fun p : ℝ≥0 × Ω => g p.1 p.2 ^ 2) ((hestonTimeMeasure H).prod Q) ∧
      ∃ W : ℝ≥0 → Ω → ℝ, MathFinBridge.BrownianOn Q F H W ∧
        ∀ᵐ ω ∂Q, ∀ t ≤ H, W t ω = B t ω - ∫ r, g r ω ∂hestonTimeMeasure t := by
  let Q := sizeBiasedLaw μ (Z H) ε
  let θ := hestonTimeMeasure H
  let g := focalDriverDrift σ Z U X
  have hQ : IsProbabilityMeasure Q :=
    sizeBiasedLaw_isProbabilityMeasure hε (hZ.integrable H) (hNonneg H) (mass_has_mean hZ hStart H)
  have : IsProbabilityMeasure Q := hQ
  have hZH : Measurable (Z H) := ((hZ.stronglyAdapted H).mono (F.le H)).measurable
  have hQP : Q ≪ μ := withDensity_absolutelyContinuous μ _
  have hPQ : μ ≪ Q := withDensity_absolutelyContinuous' (hZH.div_const ε).ennreal_ofReal.aemeasurable
    (hPos.mono fun ω hw => (ENNReal.ofReal_pos.mpr (div_pos (hw H le_rfl) hε)).ne')
  have hPg : IsStronglyPredictable F g := focalDriverDrift_predictable hZpred hUpred hXpred
  have hZm : Measurable (Function.uncurry Z) := (hZpred.mono F.predictable_le_prod).measurable
  have hgm : Measurable (Function.uncurry g) := (hPg.mono F.predictable_le_prod).measurable
  have hWP : Integrable (fun p : ℝ≥0 × Ω => Z p.1 p.2 * g p.1 p.2 ^ 2) (θ.prod μ) :=
    focalDriverDrift_weighted_square_integrable hZ hC hStart hZ₂ hZcont hCcont hPos hMono
      hZpred hUpred hXpred hParts hUι hDensity
  have hgQ : Integrable (fun p : ℝ≥0 × Ω => g p.1 p.2 ^ 2) (θ.prod Q) :=
    sizeBiasedLaw_integrable_square_of_weighted hZ hε hNonneg hZm hPg hWP
  have hgc : Integrable (fun p : ℝ≥0 × Ω => Z p.1 p.2 * g p.1 p.2) (θ.prod μ) := by
    have hMass : Integrable (Function.uncurry Z) (θ.prod μ) := focalMass_integrable_physical hZ hStart hNonneg hZm
    have hNN : ∀ᵐ p ∂θ.prod μ, 0 ≤ Z p.1 p.2 := by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_le measurable_const hZm)).2
      exact ae_of_all _ hNonneg
    refine (hWP.add hMass).mono' (hZm.mul hgm).aestronglyMeasurable ?_
    filter_upwards [hNN] with p hp
    change ‖Z p.1 p.2 * g p.1 p.2‖ ≤ Z p.1 p.2 * g p.1 p.2 ^ 2 + Z p.1 p.2
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp]
    calc
      _ ≤ Z p.1 p.2 * (|g p.1 p.2| ^ 2 + 1) :=
        mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (|g p.1 p.2| - 1)]) hp
      _ = _ := by rw [sq_abs]; ring
  have hgte : Integrable (fun p : ℝ≥0 × Ω => g p.1 p.2 * Z H p.2) (θ.prod μ) := by
    have hi : Integrable (Function.uncurry g) (θ.prod Q) :=
      ((memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).2 hgQ).integrable one_le_two
    unfold Q sizeBiasedLaw at hi
    rw [prod_withDensity_right (hZH.div_const ε).ennreal_ofReal] at hi
    have hm : Measurable (fun p : ℝ≥0 × Ω => ENNReal.ofReal (Z H p.2 / ε)) :=
      ((hZH.comp measurable_snd).div_const ε).ennreal_ofReal
    have hi' := (integrable_withDensity_iff_integrable_smul' hm (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).1 hi
    apply (hi'.const_mul ε).congr
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := θ) (ν := μ)).ae (hNonneg H)] with p hp
    change ε * ((ENNReal.ofReal (Z H p.2 / ε)).toReal * g p.1 p.2) = g p.1 p.2 * Z H p.2
    rw [ENNReal.toReal_ofReal (div_nonneg hp hε.le)]
    field_simp
  have hCAdapt : IsStronglyPredictable F (fun t ω => Z t ω * g t ω) := hZpred.mul hPg
  have hCrossEq (t : ℝ≥0) : (fun ω => Z (min t H) ω * B (min t H) ω -
      ∫ r, σ * U r ω / Real.sqrt (X r ω) ∂hestonTimeMeasure (min t H)) =ᵐ[μ]
      fun ω => Z (min t H) ω * B (min t H) ω -
      ∫ r, Z r ω * g r ω ∂hestonTimeMeasure (min t H) := by
    filter_upwards [hPos] with ω hw
    congr 1
    apply integral_congr_ae
    rw [hestonTimeMeasure_eq_horizon]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc (a := (0 : ℝ≥0)) (b := min t H))] with r hr
    exact (focalDriverDrift_mul_mass ((hw r (hr.2.trans (min_le_right _ _))).ne')).symm
  have hCross' : Martingale (fun t ω => Z (min t H) ω * B (min t H) ω -
      ∫ r, Z r ω * g r ω ∂hestonTimeMeasure (min t H)) F μ := by
    refine ⟨fun t => ?_, fun s t hst => ?_⟩
    · apply (((hZ.stronglyMeasurable (min t H)).mul (hB.adapted (min t H))).sub
        (stronglyAdapted_timePrimitive hCAdapt (min t H))).mono (F.mono (min_le_left t H))
    · exact (condExp_congr_ae (hCrossEq t).symm).trans ((hCross.condExp_ae_eq hst).trans (hCrossEq s))
  have hZall (t : ℝ≥0) (ht : t ≤ H) : MemLp (Z t) 2 μ :=
    (hZ₂.condExp one_le_two).ae_eq (hZ.condExp_ae_eq ht)
  obtain ⟨_, hN⟩ := sizeBiasedShift_martingale hZ hε hStart (hNonneg H) hB.adapted
    hZall (finiteBrownianOn_time_memLp hB) hPg hCross' hgte hgc
  have hNull (A : Set Ω) (_ : MeasurableSet A) (hA : Q A = 0) : MeasurableSet[F 0] A :=
    Filtration.IsComplete.measurableSet_of_null (hPQ hA) 0
  exact ⟨hQ, hQP, hPQ, hgQ, sizeBiasedShift_brownianOn hB hε hZH (hNonneg H) hZ₂ hPg hNull hgQ hN⟩

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.focalDriverDrift_sizeBiasedBrownian
