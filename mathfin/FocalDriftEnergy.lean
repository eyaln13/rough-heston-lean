import SizeBiasEnergy
import MartingaleEntropyLocalization

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Interval Topology

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} {H : ℝ≥0} {Z U X C : ℝ≥0 → Ω → ℝ} {ε σ : ℝ}

noncomputable def focalDriverDrift (σ : ℝ) (Z U X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  σ * U t ω / (Z t ω * Real.sqrt (X t ω))

theorem focalDriverDrift_predictable
    (hZ : IsStronglyPredictable F Z) (hU : IsStronglyPredictable F U) (hX : IsStronglyPredictable F X) :
    IsStronglyPredictable F (focalDriverDrift σ Z U X) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let z : ℝ≥0 × Ω → ℝ := Function.uncurry Z
  let u : ℝ≥0 × Ω → ℝ := Function.uncurry U
  let x : ℝ≥0 × Ω → ℝ := Function.uncurry X
  have hz : Measurable z := hZ.measurable
  have hu : Measurable u := hU.measurable
  have hx : Measurable x := hX.measurable
  exact ((hu.const_mul σ).div (hz.mul (Real.continuous_sqrt.measurable.comp hx))).stronglyMeasurable

/-- The focal cluster is a nonnegative part of the total variance.
The resulting cross-bracket drift has the corresponding scalar energy bound. -/
theorem focalDriverDrift_weighted_sq_le {z u x σ : ℝ} (hz : 0 < z) (hu : 0 ≤ u) (hux : u ≤ x) :
    z * (σ * u / (z * Real.sqrt x)) ^ 2 ≤ σ ^ 2 * u / z := by
  rcases eq_or_lt_of_le (hu.trans hux) with h | hx
  · have hu0 : u = 0 := le_antisymm (hux.trans h.ge) hu
    simp [hu0]
  have hzz : z ≠ 0 := hz.ne'
  have hxx : x ≠ 0 := hx.ne'
  calc
    _ = σ ^ 2 * u ^ 2 / (z * x) := by
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hx.le]
      field_simp
    _ ≤ σ ^ 2 * (u * x) / (z * x) := by
      apply div_le_div_of_nonneg_right _ (mul_nonneg hz.le hx.le)
      exact mul_le_mul_of_nonneg_left (by rw [pow_two]; exact mul_le_mul_of_nonneg_left hux hu) (sq_nonneg _)
    _ = _ := by field_simp

omit [IsProbabilityMeasure μ] in
private theorem physical_prod_map [IsFiniteMeasure μ] :
    (hestonTimeMeasure H).prod μ =
      Measure.map (Prod.map Real.toNNReal (id : Ω → Ω)) ((volume.restrict (Ioc (0 : ℝ) (H : ℝ))).prod μ) := by
  let θ := volume.restrict (Ioc (0 : ℝ) (H : ℝ))
  rw [← Measure.map_prod_map θ μ continuous_real_toNNReal.measurable measurable_id, Measure.map_id]
  congr 1
  rw [hestonTimeMeasure, Measure.restrict_congr_set Ioo_ae_eq_Ioc]

private theorem physical_prod_integrable_iff
    {f : ℝ≥0 × Ω → ℝ} (hf : Measurable f) :
    Integrable f ((hestonTimeMeasure H).prod μ) ↔
      Integrable (fun p : ℝ × Ω => f (p.1.toNNReal, p.2)) ((volume.restrict (Ioc (0 : ℝ) (H : ℝ))).prod μ) := by
  rw [physical_prod_map]
  have hm : Measurable (Prod.map Real.toNNReal (id : Ω → Ω)) :=
    (continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd
  exact integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable

omit [IsProbabilityMeasure μ] in
private theorem physical_prod_ae_of_path
    [IsFiniteMeasure μ]
    {p : ℝ≥0 → Ω → Prop} (hp : ∀ᵐ ω ∂μ, ∀ t ≤ H, p t ω) :
    ∀ᵐ q ∂(hestonTimeMeasure H).prod μ, p q.1 q.2 := by
  let θ := hestonTimeMeasure H
  have : IsFiniteMeasure θ := by
    rw [show θ = MathFin.ItoIntegralCLM.timeMeasureHorizon H from hestonTimeMeasure_eq_horizon H]
    infer_instance
  have hθ : ∀ᵐ t ∂θ, t ≤ H := by
    rw [show θ = MathFin.ItoIntegralL2.timeMeasure.restrict (Ioc 0 H) from hestonTimeMeasure_eq_horizon H]
    exact (ae_restrict_mem measurableSet_Ioc).mono fun _ ht => ht.2
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := θ) (ν := μ)).ae hθ,
      (Measure.quasiMeasurePreserving_snd (μ := θ) (ν := μ)).ae hp] with q hq hω
  exact hω q.1 hq

/-- The focal mass times the squared cross-bracket drift is integrable
on physical time under the old law. -/
theorem focalDriverDrift_weighted_square_integrable
    [F.IsComplete μ] [F.IsRightContinuous]
    (hZ : Martingale Z F μ) (hC : Martingale (fun t => Z t * Z t - C t) F μ)
    (hStart : Z 0 =ᵐ[μ] fun _ => ε) (hZ₂ : MemLp (Z H) 2 μ)
    (hZcont : ∀ ω, Continuous (fun t => Z t ω))
    (hCcont : ∀ ω, Continuous (fun t => C t ω))
    (hPos : ∀ᵐ ω ∂μ, ∀ t ≤ H, 0 < Z t ω)
    (hMono : ∀ᵐ ω ∂μ, Monotone (fun t => C t ω))
    (hZpred : IsStronglyPredictable F Z) (hUpred : IsStronglyPredictable F U)
    (hXpred : IsStronglyPredictable F X)
    (hParts : ∀ᵐ ω ∂μ, ∀ t ≤ H, 0 ≤ U t ω ∧ U t ω ≤ X t ω)
    (hUι : Integrable (Function.uncurry U) ((hestonTimeMeasure H).prod μ))
    (hDensity : ∀ᵐ ω ∂μ, ∀ t ≤ H, C t ω =
      ∫ r in (0 : ℝ)..(t : ℝ), σ ^ 2 * U r.toNNReal ω) :
    Integrable (fun p : ℝ≥0 × Ω => Z p.1 p.2 * focalDriverDrift σ Z U X p.1 p.2 ^ 2)
      ((hestonTimeMeasure H).prod μ) := by
  let g := focalDriverDrift σ Z U X
  let d (p : ℝ≥0 × Ω) := σ ^ 2 * U p.1 p.2
  let dd (r : ℝ) (ω : Ω) := d (r.toNNReal, ω)
  have hZmeas : Measurable (Function.uncurry Z) := (hZpred.mono F.predictable_le_prod).measurable
  have hUmeas : Measurable (Function.uncurry U) := (hUpred.mono F.predictable_le_prod).measurable
  have hd : Measurable d := hUmeas.const_mul _
  have hdd : Measurable (Function.uncurry dd) :=
    hd.comp ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)
  have hDd : Integrable (Function.uncurry dd) ((volume.restrict (Ioc (0 : ℝ) (H : ℝ))).prod μ) :=
    (physical_prod_integrable_iff hd).1 (hUι.const_mul _)
  let θ := volume.restrict (Ioc (0 : ℝ) (H : ℝ))
  have hθ : ∀ᵐ r ∂θ, r ∈ Ioc (0 : ℝ) (H : ℝ) := ae_restrict_mem measurableSet_Ioc
  have hProdR : ∀ᵐ p ∂θ.prod μ, p.1 ∈ Ioc (0 : ℝ) (H : ℝ) :=
    (Measure.quasiMeasurePreserving_fst (μ := θ) (ν := μ)).ae hθ
  have hProdU : ∀ᵐ p ∂θ.prod μ, ∀ t ≤ H, 0 ≤ U t p.2 ∧ U t p.2 ≤ X t p.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := θ) (ν := μ)).ae hParts
  have hDd₀ : 0 ≤ᵐ[θ.prod μ] Function.uncurry dd := by
    filter_upwards [hProdR, hProdU] with p hr hU
    have hR : p.1.toNNReal ≤ H := by
      have he : (p.1.toNNReal : ℝ) = p.1 := Real.coe_toNNReal _ hr.1.le
      have hle : (p.1.toNNReal : ℝ) ≤ H := he.trans_le hr.2
      exact_mod_cast hle
    exact mul_nonneg (sq_nonneg _) (hU _ hR).1
  have hRatio := integrable_bracket_ratio_of_continuous_martingale hZ hC hStart hZ₂ hZcont hCcont
    hPos hMono hZmeas hdd hDd hDd₀ hDensity
  have hRatioPhys : Integrable (fun p : ℝ≥0 × Ω => d p / Z p.1 p.2) ((hestonTimeMeasure H).prod μ) :=
    (physical_prod_integrable_iff (hd.div hZmeas)).2 hRatio
  have hgPred : IsStronglyPredictable F g := focalDriverDrift_predictable hZpred hUpred hXpred
  have hgMeas : Measurable (Function.uncurry g) := (hgPred.mono F.predictable_le_prod).measurable
  refine hRatioPhys.mono' (hZmeas.mul (hgMeas.pow_const 2)).aestronglyMeasurable ?_
  filter_upwards [physical_prod_ae_of_path hPos, physical_prod_ae_of_path hParts] with p hz hu
  change ‖Z p.1 p.2 * g p.1 p.2 ^ 2‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hz.le (sq_nonneg _))]
  exact focalDriverDrift_weighted_sq_le hz hu.1 hu.2

/-- Combining the entropy clock with the exact conditional size-bias
density gives the physical square energy of the focal cross drift. -/
theorem focalDriverDrift_square_integrable_sizeBias
    [F.IsComplete μ] [F.IsRightContinuous]
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
    [IsProbabilityMeasure (sizeBiasedLaw μ (Z H) ε)] :
    Integrable (fun p : ℝ≥0 × Ω => focalDriverDrift σ Z U X p.1 p.2 ^ 2)
      ((hestonTimeMeasure H).prod (sizeBiasedLaw μ (Z H) ε)) :=
  sizeBiasedLaw_integrable_square_of_weighted hZ hε hNonneg (hZpred.mono F.predictable_le_prod).measurable
    (focalDriverDrift_predictable hZpred hUpred hXpred)
    (focalDriverDrift_weighted_square_integrable hZ hC hStart hZ₂ hZcont hCcont hPos hMono
      hZpred hUpred hXpred hParts hUι hDensity)

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.focalDriverDrift_square_integrable_sizeBias
#print axioms RoughHeston.GirsanovPort.focalDriverDrift_weighted_square_integrable
