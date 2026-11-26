import ProductKernelEnergy
import SizeBiasedBurst
import StochasticFoundation
import MathFin.Probability.Analysis.FiniteMeasureCauchySchwarz

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} {H : ℝ≥0} {Z : ℝ≥0 → Ω → ℝ} {ε : ℝ}

local instance timeMeasureFinite (t : ℝ≥0) : IsFiniteMeasure (hestonTimeMeasure t) := by
  rw [hestonTimeMeasure_eq_horizon]
  infer_instance

/-- The terminal mass tilt uses the mass at the observation time in
the integral of a payoff measurable in the full supplied filtration. -/
theorem sizeBiasedLaw_setIntegral_of_adapted (hZ : Martingale Z F μ) (hε : 0 < ε)
    (hNonneg : ∀ᵐ ω ∂μ, 0 ≤ Z H ω) {t : ℝ≥0} (ht : t ≤ H)
    {f : Ω → ℝ} (hf : StronglyMeasurable[F t] f)
    (hfZ : Integrable (fun ω => f ω * Z H ω) μ) {E : Set Ω} (hE : MeasurableSet[F t] E) :
    (∫ ω in E, f ω ∂sizeBiasedLaw μ (Z H) ε) =
      (∫ ω in E, Z t ω * f ω ∂μ) / ε := by
  have hEμ := F.le t E hE
  have hm : Measurable (Z H) := ((hZ.stronglyAdapted H).mono (F.le H)).measurable
  rw [← integral_indicator hEμ, integral_sizeBiasedLaw_eq hε hm hNonneg]
  have hind : (fun ω => Z H ω * E.indicator f ω) = E.indicator (fun ω => f ω * Z H ω) := by
    funext ω
    by_cases hω : ω ∈ E <;> simp [hω, mul_comm]
  rw [hind, integral_indicator hEμ, ← setIntegral_condExp (F.le t) hfZ hE]
  congr 1
  apply integral_congr_ae
  apply ae_restrict_of_ae
  have hpull := condExp_mul_of_stronglyMeasurable_left hf hfZ (hZ.integrable H)
  filter_upwards [hpull, hZ.condExp_ae_eq ht] with ω hp hω
  change μ[f * Z H | F t] ω = _
  rw [hp]
  simp [hω, mul_comm]

private theorem timeMeasure_restrict {s t : ℝ≥0} (hst : s ≤ t) :
    hestonTimeMeasure s = (hestonTimeMeasure t).restrict (Ioc 0 s) := by
  simp only [hestonTimeMeasure_eq_horizon, MathFin.ItoIntegralCLM.timeMeasureHorizon]
  rw [Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr (Ioc_subset_Ioc le_rfl hst)]

private theorem timeMeasure_split {s t H : ℝ≥0} (hst : s ≤ t) (ht : t ≤ H) :
    hestonTimeMeasure t = hestonTimeMeasure s + (hestonTimeMeasure H).restrict (Ioc s t) := by
  rw [timeMeasure_restrict ht, timeMeasure_restrict (hst.trans ht)]
  rw [← Ioc_union_Ioc_eq_Ioc (show (0 : ℝ≥0) ≤ s from zero_le) hst]
  exact Measure.restrict_union
    (disjoint_left.mpr fun _ hx hy => (not_lt_of_ge hx.2) hy.1) measurableSet_Ioc

private theorem setIntegral_timePrimitive_sub {η : Measure Ω} [IsFiniteMeasure η]
    {g : ℝ≥0 × Ω → ℝ} (hg : Integrable g ((hestonTimeMeasure H).prod η))
    {s t : ℝ≥0} (hst : s ≤ t) (ht : t ≤ H) (E : Set Ω) :
    (∫ ω in E, (∫ r, g (r, ω) ∂hestonTimeMeasure t) ∂η) -
        (∫ ω in E, (∫ r, g (r, ω) ∂hestonTimeMeasure s) ∂η) =
      ∫ r in Ioc s t, (∫ ω in E, g (r, ω) ∂η) ∂hestonTimeMeasure H := by
  have hprod (ν : Measure ℝ≥0) (hν : ν ≤ hestonTimeMeasure H) :
      Integrable g (ν.prod (η.restrict E)) :=
    hg.mono_measure (Measure.prod_mono hν Measure.restrict_le_self)
  have hsub (r : ℝ≥0) (hr : r ≤ H) : hestonTimeMeasure r ≤ hestonTimeMeasure H := by
    rw [timeMeasure_restrict hr]
    exact Measure.restrict_le_self
  have hs := hprod (hestonTimeMeasure s) (hsub s (hst.trans ht))
  have ht' := hprod (hestonTimeMeasure t) (hsub t ht)
  have hband := hprod ((hestonTimeMeasure H).restrict (Ioc s t)) Measure.restrict_le_self
  rw [← integral_prod_symm g ht', ← integral_prod_symm g hs, integral_prod g ht', integral_prod g hs,
    timeMeasure_split hst ht, integral_add_measure hs.integral_prod_left hband.integral_prod_left]
  exact add_sub_cancel_left _ _

/-- Integration over physical time preserves adaptedness of a
predictable process. -/
theorem stronglyAdapted_timePrimitive {g : ℝ≥0 → Ω → ℝ}
    (hg : IsStronglyPredictable F g) :
    StronglyAdapted F (fun t ω => ∫ r, g r ω ∂hestonTimeMeasure t) := by
  intro t
  let τ : Measure (Iic t) := (hestonTimeMeasure t).comap Subtype.val
  haveI : IsFiniteMeasure τ := by
    constructor
    exact (Measure.comap_apply_le _ _ MeasurableSet.univ.nullMeasurableSet).trans_lt (measure_lt_top _ _)
  have h := hg.isStronglyProgressive t
  letI : MeasurableSpace Ω := F t
  have hmeas := h.integral_prod_left' (μ := τ)
  convert hmeas using 1
  funext ω
  rw [show (∫ r : Iic t, g r ω ∂τ) = ∫ r in Iic t, g r ω ∂hestonTimeMeasure t
    from integral_subtype_comap (μ := hestonTimeMeasure t) (s := Iic t) measurableSet_Iic (fun r => g r ω)]
  have hs : (hestonTimeMeasure t).restrict (Iic t) = hestonTimeMeasure t := by
    simp only [hestonTimeMeasure_eq_horizon, MathFin.ItoIntegralCLM.timeMeasureHorizon]
    rw [Measure.restrict_restrict measurableSet_Iic, inter_eq_right.mpr Ioc_subset_Iic_self]
  rw [hs]

/-- The squared increments of an ordinary drift primitive are bounded
by the time mesh times its total square energy. -/
theorem physicalDrift_gridQuadraticSum_mesh_bound {g : ℝ≥0 → ℝ}
    (hg : AEStronglyMeasurable g (hestonTimeMeasure H))
    (hg₂ : Integrable (fun r => g r ^ 2) (hestonTimeMeasure H))
    (grid : ℕ →o ℝ≥0) (n : ℕ) (hn : grid n ≤ H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hmesh : ∀ k ∈ Finset.range n, (grid (k + 1) : ℝ) - (grid k : ℝ) ≤ δ) :
    (∑ k ∈ Finset.range n, ((∫ r, g r ∂hestonTimeMeasure (grid (k + 1))) -
      (∫ r, g r ∂hestonTimeMeasure (grid k))) ^ 2) ≤
      δ * ∫ r, g r ^ 2 ∂hestonTimeMeasure H := by
  have hg₁ := ((memLp_two_iff_integrable_sq hg).2 hg₂).integrable one_le_two
  let e (t : ℝ≥0) := ∫ r, g r ^ 2 ∂hestonTimeMeasure t
  have hsub {t : ℝ≥0} (ht : t ≤ H) : hestonTimeMeasure t ≤ hestonTimeMeasure H := by
    rw [timeMeasure_restrict ht]
    exact Measure.restrict_le_self
  have hcell (k : ℕ) (hk : k ∈ Finset.range n) :
      ((∫ r, g r ∂hestonTimeMeasure (grid (k + 1))) - (∫ r, g r ∂hestonTimeMeasure (grid k))) ^ 2 ≤
        δ * (e (grid (k + 1)) - e (grid k)) := by
    let a := grid k
    let b := grid (k + 1)
    let κ := (hestonTimeMeasure H).restrict (Ioc a b)
    have hab : a ≤ b := grid.monotone (Nat.le_succ k)
    have hb : b ≤ H := (grid.monotone (Nat.succ_le_of_lt (Finset.mem_range.mp hk))).trans hn
    have hκ : κ ≤ hestonTimeMeasure H := Measure.restrict_le_self
    have hsplit : hestonTimeMeasure b = hestonTimeMeasure a + κ := timeMeasure_split hab hb
    have hfst : (∫ r, g r ∂hestonTimeMeasure b) - (∫ r, g r ∂hestonTimeMeasure a) = ∫ r, g r ∂κ := by
      rw [hsplit, integral_add_measure (hg₁.mono_measure (hsub (hab.trans hb))) (hg₁.mono_measure hκ)]
      ring
    have hsnd : e b - e a = ∫ r, g r ^ 2 ∂κ := by
      change (∫ r, g r ^ 2 ∂hestonTimeMeasure b) - (∫ r, g r ^ 2 ∂hestonTimeMeasure a) = _
      rw [hsplit, integral_add_measure (hg₂.mono_measure (hsub (hab.trans hb))) (hg₂.mono_measure hκ)]
      ring
    have hκ' : κ = MathFin.ItoIntegralL2.timeMeasure.restrict (Ioc a b) := by
      simp only [κ, hestonTimeMeasure_eq_horizon, MathFin.ItoIntegralCLM.timeMeasureHorizon]
      rw [Measure.restrict_restrict measurableSet_Ioc,
        inter_eq_left.mpr (Ioc_subset_Ioc (show (0 : ℝ≥0) ≤ a from zero_le) hb)]
    have hmass : κ.real univ = (b : ℝ) - (a : ℝ) := by
      rw [hκ', Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter,
        MathFin.ItoIntegralL2.timeMeasure_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr (by exact_mod_cast hab))]
    have hL₂ : MemLp g 2 κ := (memLp_two_iff_integrable_sq (hg.mono_measure hκ)).2 (hg₂.mono_measure hκ)
    change ((∫ r, g r ∂hestonTimeMeasure b) - (∫ r, g r ∂hestonTimeMeasure a)) ^ 2 ≤ δ * (e b - e a)
    rw [hfst, hsnd]
    exact (MathFin.sq_integral_le_measureReal_mul hL₂).trans (mul_le_mul_of_nonneg_right
      (hmass.trans_le (hmesh k hk)) (integral_nonneg fun _ => sq_nonneg _))
  calc
    _ ≤ ∑ k ∈ Finset.range n, δ * (e (grid (k + 1)) - e (grid k)) := Finset.sum_le_sum hcell
    _ = δ * (e (grid n) - e (grid 0)) := by
      rw [← Finset.mul_sum, Finset.sum_range_sub (fun k => e (grid k))]
    _ ≤ _ := by
      have hz : 0 ≤ e (grid 0) := integral_nonneg fun _ => sq_nonneg _
      have hm : e (grid n) ≤ ∫ r, g r ^ 2 ∂hestonTimeMeasure H :=
        integral_mono_measure (hsub hn) (ae_of_all _ fun _ => sq_nonneg _) hg₂
      exact mul_le_mul_of_nonneg_left ((sub_le_self _ hz).trans hm) hδ

private theorem integrable_sizeBiased_of_mixed {A : Type*} [MeasurableSpace A]
    {η : Measure A} {z f : A → ℝ} (hε : 0 < ε) (hz : Measurable z)
    (hz₀ : ∀ᵐ x ∂η, 0 ≤ z x) (hf : Integrable (fun x => f x * z x) η) :
    Integrable f (sizeBiasedLaw η z ε) := by
  unfold sizeBiasedLaw
  apply (integrable_withDensity_iff_integrable_smul' (hz.div_const ε).ennreal_ofReal
    (ae_of_all η fun _ => ENNReal.ofReal_lt_top)).2
  apply (hf.div_const ε).congr
  filter_upwards [hz₀] with x hx
  rw [ENNReal.toReal_ofReal (div_nonneg hx hε.le), smul_eq_mul]
  ring

/-- Under the terminal focal mass tilt, the common driver with its
cross-bracket drift subtracted is a martingale on the original joint
filtration. The compensator input is the old-law cross bracket; the
two mixed-integrability assumptions justify Fubini for the signed
drift before and after changing measure. -/
theorem sizeBiasedShift_martingale {B g : ℝ≥0 → Ω → ℝ}
    (hZ : Martingale Z F μ) (hε : 0 < ε) (hZ₀ : Z 0 =ᵐ[μ] fun _ => ε)
    (hNonneg : ∀ᵐ ω ∂μ, 0 ≤ Z H ω) (hB : StronglyAdapted F B)
    (hZ₂ : ∀ t ≤ H, MemLp (Z t) 2 μ) (hB₂ : ∀ t ≤ H, MemLp (B t) 2 μ)
    (hg : IsStronglyPredictable F g)
    (hcross : Martingale (fun t ω => Z (min t H) ω * B (min t H) ω -
      ∫ r, Z r ω * g r ω ∂hestonTimeMeasure (min t H)) F μ)
    (hgTerm : Integrable (fun p : ℝ≥0 × Ω => g p.1 p.2 * Z H p.2) ((hestonTimeMeasure H).prod μ))
    (hgCross : Integrable (fun p : ℝ≥0 × Ω => Z p.1 p.2 * g p.1 p.2) ((hestonTimeMeasure H).prod μ)) :
    let Q := sizeBiasedLaw μ (Z H) ε
    IsProbabilityMeasure Q ∧ Martingale (fun t ω => B (min t H) ω -
      ∫ r, g r ω ∂hestonTimeMeasure (min t H)) F Q := by
  let Q := sizeBiasedLaw μ (Z H) ε
  have hZH : Measurable (Z H) := ((hZ.stronglyAdapted H).mono (F.le H)).measurable
  have hmean : (∫ ω, Z H ω ∂μ) = ε := by
    have he := hZ.setIntegral_eq (show (0 : ℝ≥0) ≤ H from zero_le)
      (MeasurableSet.univ : MeasurableSet[F 0] (univ : Set Ω))
    simp only [Measure.restrict_univ] at he
    rw [← he, integral_congr_ae hZ₀, integral_const]
    simp
  have hQ : IsProbabilityMeasure Q := sizeBiasedLaw_isProbabilityMeasure hε (hZ.integrable H) hNonneg hmean
  letI : IsProbabilityMeasure Q := hQ
  let gQ := Function.uncurry g
  let c (r : ℝ≥0) (ω : Ω) := Z r ω * g r ω
  let cP := Function.uncurry c
  have hCrossProd : Integrable cP ((hestonTimeMeasure H).prod μ) := hgCross
  have hMix (t : ℝ≥0) (ht : t ≤ H) : Integrable (fun ω => B t ω * Z H ω) μ :=
    (hB₂ t ht).integrable_mul (hZ₂ H le_rfl)
  have hBg (t : ℝ≥0) (ht : t ≤ H) : Integrable (B t) Q :=
    integrable_sizeBiased_of_mixed hε hZH hNonneg (hMix t ht)
  have hgQ : Integrable gQ ((hestonTimeMeasure H).prod Q) := by
    unfold Q sizeBiasedLaw
    rw [prod_withDensity_right (hZH.div_const ε).ennreal_ofReal]
    exact integrable_sizeBiased_of_mixed hε (hZH.comp measurable_snd)
      (Measure.quasiMeasurePreserving_snd.ae hNonneg) hgTerm
  let D (t : ℝ≥0) (ω : Ω) := ∫ r, g r ω ∂hestonTimeMeasure t
  let C (t : ℝ≥0) (ω : Ω) := ∫ r, c r ω ∂hestonTimeMeasure t
  let N (t : ℝ≥0) (ω : Ω) := B (min t H) ω - D (min t H) ω
  have htime (t : ℝ≥0) (ht : t ≤ H) : hestonTimeMeasure t ≤ hestonTimeMeasure H := by
    rw [timeMeasure_restrict ht]
    exact Measure.restrict_le_self
  have hDQ (t : ℝ≥0) (ht : t ≤ H) : Integrable (D t) Q :=
    (hgQ.mono_measure (Measure.prod_mono (htime t ht) le_rfl)).integral_prod_right
  have hCP (t : ℝ≥0) (ht : t ≤ H) : Integrable (C t) μ :=
    (hCrossProd.mono_measure (Measure.prod_mono (htime t ht) le_rfl)).integral_prod_right
  have hZB (t : ℝ≥0) (ht : t ≤ H) : Integrable (fun ω => Z t ω * B t ω) μ :=
    (hZ₂ t ht).integrable_mul (hB₂ t ht)
  have hDadapt : StronglyAdapted F D := stronglyAdapted_timePrimitive hg
  have hN : StronglyAdapted F N := fun t =>
    ((hB (min t H)).sub (hDadapt (min t H))).mono (F.mono (min_le_left t H))
  have hNint (t : ℝ≥0) : Integrable (N t) Q :=
    (hBg (min t H) (min_le_right _ _)).sub (hDQ (min t H) (min_le_right _ _))
  refine ⟨hQ, martingale_of_past_set_integrals hN hNint ?_⟩
  intro s t hst E hE
  by_cases hs : s ≤ H
  · let t' := min t H
    have hst' : s ≤ t' := le_min hst hs
    have ht' : t' ≤ H := min_le_right _ _
    have hE' := F.mono hst' E hE
    have hCdiff : (∫ ω in E, D t' ω ∂Q) - (∫ ω in E, D s ω ∂Q) =
        ((∫ ω in E, C t' ω ∂μ) - (∫ ω in E, C s ω ∂μ)) / ε := by
      change (∫ ω in E, (∫ r, gQ (r, ω) ∂hestonTimeMeasure t') ∂Q) -
        (∫ ω in E, (∫ r, gQ (r, ω) ∂hestonTimeMeasure s) ∂Q) =
        ((∫ ω in E, (∫ r, cP (r, ω) ∂hestonTimeMeasure t') ∂μ) -
          (∫ ω in E, (∫ r, cP (r, ω) ∂hestonTimeMeasure s) ∂μ)) / ε
      rw [setIntegral_timePrimitive_sub hgQ hst' ht' E,
        setIntegral_timePrimitive_sub hCrossProd hst' ht' E, ← integral_div]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hgTerm.prod_right_ae]
        with r hr hgZ
      exact sizeBiasedLaw_setIntegral_of_adapted hZ hε hNonneg (hr.2.trans ht')
        (hg.stronglyAdapted r) hgZ (F.mono hr.1.le E hE)
    have hZBC := hcross.setIntegral_eq hst' hE
    change (∫ ω in E, Z (min s H) ω * B (min s H) ω - C (min s H) ω ∂μ) =
      ∫ ω in E, Z (min t' H) ω * B (min t' H) ω - C (min t' H) ω ∂μ at hZBC
    rw [min_eq_left hs, min_eq_left ht', integral_sub (hZB t' ht').integrableOn (hCP t' ht').integrableOn,
      integral_sub (hZB s hs).integrableOn (hCP s hs).integrableOn] at hZBC
    have hBdiff : (∫ ω in E, B t' ω ∂Q) - (∫ ω in E, B s ω ∂Q) =
        (∫ ω in E, D t' ω ∂Q) - (∫ ω in E, D s ω ∂Q) := by
      rw [sizeBiasedLaw_setIntegral_of_adapted hZ hε hNonneg ht' (hB t') (hMix t' ht') hE',
        sizeBiasedLaw_setIntegral_of_adapted hZ hε hNonneg hs (hB s) (hMix s hs) hE,
        ← sub_div, hCdiff]
      congr 1
      linarith
    change (∫ ω in E, B (min s H) ω - D (min s H) ω ∂Q) =
      ∫ ω in E, B t' ω - D t' ω ∂Q
    rw [min_eq_left hs, integral_sub (hBg s hs).integrableOn (hDQ s hs).integrableOn,
      integral_sub (hBg t' ht').integrableOn (hDQ t' ht').integrableOn]
    linarith
  · have hsH := le_of_not_ge hs
    simp only [min_eq_right hsH, min_eq_right (hsH.trans hst)]

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.sizeBiasedLaw_setIntegral_of_adapted
#print axioms RoughHeston.GirsanovPort.stronglyAdapted_timePrimitive
#print axioms RoughHeston.GirsanovPort.physicalDrift_gridQuadraticSum_mesh_bound
#print axioms RoughHeston.GirsanovPort.sizeBiasedShift_martingale
