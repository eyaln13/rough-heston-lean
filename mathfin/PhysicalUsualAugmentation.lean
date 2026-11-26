import StochasticFoundation
import MathFin.Probability.Brownian.Ito.ItoIntegralProcessLocalMartingaleGeneral
import Mathlib.Probability.Martingale.Convergence

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω}

@[reducible] noncomputable def physicalCompletedSpace (P : Measure Ω) : MeasurableSpace Ω :=
  eventuallyMeasurableSpace m (ae P)

noncomputable def physicalCompletedMeasure (P : Measure Ω) : @Measure Ω (physicalCompletedSpace P) :=
  P.completion

theorem physical_ambient_le_completion (P : Measure Ω) : m≤physicalCompletedSpace P :=
  le_eventuallyMeasurableSpace

theorem physical_completion_trim (P : Measure Ω) :
    (physicalCompletedMeasure P).trim (physical_ambient_le_completion P)=P := by
  ext s hs
  rw [trim_measurableSet_eq (physical_ambient_le_completion P) hs]
  rfl

instance physicalCompletedMeasure_isComplete (P : Measure Ω) :
    (physicalCompletedMeasure P).IsComplete :=
  inferInstanceAs P.completion.IsComplete

instance physicalCompletedMeasure_isProbability (P : Measure Ω) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (physicalCompletedMeasure P) :=
  ⟨by change P univ=1; exact measure_univ⟩

instance physicalCompletedMeasure_isFinite (P : Measure Ω) [IsFiniteMeasure P] :
    IsFiniteMeasure (physicalCompletedMeasure P) :=
  ⟨by change P univ<∞; exact measure_lt_top _ _⟩

theorem physical_completion_integral (P : Measure Ω) {f : Ω→ℝ} (hf : StronglyMeasurable[m] f) :
    (∫ ω,f ω ∂physicalCompletedMeasure P)=∫ ω,f ω ∂P := by
  rw [integral_trim (physical_ambient_le_completion P) hf,physical_completion_trim]

theorem physical_completion_setIntegral (P : Measure Ω) {f : Ω→ℝ} (hf : StronglyMeasurable[m] f)
    {A : Set Ω} (hA : MeasurableSet[m] A) :
    (∫ ω in A,f ω ∂physicalCompletedMeasure P)=∫ ω in A,f ω ∂P := by
  rw [← integral_indicator (physical_ambient_le_completion P A hA),← integral_indicator hA]
  exact physical_completion_integral P (hf.indicator hA)

theorem physical_completion_memLp {f : Ω→ℝ} {p : ℝ≥0∞} (hf : MemLp f p P) :
    MemLp f p (physicalCompletedMeasure P) := by
  apply memLp_of_memLp_trim (physical_ambient_le_completion P)
  simpa only [physical_completion_trim] using hf

noncomputable def physicalCompletedFiltration (P : Measure Ω) (F : Filtration ℝ≥0 m) :
    Filtration ℝ≥0 (physicalCompletedSpace P) :=
  ⟨F.seq,F.mono',fun t => (F.le t).trans (physical_ambient_le_completion P)⟩

open MathFin.ItoLocalMartingale in
noncomputable def physicalUsualFiltration (P : Measure Ω) (F : Filtration ℝ≥0 m) :
    Filtration ℝ≥0 (physicalCompletedSpace P) :=
  (nullAugmentation (physicalCompletedFiltration P F) (physicalCompletedMeasure P)).rightCont

open MathFin.ItoLocalMartingale in
theorem physicalCompletedFiltration_le_usual (P : Measure Ω) (F : Filtration ℝ≥0 m) :
    physicalCompletedFiltration P F ≤ physicalUsualFiltration P F :=
  le_trans le_sup_left (nullAugmentation (physicalCompletedFiltration P F)
    (physicalCompletedMeasure P)).le_rightCont

instance physicalUsualFiltration_isRightContinuous (P : Measure Ω) (F : Filtration ℝ≥0 m) :
    (physicalUsualFiltration P F).IsRightContinuous := by
  unfold physicalUsualFiltration
  infer_instance

open MathFin.ItoLocalMartingale in
instance physicalUsualFiltration_isComplete (P : Measure Ω) (F : Filtration ℝ≥0 m) :
    (physicalUsualFiltration P F).IsComplete (physicalCompletedMeasure P) := by
  constructor
  intro s hs t
  unfold physicalUsualFiltration
  apply (nullAugmentation (physicalCompletedFiltration P F) (physicalCompletedMeasure P)).le_rightCont t
  apply (show nullsAlg (physicalCompletedSpace P) (physicalCompletedMeasure P) ≤
    nullAugmentation (physicalCompletedFiltration P F) (physicalCompletedMeasure P) t from le_sup_right)
  exact MeasurableSpace.measurableSet_generateFrom ⟨measurableSet_of_null hs,hs⟩

theorem StronglyAdapted.physicalUsual {F : Filtration ℝ≥0 m} {X : ℝ≥0→Ω→ℝ}
    (hX : StronglyAdapted F X) :
    StronglyAdapted (physicalUsualFiltration P F) X :=
  fun t => (hX t).mono (physicalCompletedFiltration_le_usual P F t)

theorem martingale_physical_completion [IsFiniteMeasure P] {F : Filtration ℝ≥0 m} {X : ℝ≥0→Ω→ℝ}
    (hX : Martingale X F P) :
    Martingale X (physicalCompletedFiltration P F) (physicalCompletedMeasure P) := by
  apply martingale_of_past_set_integrals (𝒢 := physicalCompletedFiltration P F) (fun t => hX.stronglyAdapted t)
    (fun t => (physical_completion_memLp ((memLp_one_iff_integrable).2 (hX.integrable t))).integrable le_rfl)
  intro s t hst A hA
  have hAm : MeasurableSet[m] A := F.le s A hA
  have hsm (r : ℝ≥0) : StronglyMeasurable[m] (X r) := (hX.stronglyAdapted r).mono (F.le r)
  rw [physical_completion_setIntegral P (hsm s) hAm,physical_completion_setIntegral P (hsm t) hAm]
  exact hX.setIntegral_eq hst hA

open MathFin.ItoLocalMartingale in
theorem martingale_physical_nullAugmentation [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {X : ℝ≥0→Ω→ℝ} (hX : Martingale X F P) :
    Martingale X (nullAugmentation F P) P := by
  refine ⟨fun t => (hX.stronglyAdapted t).mono le_sup_left,?_⟩
  intro s t hst
  exact (condExp_sup_nulls (F.le s) (hX.integrable t)).trans (hX.condExp_ae_eq hst)

/-- Right-continuous enlargement preserves any a.e. continuous martingale.
The family before a fixed future time is uniformly integrable because all
its sections are conditional expectations of the same terminal variable. -/
theorem martingale_physical_rightCont [IsFiniteMeasure P] {F : Filtration ℝ≥0 m} {X : ℝ≥0→Ω→ℝ}
    (hX : Martingale X F P) (hc : ∀ᵐ ω ∂P,Continuous (fun t => X t ω)) :
    Martingale X F.rightCont P := by
  apply martingale_of_past_set_integrals
    (fun t => (hX.stronglyAdapted t).mono (F.le_rightCont t)) hX.integrable
  intro i j hij A hA
  rcases hij.eq_or_lt with rfl|hij'
  · rfl
  let e (n : ℕ) : ℝ≥0 := (1:ℝ≥0)/((n:ℝ≥0)+1)
  have he (n : ℕ) : 0<e n := div_pos zero_lt_one (by positivity)
  have he0 : Tendsto e atTop (𝓝 0) := by
    have hreal : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    apply NNReal.tendsto_coe.mp
    simpa only [e,NNReal.coe_div,NNReal.coe_one,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_zero] using hreal
  let u (n : ℕ) := min j (i+e n)
  have hi (n : ℕ) : i<u n := lt_min hij' (lt_add_of_pos_right _ (he n))
  have hj (n : ℕ) : u n≤j := min_le_left _ _
  have hu : Tendsto u atTop (𝓝 i) := by
    simpa only [u,add_zero,min_eq_right hij] using
      (tendsto_const_nhds (x := j)).min ((tendsto_const_nhds (x := i)).add he0)
  have hAu (n : ℕ) : MeasurableSet[F (u n)] A := by
    apply (show F.rightCont i≤F (u n) by rw [Filtration.rightCont_eq]; exact iInf₂_le (u n) (hi n))
    exact hA
  have hUniform : UnifIntegrable (fun n => X (u n)) 1 P := by
    refine (unifIntegrable_congr_ae (fun n => hX.condExp_ae_eq (hj n))).mp ?_
    exact ((hX.integrable j).uniformIntegrable_condExp (ℱ := fun n => F (u n))
      (fun n => F.le (u n))).1
  have hLp := tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top
    (fun n => (hX.integrable (u n)).aestronglyMeasurable)
    (memLp_one_iff_integrable.mpr (hX.integrable i)) hUniform
    (hc.mono fun ω hw => (hw.tendsto i).comp hu)
  have hlim : Tendsto (fun n => ∫ ω in A,X (u n) ω ∂P) atTop (𝓝 (∫ ω in A,X i ω ∂P)) :=
    tendsto_integral_of_L1' (X i) (Eventually.of_forall fun n => (hX.integrable (u n)).restrict)
      (tendsto_nhds_bot_mono hLp (Eventually.of_forall fun n => eLpNorm_restrict_le _ _ _ _))
  exact tendsto_nhds_unique hlim
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => ∫ ω in A,X j ω ∂P) atTop _).congr
      (fun n => (hX.setIntegral_eq (hj n) (hAu n)).symm))

theorem martingale_physical_usual [IsFiniteMeasure P] {F : Filtration ℝ≥0 m} {X : ℝ≥0→Ω→ℝ}
    (hX : Martingale X F P) (hc : ∀ᵐ ω ∂P,Continuous (fun t => X t ω)) :
    Martingale X (physicalUsualFiltration P F) (physicalCompletedMeasure P) :=
  martingale_physical_rightCont (martingale_physical_nullAugmentation (martingale_physical_completion hX)) hc

#print axioms physicalUsualFiltration_isComplete
#print axioms martingale_physical_usual

end RoughHeston
