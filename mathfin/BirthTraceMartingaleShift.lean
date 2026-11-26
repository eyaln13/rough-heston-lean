import BirthEventTrace
import CommonDriverLimit
import StochasticFoundation
import SizeBiasGirsanov
import ProductKernelEnergy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Interval

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 m} {b : ℝ≥0} {A : Set Ω}

omit [IsProbabilityMeasure P] in
private theorem measurableSet_predictable_univ_prod {S : Type*} [mS : MeasurableSpace S]
    {G : Filtration ℝ≥0 mS} {E : Set S} (hE : MeasurableSet[G 0] E) :
    MeasurableSet[G.predictable] ((univ : Set ℝ≥0) ×ˢ E) := by
  have hsplit : (univ : Set ℝ≥0) ×ˢ E = ({⊥} ×ˢ E) ∪ (Ioi ⊥ ×ˢ E) := by
    ext p
    rcases eq_or_lt_of_le (show (⊥ : ℝ≥0) ≤ p.1 from bot_le) with hp | hp
    · simp [hp.symm]
    · have hp' : 0 < p.1 := hp
      simp [hp', hp'.ne']
  rw [hsplit]
  exact (measurableSet_predictable_singleton_bot_prod hE).union (measurableSet_predictable_Ioi_prod hE)

omit [IsProbabilityMeasure P] in
/-- Predictable processes can be observed on the birth trace with age as time. -/
theorem measurable_birthTrace_predictableShift :
    @Measurable (ℝ≥0 × A) (ℝ≥0 × Ω) (birthTraceFiltration F b A).predictable F.predictable
      (fun p => (b + p.1, p.2.val)) := by
  let G := birthTraceFiltration F b A
  let ψ (p : ℝ≥0 × A) : ℝ≥0 × Ω := (b + p.1, p.2.val)
  rw [measurable_iff_comap_le]
  refine MeasurableSpace.comap_le_iff_le_map.2 (measurableSpace_le_predictable_of_measurableSet ?_ ?_)
  · intro E hE
    let S : Set A := Subtype.val ⁻¹' E
    change MeasurableSet[G.predictable] (ψ ⁻¹' ({⊥} ×ˢ E))
    by_cases hb : b = 0
    · have hS : MeasurableSet[G 0] S := ⟨E, by
        rw [hb, add_zero]
        exact hE, rfl⟩
      have he : ψ ⁻¹' ({⊥} ×ˢ E) = ({⊥} ×ˢ S) := by ext p; simp [ψ, S, hb]
      rw [he]
      exact measurableSet_predictable_singleton_bot_prod hS
    · have he : ψ ⁻¹' ({⊥} ×ˢ E) = ∅ := by
        ext p
        have hn : b + p.1 ≠ (0 : ℝ≥0) := ((pos_iff_ne_zero.mpr hb).trans_le (le_add_of_nonneg_right zero_le)).ne'
        simp [ψ, hn]
      rw [he]
      exact @MeasurableSet.empty _ G.predictable
  · intro i E hE
    let S : Set A := Subtype.val ⁻¹' E
    change MeasurableSet[G.predictable] (ψ ⁻¹' (Ioi i ×ˢ E))
    by_cases h : i < b
    · have hS : MeasurableSet[G 0] S := ⟨E, by
        rw [add_zero]
        exact F.mono h.le E hE, rfl⟩
      have he : ψ ⁻¹' (Ioi i ×ˢ E) = (univ ×ˢ S) := by
        ext p
        have hp : i < b + p.1 := h.trans_le (le_add_of_nonneg_right zero_le)
        simp [ψ, S, hp]
      rw [he]
      exact measurableSet_predictable_univ_prod hS
    · have hi := le_of_not_gt h
      have hrel : b + (i - b) = i := add_tsub_cancel_of_le hi
      have hS : MeasurableSet[G (i - b)] S := ⟨E, by rwa [hrel], rfl⟩
      have he : ψ ⁻¹' (Ioi i ×ˢ E) = (Ioi (i - b) ×ˢ S) := by
        ext p
        have hp : i < b + p.1 ↔ i - b < p.1 := by
          constructor
          · intro hp
            exact lt_of_add_lt_add_left (hrel.trans_lt hp)
          · intro hp
            have hr := add_lt_add_right hp b
            rwa [hrel] at hr
        simp [ψ, S, hp]
      rw [he]
      exact measurableSet_predictable_Ioi_prod hS

omit [IsProbabilityMeasure P] in
theorem stronglyPredictable_birthTrace {V : ℝ≥0 → Ω → ℝ} (hV : IsStronglyPredictable F V) :
    IsStronglyPredictable (birthTraceFiltration F b A) (fun t (ω : A) => V (b+t) ω) :=
  hV.comp_measurable measurable_birthTrace_predictableShift

omit [IsProbabilityMeasure P] in
private theorem birthTrace_val_preserving (hA : MeasurableSet[F b] A) :
    MeasurePreserving (Subtype.val : A → Ω) (birthTraceLaw P A) (boundaryConditionedMeasure P A) :=
  ⟨measurable_subtype_coe, birthTraceLaw_map (F.le b A hA)⟩

omit [IsProbabilityMeasure P] in
theorem birthTrace_memLp (hA : MeasurableSet[F b] A) (hp : 0 < P A)
    {f : Ω → ℝ} {p : ℝ≥0∞} (hf : MemLp f p P) :
    MemLp (fun ω : A => f ω) p (birthTraceLaw P A) := by
  have hr : MemLp f p (boundaryConditionedMeasure P A) :=
    (hf.mono_measure Measure.restrict_le_self).smul_measure (ENNReal.inv_ne_top.mpr hp.ne')
  exact hr.comp_measurePreserving (birthTrace_val_preserving hA)

omit [IsProbabilityMeasure P] in
private theorem setIntegral_birthConditioned {E : Set Ω} (hE : MeasurableSet E) (f : Ω → ℝ) :
    (∫ ω in E, f ω ∂boundaryConditionedMeasure P A) =
      ((P A)⁻¹).toReal * ∫ ω in E ∩ A, f ω ∂P := by
  rw [boundaryConditionedMeasure, Measure.restrict_smul, Measure.restrict_restrict hE,
    integral_smul_measure, smul_eq_mul]

/-- A physical martingale remains a martingale after a positive-probability
birth restriction, with all past information measured in the trace. -/
theorem martingale_birthTrace (hA : MeasurableSet[F b] A) (hp : 0 < P A)
    {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M F P) :
    Martingale (fun t (ω : A) => M (b+t) ω) (birthTraceFiltration F b A) (birthTraceLaw P A) := by
  have : IsProbabilityMeasure (birthTraceLaw P A) := birthTraceLaw_isProbability (F.le b A hA) hp
  have hEmb := MeasurableEmbedding.subtype_coe (F.le b A hA)
  have hPres := birthTrace_val_preserving (P := P) hA
  refine martingale_of_past_set_integrals
    (fun t => (hM.stronglyMeasurable (b+t)).comp_measurable (Measurable.of_comap_le le_rfl))
    (fun t => hPres.integrable_comp_of_integrable ?_) ?_
  · exact ((hM.integrable _).mono_measure Measure.restrict_le_self).smul_measure
      (ENNReal.inv_ne_top.mpr hp.ne')
  · intro s t hst S hS
    change MeasurableSet[(F (b+s)).comap (Subtype.val : A → Ω)] S at hS
    obtain ⟨E, hE, rfl⟩ := hS
    have hEμ := F.le (b+s) E hE
    rw [hPres.setIntegral_preimage_emb hEmb, hPres.setIntegral_preimage_emb hEmb,
      setIntegral_birthConditioned hEμ, setIntegral_birthConditioned hEμ,
      hM.setIntegral_eq (add_le_add_right hst b) (hE.inter (F.mono (by simp) A hA))]

private theorem constant_L2_times_martingale
    {S : Type*} [mS : MeasurableSpace S] {μ : Measure S} [IsFiniteMeasure μ]
    {G : Filtration ℝ≥0 mS} {M : ℝ≥0 → S → ℝ} {U : S → ℝ}
    (hM : Martingale M G μ) (hM₂ : ∀ t, MemLp (M t) 2 μ)
    (hU : StronglyMeasurable[G 0] U) (hU₂ : MemLp U 2 μ) :
    Martingale (fun t => U * M t) G μ := by
  refine ⟨fun t => (hU.mono (G.mono zero_le)).mul (hM.stronglyMeasurable t), ?_⟩
  intro s t hst
  exact (condExp_mul_of_stronglyMeasurable_left (hU.mono (G.mono zero_le))
    (hU₂.integrable_mul (hM₂ t)) (hM.integrable t)).trans
    (EventuallyEq.rfl.mul (hM.condExp_ae_eq hst))

private theorem constant_martingale
    {S : Type*} [mS : MeasurableSpace S] {μ : Measure S} [IsFiniteMeasure μ]
    {G : Filtration ℝ≥0 mS} {U : S → ℝ}
    (hU : StronglyMeasurable[G 0] U) (hUi : Integrable U μ) :
    Martingale (fun _ => U) G μ :=
  ⟨fun t => hU.mono (G.mono zero_le), fun s _ _ => by
    rw [condExp_of_stronglyMeasurable (G.le s) (hU.mono (G.mono zero_le)) hUi]⟩

/-- Centering each factor at birth changes the square/cross compensator
by its birth value. A deterministic mass can be added to the second factor. -/
theorem martingale_compensatedProduct_birthTrace
    (hA : MeasurableSet[F b] A) (hp : 0 < P A)
    {M N C : ℝ≥0 → Ω → ℝ} (hM : Martingale M F P) (hN : Martingale N F P)
    (hM₂ : ∀ t, MemLp (M t) 2 P) (hN₂ : ∀ t, MemLp (N t) 2 P)
    (hC : Martingale (fun t => M t * N t - C t) F P) (c : ℝ) :
    Martingale (fun t (ω : A) => (M (b+t) ω - M b ω) * (N (b+t) ω - N b ω + c) -
      (C (b+t) ω - C b ω)) (birthTraceFiltration F b A) (birthTraceLaw P A) := by
  let Q := birthTraceLaw P A
  let G := birthTraceFiltration F b A
  let M' (t : ℝ≥0) (ω : A) := M (b+t) ω
  let N' (t : ℝ≥0) (ω : A) := N (b+t) ω
  let J (t : ℝ≥0) (ω : A) := C (b+t) ω
  let U (ω : A) := c - N' 0 ω
  have : IsProbabilityMeasure Q := birthTraceLaw_isProbability (F.le b A hA) hp
  have hM' : Martingale M' G Q := martingale_birthTrace hA hp hM
  have hN' : Martingale N' G Q := martingale_birthTrace hA hp hN
  have hJ : Martingale (fun t => M' t * N' t - J t) G Q := martingale_birthTrace hA hp hC
  have hM'₂ (t : ℝ≥0) : MemLp (M' t) 2 Q := birthTrace_memLp hA hp (hM₂ (b+t))
  have hN'₂ (t : ℝ≥0) : MemLp (N' t) 2 Q := birthTrace_memLp hA hp (hN₂ (b+t))
  have hU : StronglyMeasurable[G 0] U := stronglyMeasurable_const.sub (hN'.stronglyMeasurable 0)
  have hU₂ : MemLp U 2 Q := (memLp_const c).sub (hN'₂ 0)
  have hW₁ := constant_L2_times_martingale hM' hM'₂ hU hU₂
  have hW₂ := constant_L2_times_martingale hN' hN'₂ (hM'.stronglyMeasurable 0) (hM'₂ 0)
  have hConst (ω : A) := J 0 ω - M' 0 ω * U ω
  have hJ₀ : StronglyMeasurable[G 0] (J 0) := by
    have hs := ((hM'.stronglyMeasurable 0).mul (hN'.stronglyMeasurable 0)).sub (hJ.stronglyMeasurable 0)
    simpa only [sub_sub_cancel] using hs
  have hJi : Integrable (J 0) Q := by
    have hi := ((hM'₂ 0).integrable_mul (hN'₂ 0)).sub (hJ.integrable 0)
    simpa only [sub_sub_cancel] using hi
  have hCst := constant_martingale (hJ₀.sub ((hM'.stronglyMeasurable 0).mul hU))
    (hJi.sub ((hM'₂ 0).integrable_mul hU₂))
  convert ((hJ.add hW₁).sub hW₂).add hCst using 1
  ext t ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, M', N', J, U, add_zero]
  ring

/-- Shifting the old interval primitive subtracts its physical birth
value and produces the ordinary integral on the age clock. -/
theorem birthAge_integral_difference {d : ℝ≥0 → ℝ} {t : ℝ≥0}
    (hm : Measurable d)
    (hd : IntervalIntegrable (fun r : ℝ => d r.toNNReal) volume (0 : ℝ) (b+t : ℝ≥0)) :
    (∫ r in (0 : ℝ)..((b+t : ℝ≥0) : ℝ), d r.toNNReal) -
        (∫ r in (0 : ℝ)..(b : ℝ), d r.toNNReal) =
      ∫ r, d (b+r) ∂hestonTimeMeasure t := by
  have hbt : (b : ℝ) ≤ ((b+t : ℝ≥0) : ℝ) := by exact_mod_cast (show b ≤ b+t by simp)
  have hb₀ : (0 : ℝ) ≤ (b : ℝ) := NNReal.coe_nonneg _
  have hbt₀ : (0 : ℝ) ≤ ((b+t : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  have ha := hd.mono_set (by
    rw [uIcc_of_le hb₀, uIcc_of_le hbt₀]
    exact Icc_subset_Icc le_rfl hbt)
  have h₂ := hd.mono_set (by
    rw [uIcc_of_le hbt, uIcc_of_le hbt₀]
    exact Icc_subset_Icc hb₀ le_rfl)
  have he : (∫ r in (0 : ℝ)..((b+t : ℝ≥0) : ℝ), d r.toNNReal) -
      (∫ r in (0 : ℝ)..(b : ℝ), d r.toNNReal) = ∫ r in (b : ℝ)..((b+t : ℝ≥0) : ℝ), d r.toNNReal := by
    rw [← intervalIntegral.integral_add_adjacent_intervals ha h₂]
    ring
  rw [he]
  have hmb : Measurable (fun r : ℝ≥0 => d (b+r)) := hm.comp (measurable_const.add measurable_id)
  rw [hestonTimeMeasure, integral_map continuous_real_toNNReal.measurable.aemeasurable
    hmb.aestronglyMeasurable]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (show (0:ℝ) ≤ (t:ℝ) from t.2)]
  have hh := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := (t : ℝ))
    (fun r : ℝ => d r.toNNReal) (b : ℝ)
  simp only [add_zero] at hh
  rw [NNReal.coe_add, ← hh]
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le (show (0:ℝ) ≤ (t:ℝ) from t.2)] at hr
  change d ((b : ℝ) + r).toNNReal = d (b + r.toNNReal)
  rw [Real.toNNReal_add hb₀ hr.1, Real.toNNReal_coe]

/-- A physical-time compensated product becomes an age-time
compensated product under the actual birth trace law. The statement
uses the same physical time measure as the focal change of measure. -/
theorem martingale_compensatedProduct_birthTrace_density
    (hA : MeasurableSet[F b] A) (hp : 0 < P A) {T H : ℝ≥0} (hBH : b+H ≤ T)
    {M N C d : ℝ≥0 → Ω → ℝ} (hM : Martingale M F P) (hN : Martingale N F P)
    (hM₂ : ∀ t, MemLp (M t) 2 P) (hN₂ : ∀ t, MemLp (N t) 2 P)
    (hC : Martingale (fun t => M t * N t - C t) F P)
    (hd : IsStronglyPredictable F d)
    (hInt : ∀ᵐ ω ∂P, IntervalIntegrable (fun r : ℝ => d r.toNNReal ω) volume 0 (T : ℝ))
    (hCeq : ∀ t ≤ T, C t =ᵐ[P] fun ω => ∫ r in (0 : ℝ)..(t : ℝ), d r.toNNReal ω) (c : ℝ) :
    Martingale (fun t (ω : A) => (M (b+min t H) ω - M b ω) * (N (b+min t H) ω - N b ω + c) -
      ∫ r, d (b+r) ω ∂hestonTimeMeasure (min t H)) (birthTraceFiltration F b A) (birthTraceLaw P A) := by
  let Q := birthTraceLaw P A
  let G := birthTraceFiltration F b A
  have : IsProbabilityMeasure Q := birthTraceLaw_isProbability (F.le b A hA) hp
  have hEmb := birthTrace_val_preserving (P := P) hA
  have hAC : boundaryConditionedMeasure P A ≪ P :=
    (Measure.AbsolutelyContinuous.refl (P.restrict A)).smul_left _ |>.trans
      Measure.restrict_le_self.absolutelyContinuous
  have hEq (t : ℝ≥0) (ht : t ≤ H) :
      (fun ω : A => C (b+t) ω - C b ω) =ᵐ[Q] fun ω => ∫ r, d (b+r) ω ∂hestonTimeMeasure t := by
    suffices he : ∀ᵐ ω ∂P, C (b+t) ω - C b ω = ∫ r, d (b+r) ω ∂hestonTimeMeasure t by
      exact hEmb.quasiMeasurePreserving.ae (hAC.ae_le he)
    have hbT : b ≤ T := (show b ≤ b+H by simp).trans hBH
    have hbtT : b+t ≤ T := (add_le_add_right ht b).trans hBH
    filter_upwards [hCeq (b+t) hbtT, hCeq b hbT, hInt] with ω hbt hb hi
    rw [hbt, hb]
    have hm : Measurable (fun r => d r ω) :=
      ((hd.mono F.predictable_le_prod).comp_measurable (measurable_id.prodMk measurable_const)).measurable
    apply birthAge_integral_difference hm
    have hbt₀ : (0 : ℝ) ≤ ((b+t : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
    have hT₀ : (0 : ℝ) ≤ (T : ℝ) := NNReal.coe_nonneg _
    apply hi.mono_set
    rw [uIcc_of_le hbt₀, uIcc_of_le hT₀]
    exact Icc_subset_Icc le_rfl (by exact_mod_cast hbtT)
  have hOld := martingale_freeze_at (martingale_compensatedProduct_birthTrace hA hp hM hN hM₂ hN₂ hC c) H
  have hAd (E : ℝ≥0 → Ω → ℝ) (hE : Martingale E F P) :
      StronglyAdapted G (fun t (ω : A) => E (b+t) ω - E b ω) := by
    have he := (martingale_birthTrace hA hp hE).stronglyAdapted
    intro t
    have h0 : StronglyMeasurable[G t] (fun ω : A => E b ω) := by
      simpa only [add_zero] using (he 0).mono (G.mono (show 0 ≤ t from zero_le))
    exact (he t).sub h0
  have ha1 := hAd M hM
  have ha2 := hAd N hN
  have hda := stronglyAdapted_timePrimitive (stronglyPredictable_birthTrace (b := b) (A := A) hd)
  refine ⟨fun t => (((ha1 (min t H)).mul ((ha2 (min t H)).add stronglyMeasurable_const)).sub
      (hda (min t H))).mono (G.mono (min_le_left t H)), fun s t hst => ?_⟩
  have he (r : ℝ≥0) : (fun ω : A => (M (b+min r H) ω - M b ω) * (N (b+min r H) ω - N b ω + c) -
      (C (b+min r H) ω - C b ω)) =ᵐ[Q]
      fun ω => (M (b+min r H) ω - M b ω) * (N (b+min r H) ω - N b ω + c) -
        ∫ u, d (b+u) ω ∂hestonTimeMeasure (min r H) :=
    (hEq (min r H) (min_le_right _ _)).mono fun ω hw => congrArg (fun v => _ - v) hw
  exact (condExp_congr_ae (he t).symm).trans ((hOld.condExp_ae_eq hst).trans (he s))

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.martingale_birthTrace
#print axioms RoughHeston.GirsanovPort.martingale_compensatedProduct_birthTrace
#print axioms RoughHeston.GirsanovPort.birthAge_integral_difference
#print axioms RoughHeston.GirsanovPort.stronglyPredictable_birthTrace
#print axioms RoughHeston.GirsanovPort.martingale_compensatedProduct_birthTrace_density
