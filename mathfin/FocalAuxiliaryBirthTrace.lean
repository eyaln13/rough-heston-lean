import FocalPulseDynamics
import CanonicalPulseBirthTrace

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

open GirsanovPort

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {A : Set Ω} {b H T : ℝ≥0}

/-- A physical martingale increment read at a birth age and frozen at
the age horizon. -/
def birthTraceStoppedIncrement (A : Set Ω) (b H : ℝ≥0) (X : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : A) : ℝ :=
  X (b+min t H) ω-X b ω

/-- Conditioning at birth, recentering both physical martingales, and
stopping at the common age leaves their compensated products intact. -/
theorem orthogonal_unit_clock_birthTrace
    (hA : MeasurableSet[F b] A) (hp : 0<P A) (hT : b+H≤T)
    {W J : ℝ≥0 → Ω → ℝ} (hW : Martingale W F P) (hJ : Martingale J F P)
    (hW₂ : ∀ t,MemLp (W t) 2 P) (hJ₂ : ∀ t,MemLp (J t) 2 P)
    (hWc : ∀ᵐ ω ∂P,Continuous (fun t => W t ω))
    (hWsq : Martingale (fun t ω => W t ω*W t ω-((min t T:ℝ≥0):ℝ)) F P)
    (hWJ : Martingale (fun t => W t*J t) F P) :
    let Q := birthTraceLaw P A
    let G := birthTraceFiltration F b A
    let W' := birthTraceStoppedIncrement A b H W
    let J' := birthTraceStoppedIncrement A b H J
    Martingale W' G Q ∧
      (∀ t,MemLp (W' t) 2 Q) ∧
      (∀ᵐ ω ∂Q,Continuous (fun t => W' t ω)) ∧
      Martingale (fun t ω => W' t ω*W' t ω-((min t H:ℝ≥0):ℝ)) G Q ∧
      Martingale (fun t => W' t*J' t) G Q := by
  let Q := birthTraceLaw P A
  let G := birthTraceFiltration F b A
  let W' := birthTraceStoppedIncrement A b H W
  let J' := birthTraceStoppedIncrement A b H J
  let hQ := birthTraceLaw_isProbability (F.le b A hA) hp
  let D (t : ℝ≥0) (_ : Ω) := ((min t T:ℝ≥0):ℝ)
  let P' := boundaryConditionedMeasure P A
  have hPres : MeasurePreserving (Subtype.val : A→Ω) Q P' :=
    ⟨measurable_subtype_coe,birthTraceLaw_map (F.le b A hA)⟩
  have hAC : P' ≪ P :=
    ((Measure.AbsolutelyContinuous.refl (P.restrict A)).smul_left _).trans
      Measure.restrict_le_self.absolutelyContinuous
  have hWsq' : Martingale (fun t => W t*W t-D t) F P := hWsq
  have hWJ' : Martingale (fun t => W t*J t-(0:Ω→ℝ)) F P := by
    simpa only [sub_zero] using hWJ
  have hl (t : ℝ≥0) : b+min t H≤T := (add_le_add_right (min_le_right t H) b).trans hT
  have hbT : b≤T := (le_add_of_nonneg_right (show 0≤H from zero_le)).trans hT
  have hWB : Martingale (fun t (ω : A) => W (b+t) ω) G Q :=
    martingale_birthTrace hA hp hW
  have hWConst : Martingale (fun _ (ω : A) => W b ω) G Q := by
    refine ⟨fun t => ?_,?_⟩
    · have he := hWB.stronglyAdapted (0:ℝ≥0)
      simp only [add_zero] at he
      exact he.mono (G.mono zero_le)
    · intro s t hst
      have he := hWB.stronglyAdapted (0:ℝ≥0)
      simp only [add_zero] at he
      have hi := hWB.integrable (0:ℝ≥0)
      simp only [add_zero] at hi
      rw [condExp_of_stronglyMeasurable (G.le s) (he.mono (G.mono zero_le)) hi]
  have hWs := martingale_freeze_at (hWB.sub hWConst) H
  have hW2 (t : ℝ≥0) : MemLp (W' t) 2 Q :=
    birthTrace_memLp hA hp ((hW₂ (b+min t H)).sub (hW₂ b))
  have hWc' : ∀ᵐ ω ∂Q,Continuous (fun t => W' t ω) := by
    filter_upwards [hPres.quasiMeasurePreserving.ae (hAC.ae_le hWc)] with ω hw
    exact (hw.comp (continuous_const.add (continuous_id.min continuous_const))).sub continuous_const
  have hSq := martingale_freeze_at
    (martingale_compensatedProduct_birthTrace hA hp hW hW hW₂ hW₂ hWsq' 0) H
  have hCross := martingale_freeze_at
    (martingale_compensatedProduct_birthTrace hA hp hW hJ hW₂ hJ₂ hWJ' 0) H
  refine ⟨hWs,hW2,hWc',?_,?_⟩
  · convert hSq using 1
    funext t ω
    simp only [birthTraceStoppedIncrement,D,add_zero,min_eq_left (hl t),min_eq_left hbT,NNReal.coe_add]
    ring
  · convert hCross using 1
    funext t ω
    simp only [birthTraceStoppedIncrement,add_zero,sub_self,sub_zero,Pi.mul_apply]

/-- A physical Brownian remains Brownian up to the specified age on the
same birth trace after recentering and deterministic freezing. -/
theorem brownianOn_frozen_birthTrace {W : ℝ≥0→Ω→ℝ}
    (hW : MathFinBridge.BrownianOn P F T W)
    (hA : MeasurableSet[F b] A) (hp : 0<P A) (hT : b+H≤T) :
    MathFinBridge.BrownianOn (birthTraceLaw P A) (birthTraceFiltration F b A) H
      (birthTraceStoppedIncrement A b H W) := by
  have hs : MathFinBridge.BrownianOn P F (b+H) W :=
    ⟨hW.adapted,hW.zero_at_start,hW.continuous_paths.mono
      (fun _ h => h.mono (Icc_subset_Icc_right hT)),
      (fun s t hst ht => hW.normal_increment s t hst (ht.trans hT)),
      (fun s t hst ht => hW.independent_of_past s t hst (ht.trans hT))⟩
  have h := brownianOn_birthTrace hs hA hp
  refine ⟨fun t => (h.adapted (min t H)).mono
    ((birthTraceFiltration F b A).mono (min_le_left _ _)),?_ ,?_ ,?_ ,?_⟩
  · exact ae_of_all _ fun ω => by simp [birthTraceStoppedIncrement]
  · filter_upwards [h.continuous_paths] with ω hc
    exact (hc.comp_continuous (continuous_id.min continuous_const)
      (fun t => ⟨zero_le,min_le_right t H⟩)).continuousOn
  · intro s t hst ht
    simpa only [birthTraceStoppedIncrement,min_eq_left (hst.trans ht),min_eq_left ht]
      using h.normal_increment s t hst ht
  · intro s t hst ht
    simpa only [birthTraceStoppedIncrement,min_eq_left (hst.trans ht),min_eq_left ht]
      using h.independent_of_past s t hst ht

#print axioms brownianOn_frozen_birthTrace

#print axioms orthogonal_unit_clock_birthTrace

end RoughHeston
