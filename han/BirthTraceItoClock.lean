import PredictableBirthTimeMeasure
import DominatedLpPullback
import LpBirthWindow

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace RoughHeston.GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 m} {A : Set Ω} {b r : ℝ≥0}

local notation "G" => birthTraceFiltration F b A
local notation "Q" => birthTraceLaw P A
local notation "ν" => jointPredictableMeasure F P (b+r)
local notation "ν'" => jointPredictableMeasure (birthTraceFiltration F b A) (birthTraceLaw P A) r

omit [IsProbabilityMeasure P] in
theorem birthTrace_subtype_dom (hA : MeasurableSet[F b] A) :
    Measure.map (Subtype.val : A → Ω) Q ≤ (P A)⁻¹ • P := by
  rw [birthTraceLaw_map (F.le b A hA),boundaryConditionedMeasure]
  exact smul_mono_right _ Measure.restrict_le_self

theorem birthTrace_joint_dom (hA : MeasurableSet[F b] A) (hPA : 0<P A) :
    @Measure.map (ℝ≥0 × A) (ℝ≥0 × Ω) (G).predictable F.predictable
      (fun p => (b+p.1,p.2.val)) ν' ≤ (P A)⁻¹ • ν := by
  let μ := boundaryConditionedMeasure P A
  let : IsProbabilityMeasure μ := boundaryConditionedMeasure_isProbability hPA
  let c := (P A)⁻¹
  have h : μ≤c•P := by
    dsimp [μ,c]
    exact smul_mono_right _ Measure.restrict_le_self
  have hProd : (MathFin.ItoIntegralCLM.timeMeasureHorizon (b+r)).prod μ ≤
      c • (MathFin.ItoIntegralCLM.timeMeasureHorizon (b+r)).prod P := by
    have : IsFiniteMeasure (c • P) := ⟨by
      rw [Measure.smul_apply,smul_eq_mul,measure_univ,mul_one]
      exact (ENNReal.inv_ne_top.mpr hPA.ne').lt_top⟩
    rw [←Measure.prod_smul_right]
    exact Measure.prod_mono le_rfl h
  letI : MeasurableSpace (ℝ≥0 × A) := (G).predictable
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  rw [(birthTrace_jointPredictableMeasure_shift hA hPA (T:=b+r) le_rfl).map_eq]
  apply Measure.restrict_le_self.trans
  apply Measure.le_iff.mpr
  intro E hE
  rw [Measure.smul_apply,smul_eq_mul,jointPredictableMeasure,
    trim_measurableSet_eq F.predictable_le_prod hE,jointPredictableMeasure,
    trim_measurableSet_eq F.predictable_le_prod hE]
  exact hProd E

set_option maxHeartbeats 2500000 in
/-- A physical predictable Itô row supported after birth becomes the
same Itô integral on the genuine birth-conditioned age filtration.
The comparison uses unchanged simple Brownian increments and the
bounded change of measure for the full L² limits. -/
theorem birthTrace_jointIto_shift
    (hA : MeasurableSet[F b] A) (hPA : 0<P A)
    [IsProbabilityMeasure Q]
    {B : ℝ≥0 → Ω → ℝ} {B' : ℝ≥0 → A → ℝ}
    (hB₂ : ∀ t, MemLp (B t) 2 P) (hB : Martingale B F P)
    (hBc : Martingale (fun t ω => B t ω ^ 2-((min t (b+r):ℝ≥0):ℝ)) F P)
    (hB'₂ : ∀ t, MemLp (B' t) 2 Q) (hB' : Martingale B' G Q)
    (hB'c : Martingale (fun t ω => B' t ω ^ 2-((min t r:ℝ≥0):ℝ)) G Q)
    (hAgree : ∀ t≤r, B' t =ᵐ[Q] (fun ω => B (b+t) ω - B b ω))
    (u : Lp ℝ 2 ν) (v : Lp ℝ 2 ν')
    (hSupport : ∀ᵐ p ∂ν, p.1≤b → u p=0)
    (hv : ⇑v =ᵐ[ν'] fun p => u (b+p.1,p.2.val)) :
    ⇑(jointItoIntegralCLM r hB'₂ v) =ᵐ[Q]
      (fun ω => jointItoIntegralCLM (b+r) hB₂ u ω) := by
  let φ (p : ℝ≥0 × A) : ℝ≥0 × Ω := (b+p.1,p.2.val)
  letI : MeasurableSpace (ℝ≥0 × A) := (G).predictable
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let I : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν' :=
    dominatedLpPullback (φ:=φ) measurable_birthTrace_predictableShift (ENNReal.inv_ne_top.mpr hPA.ne')
      (birthTrace_joint_dom hA hPA)
  let O : Lp ℝ 2 P →L[ℝ] Lp ℝ 2 Q :=
    dominatedLpPullback measurable_subtype_coe (ENNReal.inv_ne_top.mpr hPA.ne') (birthTrace_subtype_dom hA)
  let J := jointItoIntegralCLM (𝒢:=F) (b+r) hB₂
  let J' := jointItoIntegralCLM (𝒢:=G) r hB'₂
  let K : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν := jointAfterCLM b
  have hI (u₀ : Lp ℝ 2 ν) : ⇑(I u₀) =ᵐ[ν'] fun p => u₀ (φ p) :=
    dominatedLpPullback_ae _ _ _ u₀
  have hO (x : Lp ℝ 2 P) : ⇑(O x) =ᵐ[Q] fun ω : A => x ω :=
    dominatedLpPullback_ae _ _ _ x
  have hφ : @QuasiMeasurePreserving (ℝ≥0 × A) (ℝ≥0 × Ω) F.predictable (G).predictable φ ν' ν :=
    ⟨measurable_birthTrace_predictableShift, Measure.absolutelyContinuous_of_le_smul (birthTrace_joint_dom hA hPA)⟩
  have hSub : QuasiMeasurePreserving (Subtype.val : A → Ω) Q P :=
    ⟨measurable_subtype_coe, Measure.absolutelyContinuous_of_le_smul (birthTrace_subtype_dom hA)⟩
  have hComparison : J'.comp I = O.comp (J.comp K) := by
    apply ContinuousLinearMap.ext_on (dense_span_jointPredictableMeasure F P (b+r))
    rintro _ ⟨a,d,had,hdT,E,hE,rfl⟩
    let x := jointRectangleLp ν d hE
    let E' : Set A := Subtype.val ⁻¹' E
    have hx : ⇑x =ᵐ[ν] (Ioc a d ×ˢ E).indicator (fun _ => (1:ℝ)) := indicatorConstLp_coeFn
    change J' (I x) = O (J (K x))
    by_cases hdb : d≤b
    · have hxI : I x = 0 := by
        apply Lp.ext
        filter_upwards [hI x,hφ.ae hx,ae_mem_joint_timeBand G Q r,Lp.coeFn_zero ℝ 2 ν'] with p h₁ h₂ ht hz
        rw [h₁,h₂,hz,Pi.zero_apply]
        apply indicator_of_notMem
        exact fun hp => (not_le_of_gt (lt_add_of_pos_right b ht.1.1)) (hp.1.2.trans hdb)
      have hxK : K x = 0 := by
        apply Lp.ext
        filter_upwards [jointAfterCLM_ae b x,hx,Lp.coeFn_zero ℝ 2 ν] with p h₁ h₂ hz
        rw [h₁,hz,Pi.zero_apply]
        by_cases hp : b<p.1
        · rw [ite_eq_left hp,h₂]
          apply indicator_of_notMem
          exact fun hn => (hp.not_ge (hn.1.2.trans hdb))
        · exact ite_eq_right hp
      simp only [hxI,hxK,map_zero]
    · have hbd : b≤d := (lt_of_not_ge hdb).le
      let a₀ := max b a
      let l := a₀-b
      let j := d-b
      have ha₀d : a₀≤d := max_le hbd had
      have ha₀b : b≤a₀ := le_max_left _ _
      have hbl : b+l=a₀ := add_tsub_cancel_of_le ha₀b
      have hbj : b+j=d := add_tsub_cancel_of_le hbd
      have hlj : l≤j := tsub_le_tsub_right ha₀d b
      have hjr : j≤r := by
        apply le_of_add_le_add_left (a:=b)
        rwa [hbj]
      have hE₀ : MeasurableSet[F a₀] E := F.mono (le_max_right _ _) E hE
      have hE' : MeasurableSet[G l] E' := by
        refine ⟨E,?_,rfl⟩
        exact (congrArg (fun t => MeasurableSet[F t] E) hbl).mpr hE₀
      let x₀ := jointRectangleLp ν d hE₀
      let x' := jointRectangleLp ν' j hE'
      have hx₀ : ⇑x₀ =ᵐ[ν] (Ioc a₀ d ×ˢ E).indicator (fun _ => (1:ℝ)) :=
        indicatorConstLp_coeFn
      have hx' : ⇑x' =ᵐ[ν'] (Ioc l j ×ˢ E').indicator (fun _ => (1:ℝ)) :=
        indicatorConstLp_coeFn
      have hxK : K x = x₀ := by
        apply Lp.ext
        filter_upwards [jointAfterCLM_ae b x,hx,hx₀] with p h₁ h₂ h₃
        rw [h₁,h₂,h₃]
        by_cases ht : b<p.1
        · rw [ite_eq_left ht]
          have hEq : p ∈ Ioc a d ×ˢ E ↔ p ∈ Ioc a₀ d ×ˢ E := by
            change ((a<p.1 ∧ p.1≤d) ∧ p.2∈E) ↔ ((max b a<p.1 ∧ p.1≤d) ∧ p.2∈E)
            rw [max_lt_iff,and_iff_right ht]
          by_cases hm : p ∈ Ioc a d ×ˢ E
          · rw [indicator_of_mem hm,indicator_of_mem (hEq.mp hm)]
          · rw [indicator_of_notMem hm,indicator_of_notMem (hm ∘ hEq.mpr)]
        · rw [ite_eq_right ht,indicator_of_notMem]
          exact fun h => ht ((le_max_left b a).trans_lt h.1.1)
      have hxI : I x = x' := by
        apply Lp.ext
        filter_upwards [hI x,hφ.ae hx,hx',ae_mem_joint_timeBand G Q r] with p h₁ h₂ h₃ hp
        rw [h₁,h₂,h₃]
        have hpos : b<b+p.1 := lt_add_of_pos_right b hp.1.1
        have hbeg : a<b+p.1 ↔ l<p.1 := by
          calc
            a<b+p.1 ↔ a₀<b+p.1 := by
              dsimp [a₀]
              rw [max_lt_iff]
              exact ⟨fun hh => ⟨hpos,hh⟩,And.right⟩
            _ ↔ l<p.1 := by rw [←hbl,add_lt_add_iff_left]
        have hend : b+p.1≤d ↔ p.1≤j := by rw [←hbj,add_le_add_iff_left]
        have hEq : φ p∈Ioc a d ×ˢ E ↔ p∈Ioc l j ×ˢ E' := by
          change ((a<b+p.1 ∧ b+p.1≤d) ∧ p.2.val∈E) ↔
            ((l<p.1 ∧ p.1≤j) ∧ p.2.val∈E)
          rw [hbeg,hend]
        by_cases hm : φ p∈Ioc a d ×ˢ E
        · rw [indicator_of_mem hm,indicator_of_mem (hEq.mp hm)]
        · rw [indicator_of_notMem hm,indicator_of_notMem (hm ∘ hEq.mpr)]
      rw [hxK,hxI]
      apply Lp.ext
      filter_upwards [jointIto_rectangle_ae hB'₂ hB' hB'c hlj hjr hE',
        hO (J x₀),hSub.ae (jointIto_rectangle_ae hB₂ hB hBc ha₀d hdT hE₀),
        hAgree l (hlj.trans hjr),hAgree j hjr] with ω h₁ h₂ h₃ hl hj
      change J' x' ω = O (J x₀) ω
      rw [h₁,h₂,h₃]
      by_cases hω : ω.val∈E
      · have h'ω : ω∈E' := hω
        rw [indicator_of_mem hω,indicator_of_mem h'ω,hj,hl,hbl,hbj]
        ring
      · have h'ω : ω∉E' := hω
        rw [indicator_of_notMem hω,indicator_of_notMem h'ω]
  have hvI : v = I u := Lp.ext (hv.trans (hI u).symm)
  have huK : K u = u := by
    apply Lp.ext
    filter_upwards [jointAfterCLM_ae b u,hSupport] with p hp h
    rw [hp]
    by_cases ht : b<p.1
    · exact ite_eq_left ht
    · rw [ite_eq_right ht,h (le_of_not_gt ht)]
  have he := DFunLike.congr_fun hComparison u
  change J' (I u) = O (J (K u)) at he
  rw [huK,←hvI] at he
  rw [he]
  exact hO (J u)

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.birthTrace_jointIto_shift
