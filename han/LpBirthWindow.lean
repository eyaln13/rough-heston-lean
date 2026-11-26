import SHEStochastic.NativeTimeCut
import JointItoAssembly

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace RoughHeston.GirsanovPort

open SHEStochastic

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 m} {T : ℝ≥0}

local notation "ν" => jointPredictableMeasure F P T

/-- The post-birth time cut is a bounded linear map of joint L². -/
noncomputable def jointAfterCLM (b : ℝ≥0) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν := by
  let a (u : Lp ℝ 2 ν) : Lp ℝ 2 ν := NativeTimeCut.after b u
  have ha (u : Lp ℝ 2 ν) : ⇑(a u) =ᵐ[ν] fun p => if b<p.1 then u p else 0 :=
    NativeTimeCut.after_ae b u
  let A : Lp ℝ 2 ν →ₗ[ℝ] Lp ℝ 2 ν := {
    toFun := a
    map_add' := fun u v => by
      apply Lp.ext
      filter_upwards [ha (u+v),ha u,ha v,Lp.coeFn_add u v,Lp.coeFn_add (a u) (a v)] with p h₁ h₂ h₃ h₄ h₅
      change a (u+v) p = (a u+a v) p
      rw [h₁,h₅,Pi.add_apply,h₂,h₃,h₄,Pi.add_apply]
      by_cases h : b<p.1 <;> simp [h]
    map_smul' := fun c u => by
      apply Lp.ext
      filter_upwards [ha (c•u),ha u,
        Lp.coeFn_smul c u,Lp.coeFn_smul c (a u)] with p h₁ h₂ h₃ h₄
      change a (c•u) p = (c•a u) p
      simp only [Pi.smul_apply] at h₃ h₄
      rw [h₁,h₄,h₂,h₃]
      by_cases h : b<p.1 <;> simp [h]
  }
  refine A.mkContinuous 1 (fun u => ?_)
  rw [one_mul]
  have hA : MeasurableSet[F.predictable] (Ioi b ×ˢ (univ : Set Ω)) :=
    measurableSet_predictable_Ioi_prod MeasurableSet.univ
  let hi := (Lp.memLp u).indicator hA.nullMeasurableSet
  change ‖hi.toLp _‖ ≤ ‖u‖
  rw [Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp u).eLpNorm_lt_top.ne (eLpNorm_indicator_le u hA.nullMeasurableSet)

theorem jointAfterCLM_ae (b : ℝ≥0) (u : Lp ℝ 2 ν) :
    ⇑(jointAfterCLM b u) =ᵐ[ν] fun p => if b<p.1 then u p else 0 :=
  NativeTimeCut.after_ae b u

/-- The scalar completed integral takes a predictable rectangle to
the corresponding Brownian increment times its adapted indicator. -/
theorem jointIto_rectangle_ae {B : ℝ≥0 → Ω → ℝ}
    (hB₂ : ∀ t, MemLp (B t) 2 P) (hB : Martingale B F P)
    (hClock : Martingale (fun t ω => B t ω ^ 2-((min t T:ℝ≥0):ℝ)) F P)
    {a d : ℝ≥0} (had : a≤d) (hdT : d≤T) {E : Set Ω} (hE : MeasurableSet[F a] E) :
    ⇑(jointItoIntegralCLM T hB₂ (jointRectangleLp ν d hE)) =ᵐ[P]
      fun ω => E.indicator (fun ω => B d ω-B a ω) ω := by
  classical
  let v := jointRectangleSP had hdT hE
  rw [←jointSimpleAssembly_rectangle had hdT hE,jointItoIntegralCLM_agrees T hB₂ hB hClock]
  have hv := (memLp_jointItoSimple hB₂ v.val).coeFn_toLp
  refine hv.trans (ae_of_all _ fun ω => ?_)
  change jointItoSimple B ((ElementaryPredictableSet.IocProd a d hE).indicator (1:ℝ)) ω = _
  simp only [jointItoSimple,ElementaryPredictableSet.indicator,
    ElementaryPredictableSet.IocProd,ite_eq_left had,Finset.mem_singleton]
  by_cases hω : ω∈E <;> simp [hω]

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.jointAfterCLM_ae
#print axioms RoughHeston.GirsanovPort.jointIto_rectangle_ae
