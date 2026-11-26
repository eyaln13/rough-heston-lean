import FocalPulseDynamics
import CanonicalPulseBirthTrace

open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

open GirsanovPort

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {A : Set Ω} {H K : ℝ≥0}
  {α κ a σ ε d : ℝ} {M U C : ℝ≥0→Ω→ℝ}

/-- Freeze the pulse observables past the requested age horizon without
changing any of the inverse or compensation identities on the horizon. -/
theorem FractionalPulseProcess.freeze_horizon
    (hP : FractionalPulseProcess P F K α κ a ε d M U C) (hH : H≤K) :
    FractionalPulseProcess P F H α κ a ε d
      (fun t => M (min t H)) (fun t => U (min t H)) (fun t => C (min t H)) := by
  refine ⟨martingale_freeze_at hP.martingale H,fun t => hP.martingale_memLp (min t H),
    (fun ω => (hP.martingale_continuous ω).comp (continuous_id.min continuous_const)),?_ ,
    (fun t => (hP.variance_adapted (min t H)).mono (F.mono (min_le_left _ _))),
    (fun ω => (hP.variance_continuous ω).comp (continuous_id.min continuous_const)),
    (fun t ω => hP.variance_nonnegative (min t H) ω),?_ ,
    martingale_freeze_at hP.compensated_square H,fun t => hP.compensator_integrable (min t H),
    (fun s t hst => hP.compensator_monotone _ _ (min_le_min_right H hst)),?_ ,?_⟩
  · simpa only [min_eq_left (show (0:ℝ≥0)≤H from zero_le)] using hP.martingale_zero
  · intro ω
    simpa only [min_eq_left (show (0:ℝ≥0)≤H from zero_le)] using hP.variance_zero ω
  · intro t ht
    filter_upwards [hP.compensator t (ht.trans hH)] with ω hh
    rw [min_eq_left ht,hh]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le (NNReal.coe_nonneg t)] at hr
    change (2*a)*U r.toNNReal ω=(2*a)*U (min r.toNNReal H) ω
    rw [min_eq_left ((Real.toNNReal_le_iff_le_coe.mpr hr.2).trans ht)]
  · filter_upwards [hP.inverse] with ω hh
    intro r hr
    have hrt : r.toNNReal≤H := Real.toNNReal_le_iff_le_coe.mpr hr.2
    have hEq := hh r ⟨hr.1,hr.2.trans (NNReal.coe_le_coe.mpr hH)⟩
    change M (min r.toNNReal H) ω =
      volterraConvolution (fractionalL α) (fun u => U (min u.toNNReal H) ω) r +
        ∫ u in Ioc (0:ℝ) r,κ*U (min u.toNNReal H) ω-rectangularPulseRate ε d u
    rw [min_eq_left hrt,hEq]
    have hV (u : ℝ) (hu : u∈Ioc (0:ℝ) r) : U (min u.toNNReal H) ω=U u.toNNReal ω :=
      congrArg (fun s => U s ω) (min_eq_left ((Real.toNNReal_le_iff_le_coe.mpr (hu.2.trans hr.2))))
    congr 1
    · unfold volterraConvolution
      apply setIntegral_congr_fun measurableSet_Ioc
      intro u hu
      change fractionalL α (r-u)*U u.toNNReal ω=fractionalL α (r-u)*U (min u.toNNReal H) ω
      rw [hV u hu]
    · apply setIntegral_congr_fun measurableSet_Ioc
      intro u hu
      change κ*U u.toNNReal ω-rectangularPulseRate ε d u = κ*U (min u.toNNReal H) ω-rectangularPulseRate ε d u
      rw [hV u hu]

omit [IsProbabilityMeasure P] in
/-- The slice clock of a pulse has a simultaneous version on its whole
horizon, using continuity and a countable dense set of deterministic ages. -/
theorem FractionalPulseProcess.clock_ae_all
    (hP : FractionalPulseProcess P F H α κ (σ^2/2) ε d M U C)
    (hc : ∀ᵐ ω ∂P,Continuous (fun t => C t ω)) :
    ∀ᵐ ω ∂P,∀ t≤H,C t ω=∫ r in (0:ℝ)..(t:ℝ),σ^2*U r.toNNReal ω := by
  let X (t : ℝ≥0) := C (min t H)
  let Y (t : ℝ≥0) (ω : Ω) := ∫ r in (0:ℝ)..((min t H:ℝ≥0):ℝ),σ^2*U r.toNNReal ω
  obtain ⟨D,hD,hDense⟩ := exists_countable_dense (α := ℝ≥0)
  have hx : ∀ᵐ ω ∂P,Continuous (fun t => X t ω) :=
    hc.mono fun _ hw => hw.comp (continuous_id.min continuous_const)
  have hy : ∀ᵐ ω ∂P,Continuous (fun t => Y t ω) := by
    apply ae_of_all
    intro ω
    have hfc : Continuous (fun r : ℝ => σ^2*U r.toNNReal ω) :=
      continuous_const.mul ((hP.variance_continuous ω).comp continuous_real_toNNReal)
    have hp := intervalIntegral.continuous_primitive (μ := volume)
      (fun s t => hfc.intervalIntegrable s t) 0
    exact hp.comp (NNReal.continuous_coe.comp (continuous_id.min continuous_const))
  have he (t : ℝ≥0) (_ : t∈D) : X t =ᵐ[P] Y t := by
    have he := hP.compensator (min t H) (min_le_right _ _)
    simpa only [X,Y,show 2*(σ^2/2)=σ^2 by ring] using he
  filter_upwards [indistinguishable_of_ae_eq_on_dense hD hDense hx hy he] with ω hh t ht
  simpa only [X,Y,min_eq_left ht] using hh t

/-- Birth restriction changes a finite fourth-norm envelope by only a
finite deterministic factor. The frozen path remains L²-continuous. -/
theorem FocalPulseRegularity.of_frozen_birthTrace_fourth
    {b : ℝ≥0} (hA : MeasurableSet[F b] A) (hp : 0<P A)
    (hm : ∀ t≤H, Measurable (U t)) (hc : ∀ ω, Continuous (fun t => U t ω))
    {D : ℝ≥0∞} (hD : D≠∞) (hFourth : ∀ t≤H,eLpNorm (U t) 4 P≤D) :
    let Q := birthTraceLaw P A
    let _ : IsProbabilityMeasure Q := birthTraceLaw_isProbability (F.le b A hA) hp
    FocalPulseRegularity Q (fun t (ω : A) => U (min t H) ω) := by
  let Q := birthTraceLaw P A
  let hQ := birthTraceLaw_isProbability (F.le b A hA) hp
  let P' := boundaryConditionedMeasure P A
  let d := (P A)⁻¹ ^ (1/(4:ℝ≥0∞)).toReal
  have hPres : MeasurePreserving (Subtype.val : A→Ω) Q P' :=
    ⟨measurable_subtype_coe,birthTraceLaw_map (F.le b A hA)⟩
  have hd : d≠∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) (ENNReal.inv_ne_top.mpr hp.ne')
  have hw : ∀ t,eLpNorm (fun ω : A => U (min t H) ω) 4 Q≤d*D := by
    intro t
    have hms := hm (min t H) (min_le_right _ _)
    change eLpNorm (U (min t H) ∘ (Subtype.val : A→Ω)) 4 Q≤d*D
    rw [eLpNorm_comp_measurePreserving hms.aestronglyMeasurable hPres]
    calc
      _ ≤ d*eLpNorm (U (min t H)) 4 (P.restrict A) :=
        eLpNorm_smul_measure_le _ _ _ _
      _ ≤ d*D := by
        gcongr
        exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hFourth _ (min_le_right _ _))
  exact FocalPulseRegularity.of_uniform_fourth
    (fun t => (hm (min t H) (min_le_right _ _)).comp measurable_subtype_coe)
    (ae_of_all _ fun ω => (hc ω).comp (continuous_id.min continuous_const))
    (ENNReal.mul_ne_top hd hD) hw

#print axioms FractionalPulseProcess.freeze_horizon
#print axioms FractionalPulseProcess.clock_ae_all
#print axioms FocalPulseRegularity.of_frozen_birthTrace_fourth

end RoughHeston
