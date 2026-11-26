import CanonicalBirthEventVersions

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston

theorem physical_completion_measurePreserving_id {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) :
    @MeasurePreserving Ω Ω (physicalCompletedSpace P) m id (physicalCompletedMeasure P) P := by
  have hm : @Measurable Ω Ω (physicalCompletedSpace P) m id :=
    fun _ hs => physical_ambient_le_completion P _ hs
  have hmap : @Measure.map Ω Ω (physicalCompletedSpace P) m id (physicalCompletedMeasure P) = P :=
    (trim_eq_map (μ := physicalCompletedMeasure P) (physical_ambient_le_completion P)).symm.trans
      (physical_completion_trim P)
  exact @MeasurePreserving.mk Ω Ω (physicalCompletedSpace P) m id (physicalCompletedMeasure P) P hm hmap

namespace FractionalFixedMeshLaw

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
  {α κ σ : ℝ} {v : Option ι→ℝ} {β : Option ι→ℝ≥0→ℝ}
  (L : FractionalFixedMeshLaw T α κ σ v β)
local notation "Path" => CanonicalPath T (CoupledPhysicalState ι)

/-- A finite fourth-norm envelope on the physical horizon follows from
the row moment estimates in the fixed-mesh law. -/
theorem variance_fourth_eLpNorm_on_horizon :
    ∃ D : ℝ≥0∞,D≠∞ ∧ ∀ i t, t≤T →
      eLpNorm (canonicalPhysicalVariance T i t) 4 (L.law:Measure Path)≤D := by
  obtain ⟨D,hD,hq⟩ := L.varianceMoments 2
  refine ⟨D^(1/4:ℝ),ENNReal.rpow_ne_top_of_nonneg (by norm_num) hD,?_⟩
  intro i t ht
  have hs : (fun p => ‖canonicalPhysicalVariance T i t p‖ₑ ^ (4:ℕ)) =ᵐ[(L.law:Measure Path)]
      fun p => ENNReal.ofReal (max (canonicalPhysicalVariance T i t p) 0)^(4:ℕ) := by
    filter_upwards [L.nonnegative] with p hp
    have h0 : 0≤canonicalPhysicalVariance T i t p := hp i (canonicalEvalTime T t)
    rw [← ofReal_norm,Real.norm_of_nonneg h0,max_eq_left h0]
  have hm : AEStronglyMeasurable (canonicalPhysicalVariance T i t) (L.law:Measure Path) :=
    (((continuous_apply i).comp continuous_fst).comp (continuous_canonicalPathEval T t)).stronglyMeasurable.aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (4:ℝ≥0∞) ≠ 0)
    (by simp : (4:ℝ≥0∞) ≠ ∞) hm]
  norm_num only [ENNReal.toReal_ofNat,ENNReal.rpow_natCast,ENNReal.rpow_ofNat,one_div]
  rw [lintegral_congr_ae hs]
  exact ENNReal.rpow_le_rpow (by simpa using hq i t ht) (by positivity)

theorem pulse_residual_zero_at_birth {i : ι} {τ : ℝ≥0} {ε d : ℝ}
    (hα : α<1) (hκ : 0≤κ) (hτ : τ≤T) (hv : v (some i)=0)
    (hβ : β (some i)=translatedPulseRate τ ε d) :
    canonicalPhysicalResidual T (some i) τ =ᵐ[(L.law:Measure Path)] 0 := by
  have hInv := L.inverse (some i)
  rw [hβ] at hInv
  exact (canonical_pulse_zero_through_birth hα hκ hv L.law L.starts L.nonnegative hτ hInv
    (L.residualMartingale (some i))).mono fun _ hp => hp.2

/-- The focal age martingale is precisely the physical residual increment
after birth; the assertion survives every measure-preserving extension. -/
theorem lifted_pulse_residual_ae_increment {S : Type*} [MeasurableSpace S]
    {Q : Measure S} {f : S→Path} (hf : MeasurePreserving f Q (L.law:Measure Path))
    {i : ι} {τ : ℝ≥0} {ε d : ℝ}
    (hα : α<1) (hκ : 0≤κ) (hτ : τ≤T) (hv : v (some i)=0)
    (hβ : β (some i)=translatedPulseRate τ ε d) :
    ∀ᵐ p ∂Q,∀ t,canonicalPhysicalResidual T (some i) (τ+t) (f p) =
      canonicalPhysicalResidual T (some i) (τ+t) (f p)-canonicalPhysicalResidual T (some i) τ (f p) := by
  filter_upwards [hf.quasiMeasurePreserving.ae (L.pulse_residual_zero_at_birth hα hκ hτ hv hβ)] with p hp t
  change canonicalPhysicalResidual T (some i) τ (f p)=0 at hp
  rw [hp,sub_zero]

/-- Transfer the physical fourth-norm envelope to the actual age variance
on any measure-preserving product or completion. The envelope can depend
on this fixed mesh; no uniform estimate is needed for continuity. -/
theorem lifted_pulse_age_fourth_bound {S : Type*} [MeasurableSpace S]
    {Q : Measure S} {f : S→Path} (hf : MeasurePreserving f Q (L.law:Measure Path))
    {i : ι} {τ H : ℝ≥0} {ε d : ℝ}
    (hα : α<1) (hκ : 0≤κ) (hτ : τ≤T) (hTH : τ+H≤T) (hv : v (some i)=0)
    (hβ : β (some i)=translatedPulseRate τ ε d) :
    ∃ D : ℝ≥0∞,D≠∞ ∧ ∀ t≤H,eLpNorm
      (fun p => canonicalPulseAgeVariance T τ i (v (some i)) t (f p)) 4 Q≤D := by
  obtain ⟨D,hD,hb⟩ := L.variance_fourth_eLpNorm_on_horizon
  refine ⟨D,hD,?_⟩
  intro t ht
  have h₁ : τ+t≤T := (add_le_add_right ht τ).trans hTH
  have he : (fun p => canonicalPulseAgeVariance T τ i (v (some i)) t (f p)) =ᵐ[Q]
      canonicalPhysicalVariance T (some i) (τ+t) ∘ f :=
    hf.quasiMeasurePreserving.ae ((L.pulseAge_ae_eq_physical hα hκ hτ hv hβ).mono fun _ hp => hp t)
  have hm : AEStronglyMeasurable (canonicalPhysicalVariance T (some i) (τ+t)) (L.law:Measure Path) :=
    (((continuous_apply (some i)).comp continuous_fst).comp (continuous_canonicalPathEval T (τ+t))).stronglyMeasurable.aestronglyMeasurable
  rw [eLpNorm_congr_ae he,eLpNorm_comp_measurePreserving hm hf]
  exact hb _ _ h₁

#print axioms variance_fourth_eLpNorm_on_horizon
#print axioms lifted_pulse_residual_ae_increment
#print axioms lifted_pulse_age_fourth_bound

end FractionalFixedMeshLaw
end RoughHeston
