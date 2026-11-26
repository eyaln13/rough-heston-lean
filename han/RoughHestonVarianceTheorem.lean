import ExplicitLebesgueBirthEndpoint
import MeshPhysicalStopCertificates
import PhysicalMeshFocalDynamics
import PhysicalMeshBirthIdentities
import UniformCompanionSecondMoments
import FractionalResolventLocalBounds

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston
open GirsanovPort

set_option maxHeartbeats 3200000 in
/-- The linear lower bound for an individual birth on the original
fixed-mesh law. The age, threshold and probability coefficient are
chosen before the mesh and its probability space. -/
theorem explicitLebesgueBirthLowerBound_proved : ExplicitLebesgueBirthLowerBound := by
  intro T α v₀ κ θ σ hT hα hα' hv₀ hκ hθ hσ
  let b := κ*θ
  have hb : 0<b := mul_pos hκ hθ
  have hTr : 0<(T:ℝ) := NNReal.coe_pos.mpr hT
  obtain ⟨cB,D,η,h₀,hcB,hD,hη,hh₀,hBound⟩ :=
    uniform_explicitLebesgueCompanion_zero_boundary (b:=b) hT hα hα' hκ.le hσ hb hv₀.le
  obtain ⟨rL,hrL,hL⟩ := fractionalResolvent_uniform_local_comparison (α:=α) (K:=κ)
    (by linarith) hκ.le
  let H := (min ((T:ℝ)/3) rL).toNNReal
  have hHr : (H:ℝ)=min ((T:ℝ)/3) rL := Real.coe_toNNReal _ (le_min (by positivity) hrL.le)
  have hH : 0<H := Real.toNNReal_pos.mpr (lt_min (by positivity) hrL)
  have hCmp (x : ℝ) (hx : x∈Ioc 0 (H:ℝ)) := hL κ x (by rw [abs_of_pos hκ]) hx.1
    (hx.2.trans (hHr.le.trans (min_le_right _ _)))
  let cap := min ((T:ℝ)/3) h₀
  have hCap : 0<cap := lt_min (by positivity) hh₀
  obtain ⟨r,ε₀,ℓ,c,hr,hrH,hrC,hε₀,_,hℓ,hc,hSep⟩ :=
    uniform_physical_single_birth_trace_separation.{0} hα hα' hκ.le hσ hH hη hD.le hCap hCmp
  refine ⟨r,cB*c,ℓ,ε₀,hr,hrC.trans_le (min_le_left _ _),mul_pos hcB hc,hℓ,hε₀,?_⟩
  intro ε hε _ hSmall _
  obtain ⟨L⟩ := exists_explicitLebesguePulseLaw (σ:=σ) hT hα hα' hκ.le hb hε hv₀.le
  refine ⟨L,?_⟩
  intro k
  let I := FixedMeshClusterIndex (T:ℝ) b ε
  let i : I := interiorLebesguePulseIndex T.coe_nonneg hb hε k
  let τ := lebesguePulseBirthTime b ε k.val
  let d := lebesguePulseDuration α ε
  have hi : lebesgueMeshInitial T b ε v₀ (some i)=0 := rfl
  have hβ : lebesgueMeshInput T α b ε (some i)=translatedPulseRate τ ε d := rfl
  have hτ : (τ:ℝ)∈Icc ((T:ℝ)/3) (2*(T:ℝ)/3) :=
    interior_lebesguePulseBirthTime T.coe_nonneg hb hε k.property
  have hτH : τ+H≤T := by
    apply NNReal.coe_le_coe.mp
    rw [NNReal.coe_add]
    linarith [hτ.2,hHr.le.trans (min_le_left _ _)]
  let Path := CanonicalPath T (CoupledPhysicalState I)
  let Ω := Path × (ℝ≥0→ℝ)
  let P₀ := (L.law:Measure Path)
  let F := physicalUsualFiltration L.physicalMeshProduct L.physicalMeshProductFiltration
  let P := physicalCompletedMeasure L.physicalMeshProduct
  let A₀ : Set Path := {p | canonicalRegularVariance T none v₀ τ p=0}
  let A : Set Ω := Prod.fst ⁻¹' A₀
  let E : Set Path := {p | ℓ≤canonicalPhysicalVariance T (some i) (τ+r) p ∧ canonicalPhysicalVariance T none (τ+r) p=0}
  let raw := canonicalPathNaturalFiltration (E:=CoupledPhysicalState I) T
  have hmA : MeasurableSet A₀ := measurableSet_eq_fun
    (((canonicalRegularVariance_adapted (T:=T) (none : Option I) v₀ τ).mono (raw.le τ)).measurable) measurable_const
  have hmE : MeasurableSet E := (measurableSet_le measurable_const
    (((canonicalPhysicalVariance_adapted (T:=T) (some i) (τ+r)).mono (raw.le _)).measurable)).inter
      (measurableSet_eq_fun (((canonicalPhysicalVariance_adapted (T:=T) (none : Option I) (τ+r)).mono
        (raw.le _)).measurable) measurable_const)
  have hbnd := hBound hε L (τ:ℝ) hτ
  simp only [Real.toNNReal_coe] at hbnd
  have hBirth : cB≤(physicalCompletedMeasure P₀).real A₀ := hbnd.1
  have hBp : cB≤P.real A := hBirth.trans_eq (completedProduct_fst_event P₀ gaussianLimit hmA).symm
  have hp : 0<P A := (ENNReal.toReal_pos_iff.mp (hcB.trans_le hBp)).1
  have hOccupation (s : ℝ≥0) (hs : s∈Ioc 0 r) :
      (@boundaryConditionedMeasure Ω (physicalCompletedSpace L.physicalMeshProduct) P A).real
        {z | 0<canonicalRegularVariance T none v₀ (τ+s) z.1}≤D*(s:ℝ)^η := by
    have hm := ((canonicalRegularVariance_adapted (T:=T) (none : Option I) v₀ (τ+s)).mono (raw.le _)).measurable
    have h := completedProduct_birth_conditional P₀ gaussianLimit (E:={p : Path | 0<canonicalRegularVariance T none v₀ (τ+s) p}) hmA (measurableSet_lt measurable_const hm)
    have hold := hbnd.2 (s:ℝ) ⟨NNReal.coe_pos.mpr hs.1,
      (NNReal.coe_le_coe.mpr hs.2).trans (hrC.le.trans (min_le_right _ _))⟩
    simp only [←NNReal.coe_add,Real.toNNReal_coe] at hold
    exact h.le.trans hold
  have hTransfer := completedProduct_birthTrace_to_original P₀ gaussianLimit hmA hmE hc.le hcB hε.le hBirth
  have hId := L.physicalMeshBirthIdentities hα' hκ.le hτH hrH hi hβ
  have hPhys := L.meshPhysicalStopCertificates hα hα' hκ.le hσ hb.le (show 0≤lebesgueMeshInitial T b ε v₀ none from hv₀.le)
    hτH hrH hi hβ (show lebesgueMeshInput T α b ε none=fun _ => b from rfl)
  have hDyn := L.productBirthTraceFocalDynamics hα' hκ.le hτH hi hβ hp
  have hA : MeasurableSet[F τ] A := L.productCompanionBirthZero_measurable τ
  let _ : MeasurableSpace Ω := physicalCompletedSpace L.physicalMeshProduct
  let _ : IsProbabilityMeasure (birthTraceLaw P A) := birthTraceLaw_isProbability (F.le τ A hA) hp
  obtain ⟨B,Cf,phys,focal⟩ := hPhys
  obtain ⟨W,dyn⟩ := hDyn
  obtain ⟨hU,hJ,hUX,hEvents⟩ := hId
  have hTrace := hSep hA hp hε hSmall phys focal dyn hU hJ hUX hOccupation
  exact hTransfer (hTrace.trans_eq (hEvents ℓ))

/-- Pathwise nonuniqueness for the rough Heston variance equation.
Both continuous solutions have the same Brownian driver in their joint filtration. -/
theorem theorem1_1 : Theorem1_1 :=
  theorem1_1_of_explicitLebesgueBirthLowerBound explicitLebesgueBirthLowerBound_proved

#print axioms explicitLebesgueBirthLowerBound_proved
#print axioms theorem1_1

end RoughHeston
