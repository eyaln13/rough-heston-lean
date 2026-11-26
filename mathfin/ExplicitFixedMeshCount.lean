import ExplicitLebesguePulseLaw
import CanonicalPulsePointMoments
import PhysicalResolventGlobalBound

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston
namespace FractionalFixedMeshLaw

variable {T : ℝ≥0} {α κ σ b ε v₀ : ℝ}
  (L : FractionalFixedMeshLaw T α κ σ (lebesgueMeshInitial T b ε v₀) (lebesgueMeshInput T α b ε))
local notation "Path" => CanonicalPath T (CoupledPhysicalState (FixedMeshClusterIndex (T:ℝ) b ε))

/-- The finite physical Lebesgue mesh gives a uniform closed separation
probability, from the individual original-law burst probabilities and
the uniform first-moment bound of a pulse at the fixed age. -/
theorem explicitLebesgueMesh_separation
    (hT : 0<T) (hα : 1/2<α) (hα' : α<1)
    (hb : 0<b) (hε : 0<ε) (hmesh : ε≤b*(T:ℝ)/12)
    {r : ℝ≥0} (hr : 0<r) (hrT : (r:ℝ)<(T:ℝ)/3)
    {c K ℓ : ℝ} (hc : 0<c) (hK : 0≤K) (hℓ : 0<ℓ)
    (hMean : ∀ i : {i : ℕ // i ∈ interiorPulseBirths T b ε},
      (∫ p,canonicalPhysicalVariance T
        (some (interiorLebesguePulseIndex (NNReal.coe_nonneg T) hb hε i))
        (lebesguePulseBirthTime b ε i.val+r) p ∂(L.law:Measure Path))≤K*ε)
    (hLower : ∀ i : {i : ℕ // i ∈ interiorPulseBirths T b ε},
      c*ε ≤ (L.law:Measure Path).real {p | ℓ ≤ canonicalPhysicalVariance T
        (some (interiorLebesguePulseIndex (NNReal.coe_nonneg T) hb hε i))
        (lebesguePulseBirthTime b ε i.val+r) p ∧
        canonicalPhysicalVariance T none (lebesguePulseBirthTime b ε i.val+r) p=0}) :
    ENNReal.ofReal ((c*(b*(T:ℝ)/4))^2/(1+2*(K/ℓ)^2*(b*(T:ℝ))^2)) ≤
      (L.pairLaw : Measure (CanonicalPath T (ℝ×ℝ))) {p | ℓ≤canonicalPairGap T p} := by
  let μ := (L.law:Measure Path)
  let F := interiorPulseBirths T b ε
  let idx (i : {i : ℕ // i ∈ F}) := interiorLebesguePulseIndex (NNReal.coe_nonneg T) hb hε i
  let obs (i : ℕ) := lebesguePulseBirthTime b ε i+r
  let A (i : ℕ) : Path→ℝ := if hi : i∈F then canonicalPhysicalVariance T (some (idx ⟨i,hi⟩)) (obs i) else 0
  let m (i : ℕ) := ∫ p,A i p ∂μ
  have hObs (i : ℕ) (hi : i∈F) : 0<obs i ∧ obs i<T := by
    have hτ := interior_lebesguePulseBirthTime (NNReal.coe_nonneg T) hb hε hi
    refine ⟨hr.trans_le (le_add_of_nonneg_left zero_le),NNReal.coe_lt_coe.mp ?_⟩
    change ((lebesguePulseBirthTime b ε i:ℝ≥0):ℝ)+(r:ℝ)<(T:ℝ)
    linarith [hτ.2]
  have hA (i : ℕ) (hi : i∈F) :
      A i = canonicalPhysicalVariance T (some (idx ⟨i,hi⟩)) (obs i) := dite_eq_left hi
  have hAm (i : ℕ) (hi : i∈F) : Measurable (A i) := by
    rw [hA i hi]
    exact (((canonicalPhysicalVariance_adapted (T := T) (some (idx ⟨i,hi⟩)) (obs i)).mono
      ((canonicalPathNaturalFiltration (E := CoupledPhysicalState (FixedMeshClusterIndex (T:ℝ) b ε)) T).le
        (obs i)))).measurable
  obtain ⟨C,hC⟩ := L.variance_uniform_memLp 1
  norm_num at hC
  have hA₂ (i : ℕ) (hi : i∈F) : MemLp (A i) 2 μ := by
    rw [hA i hi]
    exact (hC (some (idx ⟨i,hi⟩)) (obs i) (hObs i hi).2.le).1
  have hAp (i : ℕ) (hi : i∈F) : 0≤ᵐ[μ] A i := by
    rw [hA i hi]
    exact L.nonnegative.mono fun p hp => hp (some (idx ⟨i,hi⟩)) (canonicalEvalTime T (obs i))
  have hm (i : ℕ) (hi : i∈F) : m i≤K*ε := by
    dsimp [m,μ]
    rw [hA i hi]
    exact hMean ⟨i,hi⟩
  have hα₀ : 0<α := by linarith
  obtain ⟨D,_,hD⟩ := fractionalSecondKindResolvent_finite_kernel_bound (κ := κ) hα₀ (NNReal.coe_nonneg T)
  have hmix (i : ℕ) (hi : i∈F) (j : ℕ) (hj : j∈F) (hij : i≠j) :
      (∫ p,A i p*A j p ∂μ)=m i*m j := by
    change (∫ p,A i p*A j p ∂μ)=(∫ p,A i p ∂μ)*(∫ p,A j p ∂μ)
    rw [hA i hi,hA j hj]
    have hne : idx ⟨i,hi⟩ ≠ idx ⟨j,hj⟩ := fun he =>
      hij (congrArg Subtype.val (interiorLebesguePulseIndex_injective (NNReal.coe_nonneg T) hb hε he))
    exact L.pulse_mixed_covariance hne rfl rfl hα hα'
      (measurable_physical_fractionalSecondKindResolvent α κ) hD
      (fun t ht => fractionalSecondKindResolvent_identity hα₀ ht.1)
      (lebesgueMeshInput_measurable _ _ _ _) (lebesgueMeshInput_norm_le _ _ _ _)
      (hObs i hi).1 (hObs i hi).2 (hObs j hj).1 (hObs j hj).2
  have hDom (i : ℕ) (hi : i∈F) :
      ∀ᵐ p ∂μ,A i p≤(canonicalPathEval T (obs i) (canonicalAggregatePair p)).1 := by
    rw [hA i hi]
    exact L.nonnegative.mono fun p hp => by
      rw [canonicalPathEval_canonicalAggregatePair]
      unfold canonicalPhysicalAggregate
      exact Finset.single_le_sum (fun j _ => hp (some j) (canonicalEvalTime T (obs i)))
        (Finset.mem_univ (idx ⟨i,hi⟩))
  have hLo (i : ℕ) (hi : i∈F) : c*ε≤μ.real
      {p | ℓ≤A i p ∧ (canonicalPathEval T (obs i) (canonicalAggregatePair p)).2=0} := by
    simp only [hA i hi,canonicalPathEval_canonicalAggregatePair]
    exact hLower ⟨i,hi⟩
  have hsep := interior_pulse_mesh_uniform_separation (μ := μ) hT hb hε hmesh hc hK hℓ
    canonicalAggregatePair continuous_canonicalAggregatePair.measurable obs A m
    hAm hA₂ hAp (fun _ _ => rfl) hm hmix hDom hLo
  change _≤(Measure.map canonicalAggregatePair μ) {p | ℓ≤canonicalPairGap T p}
  rw [Measure.map_apply continuous_canonicalAggregatePair.measurable
    (isClosed_canonicalPairSeparation T ℓ).measurableSet]
  exact hsep

#print axioms explicitLebesgueMesh_separation

end FractionalFixedMeshLaw
end RoughHeston
