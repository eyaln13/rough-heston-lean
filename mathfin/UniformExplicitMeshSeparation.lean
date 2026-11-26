import ExplicitFixedMeshCount
import CanonicalPulseOriginalMean
import PulseAgeMeanBound

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston

/-- The mesh count is uniform over the actual fixed-mesh laws. The pulse
first and mixed second moments are supplied by the original-law resolvent.
Only the single-birth lower bound remains as a probability input. -/
theorem uniform_explicitLebesgueMesh_separation
    {T r : ℝ≥0} {α κ σ b v₀ c ℓ : ℝ}
    (hT : 0<T) (hα : 1/2<α) (hα' : α<1) (hb : 0<b)
    (hr : 0<r) (hrT : (r:ℝ)<(T:ℝ)/3) (hc : 0<c) (hℓ : 0<ℓ) :
    ∃ p : ℝ≥0∞,0<p ∧
      ∀ (ε : ℝ) (hε : 0<ε), ε≤b*(T:ℝ)/12 → lebesguePulseDuration α ε≤(r:ℝ)/2 →
      ∀ (L : FractionalFixedMeshLaw T α κ σ (lebesgueMeshInitial T b ε v₀) (lebesgueMeshInput T α b ε)),
      (∀ i : {i : ℕ // i ∈ interiorPulseBirths T b ε},
        c*ε ≤ (L.law : Measure (CanonicalPath T (CoupledPhysicalState (FixedMeshClusterIndex (T:ℝ) b ε)))).real
          {p | ℓ≤canonicalPhysicalVariance T
            (some (interiorLebesguePulseIndex (NNReal.coe_nonneg T) hb hε i))
            (lebesguePulseBirthTime b ε i.val+r) p ∧
            canonicalPhysicalVariance T none (lebesguePulseBirthTime b ε i.val+r) p=0}) →
      p≤(L.pairLaw:Measure (CanonicalPath T (ℝ×ℝ))) {q | ℓ≤canonicalPairGap T q} := by
  have hα₀ : 0<α := by linarith
  obtain ⟨D,hD,hRb⟩ := fractionalSecondKindResolvent_finite_kernel_bound (κ := κ) hα₀ (NNReal.coe_nonneg T)
  let R := fractionalSecondKindResolvent α κ
  let K := D*fractionalK α ((r:ℝ)/2)
  have hr₀ : 0<(r:ℝ) := NNReal.coe_pos.mpr hr
  have hK : 0≤K := mul_nonneg hD (fractionalK_nonnegative_on_positive hα₀ (half_pos hr₀))
  have hR : Measurable R := measurable_physical_fractionalSecondKindResolvent α κ
  have hR0 : ∀ u≤0,R u=0 := fractionalSecondKindResolvent_causal α κ
  have hRes : ∀ u∈Ioc (0:ℝ) (T:ℝ),R u=fractionalK α u-κ*volterraConvolution (fractionalK α) R u :=
    fun u hu => fractionalSecondKindResolvent_identity hα₀ hu.1
  refine ⟨ENNReal.ofReal ((c*(b*(T:ℝ)/4))^2/(1+2*(K/ℓ)^2*(b*(T:ℝ))^2)),
    ENNReal.ofReal_pos.mpr (by positivity),?_⟩
  intro ε hε hmesh hdsmall L hLower
  refine L.explicitLebesgueMesh_separation hT hα hα' hb hε hmesh hr hrT hc hK hℓ ?_ hLower
  intro i
  let j := interiorLebesguePulseIndex (NNReal.coe_nonneg T) hb hε i
  let τ := lebesguePulseBirthTime b ε i.val
  let d := lebesguePulseDuration α ε
  have hd : 0<d := Real.rpow_pos_of_pos hε _
  have hτ := interior_lebesguePulseBirthTime (NNReal.coe_nonneg T) hb hε i.property
  have htR : (τ:ℝ)+(r:ℝ)<(T:ℝ) := by dsimp [τ]; linarith [hτ.2]
  have ht : τ+r<T := NNReal.coe_lt_coe.mp htR
  have ht₀ : 0<τ+r := hr.trans_le (le_add_of_nonneg_left zero_le)
  have hm := L.pulse_original_mean (i := j) (τ := τ) (ε := ε) (d := d)
    rfl rfl hα hα' hd hR hR0 hD hRb hRes ht₀ ht
  rw [NNReal.coe_add] at hm
  change (∫ p,canonicalPhysicalVariance T (some j) (τ+r) p
    ∂(L.law:Measure (CanonicalPath T (CoupledPhysicalState (FixedMeshClusterIndex (T:ℝ) b ε)))))≤K*ε
  rw [hm]
  exact translatedPulse_resolvent_mean_le hα₀ hα' hε.le hd hr₀ hdsmall htR.le hD hR hR0 hRb

#print axioms uniform_explicitLebesgueMesh_separation

end RoughHeston
