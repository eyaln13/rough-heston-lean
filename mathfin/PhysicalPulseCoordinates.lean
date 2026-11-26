import IndependentProductPulseModels

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
local notation "Path" => CanonicalPath T (CoupledPhysicalState ι)
local notation "G" => canonicalPathNaturalFiltration (E := CoupledPhysicalState ι) T

/-- Physical-time version of the actual age pulse. It vanishes up to
birth on every path and has the same age coordinates after birth. -/
noncomputable def canonicalBirthFocalVariance (T τ : ℝ≥0) (i : ι)
    (t : ℝ≥0) (p : CanonicalPath T (CoupledPhysicalState ι)) : ℝ :=
  canonicalPulseAgeVariance T τ i 0 (t-τ) p

noncomputable def canonicalBirthDominatingAggregate (T τ : ℝ≥0) (i : ι)
    (t : ℝ≥0) (p : CanonicalPath T (CoupledPhysicalState ι)) : ℝ :=
  max (canonicalPhysicalAggregate T t p) (canonicalBirthFocalVariance T τ i t p)

theorem canonicalBirthFocal_age (τ : ℝ≥0) (i : ι) (s : ℝ≥0) (p : Path) :
    canonicalBirthFocalVariance T τ i (τ+s) p=canonicalPulseAgeVariance T τ i 0 s p := by
  simp [canonicalBirthFocalVariance]

theorem canonicalBirthFocal_data (τ : ℝ≥0) (i : ι) :
    StronglyAdapted G (canonicalBirthFocalVariance T τ i) ∧
      (∀ p : Path, Continuous (fun t => canonicalBirthFocalVariance T τ i t p)) ∧
      (∀ t (p : Path),0≤canonicalBirthFocalVariance T τ i t p) := by
  let V := canonicalRegularVariance T (some i) 0
  obtain ⟨hVc,hVn,_⟩ := canonicalRegularVariance_continuous_nonnegative_initial (T:=T)
    (v:=(0:ℝ)) (some i) le_rfl
  have hVa := canonicalRegularVariance_adapted (T:=T) (some i) (0:ℝ)
  refine ⟨?_,?_,?_⟩
  · intro t
    by_cases h : τ≤t
    · have ht := (hVa t).measurable
      have hb := ((hVa τ).mono ((G).mono h)).measurable
      change StronglyMeasurable[(G) t] (fun p => if V τ p=0 then V (τ+(t-τ)) p else 0)
      rw [add_tsub_cancel_of_le h]
      exact (ht.ite (measurableSet_eq_fun hb measurable_const) measurable_const).stronglyMeasurable
    · have hzero : canonicalBirthFocalVariance T τ i t=0 := by
        funext p
        simp only [canonicalBirthFocalVariance,canonicalPulseAgeVariance,tsub_eq_zero_of_le (le_of_not_ge h),add_zero,Pi.zero_apply]
        split <;> simp_all
      rw [hzero]
      exact stronglyMeasurable_const
  · intro p
    change Continuous (fun t => if V τ p=0 then V (τ+(t-τ)) p else 0)
    by_cases h : V τ p=0
    · simp only [ite_eq_left h]
      exact (hVc p).comp (continuous_const.add (continuous_id.sub continuous_const))
    · simp only [ite_eq_right h]
      exact continuous_const
  · intro t p
    unfold canonicalBirthFocalVariance canonicalPulseAgeVariance
    split <;> first | exact hVn _ _ | exact le_rfl

theorem canonicalBirthDominatingAggregate_data (τ : ℝ≥0) (i : ι) :
    StronglyAdapted G (canonicalBirthDominatingAggregate T τ i) ∧
      (∀ p : Path, Continuous (fun t => canonicalBirthDominatingAggregate T τ i t p)) ∧
      (∀ t (p : Path),canonicalBirthFocalVariance T τ i t p≤canonicalBirthDominatingAggregate T τ i t p) := by
  obtain ⟨hF,hc,_⟩ := canonicalBirthFocal_data (T:=T) τ i
  refine ⟨?_,?_,fun _ _ => le_max_right _ _⟩
  · intro t
    exact ((Finset.measurable_fun_sum _ (fun j _ => (canonicalPhysicalVariance_adapted (T:=T) (some j) t).measurable)).max
      (hF t).measurable).stronglyMeasurable
  · intro p
    exact (continuous_finsetSum Finset.univ (fun j _ => canonicalPhysicalVariance_time_continuous (T:=T) (some j) p)).max (hc p)

theorem FractionalFixedMeshLaw.birthCoordinates_ae {α κ σ ε d : ℝ}
    {v : Option ι → ℝ} {β : Option ι → ℝ≥0 → ℝ} (L : FractionalFixedMeshLaw T α κ σ v β)
    {i : ι} {τ : ℝ≥0} (hα : α<1) (hκ : 0≤κ) (hτ : τ≤T) (hv : v (some i)=0)
    (hβ : β (some i)=translatedPulseRate τ ε d) :
    ∀ᵐ p ∂(L.law:Measure Path), (∀ t, canonicalBirthFocalVariance T τ i t p=canonicalPhysicalVariance T (some i) t p) ∧
      (∀ t, canonicalBirthDominatingAggregate T τ i t p=canonicalFirstVariance
        (canonicalPathEval T t (canonicalAggregatePair p))) ∧ canonicalPhysicalResidual T (some i) τ p=0 := by
  have hInv := L.inverse (some i)
  rw [hβ] at hInv
  have hpre := canonical_pulse_zero_through_birth hα hκ hv L.law L.starts L.nonnegative hτ hInv (L.residualMartingale (some i))
  have heq := canonicalRegularVariance_ae_paths L.starts L.nonnegative (some i)
  rw [hv] at hpre heq
  filter_upwards [hpre,heq,L.nonnegative] with p hp hV hn
  have hU (t : ℝ≥0) : canonicalBirthFocalVariance T τ i t p=canonicalPhysicalVariance T (some i) t p := by
    unfold canonicalBirthFocalVariance canonicalPulseAgeVariance
    rw [ite_eq_left (hp.1 τ le_rfl)]
    by_cases h : τ≤t
    · simpa only [add_tsub_cancel_of_le h] using hV t
    · have ht := le_of_not_ge h
      rw [tsub_eq_zero_of_le ht,add_zero,hp.1 τ le_rfl,←hV t,hp.1 t ht]
  refine ⟨hU,?_,hp.2⟩
  intro t
  have hpos (j : ι) : 0≤canonicalPhysicalVariance T (some j) t p := hn (some j) (canonicalEvalTime T t)
  have hag : 0≤canonicalPhysicalAggregate T t p := Finset.sum_nonneg (fun j _ => hpos j)
  have hle : canonicalPhysicalVariance T (some i) t p≤canonicalPhysicalAggregate T t p :=
    Finset.single_le_sum (f:=fun j => canonicalPhysicalVariance T (some j) t p) (fun j _ => hpos j) (Finset.mem_univ i)
  change max _ _=max 0 (canonicalPhysicalAggregate T t p)
  rw [hU,max_eq_left hle,max_eq_right hag]

#print axioms canonicalBirthFocal_data
#print axioms canonicalBirthDominatingAggregate_data
#print axioms FractionalFixedMeshLaw.birthCoordinates_ae

end RoughHeston
