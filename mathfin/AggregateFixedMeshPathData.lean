import FractionalFixedMeshAggregateLp

/-! Observable rows on the actual Brownian extension, including their
samplewise and L² inverse data. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

open MathFin.ItoLocalMartingale (nullAugmentation)

set_option maxHeartbeats 1800000

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
  {α κ σ : ℝ} {v : Option ι → ℝ} {β : Option ι → ℝ≥0 → ℝ}
local notation "Ω" => CanonicalPath T (CoupledPhysicalState ι)
local notation "Ω'" => Ω × (ℝ≥0 → ℝ)
local notation "G" => canonicalPathNaturalFiltration (E := CoupledPhysicalState ι) T

namespace FractionalFixedMeshLaw

variable (L : FractionalFixedMeshLaw T α κ σ v β)
local notation "Physμ" => (L.law : Measure Ω)
local notation "Extμ" => Measure.prod (L.law : Measure Ω) gaussianLimit
local notation "ExtF" => nullAugmentation (prodFiltration G canonicalAuxiliaryFiltration) Extμ

noncomputable def liftedAggregateVariance (f : C(ℝ × ℝ, ℝ)) : ℝ≥0 → Ω' → ℝ :=
  fun t z => f (canonicalPathEval T t (canonicalAggregatePair z.1))

/-- Fixed-mesh trajectories satisfy the predictability, first-moment
and L² continuity properties used in the fractional inversion theorem. -/
theorem liftedAggregateVariance_L2_data {f : C(ℝ × ℝ, ℝ)}
    (hf : f = canonicalFirstVariance ∨ f = canonicalSecondVariance) :
    let U := liftedAggregateVariance (ι := ι) (T := T) f
    IsStronglyPredictable ExtF U ∧ StronglyAdapted ExtF U ∧
    (∀ z, Continuous (fun t => U t z)) ∧ (∀ t z, 0 ≤ U t z) ∧
    (∀ t, Integrable (U t) Extμ) ∧ (∃ A : ℝ, ∀ t, (∫ z, U t z ∂Extμ) ≤ A) ∧
    ∃ w : ℝ → Lp ℝ 2 Extμ, Continuous w ∧ ∀ s, ⇑(w s) =ᵐ[Extμ] U s.toNNReal := by
  intro U
  have hAdapt : StronglyAdapted ExtF U := by
    intro t
    let Gp := prodFiltration G canonicalAuxiliaryFiltration
    have h1 := (stronglyAdapted_canonicalVarianceCoordinate T f t).comp_measurable
      (filtration_measurable_canonicalAggregatePair (ι := ι) (T := T) t)
    have h2 := h1.comp_measurable (@measurable_fst Ω (ℝ≥0 → ℝ) (G t) (canonicalAuxiliaryFiltration t))
    exact h2.mono (show Gp t ≤ ExtF t from le_sup_left)
  have hCont (z : Ω') : Continuous (fun t => U t z) :=
    continuous_canonicalVarianceCoordinate_time T f (canonicalAggregatePair z.1)
  have hPred := hAdapt.isStronglyPredictable_of_leftContinuous (fun z _ => (hCont z).continuousWithinAt)
  have hZero (t : ℝ≥0) (z : Ω') : 0 ≤ U t z := by
    change 0 ≤ f (canonicalPathEval T t (canonicalAggregatePair z.1))
    rcases hf with h | h <;> rw [h] <;> exact le_max_left _ _
  obtain ⟨C₂,hC₂,h₂⟩ := L.lifted_aggregate_eLpNorm_uniform_dyadic 1
  obtain ⟨C₄,hC₄,h₄⟩ := L.lifted_aggregate_eLpNorm_uniform_dyadic 2
  have hBounds {j : ℕ} {C : ℝ≥0∞} (h : ∀ t,
      eLpNorm (fun z : Ω' => aggregateVarianceX T t z.1) ((2^j:ℕ):ℝ≥0∞) Extμ ≤ C ∧
      eLpNorm (fun z : Ω' => aggregateVarianceY T t z.1) ((2^j:ℕ):ℝ≥0∞) Extμ ≤ C) (t : ℝ≥0) :
      eLpNorm (U t) ((2^j:ℕ):ℝ≥0∞) Extμ ≤ C := by
    change eLpNorm (fun z : Ω' => f (canonicalPathEval T t (canonicalAggregatePair z.1)))
      ((2^j:ℕ):ℝ≥0∞) Extμ ≤ C
    rcases hf with hF | hF
    · rw [hF]; exact (h t).1
    · rw [hF]; exact (h t).2
  have h₂' (t : ℝ≥0) : eLpNorm (U t) 2 Extμ ≤ C₂ := by
    simpa only [pow_one, Nat.cast_ofNat] using hBounds h₂ t
  have h₄' (t : ℝ≥0) : eLpNorm (U t) 4 Extμ ≤ C₄ := by
    simpa only [Nat.reducePow, Nat.cast_ofNat] using hBounds h₄ t
  have hMeas (t : ℝ≥0) : AEStronglyMeasurable (U t) Extμ :=
    ((hAdapt t).mono ((ExtF).le t)).aestronglyMeasurable
  have hMem (t : ℝ≥0) : MemLp (U t) 2 Extμ := by
    exact (h₂' t).trans_lt (lt_top_iff_ne_top.mpr hC₂)
  have hInt (t : ℝ≥0) : Integrable (U t) Extμ := (hMem t).integrable one_le_two
  have hMean (t : ℝ≥0) : (∫ z, U t z ∂Extμ) ≤ C₂.toReal := by
    have he := (eLpNorm_le_eLpNorm_of_exponent_le (μ := Extμ) (f := U t) one_le_two).trans (h₂' t)
    rw [eLpNorm_one_eq_lintegral_enorm (hMeas t)] at he
    have hEq : (∫⁻ z, ‖U t z‖ₑ ∂Extμ) = ENNReal.ofReal (∫ z, U t z ∂Extμ) := by
      rw [ofReal_integral_eq_lintegral_ofReal (hInt t) (ae_of_all Extμ (hZero t))]
      exact lintegral_congr fun z => by rw [← ofReal_norm, Real.norm_of_nonneg (hZero t z)]
    rw [hEq] at he
    exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).1 (by simpa [ENNReal.ofReal_toReal hC₂] using he)
  let w (s : ℝ) := (hMem s.toNNReal).toLp (U s.toNNReal)
  have hw : Continuous w :=
    (continuous_toLp_two_of_continuous_paths_uniform_fourth hMem (ae_of_all Extμ hCont) hC₄ h₄').comp
      continuous_real_toNNReal
  exact ⟨hPred, hAdapt, hCont, hZero, hInt, ⟨C₂.toReal,hMean⟩, ⟨w,hw,fun s => (hMem s.toNNReal).coeFn_toLp⟩⟩

/-- Translate a projected scalar inverse identity into the samplewise
form required by the centered stochastic forward equation. -/
theorem liftedAggregateVariance_inverse_of_pullback {f : C(ℝ × ℝ, ℝ)} {M : ℝ≥0 → Ω → ℝ}
    {βR : ℝ → ℝ} {βN : ℝ≥0 → ℝ} (hRN : ∀ s ≥ 0, βR s = βN s.toNNReal)
    (hβR : Measurable βR) {D : ℝ} (hDR : ∀ s, ‖βR s‖ ≤ D)
    {v₀ : ℝ} (hInv : ∀ᵐ p ∂Physμ, ∀ t,
      canonicalVarianceMartingale T α v₀ κ 0 f t (canonicalAggregatePair p)+
        canonicalImmigrationShift T 0 βN t = M t p) :
    let U := liftedAggregateVariance (ι := ι) (T := T) f
    ∀ u : ℝ≥0, u ≤ T →
      (fun z => ∫ s in Ioc (0:ℝ) (u:ℝ), fractionalL α ((u:ℝ)-s)*(U s.toNNReal z-v₀)) =ᵐ[Extμ]
      (fun z => (∫ s in Ioc (0:ℝ) (u:ℝ), βR s-κ*U s.toNNReal z)+M u z.1) := by
  intro U u hu
  have hp : ∀ᵐ z : Ω' ∂Extμ, ∀ t,
      canonicalVarianceMartingale T α v₀ κ 0 f t (canonicalAggregatePair z.1)+
        canonicalImmigrationShift T 0 βN t = M t z.1 :=
    (measurePreserving_fst (μ := Physμ) (ν := gaussianLimit)).quasiMeasurePreserving.ae hInv
  filter_upwards [hp] with z hz
  have hZ := hz u
  unfold canonicalVarianceMartingale recoveredVarianceMartingale canonicalImmigrationShift at hZ
  rw [min_eq_left hu, mul_zero, zero_mul, sub_zero, zero_sub,
    intervalIntegral.integral_of_le u.coe_nonneg] at hZ
  have hV : Continuous (fun r : ℝ => U r.toNNReal z) :=
    (continuous_canonicalVarianceCoordinate_time T f (canonicalAggregatePair z.1)).comp continuous_real_toNNReal
  have hVi := (intervalIntegrable_iff_integrableOn_Ioc_of_le u.coe_nonneg).1 (hV.intervalIntegrable (μ := volume) 0 (u:ℝ))
  have hβi : IntegrableOn βR (Ioc 0 (u:ℝ)) :=
    (integrable_const D).mono' hβR.aestronglyMeasurable (ae_of_all _ hDR)
  have hβe : (∫ s in Ioc (0:ℝ) (u:ℝ), βN s.toNNReal) = ∫ s in Ioc (0:ℝ) (u:ℝ), βR s :=
    setIntegral_congr_fun measurableSet_Ioc (fun s hs => (hRN s hs.1.le).symm)
  rw [hβe] at hZ
  change (∫ s in Ioc (0:ℝ) (u:ℝ), fractionalL α ((u:ℝ)-s)*(U s.toNNReal z-v₀)) =
    (∫ s in Ioc (0:ℝ) (u:ℝ), βR s-κ*U s.toNNReal z)+M u z.1
  rw [integral_sub hβi (hVi.const_mul κ), integral_const_mul]
  change ((∫ s in Ioc (0:ℝ) (u:ℝ), fractionalL α ((u:ℝ)-s)*(U s.toNNReal z-v₀)) +
    κ*(∫ s in Ioc (0:ℝ) (u:ℝ), U s.toNNReal z)) - (∫ s in Ioc (0:ℝ) (u:ℝ), βR s) = M u z.1 at hZ
  linarith

end FractionalFixedMeshLaw

#print axioms RoughHeston.FractionalFixedMeshLaw.liftedAggregateVariance_L2_data
#print axioms RoughHeston.FractionalFixedMeshLaw.liftedAggregateVariance_inverse_of_pullback

end RoughHeston
