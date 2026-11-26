import FocalSizeBiasBrownian
import PulsedFocalCompensator
import SHE.ContinuousPredictable
import FiniteBrownianFreezing
import BirthTraceMartingaleShift
import ActualFractionalPulse
import PulseActivation

open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped NNReal ENNReal Interval Topology

namespace RoughHeston.GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 m} [F.IsComplete P] [F.IsRightContinuous]
  {A : Set Ω} {b r : ℝ≥0} {B Xphysical Uphysical Mphysical FocalClock : ℝ≥0 → Ω → ℝ}

local notation "G" => birthTraceFiltration F b A
local notation "μ" => birthTraceLaw P A

set_option maxHeartbeats 4500000 in
/-- Focal mass positivity and the first tilted Brownian are obtained
from the actual rectangular pulse and its physical mixed compensator. -/
theorem raw_focal_first_tilt_on_birth_trace
    (hA : MeasurableSet[F b] A) (hPA : 0<P A) [IsProbabilityMeasure μ]
    (hB : MathFinBridge.BrownianOn P F (b+r) B)
    (hBm : Martingale B F P) (hB₂ : ∀ t, MemLp (B t) 2 P)
    {α κ σ ε d : ℝ} (hα : 0<α) (hα' : α<1) (hκ : 0≤κ) (hε : 0<ε) (hd : 0<d)
    (hdr : d≤(r:ℝ))
    {J U C : ℝ≥0 → A → ℝ} (hPulse : FractionalPulseProcess μ G r α κ (σ^2/2) ε d J U C)
    (hCc : ∀ ω, Continuous (fun t => C t ω))
    (hCmon : ∀ᵐ ω ∂μ, Monotone (fun t => C t ω))
    (hUJ : ∀ t (ω : A), U t ω = Uphysical (b+t) ω)
    (hJ : ∀ᵐ ω ∂μ, ∀ t≤r, J t ω = Mphysical (b+t) ω-Mphysical b ω)
    (hXpred : IsStronglyPredictable F Xphysical)
    (hParts : ∀ t≤r, ∀ ω : A, U t ω≤Xphysical (b+t) ω)
    (hUint : Integrable (Function.uncurry U) ((hestonTimeMeasure r).prod μ))
    (hMold : Martingale Mphysical F P) (hMold₂ : ∀ t, MemLp (Mphysical t) 2 P)
    (hMixed : Martingale (fun t => B t*Mphysical t-FocalClock t) F P)
    (hDensity : IsStronglyPredictable F (focalBracketDensity σ Uphysical Xphysical))
    (hiDensity : ∀ᵐ ω ∂P, IntervalIntegrable
      (fun u : ℝ => focalBracketDensity σ Uphysical Xphysical u.toNNReal ω) volume 0 ((b+r:ℝ≥0):ℝ))
    (hFocalClock : ∀ t≤b+r, FocalClock t =ᵐ[P] fun ω => ∫ u in (0:ℝ)..(t:ℝ),
      focalBracketDensity σ Uphysical Xphysical u.toNNReal ω) :
    let Z (t : ℝ≥0) (ω : A) := fractionalPulseMass ε J (min t r) ω
    let X (t : ℝ≥0) (ω : A) := Xphysical (b+t) ω
    let D (t : ℝ≥0) (ω : A) := B (b+min t r) ω-B b ω
    let Q := sizeBiasedLaw μ (Z r) ε
    Martingale Z G μ ∧ (Z 0 =ᵐ[μ] fun _ => ε) ∧
      (∀ᵐ ω ∂μ, ∀ t, 0<Z t ω) ∧ (∀ t, MemLp (Z t) 2 μ) ∧
      IsProbabilityMeasure Q ∧ Q ≪ μ ∧ μ ≪ Q ∧
      Integrable (fun p : ℝ≥0 × A => (focalDriverDrift σ Z U X p.1 p.2)^2) ((hestonTimeMeasure r).prod Q) ∧
      ∃ W : ℝ≥0 → A → ℝ, MathFinBridge.BrownianOn Q G r W ∧
        ∀ᵐ ω ∂Q, ∀ t≤r, W t ω=D t ω-∫ u, focalDriverDrift σ Z U X u ω ∂hestonTimeMeasure t := by
  let Z (t : ℝ≥0) (ω : A) := fractionalPulseMass ε J (min t r) ω
  let X (t : ℝ≥0) (ω : A) := Xphysical (b+t) ω
  let D (t : ℝ≥0) (ω : A) := B (b+min t r) ω-B b ω
  let Q := sizeBiasedLaw μ (Z r) ε
  let : (G).IsComplete μ := birthTraceFiltration_complete hA
  let : (G).IsRightContinuous := birthTraceFiltration_rightContinuous hA
  have hU : IsStronglyPredictable G U :=
    SHE.ContinuousPredictable.stronglyMeasurable _ _ hPulse.variance_adapted hPulse.variance_continuous
  have hX : IsStronglyPredictable G X := stronglyPredictable_birthTrace hXpred
  have hMass := fractional_pulse_mass_identity hα hα' hε.le hd hPulse
  have hi : ∀ᵐ ω ∂μ, ∀ t≤r, J t ω =
      volterraConvolution (fractionalL α) (fun u => U u.toNNReal ω) t +
        κ*(∫ u in Ioc (0:ℝ) t,U u.toNNReal ω) - ε/d*min (t:ℝ) d := by
    filter_upwards [hMass] with ω hω t ht
    specialize hω (t:ℝ) ⟨t.coe_nonneg,NNReal.coe_le_coe.mpr ht⟩
    rw [Real.toNNReal_coe] at hω
    change ε+J t ω = _ at hω
    unfold clusterAccumulatedVariance at hω
    linarith
  have hdp : 0<d.toNNReal := Real.toNNReal_pos.mpr hd
  have hdr' : d.toNNReal≤r := Real.toNNReal_le_iff_le_coe.mpr hdr
  have hi' : ∀ᵐ ω ∂μ, ∀ t≤r, J t ω =
      volterraConvolution (fractionalL α) (fun s => U s.toNNReal ω) t +
      κ * (∫ s in Ioc (0 : ℝ) t, U s.toNNReal ω) -
        ε / (d.toNNReal:ℝ) * min (t:ℝ) (d.toNNReal:ℝ) := by
    simpa only [Real.coe_toNNReal d hd.le] using hi
  have hPos := focal_mass_positive_of_rectangular_inverse hdp hdr' hε hα' hκ
    hPulse.martingale hU hPulse.martingale_continuous hPulse.martingale_zero
    hPulse.variance_continuous hPulse.variance_zero (fun t _ => hPulse.variance_nonnegative t) hi'
  have hZp : ∀ᵐ ω ∂μ, ∀ t, 0<Z t ω :=
    hPos.mono fun ω hω t => hω _ (min_le_right _ _)
  have hJm := martingale_freeze_at hPulse.martingale r
  have hZ₂ (t : ℝ≥0) : MemLp (Z t) 2 μ := (memLp_const ε).add (hPulse.martingale_memLp (min t r))
  have hZm : Martingale Z G μ := (martingale_const G μ ε).add hJm
  have hZb : Z 0 =ᵐ[μ] fun _ => ε := by
    filter_upwards [hPulse.martingale_zero] with ω hω
    simp [Z,fractionalPulseMass,hω]
  have hZc (ω : A) : Continuous (fun t => Z t ω) := continuous_const.add
    ((hPulse.martingale_continuous ω).comp (continuous_id.min continuous_const))
  have hZpred : IsStronglyPredictable G Z :=
    SHE.ContinuousPredictable.stronglyMeasurable _ _ hZm.stronglyAdapted hZc
  let C' (t : ℝ≥0) := C (min t r)
  have hCS := martingale_freeze_at hPulse.compensated_square r
  have hLinear := (hJm.smul (2*ε)).add (martingale_const G μ (ε^2))
  have hZclock : Martingale (fun t => Z t*Z t-C' t) G μ := by
    have he :
        ((fun t => J (min t r)*J (min t r)-C (min t r)) +
          (((2*ε) • (fun t => J (min t r))) + (fun _ _ => ε^2))) =
          (fun t => Z t*Z t-C' t) := by
      funext t ω
      simp only [Pi.add_apply,Pi.smul_apply,Pi.mul_apply,Pi.sub_apply,smul_eq_mul]
      dsimp [Z,C',fractionalPulseMass]
      ring
    rw [←he]
    exact hCS.add hLinear
  have hC' (ω : A) : Continuous (fun t => C' t ω) :=
    (hCc ω).comp (continuous_id.min continuous_const)
  have hCmon' : ∀ᵐ ω ∂μ, Monotone (fun t => C' t ω) :=
    hCmon.mono fun ω hω => hω.comp (monotone_id.min monotone_const)
  have hClock : ∀ᵐ ω ∂μ, ∀ t≤r, C' t ω = ∫ u in (0:ℝ)..(t:ℝ), σ^2*U u.toNNReal ω := by
    have hf (t : ℝ≥0) : C' t =ᵐ[μ] fun ω =>
        ∫ u in (0:ℝ)..((min t r:ℝ≥0):ℝ), σ^2*U u.toNNReal ω := by
      have htwo : 2*(σ^2/2)=σ^2 := by ring
      simpa only [C',htwo] using hPulse.compensator (min t r) (min_le_right t r)
    obtain ⟨S,hSc,hSd⟩ := exists_countable_dense ℝ≥0
    have hf' := (ae_ball_iff hSc).mpr fun t _ => hf t
    filter_upwards [hf'] with ω hω t ht
    have hPrim : Continuous (fun t : ℝ≥0 =>
        ∫ u in (0:ℝ)..((min t r:ℝ≥0):ℝ), σ^2*U u.toNNReal ω) := by
      have hc : Continuous (fun u : ℝ => σ^2*U u.toNNReal ω) :=
        continuous_const.mul ((hPulse.variance_continuous ω).comp continuous_real_toNNReal)
      exact (intervalIntegral.continuous_primitive (fun a d => hc.intervalIntegrable a d) 0).comp
        (NNReal.continuous_coe.comp (continuous_id.min continuous_const))
    have hClose : IsClosed {t : ℝ≥0 | C' t ω=
        ∫ u in (0:ℝ)..((min t r:ℝ≥0):ℝ), σ^2*U u.toNNReal ω} := isClosed_eq (hC' ω) hPrim
    have hsub : S ⊆ {t : ℝ≥0 | C' t ω=
        ∫ u in (0:ℝ)..((min t r:ℝ≥0):ℝ), σ^2*U u.toNNReal ω} := fun t ht => hω t ht
    have hx := closure_minimal hsub hClose
    rw [hSd.closure_eq] at hx
    have ht' := hx (mem_univ t)
    simpa only [mem_ofPred_eq,min_eq_left ht] using ht'
  have hD : MathFinBridge.BrownianOn μ G r D :=
    finiteBrownianOn_freeze (brownianOn_birthTrace hB hA hPA)
  have hMix := martingale_compensatedProduct_birthTrace_density (P:=P) (F:=F) (A:=A)
    (b:=b) (T:=b+r) (H:=r) (M:=B) (N:=Mphysical) (C:=FocalClock)
    (d:=focalBracketDensity σ Uphysical Xphysical) hA hPA
    (show b+r≤b+r from le_rfl) hBm hMold hB₂ hMold₂ hMixed hDensity hiDensity hFocalClock ε
  have hEqMix (t : ℝ≥0) : (fun (ω : A) => (B (b+min t r) ω-B b ω) *
        (Mphysical (b+min t r) ω-Mphysical b ω+ε) -
       ∫ u, focalBracketDensity σ Uphysical Xphysical (b+u) ω ∂hestonTimeMeasure (min t r)) =ᵐ[μ]
      (fun ω => Z (min t r) ω*D (min t r) ω -
        ∫ u, σ*U u ω/Real.sqrt (X u ω) ∂hestonTimeMeasure (min t r)) := by
    filter_upwards [hJ] with ω hJω
    simp only [Z,D,fractionalPulseMass,min_assoc,min_self,hJω _ (min_le_right t r)]
    have hEq (u : ℝ≥0) : focalBracketDensity σ Uphysical Xphysical (b+u) ω =
        σ * U u ω / Real.sqrt (X u ω) := by
      rw [hUJ u ω]
      rfl
    simp_rw [hEq]
    ring
  have hrho : IsStronglyPredictable G (focalBracketDensity σ U X) :=
    focalBracketDensity_predictable hU hX
  have hMixedAdapted : StronglyAdapted G
      (fun t ω => Z (min t r) ω*D (min t r) ω -
        ∫ u, σ*U u ω/Real.sqrt (X u ω) ∂hestonTimeMeasure (min t r)) := by
    intro t
    let i := min t r
    have hn : StronglyMeasurable[G i] (fun ω => Z i ω * D i ω) :=
      (hZm.stronglyAdapted i).mul (hD.adapted i)
    have hc : StronglyMeasurable[G i] (fun ω : A =>
        ∫ u, σ*U u ω/Real.sqrt (X u ω) ∂hestonTimeMeasure i) :=
      stronglyAdapted_timePrimitive hrho i
    exact (hn.sub hc).mono ((G).mono (min_le_left t r))
  have hMix' := hMix.congr hMixedAdapted hEqMix
  refine ⟨hZm,hZb,hZp,hZ₂,?_⟩
  exact focalDriverDrift_sizeBiasedBrownian («μ»:=μ) (F:=G) (H:=r) (B:=D)
    (Z:=Z) (U:=U) (X:=X) (C:=C') (ε:=ε) (σ:=σ) hD hZm hZclock hε hZb (hZ₂ r) hZc hC'
    (hZp.mono fun _ hω t _ => hω t) (fun t => hZp.mono fun _ hω => (hω t).le)
    hCmon' hZpred hU hX (ae_of_all _ fun ω t ht => ⟨hPulse.variance_nonnegative t ω,hParts t ht ω⟩)
    hUint hClock hMix'

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.raw_focal_first_tilt_on_birth_trace
