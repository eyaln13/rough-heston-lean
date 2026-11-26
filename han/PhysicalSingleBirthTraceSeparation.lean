import SinglePulseTraceSeparation
import PhysicalBirthStopCertificate
import FocalPulseStopAtAge
import RawBirthTracePulseStoppedLaw
import PulseEnvelopeHorizon

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston.GirsanovPort

universe u

/-- The original physical focal residual and its mixed compensator
with the common Brownian driver on the selected observation horizon. -/
structure PhysicalBirthFocalCertificate {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) (F : Filtration ℝ≥0 m) (T : ℝ≥0) (σ : ℝ)
    (B J U X C : ℝ≥0 → Ω → ℝ) : Prop where
  residual_martingale : Martingale J F P
  residual_memLp : ∀ t, MemLp (J t) 2 P
  focal_predictable : IsStronglyPredictable F U
  aggregate_predictable : IsStronglyPredictable F X
  compensated_product : Martingale (fun t => B t*J t-C t) F P
  density_integrable : ∀ᵐ ω ∂P, IntervalIntegrable
    (fun u : ℝ => focalBracketDensity σ U X u.toNNReal ω) volume 0 (T:ℝ)
  compensator : ∀ t≤T, C t =ᵐ[P] fun ω => ∫ u in (0:ℝ)..(t:ℝ),
    focalBracketDensity σ U X u.toNNReal ω

set_option maxHeartbeats 3300000 in
/-- For one mesh birth, a fixed-horizon physical certificate and the
focal dynamics give the linear separation probability on the original
birth trace. The choice of observation age and constants is uniform
over meshes and filtered spaces. -/
theorem uniform_physical_single_birth_trace_separation
    {α κ σ η D rCap : ℝ} {H : ℝ≥0}
    (hα : 1/2<α) (hα' : α<1) (hκ : 0≤κ) (hσ : 0<σ) (hH : 0<H)
    (hη : 0<η) (hD : 0≤D) (hrCap : 0<rCap)
    (hcomp : ∀ x∈Ioc 0 (H:ℝ), fractionalK α x/2≤fractionalSecondKindResolvent α κ x ∧
      fractionalSecondKindResolvent α κ x≤2*fractionalK α x) :
    ∃ (r : ℝ≥0) (ε₀ ℓ c : ℝ), 0<r ∧ r≤H ∧ (r:ℝ)<rCap ∧
      0<ε₀ ∧ ε₀=((r:ℝ)/8)^α ∧ 0<ℓ ∧ 0<c ∧
      ∀ {Ω : Type u} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
        {F : Filtration ℝ≥0 m} [F.IsComplete P] [F.IsRightContinuous]
        {b : ℝ≥0} {A : Set Ω} (hA : MeasurableSet[F b] A) (hPA : 0<P A)
        [IsProbabilityMeasure (birthTraceLaw P A)]
        {ε : ℝ} (hε : 0<ε) (hεle : ε≤ε₀)
        {B M Y C Jphysical Uphysical Xphysical Cmix : ℝ≥0 → Ω → ℝ} {j : ℝ → ℝ}
        {J U Ccl W : ℝ≥0 → A → ℝ},
        let μ := birthTraceLaw P A
        let G := birthTraceFiltration F b A
        PhysicalBirthStopCertificate P F (b+r) α κ σ B M Y C j →
        PhysicalBirthFocalCertificate P F (b+r) σ B Jphysical Uphysical Xphysical Cmix →
        FocalPulseDynamics μ G H α κ σ ε (ε^(1/α)) J U Ccl W →
        (∀ t (ω : A), U t ω=Uphysical (b+t) ω) →
        (∀ᵐ ω ∂μ, ∀ t≤r, J t ω=Jphysical (b+t) ω-Jphysical b ω) →
        (∀ t≤r, ∀ ω : A, U t ω≤Xphysical (b+t) ω) →
        (∀ s ∈ Ioc (0:ℝ≥0) r,
          (boundaryConditionedMeasure P A).real {ω | 0<Y (b+s) ω}≤D*(s:ℝ)^η) →
        c*ε≤μ.real {ω : A | ℓ≤U r ω ∧ Y (b+r) ω=0} := by
  let γ := η/6
  obtain ⟨Cenv,r,ε₀,ℓ,c,hCenv,hr,hrH,hrCap',hε₀,hεeq,hℓ,hc,hSep⟩ :=
    uniform_single_pulse_trace_separation.{u} (D:=D) hα hα' hκ hσ hH hη hrCap hcomp
  refine ⟨r,ε₀,ℓ,c,hr,hrH,hrCap',hε₀,hεeq,hℓ,hc,?_⟩
  intro Ω m P _ F _ _ b A hA hPA _ ε hε hεle B M Y C Jp Up Xp Cm j J U Ccl W
  intro μ G phys focal dyn hUJ hJ hParts hBoundary
  let d := ε^(1/α)
  let δ := (r:ℝ)^(2*η/3)
  have hα₀ : 0<α := by linarith
  have hd : 0<d := Real.rpow_pos_of_pos hε _
  have hdr : d≤(r:ℝ) := by
    have hh := Real.rpow_le_rpow hε.le (hεle.trans_eq hεeq) (one_div_nonneg.mpr hα₀.le)
    rw [←Real.rpow_mul (by positivity : 0≤(r:ℝ)/8),mul_one_div_cancel hα₀.ne',Real.rpow_one] at hh
    exact hh.trans (by linarith [NNReal.coe_nonneg r])
  let hG : G.IsComplete μ := birthTraceFiltration_complete hA
  let : G.IsComplete μ := hG
  have hnull : ∀ N : Set A, MeasurableSet N → μ N=0 → MeasurableSet[G 0] N :=
    fun _ _ ht => Filtration.IsComplete.measurableSet_of_null (𝓕:=G) ht 0
  have hYm : Measurable (Y (b+r)) :=
    ((phys.variance_predictable.stronglyAdapted (b+r)).mono (F.le (b+r))).measurable
  have hYt : Measurable (fun ω : A => Y (b+r) ω) := hYm.comp measurable_subtype_coe
  have hY₀ : ∀ ω : A, 0≤Y (b+r) ω := fun ω => phys.variance_nonnegative _ _
  have hσ₂ : 0≤σ := hσ.le
  obtain ⟨Y₀,hy₀⟩ := phys.variance_initial_bound
  obtain ⟨K4,hK4⟩ := phys.variance_fourth_bound
  let J' (t : ℝ≥0) := J (min t r)
  let C' (t : ℝ≥0) (ω : A) := ∫ u, σ^2*U u ω ∂hestonTimeMeasure (min t r)
  obtain ⟨pulseR,hCc,hCmon,hUint⟩ :=
    FocalPulseDynamics.frozen_at_cap_age dyn hrH
  have hJ' : ∀ᵐ ω ∂μ, ∀ t≤r, J' t ω=Jp (b+t) ω-Jp b ω := by
    filter_upwards [hJ] with ω hω t ht
    simpa only [J',min_eq_left ht] using hω t ht
  have hin (s : ℝ≥0) (hs : s∈Ioc (0:ℝ≥0) r) : AffineInputOn ((b+s:ℝ≥0):ℝ) j :=
    phys.affine_input _ (zero_le.trans_lt (lt_add_of_pos_right b hs.1)) (add_le_add_right hs.2 b)
  have hγ : 0≤γ := div_nonneg hη.le (by norm_num)
  have hgap : 3*γ<η := by dsimp [γ]; linarith
  have hδ : 0≤δ := Real.rpow_nonneg r.coe_nonneg _
  have hρ : IsStronglyPredictable F (focalBracketDensity σ Up Xp) :=
    focalBracketDensity_predictable focal.focal_predictable focal.aggregate_predictable
  have hStop := raw_birth_trace_pulse_stopped_law hA hPA
    phys.driver phys.driver_memLp phys.driver_martingale phys.driver_clock
    hr hα hα' hκ hσ₂ hε hγ hgap hδ hCenv hD hin
    phys.residual_martingale phys.residual_memLp phys.residual_continuous
    phys.residual_zero phys.variance_predictable phys.variance_continuous
    phys.variance_nonnegative hy₀ (fun t => (hK4 t).1) (fun t => (hK4 t).2)
    phys.compensated_square phys.compensator_integrable phys.compensator_monotone
    phys.compensator phys.inverse phys.amplitude hd hdr
    pulseR hCc (ae_of_all _ hCmon) hUJ hJ' focal.aggregate_predictable hParts hUint
    focal.residual_martingale focal.residual_memLp focal.compensated_product hρ
    focal.density_integrable focal.compensator hBoundary
  let Z := fractionalPulseMass ε J
  let Z' (t : ℝ≥0) := fractionalPulseMass ε J' (min t r)
  let env := envelopeStop r (Cenv*(r:ℝ)^(3*γ)) (clusterEnvelopeValue 0 σ (1+3*γ) U Z)
  let env' := envelopeStop r (Cenv*(r:ℝ)^(3*γ)) (clusterEnvelopeValue 0 σ (1+3*γ) U Z')
  have he : env'=env := by
    apply envelopeStop_eq_of_agree_before
    intro t ht ω
    simp only [Z,Z',J',fractionalPulseMass,clusterEnvelopeValue,min_eq_left ht.le]
  have hZeq : fractionalPulseMass ε J' r=Z r := by
    funext ω
    change ε+J (min r r) ω=ε+J r ω
    rw [min_self]
  change ∃ R : Measure A, ∃ (_ : IsProbabilityMeasure R),
    Nonempty (PulseStoppedLaw (sizeBiasedLaw μ (fractionalPulseMass ε J' r) ε) R r δ
      ((Cenv*D/(η-3*γ))*(r:ℝ)^η) (D*(r:ℝ)^η) env' (fun ω : A => Y (b+r) ω)) at hStop
  rw [he,hZeq] at hStop
  exact hSep hε hεle hnull dyn hYt hY₀ hStop

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.uniform_physical_single_birth_trace_separation
