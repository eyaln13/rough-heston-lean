import ActualFocalBlockMeans
import ActualFocalBurst
import UniformAcrossMeshLaws

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace RoughHeston.GirsanovPort

set_option maxHeartbeats 1200000 in
/-- On the birth trace, the actual focal dynamics supply all the burst and
envelope inputs. A capped competitor law gives a linear probability of
separation under the original trace measure, with one deterministic choice
of age, event threshold, and probability coefficient for all meshes. -/
theorem uniform_single_pulse_trace_separation {α κ σ η D rCap : ℝ} {H : ℝ≥0}
    (hα : 1/2<α) (hα' : α<1) (hκ : 0≤κ) (hσ : 0<σ) (hH : 0<H)
    (hη : 0<η) (hrCap : 0<rCap)
    (hcomp : ∀ x∈Ioc 0 (H:ℝ), fractionalK α x/2≤fractionalSecondKindResolvent α κ x ∧
      fractionalSecondKindResolvent α κ x≤2*fractionalK α x) :
    let γ := η/6
    ∃ (Cenv : ℝ) (r : ℝ≥0) (ε₀ ℓ c : ℝ), 0≤Cenv ∧ 0<r ∧ r≤H ∧ (r:ℝ)<rCap ∧
      0<ε₀ ∧ ε₀=((r:ℝ)/8)^α ∧ 0<ℓ ∧ 0<c ∧
      ∀ {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
        {F : Filtration ℝ≥0 mΩ} {M U C W : ℝ≥0 → Ω → ℝ} {ε : ℝ} {Y : Ω → ℝ},
        let d := ε^(1/α)
        let Z := fractionalPulseMass ε M
        let Q := sizeBiasedLaw P (Z r) ε
        let env := envelopeStop r (Cenv*(r:ℝ)^(3*γ)) (clusterEnvelopeValue 0 σ (1+3*γ) U Z)
        let δ := (r:ℝ)^(2*η/3)
        0<ε → ε≤ε₀ →
        (∀ N : Set Ω, MeasurableSet N → P N=0 → MeasurableSet[F 0] N) →
        FocalPulseDynamics P F H α κ σ ε d M U C W → Measurable Y → (∀ ω,0≤Y ω) →
        (∃ R : Measure Ω, ∃ (_ : IsProbabilityMeasure R), Nonempty
          (PulseStoppedLaw Q R r δ ((Cenv*D/(η-3*γ))*(r:ℝ)^η) (D*(r:ℝ)^η) env Y)) →
        c*ε≤P.real {ω | ℓ≤U r ω ∧ Y ω=0} := by
  let γ := η/6
  let β := 2*α-1
  let L := fractionalSecondKindResolvent α κ
  have hal : 0<α := by linarith
  have hL (x : ℝ) (hx : x∈Ioc 0 (H:ℝ)) : 0≤L x ∧ L x≤2*fractionalK α x := by
    have hk : 0≤fractionalK α x := by
      rw [fractionalK,if_neg (not_le.mpr hx.1)]
      exact div_nonneg (Real.rpow_nonneg hx.1.le _) (Real.Gamma_pos_of_pos hal).le
    exact ⟨(by linarith [(hcomp x hx).1] : 0≤fractionalSecondKindResolvent α κ x),(hcomp x hx).2⟩
  obtain ⟨cU,cZ,p,hcU,hcZ,hp,hBurst⟩ := exists_focal_burst_constants hα hα' hκ hσ hcomp
  obtain ⟨K,hK,hFull⟩ := uniform_focal_biased_block_means_of_regular_inverse hα hα' hκ hσ.le hH hL
  obtain ⟨E,hE,hChoose⟩ := uniform_actual_pulse_separation_of_resolvent_mean_over_sample_spaces
    (σ:=σ) (a:=σ^2/2) (γ:=γ) (cB:=1) hα hα' hκ (by positivity) hH (by dsimp [γ];positivity)
    hK hp hcU hcZ (by norm_num) hη hrCap (fractionalSecondKindResolvent_measurable α κ) hL
  obtain ⟨r,ε₀,c,hr,hrH,hcap,heps₀,hepsEq,hc,hSep⟩ := hChoose (E*D/(η-3*γ)) D
  have hr' : 0<(r:ℝ) := hr
  dsimp only
  refine ⟨E,r,ε₀,cU*(r:ℝ)^β,c,hE,hr,hrH,hcap,heps₀,hepsEq,by positivity,hc,?_⟩
  intro Ω mΩ P inst F M U C W ε Y
  intro hε hεle hnull h hYm hY₀ hStop
  let d := ε^(1/α)
  have hd : 0<d := Real.rpow_pos_of_pos hε _
  have he : ε=d^α := by
    dsimp [d];rw [← Real.rpow_mul hε.le,one_div,inv_mul_cancel₀ hal.ne',Real.rpow_one]
  have hdr : d≤(r:ℝ)/8 := by
    have hh := Real.rpow_le_rpow hε.le (hεle.trans_eq hepsEq) (one_div_nonneg.mpr hal.le)
    rw [← Real.rpow_mul (by positivity : 0≤(r:ℝ)/8),mul_one_div_cancel hal.ne',Real.rpow_one] at hh
    exact hh
  have hmean := h.resolvent_mean hα hα' hH hε.le hd hσ.le
    (fun s hs => by rw [abs_of_nonneg (hL s hs).1];exact (hL s hs).2)
  have hBlocks := hFull hd he hnull h.pulse h.clock h.regularity h.auxiliary h.auxiliary_memLp
    h.auxiliary_continuous h.auxiliary_clock h.orthogonal r hrH
  have hBur := hBurst hd he hdr hrH hnull h
  obtain ⟨R,hR,⟨hRS⟩⟩ := hStop
  have h := hSep P F univ ε M U C Y
  dsimp only at h
  simp only [boundaryConditionedMeasure,measure_univ,inv_one,Measure.restrict_univ,one_smul,
    probReal_univ,le_refl,setOf_and,inter_univ] at h
  exact h hε hεle trivial ‹FocalPulseDynamics P F H α κ σ ε d M U C W›.pulse
    (fun t _ => hmean.1 t) hmean.2 hBlocks hYm hY₀ hBur R hRS

#print axioms uniform_single_pulse_trace_separation

end RoughHeston.GirsanovPort
