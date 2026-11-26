import RectangularPulseIncrementLaw
import ClusterOldBlockSup
import FocalSupremumExponents
import ClusterResolventIncrements

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace RoughHeston.GirsanovPort

set_option maxHeartbeats 1400000 in
/-- The old-law supremum estimate on every block in one fractional
pulse equation. The order and constant do not depend on the pulse
mass, the observation block, or the filtered space. -/
theorem rectangularPulse_uniform_old_block_sup {α κ σ : ℝ} {H : ℝ≥0}
    (hα : 1/2<α) (hα' : α<1) (hH : 0<H) :
    ∃ m : ℕ, 0<m ∧ ∃ K : ℝ, 0≤K ∧ ∀ {Ω : Type*} [mΩ : MeasurableSpace Ω]
      {P : Measure Ω} [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
      {B U : ℝ≥0 → Ω → ℝ} {ε d : ℝ},
      0<d → ε=d^α →
      (∀ N : Set Ω, MeasurableSet N → P N=0 → MeasurableSet[F 0] N) →
      ∀ (hB₂ : ∀ r, MemLp (B r) 2 P), Martingale B F P →
      (∀ᵐ ω ∂P, Continuous (fun r => B r ω)) → B 0=ᵐ[P] 0 →
      Martingale (fun r ω => B r ω^2-((min r H:ℝ≥0):ℝ)) F P →
      ∀ (hU : IsStronglyPredictable F U) (hU₀ : ∀ t ω, 0≤U t ω)
        (hUi : ∀ t, Integrable (U t) P) {A : ℝ} (hMean : ∀ t, (∫ ω, U t ω ∂P)≤A),
      StronglyAdapted F U → (∀ ω, Continuous fun t => U t ω) → (∀ ω,U 0 ω=0) →
      Continuous (fun t => ∫ ω,U t ω ∂P) →
      (∀ x∈Ioc 0 (H:ℝ), 0≤fractionalSecondKindResolvent α κ x ∧
        fractionalSecondKindResolvent α κ x≤2*fractionalK α x) →
      ∀ v : ℝ → Lp ℝ 2 P, StronglyMeasurable v → ContinuousOn v (Icc 0 (H:ℝ)) →
      (∀ x∈Ioc (0:ℝ) (H:ℝ), ⇑(v x)=ᵐ[P] U x.toNNReal) →
      (∀ s∈Icc 0 (H:ℝ), v s=
        volterraSmulConvolution (fractionalK α)
          (fun u => clusterDeterministicInputLp P (rectangularPulseRate ε d) u-κ • v u) s+
          σ • fixedHestonConvolutionLp (T:=H) hα hB₂ hU hU₀ hUi hMean s) →
      ∀ T : ℝ≥0, ∀ S : ℝ, 0<T → T≤H → d≤S → (T:ℝ)≤2*S →
      ∃ W : Ω → ℝ, Measurable[F T] W ∧ (∀ ω,0≤W ω) ∧
        (∀ t≤T, ∀ ω,U t ω≤W ω) ∧ Integrable (fun ω => W ω^(2*m)) P ∧
        (∫ ω,W ω^(2*m) ∂P) ≤ K*ε*S^(((2*m:ℕ):ℝ)*(2*α-1)-α) := by
  obtain ⟨δ,n,hδ,hq,hγ,hOld,hdet⟩ := exists_focal_block_moment_order hα hα'
  obtain ⟨C,hC,hder⟩ := fractionalResolvent_kernel_increment_bound
    (by linarith : 0<α) hα' (abs_nonneg κ) (show 0<(H:ℝ) from hH)
  let m : ℕ := 2^n
  let p := 2*m
  let β := 2*α-1
  let γ := (p:ℝ)*δ
  let A := 4/(Real.Gamma α*α)
  let D := focalPulseMomentConstant α σ n
  let C₁ := focalNoiseIncrementConstant α δ σ (2/(Real.Gamma α)) C D n
  have hA : 0≤A := by dsimp [A]; have := Real.Gamma_pos_of_pos (show 0<α by linarith); positivity
  have hp : 0<p := by dsimp [p,m];positivity
  obtain ⟨K,hK,hmax⟩ := cluster_old_block_sup hp (show 1<γ from hγ)
    (show 0≤β by dsimp [β];linarith) hA (le_max_left 0 C₁) hdet
  refine ⟨m,by dsimp [m]; positivity,K,hK,?_⟩
  intro Ω mΩ P inst F B U ε d hd hε hnull hB₂ hB hBc hB₀ hclock hU hU₀ hUi A₀
    hMean hUa hUc h0 hIc hcomp v hvM hvC hvU hEq T S hT htH hdS htS
  have hε₀ : 0≤ε := hε ▸ Real.rpow_nonneg hd.le _
  have hS := hd.trans_le hdS
  have hloc (s : ℝ) (hs : s∈Ioc 0 (H:ℝ)) : |fractionalSecondKindResolvent α κ s|≤2*fractionalK α s := by
    rw [abs_of_nonneg (hcomp s hs).1];exact (hcomp s hs).2
  have hm := rectangularPulse_resolvent_old_means_on_horizon hα hα'.le hB₂ hB hclock hU hU₀
    hUi hMean hloc v hvM hvC hvU hEq
  let Bt (r : ℝ≥0) := B (min r T)
  have hBt : Martingale Bt F P := martingale_freeze_at hB T
  have hc : Martingale (fun r ω => Bt r ω^2-((min r T:ℝ≥0):ℝ)) F P := by
    simpa only [Bt,min_assoc,min_eq_left htH] using martingale_freeze_at hclock T
  have hBt₀ : Bt 0 =ᵐ[P] 0 := by simpa only [Bt,min_eq_left (show (0:ℝ≥0)≤T from zero_le)] using hB₀
  have hEqT (x : ℝ) (hx : x∈Icc 0 (T:ℝ)) : v x=
      volterraSmulConvolution (fractionalK α)
        (fun u => clusterDeterministicInputLp P (rectangularPulseRate ε d) u-κ • v u) x+
        σ • fixedHestonConvolutionLp (T:=T) (B:=Bt) hα (fun r => hB₂ (min r T)) hU hU₀ hUi hMean x := by
    rw [← fixedHestonConvolutionLp_horizon_agrees htH hα hB₂ hB hclock hU hU₀ hUi hMean
      (Real.toNNReal_le_iff_le_coe.mpr hx.2)]
    exact hEq x ⟨hx.1,hx.2.trans htH⟩
  apply hmax P F U (fun t => ∫ ω,U t ω ∂P) hT hd hdS hε htS hUa (fun ω => (hUc ω).continuousOn)
    hIc.continuousOn (fun ω => by simp [h0])
  · intro t ht
    rcases eq_or_lt_of_le (show (0:ℝ≥0)≤t from zero_le) with he|hlt
    · subst t; simp only [h0,integral_zero]; positivity
    · have hh : (t:ℝ) ∈ Ioc 0 (H:ℝ) := ⟨hlt,ht.trans htH⟩
      have he := hm t hh
      rw [Real.toNNReal_coe] at he
      rw [he]
      exact rectangularPulse_resolvent_peak (by linarith) hα'.le hε hd hh
        (fractionalSecondKindResolvent_measurable α κ) hcomp
  · intro a b hab hbT
    have hinc := rectangularPulse_centered_increment_law hα hα' hd hε hdS htS hδ.le hq hC n hOld
      hnull (cluster_unit_clock_brownian_on_age htH hnull hB hclock hBc hB₀)
      (fun r => hB₂ (min r T)) hBt (hBc.mono fun ω hh => hh.comp (continuous_id.min continuous_const))
      hBt₀ hc hU hU₀ h0 hUi hMean
      (fun x hx => hcomp x ⟨hx.1,hx.2.trans htH⟩)
      (fun x h hx hh hxh => hder κ x h le_rfl hx hh (hxh.trans htH))
      v hvM (hvC.mono (Icc_subset_Icc_right (show (T:ℝ)≤(H:ℝ) from htH)))
      (fun x hx => hvU x ⟨hx.1,hx.2.trans htH⟩) hEqT a b hab hbT
    refine ⟨hinc.1,hinc.2.trans ?_⟩
    apply mul_le_mul_of_nonneg_right (le_max_right 0 C₁)
    exact mul_nonneg (mul_nonneg hε₀ (Real.rpow_nonneg hS.le _))
      (Real.rpow_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hab.le)) _)

#print axioms rectangularPulse_uniform_old_block_sup

end RoughHeston.GirsanovPort
