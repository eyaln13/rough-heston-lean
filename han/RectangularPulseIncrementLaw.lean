import FocalNoiseIncrementMoment
import RectangularPulseMomentLaw
import ClusterResolventIncrementRow

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston.GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 m} {T : ℝ≥0} {B U : ℝ≥0 → Ω → ℝ}

set_option maxHeartbeats 1000000 in
/-- Increments of the centered focal variance under the original law.
The estimate includes a left endpoint at the time of birth. -/
theorem rectangularPulse_centered_increment_law {α κ δ σ ε d S C : ℝ}
    (hα : 1/2<α) (hα' : α<1) (hd : 0<d) (hεd : ε=d^α)
    (hdS : d≤S) (htS : (T:ℝ)≤2*S) (hδ : 0≤δ) (hq : 0<2*α-1-2*δ)
    (hC : 0≤C) (n : ℕ) (hz : 0≤α-1+((2^n:ℕ):ℝ)*(2*α-1-2*δ))
    (hnull : ∀ N : Set Ω, MeasurableSet N → P N=0 → MeasurableSet[F 0] N)
    (hb : MathFinBridge.BrownianOn P F T B)
    (hB₂ : ∀ r, MemLp (B r) 2 P) (hB : Martingale B F P)
    (hBc : ∀ᵐ ω ∂P, Continuous (fun r => B r ω)) (hB₀ : B 0=ᵐ[P] 0)
    (hclock : Martingale (fun r ω => B r ω^2-((min r T:ℝ≥0):ℝ)) F P)
    (hU : IsStronglyPredictable F U) (hU₀ : ∀ t ω, 0≤U t ω) (hstart : ∀ ω, U 0 ω=0)
    (hUi : ∀ t, Integrable (U t) P) {A : ℝ} (hMean : ∀ t, (∫ ω, U t ω ∂P) ≤ A)
    (hcomp : ∀ x∈Ioc 0 (T:ℝ), 0≤fractionalSecondKindResolvent α κ x ∧
      fractionalSecondKindResolvent α κ x≤2*fractionalK α x)
    (hder : ∀ x h, 0<x → 0≤h → x+h≤(T:ℝ) →
      |fractionalSecondKindResolvent α κ (x+h)-fractionalSecondKindResolvent α κ x|≤C*x^(α-2)*h)
    (v : ℝ → Lp ℝ 2 P) (hvM : StronglyMeasurable v) (hvC : ContinuousOn v (Icc 0 (T:ℝ)))
    (hvU : ∀ s∈Ioc (0:ℝ) (T:ℝ), ⇑(v s)=ᵐ[P] U s.toNNReal)
    (hEq : ∀ s∈Icc 0 (T:ℝ), v s=
      volterraSmulConvolution (fractionalK α)
        (fun u => clusterDeterministicInputLp P (rectangularPulseRate ε d) u-κ • v u) s+
        σ • fixedHestonConvolutionLp (T:=T) hα hB₂ hU hU₀ hUi hMean s) :
    let p := 2*(2^n:ℕ)
    let N (t : ℝ≥0) (ω : Ω) := U t ω-∫ y, U t y ∂P
    let D := focalPulseMomentConstant α σ n
    let K := focalNoiseIncrementConstant α δ σ (2/(Real.Gamma α)) C D n
    ∀ a b : ℝ≥0, a<b → b≤T →
      Integrable (fun ω => ‖N b ω-N a ω‖^p) P ∧
      (∫ ω, ‖N b ω-N a ω‖^p ∂P) ≤ K*(ε*S^((p:ℝ)*(2*α-1)-α-(p:ℝ)*δ)*((b:ℝ)-(a:ℝ))^((p:ℝ)*δ)) := by
  let R := fractionalSecondKindResolvent α κ
  let p := 2*(2^n:ℕ)
  let D := focalPulseMomentConstant α σ n
  let mean (t : ℝ≥0) := ∫ y, U t y ∂P
  have hRzero (x : ℝ) (hx : x≤0) : R x=0 := fractionalSecondKindResolvent_zero_of_nonpos α κ hx
  have hg : 0 < Real.Gamma α := Real.Gamma_pos_of_pos (by linarith)
  have hdom (x : ℝ) (hx : x∈Ioc 0 (T:ℝ)) : |R x|≤2*fractionalK α x := by
    rw [abs_of_nonneg (hcomp x hx).1]; exact (hcomp x hx).2
  have hpnt (x : ℝ) (hx : x∈Ioc 0 (T:ℝ)) : |R x|≤(2/Real.Gamma α)*x^(α-1) := by
    exact (hdom x hx).trans_eq (by rw [fractionalK,if_neg (not_le.mpr hx.1)]; ring)
  have hmom := rectangularPulse_cluster_dyadic_moments hα hα'.le hd hεd hdS htS
    hnull hB₂ hB hBc hB₀ hclock hU hU₀ hUi hMean hcomp v hvM hvC hvU hEq
  have hcut : ∀ᵐ s ∂hestonTimeMeasure T, 0<s ∧ s<T := by
    rw [hestonTimeMeasure,ae_map_iff continuous_real_toNNReal.measurable.aemeasurable
      (by measurability : MeasurableSet {s : ℝ≥0 | 0<s ∧ s<T})]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact ⟨Real.toNNReal_pos.mpr hs.1,by change (s.toNNReal:ℝ)<(T:ℝ); rw [Real.coe_toNNReal _ hs.1.le]; exact hs.2⟩
  have hprev : ∀ᵐ t ∂hestonTimeMeasure T, Integrable (fun ω => U t ω^(2^n:ℕ)) P ∧
      (∫ ω, U t ω^(2^n:ℕ) ∂P) ≤ (D*ε*S^((((2^n:ℕ):ℝ)-1)*(2*α-1)))*(t:ℝ)^(α-1) := by
    filter_upwards [hcut] with t ht
    obtain ⟨hi,hm⟩ := hmom n t ht.1 ht.2.le
    refine ⟨?_,hm.trans_eq (by dsimp [D];ring)⟩
    have hi' := hi.integrable_norm_pow'
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hU₀ _ _)] using hi'
  have row (t : ℝ≥0) (ht : t≤T) : ∃ f : Lp ℝ 2 (jointPredictableMeasure F P t),
      (⇑f =ᵐ[jointPredictableMeasure F P t] fun z => σ*R ((t:ℝ)-(z.1:ℝ))*Real.sqrt (U z.1 z.2)) ∧
      (U t =ᵐ[P] fun ω => mean t+jointItoIntegralCLM t (fun r => hB₂ (min r t)) f ω) := by
    rcases eq_or_lt_of_le (show (0:ℝ≥0)≤t from zero_le) with he|hp
    · subst t
      refine ⟨0,?_,?_⟩
      · filter_upwards [Lp.coeFn_zero ℝ 2 (jointPredictableMeasure F P 0)] with z hz
        change (0 : Lp ℝ 2 (jointPredictableMeasure F P 0)) z = 0 at hz
        change (0 : Lp ℝ 2 (jointPredictableMeasure F P 0)) z = _
        rw [hz]
        simp [R,hRzero _ (neg_nonpos.mpr z.1.coe_nonneg)]
      · rw [map_zero]
        filter_upwards [Lp.coeFn_zero ℝ 2 P] with ω hz
        simp [mean,hstart,hz]
    · have h := rectangularPulse_resolvent_rows_on_horizon hα hα'.le hB₂ hB hclock hU hU₀
        hUi hMean hdom v hvM hvC hvU hEq t ⟨hp,ht⟩
      dsimp only at h
      rw [Real.toNNReal_coe] at h
      obtain ⟨f,hf,he,hm⟩ := h
      exact ⟨f,hf,by simpa only [mean,hm] using he⟩
  dsimp only
  intro a b hab hbT
  obtain ⟨fa,hfa,hea⟩ := row a (hab.le.trans hbT)
  obtain ⟨fb,hfb,heb⟩ := row b hbT
  obtain ⟨f,hf,he⟩ := cluster_increment_of_resolvent_rows hB₂ hB hclock (hab.le.trans hbT) hbT
    hRzero fa fb hfa hfb hea heb
  obtain ⟨hm,hest⟩ := focal_noise_increment_power_bound hα hα' hδ hq (hd.trans_le hdS)
    (hεd ▸ Real.rpow_nonneg hd.le _) (by positivity : 0≤2/Real.Gamma α) hC
    (focalPulseMomentConstant_nonneg α σ n) n hz hab hbT htS hb hnull hB₂ hB hclock
    (hU.mono F.predictable_le_prod).measurable hU₀ (fractionalSecondKindResolvent_measurable α κ)
    hRzero hpnt hder f hf hprev
  have he' : (fun ω => ‖(U b ω-mean b)-(U a ω-mean a)‖^p) =ᵐ[P]
      fun ω => ‖jointItoIntegralCLM T hB₂ f ω‖^p := he.mono fun ω h => by
    dsimp only; congr 2; linarith
  exact ⟨(hm.integrable_norm_pow' ).congr he'.symm,(integral_congr_ae he').le.trans hest⟩

#print axioms rectangularPulse_centered_increment_law

end RoughHeston.GirsanovPort
