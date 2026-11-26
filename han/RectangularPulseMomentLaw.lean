import FocalPowerMomentStep
import ClusterUnitClockRestriction
import ClusterPulsePeak

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston.GirsanovPort

/-- The constants in the cluster estimates are the same at all pulse
widths, all reference ages and all laws on which the equation is realized. -/
noncomputable def focalPulseMomentConstant (α σ : ℝ) : ℕ → ℝ
  | 0 => max 0 (4/(Real.Gamma α*α))
  | n+1 =>
    let A := 4/(Real.Gamma α*α)
    max 0 (focalPowerStepConstant α σ A A (focalPulseMomentConstant α σ n) n)

theorem focalPulseMomentConstant_nonneg (α σ : ℝ) (n : ℕ) : 0 ≤ focalPulseMomentConstant α σ n := by
  cases n <;> exact le_max_left _ _

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 m} {T : ℝ≥0} {B U : ℝ≥0 → Ω → ℝ}

theorem rectangularPulse_cluster_dyadic_moments {α κ σ ε d S : ℝ}
    (hα : 1/2<α) (hα' : α≤1) (hd : 0<d) (hεd : ε=d^α)
    (hdS : d≤S) (htS : (T:ℝ)≤2*S)
    (hnull : ∀ N : Set Ω, MeasurableSet N → P N=0 → MeasurableSet[F 0] N)
    (hB₂ : ∀ r, MemLp (B r) 2 P) (hB : Martingale B F P)
    (hBc : ∀ᵐ ω ∂P, Continuous (fun r => B r ω)) (hB₀ : B 0=ᵐ[P] 0)
    (hclock : Martingale (fun r ω => B r ω^2-((min r T:ℝ≥0):ℝ)) F P)
    (hU : IsStronglyPredictable F U) (hU₀ : ∀ t ω, 0≤U t ω)
    (hUi : ∀ t, Integrable (U t) P) {A : ℝ} (hMean : ∀ t, (∫ ω, U t ω ∂P) ≤ A)
    (hcomp : ∀ x∈Ioc 0 (T:ℝ), 0≤fractionalSecondKindResolvent α κ x ∧
      fractionalSecondKindResolvent α κ x≤2*fractionalK α x)
    (v : ℝ → Lp ℝ 2 P) (hvM : StronglyMeasurable v) (hvC : ContinuousOn v (Icc 0 (T:ℝ)))
    (hvU : ∀ s∈Ioc (0:ℝ) (T:ℝ), ⇑(v s)=ᵐ[P] U s.toNNReal)
    (hEq : ∀ s∈Icc 0 (T:ℝ), v s=
      volterraSmulConvolution (fractionalK α)
        (fun u => clusterDeterministicInputLp P (rectangularPulseRate ε d) u-κ • v u) s+
        σ • fixedHestonConvolutionLp (T:=T) hα hB₂ hU hU₀ hUi hMean s) :
    ∀ n (t : ℝ≥0), 0<t → t≤T →
      MemLp (U t) ((2^n:ℕ):ℝ≥0∞) P ∧
      (∫ ω, U t ω^(2^n:ℕ) ∂P) ≤ focalPulseMomentConstant α σ n *
        ε*(t:ℝ)^(α-1)*S^((((2^n:ℕ):ℝ)-1)*(2*α-1)) := by
  let R := fractionalSecondKindResolvent α κ
  let K := 4/(Real.Gamma α*α)
  have ha : 0<α := by linarith
  have hΓ := Real.Gamma_pos_of_pos ha
  have hK : 0≤K := div_nonneg (by norm_num) (mul_pos hΓ ha).le
  have hβ : 0≤2*α-1 := by linarith
  have hε : 0≤ε := hεd ▸ Real.rpow_nonneg hd.le _
  have hS := hd.trans_le hdS
  have hR : Measurable R := fractionalSecondKindResolvent_measurable α κ
  have hloc : ∀ x∈Ioc 0 (T:ℝ), |R x|≤2*fractionalK α x := by
    intro x hx; rw [abs_of_nonneg (hcomp x hx).1]; exact (hcomp x hx).2
  have hrows := rectangularPulse_resolvent_rows_on_horizon hα hα' hB₂ hB hclock hU hU₀
    hUi hMean hloc v hvM hvC hvU hEq
  let I (s : ℝ) := volterraConvolution R (rectangularPulseRate ε d) s
  have hOld (s : ℝ) (hs : s∈Ioc 0 (T:ℝ)) : I s ≤ K*ε*s^(α-1) := by
    have h := rectangularPulse_resolvent_mean_upper ha hα' hε hd hs hR hcomp
    rw [fractionalK,ite_eq_right (not_le.mpr hs.1)] at h
    exact h.trans_eq (by dsimp [K]; ring)
  have hPeak (s : ℝ) (hs : s∈Ioc 0 (T:ℝ)) : I s≤K*S^(2*α-1) :=
    (rectangularPulse_resolvent_peak ha hα' hεd hd hs hR hcomp).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hd.le hdS hβ) hK)
  intro n
  induction n with
  | zero =>
    intro t ht hT
    have ht' : (t:ℝ)∈Ioc 0 (T:ℝ) := ⟨ht,hT⟩
    obtain ⟨_,_,_,hmean⟩ := hrows t ht'
    have hmean' : (∫ ω, U t ω ∂P) = I t := by simpa only [Real.toNNReal_coe] using hmean
    simp only [pow_zero,Nat.cast_one,pow_one,sub_self,zero_mul,Real.rpow_zero,mul_one]
    refine ⟨memLp_one_iff_integrable.mpr (hUi t), ?_⟩
    rw [hmean',focalPulseMomentConstant,max_eq_right hK]
    exact hOld t ht'
  | succ n ih =>
    intro t ht htT
    have ht' : (t:ℝ)∈Ioc 0 (T:ℝ) := ⟨ht,htT⟩
    have hBt := martingale_freeze_at hB t
    have hct : Martingale (fun s ω => B (min s t) ω^2-((min s t:ℝ≥0):ℝ)) F P := by
      simpa only [min_assoc,min_eq_left htT] using martingale_freeze_at hclock t
    have hrow := hrows t ht'
    dsimp only at hrow
    rw [Real.toNNReal_coe] at hrow
    obtain ⟨u,hu,heq,hm⟩ := hrow
    have hi : 0 ≤ I t := (integral_nonneg (hU₀ t)).trans_eq hm
    have hprev (s : ℝ≥0) (hs : 0<s) (hst : s<t) := ih s hs (hst.le.trans htT)
    have hpow := focal_cluster_doubling_of_row ht hα hε hS (ht'.2.trans htS)
      (focalPulseMomentConstant_nonneg α σ n) hK
      (cluster_unit_clock_brownian_on_age htT hnull hB hclock hBc hB₀)
      hnull (fun r => hB₂ (min r t)) hBt hct (hU.mono F.predictable_le_prod).measurable
      hU₀ hR (fun x hx => hloc x (Ioc_subset_Ioc_right ht'.2 hx))
      n hi (hOld t ht') (hPeak t ht') u hu heq (fun s hs hst =>
        ⟨by simpa only [Real.norm_of_nonneg (hU₀ s _)] using
            (hprev s hs hst).1.integrable_norm_pow', (hprev s hs hst).2⟩)
    have he : (2^(n+1):ℕ)=2*(2^n) := by rw [pow_succ,Nat.mul_comm]
    rw [he]
    refine ⟨hpow.1,hpow.2.trans ?_⟩
    simp only [Nat.cast_mul,Nat.cast_ofNat,focalPulseMomentConstant]
    gcongr
    exact le_max_right _ _

#print axioms rectangularPulse_cluster_dyadic_moments

end RoughHeston.GirsanovPort
