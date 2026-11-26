import HestonRealKernelNoiseMoment
import ClusterResolventEnergyPowers
import ClusterNoisePlusMean
import ClusterPowerRescaling

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston.GirsanovPort

open SHEStochastic

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 m} {T : ℝ≥0} {B U : ℝ≥0 → Ω → ℝ}

/-- Uniform constant in the induction. Its arguments contain no
mesh, pulse width, cluster law, age or time horizon. -/
noncomputable def focalPowerStepConstant (α σ A₀ D₀ D : ℝ) (n : ℕ) : ℝ :=
  let β := 2*α-1
  let A := (2*|σ|/Real.Gamma α)^2
  let J := Real.Gamma 1*Real.Gamma β/Real.Gamma (1+β)
  let G := Real.Gamma α*Real.Gamma β/Real.Gamma (α+β)
  let m := (2^n:ℕ)
  (2:ℝ)^(2*m-1)*(D₀*A₀^(2*m-1)+(NativeScalarBDG.constant n:ℝ)*
    ((((A*J)^((m:ℝ)-1)*A*D*G)*2^((m:ℝ)*β))))

theorem focal_cluster_doubling_of_row (hT : 0 < T) {α σ ε S A₀ D₀ D : ℝ}
    (hα : 1/2 < α) (hε : 0 ≤ ε) (hS : 0 < S) (htS : (T:ℝ) ≤ 2*S)
    (hD : 0 ≤ D) (hA₀ : 0 ≤ A₀)
    (hb : MathFinBridge.BrownianOn P F T B)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A=0 → MeasurableSet[F 0] A)
    (hB₂ : ∀ t, MemLp (B t) 2 P) (hB : Martingale B F P)
    (hclock : Martingale (fun t ω => B t ω^2-((min t T:ℝ≥0):ℝ)) F P)
    (hU : Measurable (Function.uncurry U)) (hu₀ : ∀ t ω, 0 ≤ U t ω)
    {R : ℝ → ℝ} (hR : Measurable R)
    (hdom : ∀ x ∈ Ioc 0 (T:ℝ), |R x| ≤ 2*fractionalK α x)
    (n : ℕ) {I : ℝ} (hI : 0 ≤ I)
    (hIold : I ≤ D₀*ε*(T:ℝ)^(α-1)) (hIpeak : I ≤ A₀*S^(2*α-1))
    (u : Lp ℝ 2 (jointPredictableMeasure F P T))
    (hu : u =ᵐ[jointPredictableMeasure F P T]
      fun z => σ*R ((T:ℝ)-(z.1:ℝ))*Real.sqrt (U z.1 z.2))
    (heq : U T =ᵐ[P] fun ω => I + jointItoIntegralCLM T hB₂ u ω)
    (hprev : ∀ t : ℝ≥0, 0 < t → t<T →
      Integrable (fun ω => U t ω^(2^n:ℕ)) P ∧ (∫ ω, U t ω^(2^n:ℕ) ∂P) ≤
        D*ε*(t:ℝ)^(α-1)*S^((((2^n:ℕ):ℝ)-1)*(2*α-1))) :
    MemLp (U T) ((2*2^n:ℕ):ℝ≥0∞) P ∧
      (∫ ω, U T ω^(2*2^n:ℕ) ∂P) ≤
        focalPowerStepConstant α σ A₀ D₀ D n*ε*(T:ℝ)^(α-1)*
          S^((2*((2^n:ℕ):ℝ)-1)*(2*α-1)) := by
  let m := (2^n:ℕ)
  let β := 2*α-1
  let A := (2*|σ|/Real.Gamma α)^2
  let J := Real.Gamma 1*Real.Gamma β/Real.Gamma (1+β)
  let G := Real.Gamma α*Real.Gamma β/Real.Gamma (α+β)
  let K (s : ℝ≥0) := R ((T:ℝ)-(s:ℝ))
  let w (s : ℝ≥0) := (σ*K s)^2
  let C := D*ε*S^(((m:ℝ)-1)*β)
  let c (s : ℝ≥0) := C*(s:ℝ)^(α-1)
  have hβ : 0 < β := by dsimp [β]; linarith
  have ha : 0 < α := by linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hJ : 0 ≤ J := by
    dsimp [J]; exact div_nonneg (mul_nonneg (Real.Gamma_pos_of_pos zero_lt_one).le
      (Real.Gamma_pos_of_pos hβ).le) (Real.Gamma_pos_of_pos (by linarith)).le
  have hG : 0 ≤ G := div_nonneg (mul_nonneg (Real.Gamma_pos_of_pos ha).le
    (Real.Gamma_pos_of_pos hβ).le) (Real.Gamma_pos_of_pos (add_pos ha hβ)).le
  have hk : Measurable K := hR.comp (measurable_const.sub measurable_subtype_coe)
  have hcut : ∀ᵐ s ∂hestonTimeMeasure T, 0 < s ∧ s < T := by
    rw [hestonTimeMeasure, ae_map_iff continuous_real_toNNReal.measurable.aemeasurable
      (by measurability : MeasurableSet {s : ℝ≥0 | 0 < s ∧ s < T})]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact ⟨Real.toNNReal_pos.mpr hs.1, by
      change (s.toNNReal : ℝ)<(T:ℝ); rw [Real.coe_toNNReal _ hs.1.le]; exact hs.2⟩
  have hp : ∀ᵐ s ∂hestonTimeMeasure T,
      Integrable (fun ω => U s ω^(2^n:ℕ)) P ∧ (∫ ω, U s ω^(2^n:ℕ) ∂P) ≤ c s := by
    filter_upwards [hcut] with s hs
    obtain ⟨hi,hm⟩ := hprev s hs.1 hs.2
    exact ⟨hi,hm.trans_eq (by dsimp [c,C,m,β]; ring)⟩
  obtain ⟨hwi,hw,hwci,hwc⟩ := cluster_resolvent_energy_power_bounds hT hα hC hR hdom
  obtain ⟨hnp,hN⟩ := heston_sqrt_row_real_moment hb hnull hB₂ hB hclock n hk
    hU hu₀ u hu hp hwi hwci
  have hd : 0 ≤ (m:ℝ)-1 := sub_nonneg.mpr (by exact_mod_cast Nat.one_le_pow n 2 (by decide))
  have hw' := Real.rpow_le_rpow (integral_nonneg (fun t => sq_nonneg (σ*K t))) hw hd
  have hfactor := mul_le_mul hw' hwc
    (integral_nonneg fun t => mul_nonneg (sq_nonneg _) (mul_nonneg hC (Real.rpow_nonneg t.coe_nonneg _)))
    (Real.rpow_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg (Real.rpow_nonneg T.coe_nonneg _) hJ)) _)
  have ht' : 0 < (T:ℝ) := by exact_mod_cast hT
  have hz := cluster_age_noise_power_scaling (m:=m) (α:=α) hβ.le hε hS ht' htS
    (show 0≤A from sq_nonneg _) hD hG hJ
  have hN' := hN.trans (mul_le_mul_of_nonneg_left (hfactor.trans hz) (NNReal.coe_nonneg _))
  obtain ⟨hup,hsum⟩ := cluster_moment_of_mean_and_noise hI (hu₀ T) heq hnp hN'
  have hdet := pulse_input_power_profile (m:=2*m) (show 0<2*m by dsimp [m]; positivity)
    hI hS hA₀ hIold hIpeak
  refine ⟨hup,hsum.trans ?_⟩
  have hboth := mul_le_mul_of_nonneg_left (add_le_add_left hdet
    ((NativeScalarBDG.constant n:ℝ)*
      (((A*J)^((m:ℝ)-1)*A*D*G)*2^((m:ℝ)*β)*ε*(T:ℝ)^(α-1)*
       S^((2*(m:ℝ)-1)*β))))
    (show 0≤(2:ℝ)^(2*m-1) by positivity)
  dsimp only [focalPowerStepConstant]
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hdet hboth
  dsimp only [m,β,A,J,G] at hdet hboth ⊢
  linear_combination (norm := ring_nf) hboth <;> positivity

#print axioms focal_cluster_doubling_of_row

end RoughHeston.GirsanovPort
