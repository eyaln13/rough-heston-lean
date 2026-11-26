import AggregateFractionalNoisePowers
import AggregateVarianceDominance
import HestonKernelShiftTimeMeasure

/-! The actual forward equation gives mesh-uniform dyadic bounds from
one deterministic bound for the total immigration convolution. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston.GirsanovPort

open SHEStochastic
set_option maxHeartbeats 1500000

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {T : ℝ≥0} {B U : ℝ≥0 → Ω → ℝ}

noncomputable def fractionalAggregateMomentCap (σ α T D : ℝ) : ℕ → ℝ
  | 0 => D
  | n+1 => (2:ℝ)^(2*(2^n:ℕ)) * (D^(2*(2^n:ℕ)) + (NativeScalarBDG.constant n:ℝ)*
      ((σ^2*(2/(Real.Gamma α^2*(2*α-1))))*T^(2*α-1))^(2^n:ℕ)*
        fractionalAggregateMomentCap σ α T D n)

theorem fractionalAggregateMomentCap_nonneg {σ α T D : ℝ}
    (hα : 1/2 < α) (hT : 0 ≤ T) (hD : 0 ≤ D) : ∀ n, 0 ≤ fractionalAggregateMomentCap σ α T D n := by
  intro n
  induction n with
  | zero => exact hD
  | succ n ih =>
    rw [fractionalAggregateMomentCap]
    have he : 0 ≤ 2*α-1 := by linarith
    have hcoeff : 0 ≤ ((σ^2*(2/(Real.Gamma α^2*(2*α-1))))*T^(2*α-1)) := by positivity
    exact mul_nonneg (by positivity) (add_nonneg (pow_nonneg hD _)
      (mul_nonneg (mul_nonneg (NativeScalarBDG.constant n).coe_nonneg (pow_nonneg hcoeff _)) ih))

private theorem le_two_pow_mul_add_pow {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (q : ℕ) :
    (x+y)^q ≤ (2:ℝ)^q * (x^q+y^q) := by
  have h : x+y ≤ 2*max x y := by linarith [le_max_left x y, le_max_right x y]
  calc
    _ ≤ (2*max x y)^q := pow_le_pow_left₀ (add_nonneg hx hy) h q
    _ = (2:ℝ)^q*(max x y)^q := mul_pow _ _ _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rcases le_total x y with hxy | hyx
      · rw [max_eq_right hxy]; exact le_add_of_nonneg_left (pow_nonneg hx _)
      · rw [max_eq_left hyx]; exact le_add_of_nonneg_right (pow_nonneg hy _)

private theorem variance_power_le_of_dominance
    {X Z : Ω → ℝ} (hX : AEStronglyMeasurable X P) (hX₀ : ∀ ω, 0 ≤ X ω)
    {D : ℝ} (hD : 0 ≤ D) (hDom : ∀ᵐ ω ∂P, X ω ≤ D+Z ω)
    (q : ℕ) (hZ : MemLp Z (q:ℝ≥0∞) P) :
    Integrable (fun ω => (X ω)^q) P ∧
    (∫ ω, (X ω)^q ∂P) ≤ (2:ℝ)^q*(D^q+∫ ω, ‖Z ω‖^q ∂P) := by
  have hB : MemLp (fun ω => D+‖Z ω‖) (q:ℝ≥0∞) P := (memLp_const D).add hZ.norm
  have hXMem : MemLp X (q:ℝ≥0∞) P := by
    apply hB.mono hX
    filter_upwards [hDom] with ω hω
    rw [Real.norm_of_nonneg (hX₀ ω), Real.norm_of_nonneg (add_nonneg hD (norm_nonneg _))]
    exact hω.trans (add_le_add_right (le_abs_self _) D)
  have hXi : Integrable (fun ω => (X ω)^q) P := by
    convert hXMem.integrable_norm_pow' using 1
    funext ω
    rw [Real.norm_of_nonneg (hX₀ ω)]
  have hZi := hZ.integrable_norm_pow'
  have hPoint (ω : Ω) (hω : X ω ≤ D+Z ω) : (X ω)^q ≤ (2:ℝ)^q*(D^q+‖Z ω‖^q) := by
    have hz : Z ω ≤ ‖Z ω‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
    exact (pow_le_pow_left₀ (hX₀ ω) (hω.trans (add_le_add_right hz D)) q).trans
      (le_two_pow_mul_add_pow hD (norm_nonneg _) q)
  refine ⟨hXi, ?_⟩
  have hh := integral_mono_ae hXi (((integrable_const (D^q)).add hZi).const_mul ((2:ℝ)^q))
    (hDom.mono hPoint)
  change (∫ ω, (X ω)^q ∂P) ≤ ∫ ω, (2:ℝ)^q*(D^q+‖Z ω‖^q) ∂P at hh
  simpa only [integral_const_mul, integral_add (integrable_const (D^q)) hZi, integral_const,
    measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using hh

/-- Uniform across all approximations with the same deterministic bound,
regardless of the number of focal rows or the peak pulse rate. -/
theorem aggregateVariance_dyadic_moment_le
    {α κ σ : ℝ} (hα : 1/2 < α) (hα' : α ≤ 1) (hκ : 0 ≤ κ)
    (hBrownian : MathFinBridge.BrownianOn P F T B)
    (hNull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[F 0] A)
    (hB₂ : ∀ t, MemLp (B t) 2 P) (hB : Martingale B F P)
    (hClock : Martingale (fun t ω => B t ω^2-((min t T:ℝ≥0):ℝ)) F P)
    (hU : IsStronglyPredictable F U) (hn : ∀ t ω, 0 ≤ U t ω) (hi : ∀ t, Integrable (U t) P)
    {A : ℝ} (hA : ∀ t, (∫ ω, U t ω ∂P) ≤ A)
    {v : ℝ → Lp ℝ 2 P} (hv : StronglyMeasurable v) (hvc : ContinuousOn v (Icc 0 (T:ℝ)))
    (hvRep : ∀ s, ⇑(v s) =ᵐ[P] U s.toNNReal)
    {D : ℝ} (hD : 0 ≤ D) {det : ℝ → ℝ} (hdet : ∀ t ∈ Icc 0 (T:ℝ), det t ≤ D)
    (hEq : ∀ s ∈ Icc 0 (T:ℝ), v s = clusterDeterministicInputLp P det s +
      volterraSmulConvolution (hestonKernel α) (fun r => (-κ:ℝ) • v r) s+
      σ • fixedHestonConvolutionLp (T := T) hα hB₂ hU hn hi hA s) :
    ∀ n t, t ≤ T → Integrable (fun ω => U t ω^(2^n:ℕ)) P ∧
      (∫ ω, U t ω^(2^n:ℕ) ∂P) ≤ fractionalAggregateMomentCap σ α T D n := by
  let N := fixedHestonConvolutionLp (T := T) hα hB₂ hU hn hi hA
  let E := (σ^2*(2/(Real.Gamma α^2*(2*α-1)))) *(T:ℝ)^(2*α-1)
  let C := fractionalAggregateMomentCap σ α T D
  have hDom (t : ℝ≥0) (ht : t ≤ T) : ∀ᵐ ω ∂P, U t ω ≤ D+(σ • N (t:ℝ)) ω := by
    have ht' : (t:ℝ) ∈ Icc 0 (T:ℝ) := ⟨t.coe_nonneg, NNReal.coe_le_coe.mpr ht⟩
    have hEq' : v (t:ℝ) = clusterDeterministicInputLp P (fun _ => det (t:ℝ)) t +
      volterraSmulConvolution (hestonKernel α) (fun r => (-κ:ℝ) • v r) t+σ • N t := hEq _ ht'
    have h := aggregateVariance_ae_le_deterministic_plus_noise (by linarith : 0 < α) hκ hU hn hv hvc hvRep ht' hEq'
    simpa only [Real.toNNReal_coe] using h.mono (fun ω hw => hw.trans (add_le_add_left (hdet _ ht') _))
  have hZ0 : N 0 = 0 := fixedHestonConvolutionLp_zero hα hB₂ hU hn hi hA
  have hMeas (t : ℝ≥0) : AEStronglyMeasurable (U t) P :=
    ((hU.stronglyAdapted t).mono (F.le t)).aestronglyMeasurable
  intro n
  induction n with
  | zero =>
    intro t ht
    simp only [pow_zero,pow_one,fractionalAggregateMomentCap]
    refine ⟨hi t, ?_⟩
    have hz := integral_scaled_fixedHestonConvolutionLp_zero (σ := σ) hα hB₂ hB hClock hU hn hi hA t
    have hZi : Integrable (fun ω => (σ • N (t:ℝ)) ω) P := (Lp.memLp _).integrable one_le_two
    have hu := integral_mono_ae (hi t) ((integrable_const D).add hZi) (hDom t ht)
    change (∫ ω, U t ω ∂P) ≤ ∫ ω, D+(σ • N (t:ℝ)) ω ∂P at hu
    rw [integral_add (integrable_const D) hZi, integral_const, measureReal_def, measure_univ,
      ENNReal.toReal_one, one_smul, hz, add_zero] at hu
    exact hu
  | succ n ih =>
    intro t ht
    have ht' : (t:ℝ) ∈ Icc 0 (T:ℝ) := ⟨t.coe_nonneg, NNReal.coe_le_coe.mpr ht⟩
    have h0 : (0:ℝ) ∈ Icc 0 (T:ℝ) := ⟨le_rfl,T.coe_nonneg⟩
    have hP : ∀ᵐ u ∂hestonTimeMeasure T,
        Integrable (fun ω => U u ω^(2^n:ℕ)) P ∧ (∫ ω, U u ω^(2^n:ℕ) ∂P) ≤ C n := by
      rw [hestonTimeMeasure_eq_horizon, MathFin.ItoIntegralCLM.timeMeasureHorizon]
      exact (ae_restrict_mem measurableSet_Ioc).mono fun u hu => ih u hu.2
    obtain ⟨hw, hE⟩ := hestonKernel_shift_squared_energy_hestonTimeMeasure (σ := σ) hα hα'
      (s := 0) (t := (t:ℝ)) le_rfl t.coe_nonneg ht'.2
    have hEst := hE.trans (by
      change _ ≤ E
      rw [sub_zero]
      apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow t.coe_nonneg ht'.2 (by linarith))
      have hNonneg : 0 ≤ 2*α-1 := by linarith
      positivity)
    obtain ⟨hNoiseMem, hNoise⟩ := heston_fractional_noise_increment_even_power_of_energy hα
      hBrownian hNull hB₂ hB hClock hU hn hi hA n
      (fractionalAggregateMomentCap_nonneg hα T.coe_nonneg hD n) hP h0 ht' E hw hEst
    change MemLp (fun ω => (σ • (N (t:ℝ)-N 0)) ω) ((2*2^n:ℕ):ℝ≥0∞) P at hNoiseMem
    rw [hZ0,sub_zero] at hNoiseMem
    change (∫ ω, ‖(σ • (N (t:ℝ)-N 0)) ω‖^(2*2^n:ℕ) ∂P) ≤
      (NativeScalarBDG.constant n:ℝ)*E^(2^n:ℕ)*C n at hNoise
    rw [hZ0,sub_zero] at hNoise
    have hBound := variance_power_le_of_dominance (hMeas t) (hn t) hD (hDom t ht) (2*2^n) hNoiseMem
    have he : (2:ℕ)^(n+1) = 2*2^n := by rw [pow_succ, mul_comm]
    rw [he]
    refine ⟨hBound.1, hBound.2.trans ?_⟩
    simp only [fractionalAggregateMomentCap]
    exact mul_le_mul_of_nonneg_left (add_le_add_right hNoise _) (by positivity)

#print axioms RoughHeston.GirsanovPort.aggregateVariance_dyadic_moment_le

end RoughHeston.GirsanovPort
