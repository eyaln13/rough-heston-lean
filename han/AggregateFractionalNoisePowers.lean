import HestonRealKernelNoiseMoment
import BanachHestonInversion
import CanonicalPathIntegrals

/-! The terminal L² stochastic convolution is linear in the actual
fractional integrands. Its increments obey the high-power moment bound
with the deterministic energy of the kernel difference. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston.GirsanovPort

open SHEStochastic

set_option maxHeartbeats 1500000

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {B U : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

/-- Apply the native checked moment inequality to the difference of the
singular kernel sections on the original joint filtration. -/
theorem heston_fractional_noise_increment_even_power_of_energy
    {α σ : ℝ} (hα : 1/2 < α)
    (hBrownian : MathFinBridge.BrownianOn P F T B)
    (hNull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[F 0] A)
    (hB₂ : ∀ t, MemLp (B t) 2 P) (hB : Martingale B F P)
    (hClock : Martingale (fun t ω => B t ω^2-((min t T:ℝ≥0):ℝ)) F P)
    (hU : IsStronglyPredictable F U) (hU₀ : ∀ s ω, 0 ≤ U s ω) (hUi : ∀ s, Integrable (U s) P)
    {A : ℝ} (hMean : ∀ s, (∫ ω, U s ω ∂P) ≤ A)
    (n : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hPrev : ∀ᵐ r ∂hestonTimeMeasure T,
      Integrable (fun ω => U r ω^(2^n:ℕ)) P ∧ (∫ ω, U r ω^(2^n:ℕ) ∂P) ≤ C)
    {s t : ℝ} (hs : s ∈ Icc 0 (T:ℝ)) (ht : t ∈ Icc 0 (T:ℝ)) :
    let K := fun r : ℝ≥0 => hestonKernel α (t-(r:ℝ))-hestonKernel α (s-(r:ℝ))
    let N := fixedHestonConvolutionLp (T := T) hα hB₂ hU hU₀ hUi hMean
    let Z : Lp ℝ 2 P := σ • (N t-N s)
    ∀ E : ℝ, Integrable (fun r => (σ*K r)^2) (hestonTimeMeasure T) →
      (∫ r, (σ*K r)^2 ∂hestonTimeMeasure T) ≤ E →
      MemLp (fun ω => Z ω) ((2*2^n:ℕ):ℝ≥0∞) P ∧
        (∫ ω, ‖Z ω‖^(2*2^n:ℕ) ∂P) ≤ (NativeScalarBDG.constant n:ℝ)*E^(2^n:ℕ)*C := by
  intro K N Z E hw hE
  let H := fun u : ℝ => hestonKernelFamilyLp hα hU hU₀ hUi hMean (realTimeOnHorizon T u)
  let V := σ • (H t-H s)
  let I := jointItoIntegralCLM (𝒢 := F) T hB₂
  have hN (u : ℝ) : N u = I (H u) := rfl
  have hZI : Z = I V := by
    change σ • (N t-N s) = _
    rw [hN, hN]
    simp only [V, map_smul, map_sub]
  have hUmeas : Measurable (Function.uncurry U) := (hU.mono F.predictable_le_prod).measurable
  have hKm : Measurable K :=
    ((hestonKernel_measurable α).comp (measurable_const.sub measurable_subtype_coe)).sub
      ((hestonKernel_measurable α).comp (measurable_const.sub measurable_subtype_coe))
  have htEval : ((realTimeOnHorizon T t).val:ℝ) = t := by
    change ((min t.toNNReal T : ℝ≥0):ℝ) = _
    have ht' : t.toNNReal ≤ T := NNReal.coe_le_coe.mp ((Real.coe_toNNReal t ht.1).trans_le ht.2)
    rw [min_eq_left ht', Real.coe_toNNReal t ht.1]
  have hsEval : ((realTimeOnHorizon T s).val:ℝ) = s := by
    change ((min s.toNNReal T : ℝ≥0):ℝ) = _
    have hs' : s.toNNReal ≤ T := NNReal.coe_le_coe.mp ((Real.coe_toNNReal s hs.1).trans_le hs.2)
    rw [min_eq_left hs', Real.coe_toNNReal s hs.1]
  have hV : V =ᵐ[jointPredictableMeasure F P T] fun z => σ*K z.1*Real.sqrt (U z.1 z.2) := by
    have h₁ := hestonKernelFamilyLp_ae hα hU hU₀ hUi hMean (realTimeOnHorizon T t)
    have h₂ := hestonKernelFamilyLp_ae hα hU hU₀ hUi hMean (realTimeOnHorizon T s)
    filter_upwards [Lp.coeFn_smul σ (H t-H s), Lp.coeFn_sub (H t) (H s), h₁,h₂] with z hz hsub hx hy
    change (σ • (H t-H s)) z = _
    change H t z = _ at hx
    change H s z = _ at hy
    rw [hz, Pi.smul_apply, smul_eq_mul, hsub, Pi.sub_apply, hx, hy]
    simp only [Function.uncurry, hestonConvolutionWeight, htEval, hsEval, K]
    ring
  have hh := heston_sqrt_row_real_moment hBrownian hNull hB₂ hB hClock n hKm hUmeas hU₀ V hV
    (c := fun _ => C) hPrev hw (hw.mul_const C)
  dsimp only at hh
  rw [← hZI] at hh
  refine ⟨hh.1, hh.2.trans ?_⟩
  let m : ℕ := 2^n
  have hm : 1 ≤ m := Nat.one_le_pow n 2 (by decide)
  let E₀ := ∫ r, (σ*K r)^2 ∂hestonTimeMeasure T
  have hE₀ : 0 ≤ E₀ := integral_nonneg fun r => sq_nonneg _
  have hEng : (∫ r, (σ*K r)^2*C ∂hestonTimeMeasure T) = E₀*C := integral_mul_const _ _
  rw [hEng]
  have hExp : (m:ℝ)-1 = ((m-1:ℕ):ℝ) := by rw [Nat.cast_sub hm, Nat.cast_one]
  change (NativeScalarBDG.constant n:ℝ) * (E₀^((m:ℝ)-1)*(E₀*C)) ≤ _
  rw [hExp, Real.rpow_natCast]
  have he : (NativeScalarBDG.constant n:ℝ)*(E₀^(m-1)*(E₀*C)) =
      (NativeScalarBDG.constant n:ℝ)*E₀^m*C := by
    rw [show (NativeScalarBDG.constant n:ℝ)*(E₀^(m-1)*(E₀*C)) =
      (NativeScalarBDG.constant n:ℝ)*(E₀^(m-1)*E₀)*C by ring,
      ← pow_succ, Nat.sub_add_cancel hm]
  rw [he]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hE₀ hE m) (NativeScalarBDG.constant n).coe_nonneg) hC

#print axioms RoughHeston.GirsanovPort.heston_fractional_noise_increment_even_power_of_energy

end RoughHeston.GirsanovPort
