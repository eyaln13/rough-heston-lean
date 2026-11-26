import BridgeScalarNative
import SHEStochastic.NativeExponentialSubprobability
import SHEStochastic.NativeExponentialMartingale
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston.GirsanovPort

open SHEStochastic

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} {H : ℝ≥0}

local notation "ν" => FiniteScalarIto.inputMeasure F μ H

private theorem after_norm_sub_le (s : ℝ≥0) (u v : Lp ℝ 2 ν) :
    ‖NativeTimeCut.after s u - NativeTimeCut.after s v‖ ≤ ‖u-v‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top _)
  refine eLpNorm_mono_ae (Lp.memLp _).aestronglyMeasurable ?_
  filter_upwards [Lp.coeFn_sub (NativeTimeCut.after s u) (NativeTimeCut.after s v),
    Lp.coeFn_sub u v, NativeTimeCut.after_ae s u, NativeTimeCut.after_ae s v] with z h₁ h₂ hu hv
  rw [h₁, h₂, Pi.sub_apply, Pi.sub_apply, hu, hv]
  by_cases hz : s < z.1 <;> simp [hz]

private theorem positive_eLpNorm_one {η : Measure Ω} {f : Ω → ℝ}
    (hi : Integrable f η) (h₀ : 0 ≤ᵐ[η] f) :
    eLpNorm f 1 η = ENNReal.ofReal (∫ ω, f ω ∂η) := by
  rw [eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hi]
  congr 1
  apply integral_congr_ae
  filter_upwards [h₀] with ω hω using Real.norm_of_nonneg hω

set_option maxHeartbeats 650000 in
/-- An arbitrary square-integrable post-observation native density
has conditional expectation at most one in the original filtration. -/
theorem native_after_density_condExp_le_one
    (P : FiniteScalarIto.Family F μ H Unit) (a : ℝ) (s : ℝ≥0) (hs : s ≤ H)
    (u : Lp ℝ 2 ν) :
    μ[NativeExponential.density P scalarHilbertBasis a (NativeTimeCut.after s u) | F s]
      ≤ᵐ[μ] (fun _ => (1 : ℝ)) := by
  let e := scalarHilbertBasis
  let b := NativeTimeCut.after s u
  let D := NativeExponential.density P e a b
  obtain ⟨v, hcap, hlim⟩ := NativeEnergyLocalization.exists_sequence e u
  let k (n : ℕ) := NativeTimeCut.after s (v n)
  have hk : Tendsto k atTop (𝓝 b) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => after_norm_sub_le s (v n) u)
      (tendsto_iff_norm_sub_tendsto_zero.mp hlim)
  let Dn (n : ℕ) := NativeExponential.density P e a (k n)
  have hhn (n : ℕ) : ∀ᵐ ω ∂μ, NativeEnergy.energy (k n) ω ≤ (n : ℝ) :=
    (NativeTimeCut.energy_after_le s (v n)).trans ((hcap n).mono fun _ h => h.trans (min_le_right _ _))
  have hIn (n : ℕ) : Integrable (Dn n) μ :=
    (NativeBoundedExponential.bounded_energy P e a (k n) n (Nat.cast_nonneg _) (hhn n)).1.integrable
      (by norm_num)
  have hnn (n : ℕ) : μ[Dn n | F s] =ᵐ[μ] fun _ => 1 :=
    NativePastExponential.conditional_mean_one P e a s hs (k n)
      (NativeTimeCut.after_supported s (v n)) n (Nat.cast_nonneg _) (hhn n)
  have hI : Integrable D μ := (NativeExponentialSubprobability.integrable_and_le_one P e a b).1
  obtain ⟨ns, hns⟩ := NativeBoundedExponential.exists_density_ae_subsequence P e a hk
  have hset (A : Set Ω) (hA : MeasurableSet[F s] A) :
      (∫ ω in A, D ω ∂μ) ≤ ∫ _ in A, (1 : ℝ) ∂μ := by
    have hInt (n : ℕ) : (∫ ω in A, Dn n ω ∂μ) = ∫ _ in A, (1 : ℝ) ∂μ := by
      rw [← setIntegral_condExp (F.le s) (hIn n) hA]
      exact integral_congr_ae (ae_restrict_of_ae (hnn n))
    have hsetI (n : ℕ) : Integrable (Dn (ns n)) (μ.restrict A) := (hIn _).integrableOn
    have hnorm (n : ℕ) : eLpNorm (Dn (ns n)) 1 (μ.restrict A) ≤
        ENNReal.ofReal (∫ _ in A, (1 : ℝ) ∂μ) := by
      rw [positive_eLpNorm_one (hsetI n) (ae_of_all _ fun _ => (Real.exp_pos _).le), hInt]
    have hconv := tendstoInMeasure_of_tendsto_ae
      (fun n => (hsetI n).aestronglyMeasurable) (ae_restrict_of_ae hns)
    have hn := eLpNorm_le_of_tendstoInMeasure (Eventually.of_forall hnorm) hconv
      (fun n => (hsetI n).aestronglyMeasurable)
    rw [positive_eLpNorm_one hI.integrableOn (ae_of_all _ fun _ => (Real.exp_pos _).le)] at hn
    exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun _ => zero_le_one))).mp hn
  have hm := F.le s
  let X := μ[D | F s]
  have hXm : StronglyMeasurable[F s] X := stronglyMeasurable_condExp
  have hX : Integrable X (μ.trim hm) := integrable_condExp.trim hm hXm
  apply ae_of_ae_trim hm
  refine ae_le_of_forall_setIntegral_le hX (integrable_const (1 : ℝ)) fun A hA _ => ?_
  rw [← setIntegral_trim hm hXm hA, ← setIntegral_trim hm stronglyMeasurable_const hA,
    setIntegral_condExp hm hI hA]
  exact hset A hA

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.native_after_density_condExp_le_one
