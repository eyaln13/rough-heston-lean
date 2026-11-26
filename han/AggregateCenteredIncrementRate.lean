import AggregateDyadicVarianceMoments
import AggregateDriftCenteredIncrements
import FractionalSmoothVarianceIncrementRate

/-! The fractional centered aggregate row satisfies a mesh-uniform
Kolmogorov estimate. Its immigration rate is absent from the constant. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston.GirsanovPort

open SHEStochastic
set_option maxHeartbeats 2000000

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {T : ℝ≥0} {B U : ℝ≥0 → Ω → ℝ}

noncomputable def fractionalCenteredIncrementCap (σ α κ T D : ℝ) (n : ℕ) : ℝ≥0∞ :=
  let m : ℕ := 2^n
  let q := 2*m
  let C := fractionalAggregateMomentCap σ α T D
  let Cdr := ENNReal.ofReal (2/(Real.Gamma α*α))^q * ENNReal.ofReal (T^(m:ℝ)) *
    ENNReal.ofReal (‖κ‖^q*C (n+1))
  let Cnoise := ENNReal.ofReal (NativeScalarBDG.constant n:ℝ) *
    ENNReal.ofReal (σ^2*(2/(Real.Gamma α^2*(2*α-1))))^m * ENNReal.ofReal (C n)
  (2:ℝ≥0∞)^q*(Cdr+Cnoise)

theorem fractionalCenteredIncrementCap_ne_top (σ α κ T D : ℝ) (n : ℕ) :
    fractionalCenteredIncrementCap σ α κ T D n ≠ ⊤ := by
  unfold fractionalCenteredIncrementCap
  finiteness

private theorem coeFn_clusterDeterministicInputLp_ae (D : ℝ → ℝ) (t : ℝ) :
    ⇑(clusterDeterministicInputLp P D t) =ᵐ[P] fun _ => D t := by
  let one : Lp ℝ 2 P := (memLp_const (1:ℝ)).toLp _
  filter_upwards [Lp.coeFn_smul (D t) one, (memLp_const (1:ℝ) (μ := P)).coeFn_toLp] with ω h1 h2
  change (D t • one) ω = D t
  rw [h1, Pi.smul_apply, smul_eq_mul, h2, mul_one]

/-- High absolute moments of centered increments, uniform across the
mesh size and number of cluster rows. -/
theorem aggregate_centered_increment_lintegral_le
    {α κ σ : ℝ} (hα : 1/2 < α) (hα' : α ≤ 1) (hκ : 0 ≤ κ)
    (hBrownian : MathFinBridge.BrownianOn P F T B)
    (hNull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[F 0] A)
    (hB₂ : ∀ t, MemLp (B t) 2 P) (hB : Martingale B F P)
    (hClock : Martingale (fun t ω => B t ω^2-((min t T:ℝ≥0):ℝ)) F P)
    {D : ℝ → ℝ} (L : CenteredHestonRowData P F T α κ σ hα B U hB₂ D)
    {Dcap : ℝ} (hD : 0 ≤ Dcap) (hDet : ∀ s ∈ Icc 0 (T:ℝ), D s ≤ Dcap)
    (n : ℕ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ (T:ℝ)) :
    (∫⁻ ω, ‖(U t.toNNReal ω-D t)-(U s.toNNReal ω-D s)‖ₑ^(2*2^n:ℕ) ∂P) ≤
      fractionalCenteredIncrementCap σ α κ T Dcap n * ENNReal.ofReal ((t-s)^((2*α-1)*(2^n:ℕ))) := by
  let N := fixedHestonConvolutionLp (T := T) hα hB₂ L.predictable L.nonnegative L.integrable L.meanLe
  let G := volterraSmulConvolution (hestonKernel α) (fun r => (-κ:ℝ) • L.pathLp r)
  let m : ℕ := 2^n
  let q : ℕ := 2*m
  let C := fractionalAggregateMomentCap σ α T Dcap
  let a := 2/(Real.Gamma α*α)
  let b := σ^2*(2/(Real.Gamma α^2*(2*α-1)))
  let Δ := t-s
  let e := (2*α-1)*(m:ℝ)
  let CD := ENNReal.ofReal a^q * ENNReal.ofReal ((T:ℝ)^(m:ℝ)) * ENNReal.ofReal (‖κ‖^q*C (n+1))
  let CN := ENNReal.ofReal (NativeScalarBDG.constant n:ℝ) * ENNReal.ofReal b^m * ENNReal.ofReal (C n)
  have h0 : 0 < α := by linarith
  have he : 0 < e := mul_pos (by linarith) (by dsimp [m]; positivity)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by
    have hβ : 0 ≤ 2*α-1 := by linarith
    dsimp [b]
    positivity
  have hΔ : 0 ≤ Δ := sub_nonneg.mpr hst
  have hΔT : Δ ≤ (T:ℝ) := (sub_le_self _ hs).trans ht
  have heq : (2:ℕ)^(n+1) = q := by dsimp [q,m]; rw [pow_succ, mul_comm]
  have hMom (j : ℕ) := aggregateVariance_dyadic_moment_le hα hα' hκ hBrownian hNull hB₂ hB hClock
    L.predictable L.nonnegative L.integrable L.meanLe L.continuous_pathLp.stronglyMeasurable
    L.continuous_pathLp.continuousOn L.rep hD hDet L.forward j
  have hC (j : ℕ) : 0 ≤ C j := fractionalAggregateMomentCap_nonneg hα T.coe_nonneg hD j
  have hDriftM : ∀ r ≤ T, Integrable (fun ω => U r ω^q) P ∧ (∫ ω, U r ω^q ∂P) ≤ C (n+1) := by
    simpa only [heq] using hMom (n+1)
  have hPrev : ∀ᵐ r ∂hestonTimeMeasure T,
      Integrable (fun ω => U r ω^m) P ∧ (∫ ω, U r ω^m ∂P) ≤ C n := by
    rw [hestonTimeMeasure_eq_horizon, MathFin.ItoIntegralCLM.timeMeasureHorizon]
    exact (ae_restrict_mem measurableSet_Ioc).mono fun r hr => hMom n r hr.2
  have hm : 1 ≤ m := Nat.one_le_pow n 2 (by decide)
  have hq : 1 ≤ q := by dsimp [q]; omega
  have hD₀ := forward_drift_increment_lintegral_bound hα hα' hB₂ L hs hst ht q
    hq (hC (n+1)) hDriftM
  have hD₁ : (∫⁻ ω, ‖(G t-G s) ω‖ₑ^q ∂P) ≤ CD*ENNReal.ofReal (Δ^e) := by
    have H : ENNReal.ofReal (Δ^(α*(q:ℝ))) ≤
        ENNReal.ofReal ((T:ℝ)^(m:ℝ))*ENNReal.ofReal (Δ^e) := by
      have hE : α*(q:ℝ)-e = (m:ℝ) := by dsimp [e,q]; push_cast; ring
      have h₁ : e ≤ α*(q:ℝ) := by rw [← sub_nonneg,hE]; positivity
      have hh := ofReal_rpow_le_horizon_mul_ofReal_rpow hΔ hΔT he h₁
      rwa [hE] at hh
    have hd := ofReal_scaled_rpow_nat ha hΔ h0.le q
    change _ ≤ ENNReal.ofReal (a*Δ^α)^q*ENNReal.ofReal (‖κ‖^q*C (n+1)) at hD₀
    rw [hd] at hD₀
    refine hD₀.trans ((mul_left_mono (mul_right_mono H)).trans_eq ?_)
    dsimp [CD]
    ac_rfl
  obtain ⟨hwi,hwe⟩ := hestonKernel_shift_squared_energy_hestonTimeMeasure (σ := σ) hα hα' hs hst ht
  have hsSet : s ∈ Icc 0 (T:ℝ) := ⟨hs,hst.trans ht⟩
  have htSet : t ∈ Icc 0 (T:ℝ) := ⟨hs.trans hst,ht⟩
  let Z : Lp ℝ 2 P := σ • (N t-N s)
  obtain ⟨hZM,hZB⟩ := heston_fractional_noise_increment_even_power_of_energy hα hBrownian hNull
    hB₂ hB hClock L.predictable L.nonnegative L.integrable L.meanLe n (hC n) hPrev hsSet htSet
    (b*Δ^(2*α-1)) hwi hwe
  have hZi : Integrable (fun ω => ‖Z ω‖^q) P := hZM.integrable_norm_pow'
  have hZ₁ : (∫⁻ ω, ‖Z ω‖ₑ^q ∂P) ≤ CN*ENNReal.ofReal (Δ^e) := by
    have hZeq : (∫⁻ ω, ‖Z ω‖ₑ^q ∂P) = ENNReal.ofReal (∫ ω, ‖Z ω‖^q ∂P) := by
      calc
        _ = ∫⁻ ω, ENNReal.ofReal (‖Z ω‖^q) ∂P := lintegral_congr fun _ => by
          rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
        _ = _ := (ofReal_integral_eq_lintegral_ofReal hZi
          (ae_of_all _ fun _ => pow_nonneg (norm_nonneg _) _)).symm
    rw [hZeq]
    have hh := ENNReal.ofReal_le_ofReal hZB
    change _ ≤ ENNReal.ofReal ((NativeScalarBDG.constant n:ℝ)*(b*Δ^(2*α-1))^m*C n) at hh
    have hEng₀ : 0 ≤ b*Δ^(2*α-1) := mul_nonneg hb (Real.rpow_nonneg hΔ _)
    have hExp : 0 ≤ 2*α-1 := by linarith
    have hEng : ENNReal.ofReal ((b*Δ^(2*α-1))^m) =
        ENNReal.ofReal b^m * ENNReal.ofReal (Δ^e) := by
      rw [ENNReal.ofReal_pow hEng₀]
      exact ofReal_scaled_rpow_nat hb hΔ hExp m
    rw [ENNReal.ofReal_mul (mul_nonneg (NativeScalarBDG.constant n).coe_nonneg (by positivity)),
      ENNReal.ofReal_mul (NativeScalarBDG.constant n).coe_nonneg,hEng] at hh
    exact hh.trans_eq (by dsimp [CN,e]; ac_rfl)
  let J (s : ℝ) := L.pathLp s-clusterDeterministicInputLp P D s
  have hJ (r : ℝ) (hr : r ∈ Icc 0 (T:ℝ)) : J r = G r+σ • N r := by
    change L.pathLp r-clusterDeterministicInputLp P D r = _
    rw [L.forward r hr]
    change clusterDeterministicInputLp P D r+G r+σ • N r - clusterDeterministicInputLp P D r = _
    abel
  have hJrep (r : ℝ) : ⇑(J r) =ᵐ[P] fun ω => U r.toNNReal ω-D r :=
    (Lp.coeFn_sub _ _).trans ((L.rep r).sub (coeFn_clusterDeterministicInputLp_ae D r))
  have hPair : J t-J s = (G t-G s)+Z := by
    rw [hJ t htSet,hJ s hsSet]
    unfold Z
    rw [smul_sub]
    abel
  have hEqa : (fun ω => (U t.toNNReal ω-D t)-(U s.toNNReal ω-D s)) =ᵐ[P]
      fun ω => (G t-G s) ω+Z ω := by
    have h1 := (Lp.coeFn_sub (J t) (J s)).trans ((hJrep t).sub (hJrep s))
    rw [hPair] at h1
    exact h1.symm.trans (Lp.coeFn_add (G t-G s) Z)
  have hEqI : (∫⁻ ω, ‖(U t.toNNReal ω-D t)-(U s.toNNReal ω-D s)‖ₑ^q ∂P) =
      ∫⁻ ω, ‖(G t-G s) ω+Z ω‖ₑ^q ∂P := lintegral_congr_ae (hEqa.mono fun ω hω => congrArg (fun x : ℝ => ‖x‖ₑ^q) hω)
  change (∫⁻ ω, ‖(U t.toNNReal ω-D t)-(U s.toNNReal ω-D s)‖ₑ^q ∂P) ≤
    (2:ℝ≥0∞)^q*(CD+CN)*ENNReal.ofReal (Δ^e)
  rw [hEqI]
  apply (lintegral_enorm_add_pow_le (Lp.stronglyMeasurable (G t-G s)).measurable q).trans
  rw [mul_assoc,add_mul]
  exact mul_right_mono (add_le_add hD₁ hZ₁)

#print axioms RoughHeston.GirsanovPort.fractionalCenteredIncrementCap_ne_top
#print axioms RoughHeston.GirsanovPort.aggregate_centered_increment_lintegral_le

end RoughHeston.GirsanovPort
