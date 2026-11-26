import ActualPulseEarlyMassMoment
import ClusterBurstDeterministicBounds
import ClusterMomentCovariance
import ClusterPulseMeanUpper

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal Interval

namespace RoughHeston

/-- On a physical block ending at t ≤ 2S, the square moment of the
terminal mass is bounded by a constant times ε S^α. -/
theorem actual_block_mass_second_of_resolvent_mean
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Filtration ℝ≥0 m} {M U C : ℝ≥0 → Ω → ℝ}
    {α κ a ε d S : ℝ} {H t : ℝ≥0} {R : ℝ → ℝ}
    (hα : 0<α) (hα' : α<1) (ha : 0≤a) (hκ : 0≤κ) (hd : 0<d) (hε : ε=d^α)
    (hdS : d≤S) (ht : t≤H) (htS : (t:ℝ)≤2*S)
    (hP : FractionalPulseProcess μ F H α κ a ε d M U C)
    (hU : ∀ r≤H, Integrable (U r) μ) (hRm : Measurable R)
    (hR : ∀ x∈Ioc (0:ℝ) (H:ℝ), 0≤R x ∧ R x≤2*fractionalK α x)
    (hMean : ∀ x∈Ioc (0:ℝ) (H:ℝ), (∫ ω,U x.toNNReal ω ∂μ)=
        volterraConvolution R (rectangularPulseRate ε d) x) :
    (∫ ω,(fractionalPulseMass ε M t ω)^2 ∂μ) ≤
      (1+(2*a)*(4/α)*2^α/(Real.Gamma α*α))*ε*S^α := by
  let _ : MeasurableSpace Ω := m
  have hε₀ : 0<ε := hε ▸ Real.rpow_pos_of_pos hd _
  have hS := hd.trans_le hdS
  have hΓ := Real.Gamma_pos_of_pos hα
  obtain ⟨_,hZ,_,_,_⟩ := fractional_pulse_mass_data hα hα' hκ hε₀ hd ht hP
  have hC₀ : C 0 =ᵐ[μ] 0 := (hP.compensator 0 zero_le).mono fun ω he => by simpa using he
  have he := GirsanovPort.sizeBiased_cluster_terminal_means (o := (0:ℝ≥0)) (r := t)
    (S := fun _ : Ω => (0:ℝ)) (q := 0) (U := fun _ : Ω => (0:ℝ)) zero_le
    hP.martingale (hP.martingale_memLp t) hP.martingale_zero hC₀ hP.compensated_square hε₀
    (memLp_const 0) (by simp) (by simp) (ae_of_all μ fun _ => (show (0:ℝ)=0+0 by norm_num)) hZ
  have hz : (∫ ω,(fractionalPulseMass ε M t ω)^2 ∂μ) = ε^2+(∫ ω, C t ω ∂μ) := he.2.1
  let v (u : ℝ) := U u.toNNReal
  have hvM (u : ℝ) : Measurable (v u) := ((hP.variance_adapted _).mono (F.le _)).measurable
  have hvC (ω : Ω) : Continuous (fun u => v u ω) := (hP.variance_continuous ω).comp continuous_real_toNNReal
  have hsH (u : ℝ) (hu : u∈Ioc 0 (t:ℝ)) : u ∈ Ioc 0 (H:ℝ) := ⟨hu.1,hu.2.trans ht⟩
  have hvI (u : ℝ) (hu : u∈Ioc 0 (t:ℝ)) : Integrable (v u) μ :=
    hU _ (Real.toNNReal_le_iff_le_coe.mpr (hsH u hu).2)
  have hvB (u : ℝ) (hu : u∈Ioc 0 (t:ℝ)) : (∫ ω,‖v u ω‖ ∂μ)≤(4/(Real.Gamma α*α))*d^(2*α-1) := by
    simp only [v,Real.norm_of_nonneg (hP.variance_nonnegative _ _)]
    rw [hMean u (hsH u hu)]
    exact GirsanovPort.rectangularPulse_resolvent_peak hα hα'.le hε hd (hsH u hu) hRm hR
  have hI := affine_weighted_mean_integral hvM hvC hvI hvB
    (measurable_const (a := (1:ℝ))) (integrableOn_const (by simp [Real.volume_Ioc]))
  have hi : IntegrableOn (fun u => ∫ ω, v u ω ∂μ) (Ioc 0 (t:ℝ)) := by
    simpa only [IntegrableOn,one_mul] using hI.1.integral_prod_left
  have heI := GirsanovPort.pulse_mean_integral_upper hα t.coe_nonneg hi (A := 4/α) (ε := ε)
    (fun u hu => (hMean u (hsH u hu)).le.trans
      (GirsanovPort.rectangularPulse_resolvent_mean_upper hα hα'.le hε₀.le hd (hsH u hu) hRm hR))
  have hA := affine_weighted_mean_integral hvM hvC hvI hvB
    (measurable_const (a := (2*a))) (integrableOn_const (by simp [Real.volume_Ioc]))
  have hc : (∫ ω,C t ω ∂μ) = (2*a)*∫ u in Ioc 0 (t:ℝ), ∫ ω,v u ω ∂μ := by
    rw [integral_congr_ae (hP.compensator t ht)]
    simp_rw [intervalIntegral.integral_of_le t.coe_nonneg]
    rw [hA.2,integral_const_mul]
  have heps : ε≤S^α := hε ▸ Real.rpow_le_rpow hd.le hdS hα.le
  have hrt := Real.rpow_le_rpow t.coe_nonneg htS hα.le
  rw [Real.mul_rpow (by norm_num : 0≤(2:ℝ)) hS.le] at hrt
  rw [hz,hc]
  calc
    _ ≤ ε*S^α + (2*a)*((4/α)*ε*((2^α*S^α)/(Real.Gamma α*α))) := by
      rw [pow_two]
      apply add_le_add (mul_le_mul_of_nonneg_left heps hε₀.le)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply heI.trans
      gcongr
    _ = _ := by ring

#print axioms actual_block_mass_second_of_resolvent_mean

end RoughHeston
