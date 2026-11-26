import ActualFractionalPulse
import AffineMeanFubini
import ClusterPulsePeak

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal Interval

namespace RoughHeston

/-- The deterministic input mean and the genuine square compensator
give the early mass second moment required by the lower-tail proof. -/
theorem actual_pulse_early_mass_second_of_resolvent_mean
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} {M U C : ℝ≥0 → Ω → ℝ}
    {α κ a ε d : ℝ} {H : ℝ≥0} {R : ℝ → ℝ}
    (hα : 0<α) (hα' : α<1) (ha : 0≤a) (hd : 0<d) (hε : ε=d^α)
    (hH : d/4≤(H:ℝ)) (hP : FractionalPulseProcess μ 𝒢 H α κ a ε d M U C)
    (hU : ∀ t≤H, Integrable (U t) μ) (hRm : Measurable R)
    (hR : ∀ t∈Ioc (0:ℝ) (H:ℝ), 0≤R t ∧ R t≤2*fractionalK α t)
    (hMean : ∀ t∈Ioc (0:ℝ) (H:ℝ), (∫ ω,U t.toNNReal ω ∂μ)=
        volterraConvolution R (rectangularPulseRate ε d) t) :
    (∫ ω,(fractionalPulseMass ε M (d/4).toNNReal ω)^2 ∂μ) ≤
      (1+(2*a)*(4/(Real.Gamma α*α))/4)*ε^2 := by
  let _ : MeasurableSpace Ω := m
  let t := (d/4).toNNReal
  let s := d/4
  have hs : 0<s := div_pos hd (by norm_num)
  have hts : (t:ℝ)=s := Real.coe_toNNReal _ hs.le
  have ht : t≤H := Real.toNNReal_le_iff_le_coe.mpr hH
  let K := 4/(Real.Gamma α*α)
  let B := K*d^(2*α-1)
  let v (u : ℝ) := U u.toNNReal
  have hvM (u : ℝ) : Measurable (v u) := ((hP.variance_adapted _).mono (𝒢.le _)).measurable
  have hvC (ω : Ω) : Continuous (fun u => v u ω) :=
    (hP.variance_continuous ω).comp continuous_real_toNNReal
  have hvI (u : ℝ) (hu : u∈Ioc 0 s) : Integrable (v u) μ :=
    hU _ (Real.toNNReal_le_iff_le_coe.mpr (hu.2.trans hH))
  have hvB (u : ℝ) (hu : u∈Ioc 0 s) : (∫ ω,‖v u ω‖ ∂μ)≤B := by
    have huH : u∈Ioc (0:ℝ) (H:ℝ) := ⟨hu.1,hu.2.trans hH⟩
    simp only [v,Real.norm_of_nonneg (hP.variance_nonnegative _ _)]
    rw [hMean u huH]
    exact GirsanovPort.rectangularPulse_resolvent_peak hα hα'.le hε hd huH hRm hR
  have hMmean : (∫ ω,M t ω ∂μ)=0 := by
    have hh := hP.martingale.setIntegral_eq (show (0:ℝ≥0)≤t from zero_le) MeasurableSet.univ
    simpa only [Measure.restrict_univ,integral_congr_ae hP.martingale_zero,integral_zero] using hh.symm
  have hCs0 : C 0 =ᵐ[μ] fun _ => 0 := by
    filter_upwards [hP.compensator 0 zero_le] with ω hω
    simpa only [NNReal.coe_zero,intervalIntegral.integral_same] using hω
  have hSq0 : (fun ω => M 0 ω*M 0 ω-C 0 ω)=ᵐ[μ] fun _ => 0 := by
    filter_upwards [hP.martingale_zero,hCs0] with ω h0 hc
    rw [h0,hc]
    ring
  have hSq : (∫ ω,M t ω*M t ω-C t ω ∂μ)=0 := by
    have hh := hP.compensated_square.setIntegral_eq (show (0:ℝ≥0)≤t from zero_le) MeasurableSet.univ
    simp only [Measure.restrict_univ] at hh
    change (∫ ω,M 0 ω*M 0 ω-C 0 ω ∂μ)=(∫ ω,M t ω*M t ω-C t ω ∂μ) at hh
    rw [integral_congr_ae hSq0,integral_zero] at hh
    exact hh.symm
  have hMt2 : Integrable (fun ω => (M t ω)^2) μ := by
    convert (hP.martingale_memLp t).integrable_mul (hP.martingale_memLp t) using 1
    funext ω
    exact pow_two _
  have hM2 : (∫ ω,(M t ω)^2 ∂μ)=(∫ ω,C t ω ∂μ) := by
    simp_rw [← pow_two] at hSq
    rw [integral_sub hMt2 (hP.compensator_integrable t)] at hSq
    linarith
  have hCmean : (∫ ω,C t ω ∂μ) ≤ (2*a)*B*s := by
    have hC : C t =ᵐ[μ] fun ω => ∫ u in Ioc (0:ℝ) s,(2*a)*v u ω := by
      filter_upwards [hP.compensator t ht] with ω he
      rw [he,intervalIntegral.integral_of_le (NNReal.coe_nonneg t),hts]
    have hi : IntegrableOn (fun _ : ℝ => 2*a) (Ioc 0 s) := integrableOn_const (by simp [Real.volume_Ioc])
    have hF := affine_weighted_mean_integral hvM hvC hvI hvB measurable_const hi
    rw [integral_congr_ae hC,hF.2]
    have hIntegr : IntegrableOn (fun u => (2*a)*(∫ ω,v u ω ∂μ)) (Ioc 0 s) :=
      hF.1.integral_prod_left.congr (ae_of_all _ fun u => integral_const_mul _ _)
    have hLe : (∫ u in Ioc (0:ℝ) s,(2*a)*(∫ ω,v u ω ∂μ)) ≤
        ∫ u in Ioc (0:ℝ) s,(2*a)*B := by
      refine setIntegral_mono_on hIntegr (integrableOn_const (by simp [Real.volume_Ioc])) measurableSet_Ioc (fun u hu => ?_)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [Real.norm_of_nonneg (hP.variance_nonnegative _ _),v] using hvB u hu
    refine hLe.trans_eq ?_
    simp only [setIntegral_const,smul_eq_mul,measureReal_def,Real.volume_Ioc,sub_zero,
      ENNReal.toReal_ofReal hs.le]
    ring
  have hev : (fun ω => (fractionalPulseMass ε M t ω)^2) =
      fun ω => ε^2+(2*ε)*M t ω+(M t ω)^2 := by
    funext ω
    simp only [fractionalPulseMass]
    ring
  have hI₁ : Integrable (fun _ : Ω => ε^2) μ := integrable_const _
  have hI₂ := (hP.martingale.integrable t).const_mul (2*ε)
  rw [hev]
  have hI := integral_add (hI₁.add hI₂) hMt2
  have hJ := integral_add hI₁ hI₂
  simp only [Pi.add_apply] at hI hJ
  rw [hI,hJ,integral_const,probReal_univ,one_smul,integral_const_mul,hMmean,mul_zero,add_zero,hM2]
  refine (add_le_add (le_refl (ε^2)) hCmean).trans_eq ?_
  have hPow : d^(2*α-1)*d=ε^2 := by
    calc
      _ = d^(2*α-1)*d^(1:ℝ) := by rw [Real.rpow_one]
      _ = d^(α+α) := by rw [← Real.rpow_add hd,show 2*α-1+1=α+α by ring]
      _ = _ := by rw [Real.rpow_add hd,hε,pow_two]
  dsimp [B,K,s]
  calc
    _ = ε^2+((2*a)*(4/(Real.Gamma α*α))/4)*(d^(2*α-1)*d) := by ring
    _ = _ := by rw [hPow]; ring

#print axioms actual_pulse_early_mass_second_of_resolvent_mean

end RoughHeston
