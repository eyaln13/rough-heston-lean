import OrthogonalJointResolventRows
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston

variable {Ω S : Type*} {m : MeasurableSpace Ω} [MeasurableSpace S]
  {μ : Measure Ω} [IsFiniteMeasure μ] {ν : Measure S} [SigmaFinite ν]

/-- Integrating a deterministic time weight preserves its pairing with one L²
variable. Uniform second moments of the path suffice for Fubini. -/
theorem deterministic_weighted_path_pairing {M : S→Ω→ℝ} {Z : Ω→ℝ} {k : S→ℝ}
    (hm : Measurable (Function.uncurry M)) (hZ : Measurable Z) (hZ₂ : MemLp Z 2 μ)
    (hk : Measurable k) (hkI : Integrable k ν)
    (hm₂ : ∀ s,MemLp (M s) 2 μ)
    {C : ℝ} (hC : 0≤C) (hmC : ∀ᵐ s ∂ν,(∫ ω,(M s ω)^2 ∂μ)≤C) :
    (∫ ω,(∫ s,k s*M s ω ∂ν)*Z ω ∂μ) =
      ∫ s,k s*(∫ ω,M s ω*Z ω ∂μ) ∂ν := by
  let f (p : S×Ω) := k p.1*(M p.1 p.2*Z p.2)
  have hf : Measurable f := (hk.comp measurable_fst).mul
    (hm.mul (hZ.comp measurable_snd))
  have hZi := hZ₂.integrable_sq
  let B := (C+(∫ ω,(Z ω)^2 ∂μ))/2
  have hB : 0≤B := by
    have hz : 0≤∫ ω,(Z ω)^2 ∂μ := integral_nonneg fun _ => sq_nonneg _
    dsimp [B]
    positivity
  have hbound (s : S) (hs : (∫ ω,(M s ω)^2 ∂μ)≤C) :
      (∫ ω,‖M s ω*Z ω‖ ∂μ)≤B := by
    have hM2 := (hm₂ s).integrable_sq
    have ht := integral_mono ((hm₂ s).integrable_mul hZ₂).norm
      ((hM2.add hZi).div_const 2) (fun ω => by
        change ‖M s ω * Z ω‖ ≤ ((M s ω)^2+(Z ω)^2)/2
        rw [Real.norm_eq_abs,abs_mul]
        have ha := sq_abs (M s ω)
        have hb := sq_abs (Z ω)
        nlinarith [sq_nonneg (|M s ω|-|Z ω|)])
    rw [integral_div,integral_add' hM2 hZi] at ht
    exact ht.trans (div_le_div_of_nonneg_right (add_le_add_left hs _) (by norm_num))
  have hfI : Integrable f (ν.prod μ) := by
    refine (integrable_prod_iff hf.aestronglyMeasurable).2 ⟨ae_of_all _ ?_,?_⟩
    · intro s
      exact ((hm₂ s).integrable_mul hZ₂).const_mul (k s)
    · refine (hkI.norm.mul_const B).mono' (hf.stronglyMeasurable.norm.integral_prod_right').aestronglyMeasurable ?_
      filter_upwards [hmC] with s hs
      have hz : 0≤∫ ω,‖f (s,ω)‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
      rw [Real.norm_of_nonneg hz]
      change (∫ ω,‖k s*(M s ω*Z ω)‖ ∂μ)≤‖k s‖*B
      have he (ω : Ω) : ‖k s*(M s ω*Z ω)‖=‖k s‖*‖M s ω*Z ω‖ := norm_mul _ _
      simp_rw [he]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hbound s hs) (norm_nonneg _)
  have hfub := (integral_prod_symm f hfI).symm.trans (integral_prod f hfI)
  convert hfub using 1
  · apply integral_congr_ae
    exact ae_of_all _ fun ω => by
      change _=∫ s,k s*(M s ω*Z ω) ∂ν
      simp_rw [← mul_assoc]
      rw [integral_mul_const]
  · apply integral_congr_ae
    exact ae_of_all _ fun s => by
      change _=∫ ω,k s*(M s ω*Z ω) ∂μ
      rw [integral_const_mul]

/-- Two deterministic weighted functionals of orthogonal martingales are
orthogonal, with each weighting measure and weight allowed to differ. -/
theorem orthogonal_deterministic_weighted_paths {S' : Type*} [MeasurableSpace S']
    {ν' : Measure S'} [SigmaFinite ν'] {M : S→Ω→ℝ} {N : S'→Ω→ℝ} {k : S→ℝ} {l : S'→ℝ}
    (hm : Measurable (Function.uncurry M)) (hn : Measurable (Function.uncurry N))
    (hk : Measurable k) (hl : Measurable l) (hki : Integrable k ν) (hli : Integrable l ν')
    (hm₂ : ∀ s,MemLp (M s) 2 μ) (hn₂ : ∀ t,MemLp (N t) 2 μ)
    {C D : ℝ} (hC : 0≤C) (hD : 0≤D)
    (hmC : ∀ᵐ s ∂ν,(∫ ω,(M s ω)^2 ∂μ)≤C)
    (hnD : ∀ᵐ t ∂ν',(∫ ω,(N t ω)^2 ∂μ)≤D)
    (hN₂ : MemLp (fun ω => ∫ t,l t*N t ω ∂ν') 2 μ)
    (hc : ∀ s t,(∫ ω,M s ω*N t ω ∂μ)=0) :
    (∫ ω,(∫ s,k s*M s ω ∂ν)*(∫ t,l t*N t ω ∂ν') ∂μ)=0 := by
  have hNm : Measurable (fun ω => ∫ t,l t*N t ω ∂ν') :=
    (((hl.comp measurable_fst).mul hn).stronglyMeasurable.integral_prod_left').measurable
  rw [deterministic_weighted_path_pairing hm hNm hN₂ hk hki hm₂ hC hmC]
  have hi (s : S) : (∫ ω,M s ω*(∫ t,l t*N t ω ∂ν') ∂μ)=0 := by
    have hms : Measurable (M s) := hm.comp (measurable_const.prodMk measurable_id)
    simp_rw [mul_comm (M s _)]
    rw [deterministic_weighted_path_pairing hn hms (hm₂ s) hl hli hn₂ hD hnD]
    simp_rw [mul_comm (N _ _) (M s _),hc,mul_zero]
    simp
  simp only [hi,mul_zero,integral_zero]

variable {𝒢 : Filtration ℝ≥0 m} {M N : ℝ≥0→Ω→ℝ}

theorem orthogonal_martingale_mixed_time_mean_zero (hM : Martingale M 𝒢 μ)
    (hN : Martingale N 𝒢 μ) (hMN : Martingale (fun t => M t*N t) 𝒢 μ)
    (hM₂ : ∀ t,MemLp (M t) 2 μ) (hN₂ : ∀ t,MemLp (N t) 2 μ)
    (hM0 : M 0=ᵐ[μ]0) (s t : ℝ≥0) :
    (∫ ω,M s ω*N t ω ∂μ)=0 := by
  have hdiag (r : ℝ≥0) : (∫ ω,M r ω*N r ω ∂μ)=0 := by
    have he := hMN.setIntegral_eq (show (0:ℝ≥0)≤r from zero_le) MeasurableSet.univ
    have hz : M 0*N 0=ᵐ[μ]0 := by
      filter_upwards [hM0] with ω hω
      change M 0 ω*N 0 ω=0
      rw [hω]
      exact zero_mul _
    rw [Measure.restrict_univ,integral_congr_ae hz] at he
    simpa only [Pi.zero_apply,integral_zero,Pi.mul_apply] using he.symm
  have inner {X Y : ℝ≥0→Ω→ℝ} (hX : Martingale X 𝒢 μ) (hY : Martingale Y 𝒢 μ)
      (hX₂ : ∀ r,MemLp (X r) 2 μ) (hY₂ : ∀ r,MemLp (Y r) 2 μ) {a b : ℝ≥0} (hab : a≤b) :
      (∫ ω,X a ω*Y b ω ∂μ)=∫ ω,X a ω*Y a ω ∂μ := by
    let Z := X a*Y b
    have hZi : Integrable Z μ := (hX₂ a).integrable_mul (hY₂ b)
    have he := (condExp_mul_of_stronglyMeasurable_left (hX.stronglyAdapted a) hZi
      (hY.integrable b)).trans (EventuallyEq.rfl.mul (hY.condExp_ae_eq hab))
    exact (integral_condExp (𝒢.le a)).symm.trans (integral_congr_ae he)
  rcases le_total s t with hst|hts
  · exact (inner hM hN hM₂ hN₂ hst).trans (hdiag s)
  · simp_rw [mul_comm (M s _)]
    rw [inner hN hM hN₂ hM₂ hts]
    simp_rw [mul_comm (N t _)]
    exact hdiag t

#print axioms deterministic_weighted_path_pairing
#print axioms orthogonal_deterministic_weighted_paths
#print axioms orthogonal_martingale_mixed_time_mean_zero

end RoughHeston
