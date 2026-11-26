import Verification
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory Filter Set
open scoped MeasureTheory Topology

namespace RoughHeston

private noncomputable def conditionalHistoryKernel (α p y u : ℝ) : ℝ :=
  (y + u) ^ (-(1 + α)) * u ^ p

private theorem conditionalHistoryKernel_measurable (α p y : ℝ) :
    Measurable (conditionalHistoryKernel α p y) :=
  ((measurable_const.add measurable_id).pow_const _).mul (measurable_id.pow_const _)

private theorem conditionalHistoryKernel_nonneg {α p y u : ℝ} (hy : 0 ≤ y) (hu : 0 ≤ u) :
    0 ≤ conditionalHistoryKernel α p y u :=
  mul_nonneg (Real.rpow_nonneg (add_nonneg hy hu) _) (Real.rpow_nonneg hu _)

private theorem conditionalHistoryKernel_integrable_one {α p : ℝ} (hp₀ : 0 < p) (hp : p < α) :
    IntegrableOn (conditionalHistoryKernel α p 1) (Ioi 0) := by
  have hα : 0 < α := hp₀.trans hp
  have hfirst : IntegrableOn (conditionalHistoryKernel α p 1) (Ioc 0 1) := by
    have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
      (intervalIntegral.intervalIntegrable_rpow' (r := p) (by linarith : -1 < p))
    apply hi.mono' (conditionalHistoryKernel_measurable _ _ _).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [Real.norm_of_nonneg (conditionalHistoryKernel_nonneg zero_le_one hu.1.le)]
    have hbase : (1 + u) ^ (-(1 + α)) ≤ 1 := by
      calc
        _ ≤ (1 : ℝ) ^ (-(1 + α)) :=
          Real.rpow_le_rpow_of_nonpos zero_lt_one (le_add_of_nonneg_right hu.1.le) (by linarith)
        _ = 1 := Real.one_rpow _
    exact mul_le_of_le_one_left (Real.rpow_nonneg hu.1.le _) hbase
  have htail : IntegrableOn (conditionalHistoryKernel α p 1) (Ioi 1) := by
    have hi := integrableOn_Ioi_rpow_of_lt (a := p - α - 1) (by linarith) zero_lt_one
    apply hi.mono' (conditionalHistoryKernel_measurable _ _ _).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu₀ : 0 < u := zero_lt_one.trans hu
    rw [Real.norm_of_nonneg (conditionalHistoryKernel_nonneg zero_le_one hu₀.le),
      conditionalHistoryKernel,
      show p - α - 1 = -(1 + α) + p by ring, Real.rpow_add hu₀]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hu₀ (by linarith) (by linarith)) (Real.rpow_nonneg hu₀.le _)
  have hs : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext u
    constructor
    · rintro (hu | hu)
      · exact hu.1
      · exact zero_lt_one.trans (show 1 < u from hu)
    · intro hu
      by_cases huv : u ≤ 1
      · exact Or.inl ⟨hu, huv⟩
      · exact Or.inr (lt_of_not_ge huv)
  rw [← hs, integrableOn_union]
  exact ⟨hfirst, htail⟩

private theorem conditionalHistoryKernel_scale {α p y u : ℝ} (hy : 0 < y) (hu : 0 < u) :
    conditionalHistoryKernel α p y (y * u) =
      y ^ (p - α - 1) * conditionalHistoryKernel α p 1 u := by
  unfold conditionalHistoryKernel
  rw [show y + y * u = y * (1 + u) by ring,
    Real.mul_rpow hy.le (by linarith : 0 ≤ 1 + u), Real.mul_rpow hy.le hu.le,
    show p - α - 1 = -(1 + α) + p by ring, Real.rpow_add hy]
  ring

/-- The history kernel arising when the backward conditional mean is
bounded by a power has integrable tails and scales as y^(p-α). -/
theorem conditionalHistoryKernel_integrable_and_scale {α p y : ℝ}
    (hp₀ : 0 < p) (hp : p < α) (hy : 0 < y) :
    IntegrableOn (conditionalHistoryKernel α p y) (Ioi 0) ∧
      (∫ u in Ioi (0 : ℝ), conditionalHistoryKernel α p y u) =
        y ^ (p - α) * ∫ u in Ioi (0 : ℝ), conditionalHistoryKernel α p 1 u := by
  have hi := conditionalHistoryKernel_integrable_one hp₀ hp
  constructor
  · have hmul : IntegrableOn
        (fun u => y ^ (p - α - 1) * conditionalHistoryKernel α p 1 u) (Ioi 0) :=
      hi.const_mul _
    have hc := hmul.congr_fun (fun u (hu : u ∈ Ioi 0) => (conditionalHistoryKernel_scale hy hu).symm)
      measurableSet_Ioi
    simpa only [mul_zero] using
      (integrableOn_Ioi_comp_mul_left_iff (conditionalHistoryKernel α p y) 0 hy).1 hc
  · rw [← mul_zero y, ← integral_comp_mul_left_Ioi' _ 0 hy]
    simp only [smul_eq_mul, mul_zero]
    have he :
        (∫ u in Ioi (0 : ℝ), conditionalHistoryKernel α p y (y * u)) =
          ∫ u in Ioi (0 : ℝ), y ^ (p - α - 1) * conditionalHistoryKernel α p 1 u :=
      setIntegral_congr_fun measurableSet_Ioi (fun _ hu => conditionalHistoryKernel_scale hy hu)
    have hyfac : y * y ^ (p - α - 1) = y ^ (p - α) := by
      calc
        _ = y ^ (1 : ℝ) * y ^ (p - α - 1) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hy]; congr 1; ring
    rw [he, integral_const_mul, ← mul_assoc, hyfac]

/-- A finite past with mean bounded by C u^p has a conditional history
contribution bounded by a constant times y^(p-α). -/
theorem conditionalHistory_power_bound {α p y t C : ℝ} {f : ℝ → ℝ}
    (hp₀ : 0 < p) (hp : p < α) (hy : 0 < y) (hC : 0 ≤ C)
    (hf : Measurable f) (hf₀ : ∀ u ∈ Ioc (0 : ℝ) t, 0 ≤ f u)
    (hfC : ∀ u ∈ Ioc (0 : ℝ) t, f u ≤ C * u ^ p) :
    let D := ∫ u in Ioi (0 : ℝ), conditionalHistoryKernel α p 1 u
    (∫ u in Ioc (0 : ℝ) t, (y + u) ^ (-(1 + α)) * f u) ≤ C * D * y ^ (p - α) := by
  dsimp only
  obtain ⟨hi, he⟩ := conditionalHistoryKernel_integrable_and_scale hp₀ hp hy
  let b := conditionalHistoryKernel α p y
  let g (u : ℝ) := (y + u) ^ (-(1 + α)) * f u
  have hbC : IntegrableOn (fun u => C * b u) (Ioi 0) := hi.const_mul C
  have hgi : IntegrableOn g (Ioc (0 : ℝ) t) := by
    have hiC : IntegrableOn (fun u => C * b u) (Ioc (0 : ℝ) t) :=
      hbC.mono_set Ioc_subset_Ioi_self
    apply hiC.mono' ((((measurable_const.add measurable_id).pow_const _).mul hf).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hnon := Real.rpow_nonneg (add_nonneg hy.le hu.1.le) (-(1 + α))
    change ‖(y + u) ^ (-(1 + α)) * f u‖ ≤ C * b u
    rw [Real.norm_of_nonneg (mul_nonneg hnon (hf₀ _ hu))]
    exact (mul_le_mul_of_nonneg_left (hfC _ hu) hnon).trans_eq (by dsimp [b, conditionalHistoryKernel]; ring)
  calc
    _ = ∫ u in Ioc (0 : ℝ) t, g u := rfl
    _ ≤ ∫ u in Ioc (0 : ℝ) t, C * b u := by
      apply setIntegral_mono_on hgi (hbC.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc
      intro u hu
      have hnon := Real.rpow_nonneg (add_nonneg hy.le hu.1.le) (-(1 + α))
      exact (mul_le_mul_of_nonneg_left (hfC _ hu) hnon).trans_eq (by dsimp [g, b, conditionalHistoryKernel]; ring)
    _ ≤ ∫ u in Ioi (0 : ℝ), C * b u := by
      apply setIntegral_mono_set hbC ?_ (ae_of_all volume (fun _ h => Ioc_subset_Ioi_self h))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact mul_nonneg hC (conditionalHistoryKernel_nonneg hy.le hu.le)
    _ = _ := by rw [integral_const_mul, he]; ring

theorem real_beta_weight_scaled {a b h : ℝ} (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) :
    let f := fun y : ℝ => y ^ (a - 1) * (h - y) ^ (b - 1)
    IntegrableOn f (Ioc 0 h) ∧
      (∫ y in Ioc (0 : ℝ) h, f y) =
        h ^ (a + b - 1) * (Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)) := by
  dsimp only
  have hβ := Complex.betaIntegral_scaled (a : ℂ) (b : ℂ) hh
  rw [intervalIntegral.integral_of_le hh.le] at hβ
  have hΓpos := Real.Gamma_pos_of_pos (add_pos ha hb)
  have hG : Complex.betaIntegral (a : ℂ) (b : ℂ) =
      ((Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) : ℝ) : ℂ) := by
    have he := Complex.Gamma_mul_Gamma_eq_betaIntegral
      (s := (a : ℂ)) (t := (b : ℂ)) (by simpa) (by simpa)
    rw [← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
      Complex.Gamma_ofReal] at he
    push_cast
    exact (eq_div_iff (Complex.ofReal_ne_zero.mpr hΓpos.ne')).2 (by simpa only [mul_comm] using he.symm)
  have hexp : ((a : ℂ) + (b : ℂ) - 1) = ((a + b - 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [hG, hexp, ← Complex.ofReal_cpow hh.le, ← Complex.ofReal_mul] at hβ
  have he : (∫ y in Ioc (0 : ℝ) h, y ^ (a - 1) * (h - y) ^ (b - 1)) =
      h ^ (a + b - 1) * (Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)) := by
    apply Complex.ofReal_injective
    rw [← integral_complex_ofReal, ← hβ]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro y hy
    have hy₀ : 0 ≤ y := hy.1.le
    have hyh : 0 ≤ h - y := sub_nonneg.mpr hy.2
    change ((y ^ (a - 1) * (h - y) ^ (b - 1) : ℝ) : ℂ) =
      (y : ℂ) ^ ((a : ℂ) - 1) * ((h : ℂ) - (y : ℂ)) ^ ((b : ℂ) - 1)
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hy₀, Complex.ofReal_cpow hyh]
    push_cast
    rfl
  refine ⟨?_, he⟩
  by_contra hbad
  rw [integral_undef hbad] at he
  exact (mul_pos (Real.rpow_pos_of_pos hh _)
    (div_pos (mul_pos (Real.Gamma_pos_of_pos ha) (Real.Gamma_pos_of_pos hb)) hΓpos)).ne' he.symm

/-- A conditional history density bounded by D(1+y^(p-α)) gives the
power h^(p+1-2α) after convolution with the Riccati bound. -/
theorem conditionalHistory_forward_convolution_bound
    {α p h D : ℝ} {j : ℝ → ℝ} (hα : α < 1) (hp : p < α)
    (hpα : 0 < 1 + p - α) (hh : 0 < h) (hh₁ : h ≤ 1) (hD : 0 ≤ D)
    (hj : Measurable j)
    (hj₀ : ∀ y ∈ Ioo (0 : ℝ) h, 0 ≤ j y)
    (hjD : ∀ y ∈ Ioo (0 : ℝ) h, j y ≤ D * (1 + y ^ (p - α))) :
    let C := Real.Gamma (1 + p - α) * Real.Gamma (1 - α) / Real.Gamma (2 + p - 2 * α)
    (∫ y in Ioo (0 : ℝ) h, (h - y) ^ (-α) * j y) ≤ 2 * D * C * h ^ (p + 1 - 2 * α) := by
  dsimp only
  let g (y : ℝ) := (h - y) ^ (-α) * j y
  let b (y : ℝ) := y ^ (p - α) * (h - y) ^ (-α)
  let C := Real.Gamma (1 + p - α) * Real.Gamma (1 - α) / Real.Gamma (2 + p - 2 * α)
  obtain ⟨hbi, hbe⟩ := real_beta_weight_scaled hpα (sub_pos.mpr hα) hh
  simp only [show 1 + p - α - 1 = p - α by ring, show 1 - α - 1 = -α by ring,
    show (1 + p - α) + (1 - α) = 2 + p - 2 * α by ring,
    show 2 + p - 2 * α - 1 = p + 1 - 2 * α by ring] at hbi hbe
  have hbI : IntegrableOn b (Ioo 0 h) := hbi.mono_set Ioo_subset_Ioc_self
  have hbE : (∫ y in Ioo (0 : ℝ) h, b y) = h ^ (p + 1 - 2 * α) * C := by
    rw [setIntegral_congr_set Ioo_ae_eq_Ioc]
    exact hbe
  have hdom (y : ℝ) (hy : y ∈ Ioo 0 h) : g y ≤ (2 * D) * b y := by
    have hy₁ : y ≤ 1 := hy.2.le.trans hh₁
    have hry : 1 ≤ y ^ (p - α) := by
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow_of_nonpos hy.1 hy₁ (sub_nonpos.mpr hp.le)
    have hk : 0 ≤ (h - y) ^ (-α) := Real.rpow_nonneg (sub_nonneg.mpr hy.2.le) _
    change (h - y) ^ (-α) * j y ≤ (2 * D) * (y ^ (p - α) * (h - y) ^ (-α))
    calc
      _ ≤ (h - y) ^ (-α) * (D * (1 + y ^ (p - α))) :=
        mul_le_mul_of_nonneg_left (hjD _ hy) hk
      _ ≤ (h - y) ^ (-α) * (D * (2 * y ^ (p - α))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hD) hk
      _ = _ := by ring
  have hbD : IntegrableOn (fun y => (2 * D) * b y) (Ioo 0 h) := hbI.const_mul _
  have hgi : IntegrableOn g (Ioo 0 h) := by
    have hm : Measurable g := ((measurable_const.sub measurable_id).pow_const _).mul hj
    apply hbD.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    have hg₀ : 0 ≤ g y := mul_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hy.2.le) _) (hj₀ _ hy)
    rw [Real.norm_of_nonneg hg₀]
    exact hdom y hy
  calc
    _ = ∫ y in Ioo (0 : ℝ) h, g y := rfl
    _ ≤ ∫ y in Ioo (0 : ℝ) h, (2 * D) * b y :=
      setIntegral_mono_on hgi hbD measurableSet_Ioo hdom
    _ = _ := by rw [integral_const_mul, hbE]; ring

end RoughHeston

#print axioms RoughHeston.conditionalHistoryKernel_integrable_and_scale
#print axioms RoughHeston.conditionalHistory_power_bound

#print axioms RoughHeston.conditionalHistory_forward_convolution_bound

#print axioms RoughHeston.real_beta_weight_scaled
