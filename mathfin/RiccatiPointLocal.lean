import FractionalBoundaryHistory
import FractionalKernelL1
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.ContinuousMap.Compact

open MeasureTheory Set Filter
open scoped Topology NNReal Interval

namespace RoughHeston

/-- The integrable weight on the fixed unit interval after rescaling time. -/
noncomputable def riccatiBetaWeight (α q u : ℝ) : ℝ :=
  u ^ q * (1 - u) ^ (α - 1) / Real.Gamma α

theorem riccatiBetaWeight_integrable {α q : ℝ} (hα : 0 < α) (hq : -1 < q) :
    IntegrableOn (riccatiBetaWeight α q) (Ioo 0 1) := by
  have hq' : 0 < 1 + q := by linarith
  let gc (u : ℝ) := (u : ℂ) ^ (((1 + q : ℝ) : ℂ) - 1) *
    (1 - (u : ℂ)) ^ ((α : ℂ) - 1)
  have hgc : IntegrableOn gc (Ioo 0 1) :=
    (Complex.betaIntegral_convergent (u := ((1 + q : ℝ) : ℂ)) (v := (α : ℂ))
      hq' hα).1.mono_set Ioo_subset_Ioc_self
  have hi : IntegrableOn (fun u => (gc u).re * (Real.Gamma α)⁻¹) (Ioo 0 1) :=
    hgc.re.mul_const _
  refine hi.congr_fun ?_ measurableSet_Ioo
  intro u hu
  have h₁ : (((1 + q : ℝ) : ℂ) - 1) = (q : ℂ) := by push_cast; ring
  have h₂ : (1 - (u : ℂ)) = ((1 - u : ℝ) : ℂ) := by push_cast; rfl
  have h₃ : (α : ℂ) - 1 = ((α - 1 : ℝ) : ℂ) := by push_cast; rfl
  dsimp only [gc]
  rw [h₁, h₂, h₃, ← Complex.ofReal_cpow hu.1.le, ← Complex.ofReal_cpow (sub_nonneg.mpr hu.2.le),
    ← Complex.ofReal_mul, Complex.ofReal_re, riccatiBetaWeight, div_eq_mul_inv]

private theorem riccatiBetaWeight_nonneg {α q : ℝ} (hα : 0 < α) {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) : 0 ≤ riccatiBetaWeight α q u :=
  div_nonneg (mul_nonneg (Real.rpow_nonneg hu.1.le _)
    (Real.rpow_nonneg (sub_nonneg.mpr hu.2.le) _)) (Real.Gamma_pos_of_pos hα).le

private theorem measurable_riccatiBetaWeight (α q : ℝ) : Measurable (riccatiBetaWeight α q) :=
  ((measurable_id.pow_const q).mul ((measurable_const.sub measurable_id).pow_const (α - 1))).div_const _

/-- The weighted Volterra contribution of the power (s^q). -/
noncomputable def riccatiPowerTransform (α q : ℝ) (G : ℝ → ℝ) (t : ℝ) : ℝ :=
  t ^ (1 + q) * ∫ u in Ioo (0 : ℝ) 1, riccatiBetaWeight α q u * G (t * u)

noncomputable def riccatiBetaMass (α q : ℝ) : ℝ :=
  ∫ u in Ioo (0 : ℝ) 1, riccatiBetaWeight α q u

theorem riccatiBetaMass_nonneg {α q : ℝ} (hα : 0 < α) : 0 ≤ riccatiBetaMass α q := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  exact riccatiBetaWeight_nonneg hα hu

private theorem riccatiBeta_integrand_integrable {α q : ℝ} (hα : 0 < α) (hq : -1 < q)
    {G : ℝ → ℝ} (hm : Measurable G) {B t : ℝ}
    (hB : ∀ u ∈ Ioo (0 : ℝ) 1, ‖G (t * u)‖ ≤ B) :
    IntegrableOn (fun u => riccatiBetaWeight α q u * G (t * u)) (Ioo 0 1) := by
  have hmeas : Measurable (fun u => riccatiBetaWeight α q u * G (t * u)) :=
    (measurable_riccatiBetaWeight α q).mul (hm.comp (measurable_const.mul measurable_id))
  refine ((riccatiBetaWeight_integrable hα hq).mul_const B).mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  rw [norm_mul, Real.norm_of_nonneg (riccatiBetaWeight_nonneg hα hu)]
  exact mul_le_mul_of_nonneg_left (hB u hu) (riccatiBetaWeight_nonneg hα hu)

theorem continuous_riccatiPowerTransform {α q : ℝ} (hα : 0 < α) (hq : -1 < q)
    {G : ℝ → ℝ} (hG : Continuous G) {B : ℝ} (hB : ∀ y, ‖G y‖ ≤ B) :
    Continuous (riccatiPowerTransform α q G) := by
  unfold riccatiPowerTransform
  refine (Real.continuous_rpow_const (by linarith)).mul ?_
  refine continuous_of_dominated (bound := fun u => riccatiBetaWeight α q u * B)
    (fun t => ((measurable_riccatiBetaWeight α q).mul
      (hG.measurable.comp (measurable_const.mul measurable_id))).aestronglyMeasurable)
    ?_ ((riccatiBetaWeight_integrable hα hq).mul_const B) ?_
  · intro t
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    rw [norm_mul, Real.norm_of_nonneg (riccatiBetaWeight_nonneg hα hu)]
    exact mul_le_mul_of_nonneg_left (hB (t * u)) (riccatiBetaWeight_nonneg hα hu)
  · exact ae_of_all _ fun u => continuous_const.mul (hG.comp (continuous_id.mul continuous_const))

/-- The Lipschitz estimate for the weighted power contribution, with an
explicit factor that tends to zero at the origin. -/
theorem norm_riccatiPowerTransform_sub_le {α q t : ℝ}
    (hα : 0 < α) (hq : -1 < q) (ht : 0 ≤ t)
    {G H : ℝ → ℝ} (hG : Measurable G) (hH : Measurable H) {B₁ B₂ D : ℝ}
    (hB₁ : ∀ u ∈ Ioo (0 : ℝ) 1, ‖G (t * u)‖ ≤ B₁)
    (hB₂ : ∀ u ∈ Ioo (0 : ℝ) 1, ‖H (t * u)‖ ≤ B₂)
    (hD : ∀ u ∈ Ioo (0 : ℝ) 1, ‖G (t * u) - H (t * u)‖ ≤ D) :
    ‖riccatiPowerTransform α q G t - riccatiPowerTransform α q H t‖ ≤
      t ^ (1 + q) * (riccatiBetaMass α q * D) := by
  have hGi := riccatiBeta_integrand_integrable hα hq hG hB₁
  have hHi := riccatiBeta_integrand_integrable hα hq hH hB₂
  have hDi := ((riccatiBetaWeight_integrable hα hq).mul_const D)
  have hnorm :
      ‖(∫ u in Ioo (0 : ℝ) 1, riccatiBetaWeight α q u * G (t * u)) -
          ∫ u in Ioo (0 : ℝ) 1, riccatiBetaWeight α q u * H (t * u)‖ ≤
        riccatiBetaMass α q * D := by
    rw [← integral_sub hGi hHi, riccatiBetaMass, ← integral_mul_const]
    refine (norm_integral_le_integral_norm _).trans
      (setIntegral_mono_on (hGi.sub hHi).norm hDi measurableSet_Ioo ?_)
    intro u hu
    rw [← mul_sub, norm_mul, Real.norm_of_nonneg (riccatiBetaWeight_nonneg hα hu)]
    exact mul_le_mul_of_nonneg_left (hD u hu) (riccatiBetaWeight_nonneg hα hu)
  unfold riccatiPowerTransform
  rw [← mul_sub, norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg ht _)]
  exact mul_le_mul_of_nonneg_left hnorm (Real.rpow_nonneg ht _)

/-- Undo the change of variables (s=t u) for the weighted convolution. -/
theorem riccatiPowerTransform_eq_weighted_convolution {α q t : ℝ}
    (ht : 0 < t) (G : ℝ → ℝ) :
    riccatiPowerTransform α q G t =
      t ^ (1 - α) * volterraConvolution (fractionalK α) (fun s => s ^ q * G s) t := by
  unfold riccatiPowerTransform volterraConvolution
  let f (s : ℝ) := fractionalK α (t - s) * (s ^ q * G s)
  change _ = t ^ (1 - α) * ∫ s in Ioc 0 t, f s
  rw [← intervalIntegral.integral_of_le ht.le]
  have he := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1) f t
  rw [mul_zero, mul_one, smul_eq_mul, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo] at he
  rw [← he]
  have hf : (∫ u in Ioo (0 : ℝ) 1, f (t * u)) =
      ∫ u in Ioo (0 : ℝ) 1,
        (t ^ (α - 1) * t ^ q) * (riccatiBetaWeight α q u * G (t * u)) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro u hu
    have hu₁ : 0 < 1 - u := sub_pos.mpr hu.2
    have hp : 0 < t - t * u := by rw [← mul_one_sub]; positivity
    dsimp only [f, riccatiBetaWeight, fractionalK]
    rw [ite_eq_right (not_le.mpr hp), ← mul_one_sub, Real.mul_rpow ht.le hu₁.le,
      Real.mul_rpow ht.le hu.1.le]
    ring
  rw [hf, integral_const_mul]
  have ha : t ^ (1 - α) * t ^ (α - 1) = 1 := by
    rw [← Real.rpow_add ht, show 1 - α + (α - 1) = 0 by ring, Real.rpow_zero]
  have hq : t * t ^ q = t ^ (1 + q) := by
    rw [Real.rpow_add ht, Real.rpow_one]
  calc
    _ = (t ^ (1 - α) * t ^ (α - 1)) * (t * t ^ q) *
        ∫ u in Ioo (0 : ℝ) 1, riccatiBetaWeight α q u * G (t * u) := by rw [ha, hq, one_mul]
    _ = _ := by ring

/-- Extension by clamping time to the compact interval. -/
noncomputable def riccatiTimeExtension {δ : ℝ} (hδ : 0 ≤ δ)
    (φ : C(Icc (0 : ℝ) δ, ℝ)) (s : ℝ) : ℝ :=
  φ ⟨max 0 (min δ s), le_max_left _ _, max_le hδ (min_le_left _ _)⟩

theorem continuous_riccatiTimeExtension {δ : ℝ} (hδ : 0 ≤ δ)
    (φ : C(Icc (0 : ℝ) δ, ℝ)) : Continuous (riccatiTimeExtension hδ φ) :=
  φ.continuous.comp ((continuous_const.max (continuous_const.min continuous_id)).subtype_mk _)

theorem riccatiTimeExtension_apply_of_mem {δ : ℝ} (hδ : 0 ≤ δ)
    (φ : C(Icc (0 : ℝ) δ, ℝ)) (s : Icc (0 : ℝ) δ) :
    riccatiTimeExtension hδ φ (s : ℝ) = φ s := by
  unfold riccatiTimeExtension
  congr 1
  apply Subtype.ext
  simp [min_eq_right s.property.2, max_eq_right s.property.1]

private noncomputable def riccatiClip (R x : ℝ) : ℝ := max (-R) (min x R)

private theorem riccatiClip_lipschitz (R : ℝ) : LipschitzWith 1 (riccatiClip R) :=
  (LipschitzWith.id.min_const R).const_max (-R)

private theorem norm_riccatiClip_le {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    ‖riccatiClip R x‖ ≤ R := by
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

private theorem riccatiClip_eq_of_norm_le {R x : ℝ} (hx : ‖x‖ ≤ R) :
    riccatiClip R x = x := by
  rw [Real.norm_eq_abs, abs_le] at hx
  simp only [riccatiClip, min_eq_left hx.2, max_eq_right hx.1]

private theorem norm_riccatiClip_sub_le (R x y : ℝ) :
    ‖riccatiClip R x - riccatiClip R y‖ ≤ ‖x-y‖ := by
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using
    (riccatiClip_lipschitz R).dist_le_mul x y

/-- Global Picard map with the two scalar nonlinearities clipped outside a fixed ball. -/
private noncomputable def riccatiPointPicard {α δ : ℝ} (hα : 1 / 2 < α) (hδ : 0 ≤ δ)
    (A b c R : ℝ) (hR : 0 ≤ R) (φ : C(Icc (0 : ℝ) δ, ℝ)) :
    C(Icc (0 : ℝ) δ, ℝ) := by
  let G := (riccatiClip R) ∘ riccatiTimeExtension hδ φ
  have hG : Continuous G :=
    (riccatiClip_lipschitz R).continuous.comp (continuous_riccatiTimeExtension hδ φ)
  have hB : ∀ x, ‖G x‖ ≤ R := fun x => norm_riccatiClip_le hR (riccatiTimeExtension hδ φ x)
  have hB₂ : ∀ x, ‖G x ^ 2‖ ≤ R ^ 2 := by
    intro x
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hB x) 2
  exact ⟨fun t => A +
      b * riccatiPowerTransform α (α - 1) G t.val +
      c * riccatiPowerTransform α (2 * α - 2) (fun s => G s ^ 2) t.val,
    (continuous_const.add (continuous_const.mul ((continuous_riccatiPowerTransform
      (by linarith) (by linarith) hG hB).comp continuous_subtype_val))).add
      (continuous_const.mul ((continuous_riccatiPowerTransform (by linarith) (by linarith)
        (hG.pow 2) hB₂).comp continuous_subtype_val))⟩

private noncomputable def riccatiPointPicardFactor (α δ b c R : ℝ) : ℝ :=
  ‖b‖ * (δ ^ (1 + (α - 1)) * riccatiBetaMass α (α - 1)) +
  ‖c‖ * (δ ^ (1 + (2 * α - 2)) * riccatiBetaMass α (2 * α - 2) * (2 * R))

private theorem riccatiPointPicardFactor_nonneg {α δ b c R : ℝ}
    (hα : 0 < α) (hδ : 0 ≤ δ) (hR : 0 ≤ R) :
    0 ≤ riccatiPointPicardFactor α δ b c R := by
  unfold riccatiPointPicardFactor
  exact add_nonneg
    (mul_nonneg (norm_nonneg _) (mul_nonneg (Real.rpow_nonneg hδ _) (riccatiBetaMass_nonneg hα)))
    (mul_nonneg (norm_nonneg _) (mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hδ _) (riccatiBetaMass_nonneg hα)) (by positivity)))

private theorem norm_riccatiPointPicard_sub_le {α δ : ℝ} (hα : 1 / 2 < α) (hδ : 0 ≤ δ)
    (A b c R : ℝ) (hR : 0 ≤ R) (φ ψ : C(Icc (0 : ℝ) δ, ℝ)) :
    ‖riccatiPointPicard hα hδ A b c R hR φ - riccatiPointPicard hα hδ A b c R hR ψ‖ ≤
      riccatiPointPicardFactor α δ b c R * ‖φ - ψ‖ := by
  have hαpos : 0 < α := by linarith
  have hq₁ : -1 < α - 1 := by linarith
  have hq₂ : -1 < 2 * α - 2 := by linarith
  let Gφ := (riccatiClip R) ∘ riccatiTimeExtension hδ φ
  let Gψ := (riccatiClip R) ∘ riccatiTimeExtension hδ ψ
  have hφ : Continuous Gφ :=
    (riccatiClip_lipschitz R).continuous.comp (continuous_riccatiTimeExtension hδ φ)
  have hψ : Continuous Gψ :=
    (riccatiClip_lipschitz R).continuous.comp (continuous_riccatiTimeExtension hδ ψ)
  have hφR : ∀ x, ‖Gφ x‖ ≤ R := fun _ => norm_riccatiClip_le hR _
  have hψR : ∀ x, ‖Gψ x‖ ≤ R := fun _ => norm_riccatiClip_le hR _
  have hφR₂ : ∀ x, ‖Gφ x ^ 2‖ ≤ R ^ 2 := by
    intro x
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hφR x) 2
  have hψR₂ : ∀ x, ‖Gψ x ^ 2‖ ≤ R ^ 2 := by
    intro x
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hψR x) 2
  have hlin (x : ℝ) : ‖Gφ x - Gψ x‖ ≤ ‖φ - ψ‖ :=
    (norm_riccatiClip_sub_le R _ _).trans (ContinuousMap.norm_coe_le_norm (φ - ψ) _)
  have hquad (x : ℝ) : ‖Gφ x ^ 2 - Gψ x ^ 2‖ ≤ 2 * R * ‖φ - ψ‖ := by
    rw [show Gφ x ^ 2 - Gψ x ^ 2 = (Gφ x - Gψ x) * (Gφ x + Gψ x) by ring, norm_mul]
    have hs := (norm_add_le (Gφ x) (Gψ x)).trans (add_le_add (hφR x) (hψR x))
    calc
      _ ≤ ‖φ - ψ‖ * (R + R) :=
        mul_le_mul (hlin x) hs (norm_nonneg _) (norm_nonneg _)
      _ = _ := by ring
  refine (ContinuousMap.norm_le _ (mul_nonneg
    (riccatiPointPicardFactor_nonneg hαpos hδ hR) (norm_nonneg _))).mpr ?_
  intro t
  have h₁ := norm_riccatiPowerTransform_sub_le hαpos hq₁ t.property.1 hφ.measurable
    hψ.measurable (fun u _ => hφR (t.val * u)) (fun u _ => hψR (t.val * u))
    (fun u _ => hlin (t.val * u))
  have h₂ := norm_riccatiPowerTransform_sub_le hαpos hq₂ t.property.1 (hφ.pow 2).measurable
    (hψ.pow 2).measurable (fun u _ => hφR₂ (t.val * u)) (fun u _ => hψR₂ (t.val * u))
    (fun u _ => hquad (t.val * u))
  have h₁' := h₁.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow t.property.1 t.property.2 (by linarith : 0 ≤ 1 + (α - 1)))
    (mul_nonneg (riccatiBetaMass_nonneg hαpos) (norm_nonneg _)))
  have h₂' := h₂.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow t.property.1 t.property.2 (by linarith : 0 ≤ 1 + (2 * α - 2)))
    (mul_nonneg (riccatiBetaMass_nonneg hαpos) (by positivity)))
  let X := riccatiPowerTransform α (α - 1) Gφ t.val - riccatiPowerTransform α (α - 1) Gψ t.val
  let Y := riccatiPowerTransform α (2 * α - 2) (fun s => Gφ s ^ 2) t.val -
    riccatiPowerTransform α (2 * α - 2) (fun s => Gψ s ^ 2) t.val
  have he : (riccatiPointPicard hα hδ A b c R hR φ -
      riccatiPointPicard hα hδ A b c R hR ψ) t = b * X + c * Y := by
    change (A + b * _ + c * _) - (A + b * _ + c * _) = _
    dsimp only [X, Y, Gφ, Gψ]
    ring
  rw [he]
  calc
    _ ≤ ‖b * X‖ + ‖c * Y‖ := norm_add_le _ _
    _ = ‖b‖ * ‖X‖ + ‖c‖ * ‖Y‖ := by rw [norm_mul, norm_mul]
    _ ≤ ‖b‖ * (δ ^ (1 + (α - 1)) * (riccatiBetaMass α (α - 1) * ‖φ - ψ‖)) +
        ‖c‖ * (δ ^ (1 + (2 * α - 2)) * (riccatiBetaMass α (2 * α - 2) * (2 * R * ‖φ - ψ‖))) :=
      add_le_add (mul_le_mul_of_nonneg_left h₁' (norm_nonneg _))
        (mul_le_mul_of_nonneg_left h₂' (norm_nonneg _))
    _ = _ := by unfold riccatiPointPicardFactor; ring

private theorem exists_riccatiPointPicard_radius {α : ℝ} (hα : 1 / 2 < α) (b c R : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ riccatiPointPicardFactor α δ b c R ≤ 1 / 2 := by
  have hq₁ : 0 < 1 + (α - 1) := by linarith
  have hq₂ : 0 < 1 + (2 * α - 2) := by linarith
  have hcont : Continuous (fun δ => riccatiPointPicardFactor α δ b c R) := by
    unfold riccatiPointPicardFactor
    exact (continuous_const.mul ((Real.continuous_rpow_const hq₁.le).mul continuous_const)).add
      (continuous_const.mul (((Real.continuous_rpow_const hq₂.le).mul continuous_const).mul
        continuous_const))
  have hzero : riccatiPointPicardFactor α 0 b c R = 0 := by
    simp only [riccatiPointPicardFactor, Real.zero_rpow hq₁.ne', Real.zero_rpow hq₂.ne',
      zero_mul, mul_zero, add_zero]
  have hat : ContinuousAt (fun δ => riccatiPointPicardFactor α δ b c R) (0 : ℝ) :=
    hcont.continuousAt
  obtain ⟨ε, hε, hball⟩ := Metric.continuousAt_iff.mp hat (1 / 2) (by norm_num)
  refine ⟨ε / 2, by positivity, ?_⟩
  have hd : dist (ε / 2) (0 : ℝ) < ε := by rw [Real.dist_eq, sub_zero, abs_of_pos]; linarith; positivity
  have hb := hball hd
  rw [Real.dist_eq, hzero, sub_zero] at hb
  exact (le_abs_self _).trans hb.le

/-- A local fixed point for the weighted point-charge Riccati equation.
The initial weighted value is exactly the constant forcing term. -/
theorem exists_local_weighted_riccati {α : ℝ} (hα : 1 / 2 < α) (A b c : ℝ) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (φ : C(Icc (0 : ℝ) δ, ℝ)),
      φ ⟨0, le_rfl, hδ.le⟩ = A ∧
      ∀ t : Icc (0 : ℝ) δ,
        φ t = A + b * riccatiPowerTransform α (α - 1) (riccatiTimeExtension hδ.le φ) t.val +
          c * riccatiPowerTransform α (2 * α - 2) (fun s => (riccatiTimeExtension hδ.le φ s)^2) t.val := by
  let R : ℝ := 2 * ‖A‖ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  obtain ⟨δ, hδ, hδsmall⟩ := exists_riccatiPointPicard_radius hα b c R
  let F := riccatiPointPicard hα hδ.le A b c R hR
  have hlip (x y : C(Icc (0 : ℝ) δ, ℝ)) :
      ‖F x - F y‖ ≤ (1 / 2) * ‖x - y‖ :=
    (norm_riccatiPointPicard_sub_le hα hδ.le A b c R hR x y).trans
      (mul_le_mul_of_nonneg_right hδsmall (norm_nonneg _))
  have hf : ContractingWith ((1 / 2 : ℝ≥0)) F := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    simpa only [dist_eq_norm, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using hlip x y
  let φ := ContractingWith.fixedPoint F hf
  have hfixed : F φ = φ := hf.fixedPoint_isFixedPt
  have hFzero (t : Icc (0 : ℝ) δ) : F 0 t = A := by
    change A + b * riccatiPowerTransform α (α - 1)
        (fun s => riccatiClip R (riccatiTimeExtension hδ.le 0 s)) t.val +
      c * riccatiPowerTransform α (2 * α - 2)
        (fun s => (riccatiClip R (riccatiTimeExtension hδ.le 0 s))^2) t.val = A
    have hext (s : ℝ) : riccatiTimeExtension hδ.le 0 s = 0 := rfl
    have hclipzero : riccatiClip R 0 = 0 :=
      riccatiClip_eq_of_norm_le (x := 0) (by simpa only [norm_zero] using hR)
    simp [riccatiPowerTransform, hext, hclipzero]
  have hF0 : ‖F 0‖ ≤ ‖A‖ :=
    (ContinuousMap.norm_le _ (norm_nonneg A)).mpr fun t => by rw [hFzero]
  have hφbound : ‖φ‖ ≤ 2 * ‖A‖ := by
    have hh : ‖φ‖ ≤ (1 / 2) * ‖φ‖ + ‖A‖ := by
      calc
        ‖φ‖ = ‖F φ - F 0 + F 0‖ := by rw [sub_add_cancel, hfixed]
        _ ≤ ‖F φ - F 0‖ + ‖F 0‖ := norm_add_le _ _
        _ ≤ _ := add_le_add (by simpa only [sub_zero] using hlip φ 0) hF0
    linarith
  have hclip (s : ℝ) : riccatiClip R (riccatiTimeExtension hδ.le φ s) =
      riccatiTimeExtension hδ.le φ s := by
    apply riccatiClip_eq_of_norm_le
    exact (ContinuousMap.norm_coe_le_norm φ _).trans (hφbound.trans (by dsimp [R]; linarith))
  have heq (t : Icc (0 : ℝ) δ) :
      φ t = A + b * riccatiPowerTransform α (α - 1) (riccatiTimeExtension hδ.le φ) t.val +
        c * riccatiPowerTransform α (2 * α - 2) (fun s => (riccatiTimeExtension hδ.le φ s)^2) t.val := by
    have hh := congrArg (fun f : C(Icc (0 : ℝ) δ, ℝ) => f t) hfixed.symm
    change φ t = A + b * riccatiPowerTransform α (α - 1)
        (fun s => riccatiClip R (riccatiTimeExtension hδ.le φ s)) t.val +
      c * riccatiPowerTransform α (2 * α - 2)
        (fun s => (riccatiClip R (riccatiTimeExtension hδ.le φ s))^2) t.val at hh
    simpa only [hclip] using hh
  refine ⟨δ, hδ, φ, ?_, heq⟩
  have he := heq ⟨0, le_rfl, hδ.le⟩
  simpa only [riccatiPowerTransform, Subtype.coe_mk, Real.zero_rpow (by linarith : 1+(α-1) ≠ 0),
    Real.zero_rpow (by linarith : 1+(2*α-2) ≠ 0), zero_mul, mul_zero, add_zero] using he

private theorem riccatiWeighted_integrableOn {α q t : ℝ}
    (hα : 0 < α) (hq : -1 < q) (ht : 0 < t)
    {G : ℝ → ℝ} (hG : Measurable G) {B : ℝ} (hB : ∀ s, ‖G s‖ ≤ B) :
    IntegrableOn (fun s => fractionalK α (t - s) * (s ^ q * G s)) (Ioc 0 t) := by
  let f (s : ℝ) := fractionalK α (t-s) * (s ^ q * G s)
  change IntegrableOn f (Ioc 0 t)
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
  apply (IntervalIntegrable.comp_mul_left_iff (f := f) ht.ne').mp
  rw [zero_div, div_self ht.ne', intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one,
    integrableOn_Ioc_iff_integrableOn_Ioo]
  have hi := riccatiBeta_integrand_integrable hα hq hG (t := t) (fun u _ => hB (t * u))
  have hIc : IntegrableOn (fun u => (t ^ (α - 1) * t ^ q) *
      (riccatiBetaWeight α q u * G (t * u))) (Ioo 0 1) := hi.const_mul _
  refine hIc.congr_fun ?_ measurableSet_Ioo
  intro u hu
  have hu₁ : 0 < 1 - u := sub_pos.mpr hu.2
  have hp : 0 < t - t * u := by rw [← mul_one_sub]; positivity
  dsimp only [f, riccatiBetaWeight, fractionalK]
  rw [ite_eq_right (not_le.mpr hp), ← mul_one_sub, Real.mul_rpow ht.le hu₁.le,
    Real.mul_rpow ht.le hu.1.le]
  ring

/-- Local existence for the point-charge Riccati equation and its exact
leading asymptotic at the charge time. -/
theorem exists_local_fractional_riccati_point_charge {α : ℝ} (hα : 1 / 2 < α) (a b c : ℝ) :
    ∃ (δ : ℝ) (w : ℝ → ℝ), 0 < δ ∧ Measurable w ∧ ContinuousOn w (Ioi 0) ∧
      (∀ t ∈ Ioc 0 δ, IntegrableOn
        (fun s => fractionalK α (t - s) * (b * w s + c * w s ^ 2)) (Ioc 0 t)) ∧
      (∀ t ∈ Ioc 0 δ, w t = a * fractionalK α t +
        volterraConvolution (fractionalK α) (fun s => b * w s + c * w s ^ 2) t) ∧
      Tendsto (fun t => t ^ (1 - α) * w t) (𝓝[>] 0) (𝓝 (a / Real.Gamma α)) := by
  obtain ⟨δ, hδ, φ, hzero, hφ⟩ := exists_local_weighted_riccati hα (a / Real.Gamma α) b c
  let G := riccatiTimeExtension hδ.le φ
  let w (s : ℝ) := s ^ (α - 1) * G s
  have hG : Continuous G := continuous_riccatiTimeExtension hδ.le φ
  have hGbound (s : ℝ) : ‖G s‖ ≤ ‖φ‖ := ContinuousMap.norm_coe_le_norm φ _
  have hGbound₂ (s : ℝ) : ‖G s ^ 2‖ ≤ ‖φ‖ ^ 2 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hGbound s) 2
  have hαpos : 0 < α := by linarith
  have hq₁ : -1 < α - 1 := by linarith
  have hq₂ : -1 < 2 * α - 2 := by linarith
  have hweight (t : ℝ) (ht : 0 < t) : t ^ (1 - α) * t ^ (α - 1) = 1 := by
    rw [← Real.rpow_add ht, show 1 - α + (α - 1) = 0 by ring, Real.rpow_zero]
  have hscaled {t : ℝ} (ht : 0 < t) : t ^ (1 - α) * w t = G t := by
    change t ^ (1 - α) * (t ^ (α - 1) * G t) = _
    rw [← mul_assoc, hweight t ht, one_mul]
  have hw₂ {s : ℝ} (hs : 0 < s) : w s ^ 2 = s ^ (2 * α - 2) * G s ^ 2 := by
    unfold w
    rw [mul_pow, pow_two (s ^ (α - 1)), ← Real.rpow_add hs,
      show α - 1 + (α - 1) = 2 * α - 2 by ring]
  have hB {t : ℝ} (ht : 0 < t) :
      IntegrableOn (fun s => fractionalK α (t - s) * (b * w s + c * w s ^ 2)) (Ioc 0 t) ∧
      volterraConvolution (fractionalK α) (fun s => b * w s + c * w s ^ 2) t =
        b * volterraConvolution (fractionalK α) w t +
        c * volterraConvolution (fractionalK α) (fun s => s ^ (2 * α - 2) * G s ^ 2) t := by
    let F₁ (s : ℝ) := fractionalK α (t-s) * w s
    let F₂ (s : ℝ) := fractionalK α (t-s) * (s ^ (2 * α - 2) * G s ^ 2)
    have hF₁ : IntegrableOn F₁ (Ioc 0 t) :=
      riccatiWeighted_integrableOn hαpos hq₁ ht hG.measurable hGbound
    have hF₂ : IntegrableOn F₂ (Ioc 0 t) :=
      riccatiWeighted_integrableOn hαpos hq₂ ht (hG.pow 2).measurable hGbound₂
    have heq (s : ℝ) (hs : s ∈ Ioc 0 t) :
        b * F₁ s + c * F₂ s = fractionalK α (t - s) * (b * w s + c * w s ^ 2) := by
      dsimp only [F₁, F₂]
      rw [hw₂ hs.1]
      ring
    have hF : IntegrableOn (fun s => b * F₁ s + c * F₂ s) (Ioc 0 t) :=
      (hF₁.const_mul b).add (hF₂.const_mul c)
    refine ⟨hF.congr_fun heq measurableSet_Ioc, ?_⟩
    unfold volterraConvolution
    rw [← setIntegral_congr_fun measurableSet_Ioc heq,
      integral_add (hF₁.const_mul b) (hF₂.const_mul c), integral_const_mul b F₁,
      integral_const_mul c F₂]
  refine ⟨δ, w, hδ, (measurable_id.pow_const _).mul hG.measurable, ?_, ?_, ?_, ?_⟩
  · exact (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (show 0 < t from ht)))).mul
      hG.continuousOn
  · exact fun t ht => (hB ht.1).1
  · intro t ht
    have he := hφ ⟨t, ht.1.le, ht.2⟩
    rw [← riccatiTimeExtension_apply_of_mem hδ.le φ, riccatiPowerTransform_eq_weighted_convolution ht.1,
      riccatiPowerTransform_eq_weighted_convolution ht.1] at he
    change G t = a / Real.Gamma α + b * (t ^ (1 - α) *
      volterraConvolution (fractionalK α) w t) + c * (t ^ (1 - α) *
      volterraConvolution (fractionalK α) (fun s => s ^ (2 * α - 2) * G s ^ 2) t) at he
    have hK : t ^ (1 - α) * (a * fractionalK α t) = a / Real.Gamma α := by
      rw [fractionalK, ite_eq_right (not_le.mpr ht.1)]
      calc
        _ = (t ^ (1 - α) * t ^ (α - 1)) * (a / Real.Gamma α) := by ring
        _ = _ := by rw [hweight t ht.1, one_mul]
    apply mul_left_cancel₀ (Real.rpow_pos_of_pos ht.1 (1 - α)).ne'
    rw [hscaled ht.1, mul_add, hK, (hB ht.1).2, he]
    ring
  · have hG0 : G 0 = a / Real.Gamma α :=
      (riccatiTimeExtension_apply_of_mem hδ.le φ ⟨0, le_rfl, hδ.le⟩).trans hzero
    have hlim : Tendsto G (𝓝 (0 : ℝ)) (𝓝 (a / Real.Gamma α)) := hG0 ▸ hG.continuousAt
    apply (hlim.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hscaled (show 0 < t from ht)).symm

#print axioms continuous_riccatiPowerTransform
#print axioms norm_riccatiPowerTransform_sub_le
#print axioms riccatiPowerTransform_eq_weighted_convolution
#print axioms norm_riccatiPointPicard_sub_le
#print axioms exists_local_weighted_riccati
#print axioms exists_local_fractional_riccati_point_charge

end RoughHeston
