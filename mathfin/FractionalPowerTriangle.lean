import FractionalKernelSemigroup
import BochnerVolterraInversion

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace RoughHeston

private theorem triangular_fractionalK_nonneg {a : ℝ} (ha : 0 < a) (x : ℝ) :
    0 ≤ fractionalK a x := by
  by_cases hx : x ≤ 0
  · simp [fractionalK, hx]
  · rw [fractionalK, ite_eq_right hx]
    exact div_nonneg (Real.rpow_nonneg (lt_of_not_ge hx).le _) (Real.Gamma_pos_of_pos ha).le

private theorem triangular_fractionalK_pos {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    0 < fractionalK a x := by
  rw [fractionalK, ite_eq_right (not_le.mpr hx)]
  exact div_pos (Real.rpow_pos_of_pos hx _) (Real.Gamma_pos_of_pos ha)

private theorem ae_time_triangle_interior (t : ℝ) :
    ∀ᵐ u ∂volume.restrict (Ioc 0 t), u ∈ Ioo 0 t := by
  rw [← restrict_Ioo_eq_restrict_Ioc]
  exact ae_restrict_mem measurableSet_Ioo

private theorem fractionalK_triangle_inner {a b t u : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hu : u ∈ Ioo 0 t) :
    (∫ s in Ioc (0 : ℝ) t, fractionalK a (t-s)*fractionalK b (s-u)) =
      fractionalK (a+b) (t-u) := by
  rw [volterra_shifted_kernel_integral (fun x hx => by simp [fractionalK, hx])
    (show u ∈ Ioc 0 t from ⟨hu.1, hu.2.le⟩)]
  exact fractionalK_convolution_add ha hb (sub_pos.mpr hu.2)

/-- The three positive fractional factors are integrable on the
ordinary time rectangle. Causality restricts the integral to the
triangle, and its mass is the kernel with summed order. -/
theorem fractionalK_triangle_integrable_and_integral {a b c t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (ht : 0 < t) :
    let ν := volume.restrict (Ioc 0 t)
    let F := fun z : ℝ × ℝ => fractionalK a (t-z.1)*fractionalK b (z.1-z.2)*fractionalK c z.2
    Integrable F (ν.prod ν) ∧ (∫ z, F z ∂(ν.prod ν)) = fractionalK (a+b+c) t := by
  dsimp only
  let ν := volume.restrict (Ioc 0 t)
  let F (z : ℝ × ℝ) := fractionalK a (t-z.1)*fractionalK b (z.1-z.2)*fractionalK c z.2
  have hFm : Measurable F :=
    (((fractionalK_measurable a).comp (measurable_const.sub measurable_fst)).mul
      ((fractionalK_measurable b).comp (measurable_fst.sub measurable_snd))).mul
      ((fractionalK_measurable c).comp measurable_snd)
  have hFn (z : ℝ × ℝ) : 0 ≤ F z :=
    mul_nonneg (mul_nonneg (triangular_fractionalK_nonneg ha _) (triangular_fractionalK_nonneg hb _))
      (triangular_fractionalK_nonneg hc _)
  have hInt₂ : IntegrableOn (fun u => fractionalK (a+b) (t-u)*fractionalK c u) (Ioc 0 t) := by
    by_contra hi
    have he := fractionalK_convolution_add (add_pos ha hb) hc ht
    unfold volterraConvolution at he
    rw [integral_undef hi] at he
    exact (triangular_fractionalK_pos (add_pos (add_pos ha hb) hc) ht).ne' he.symm
  have hInner (u : ℝ) (hu : u ∈ Ioo 0 t) :
      (∫ s, F (s,u) ∂ν) = fractionalK (a+b) (t-u)*fractionalK c u := by
    change (∫ s in Ioc (0 : ℝ) t, (fractionalK a (t-s)*fractionalK b (s-u))*fractionalK c u) = _
    rw [integral_mul_const, fractionalK_triangle_inner ha hb hu]
  have hI : Integrable F (ν.prod ν) := by
    refine (integrable_prod_iff' hFm.aestronglyMeasurable).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_time_triangle_interior t] with u hu
      have hfirst : Integrable (fun s => fractionalK a (t-s)*fractionalK b (s-u)) ν := by
        by_contra hi
        have h := fractionalK_triangle_inner ha hb hu
        change (∫ s, fractionalK a (t-s)*fractionalK b (s-u) ∂ν) = _ at h
        rw [integral_undef hi] at h
        exact (triangular_fractionalK_pos (add_pos ha hb) (sub_pos.mpr hu.2)).ne' h.symm
      exact hfirst.mul_const (fractionalK c u)
    · refine (show Integrable (fun u => fractionalK (a+b) (t-u)*fractionalK c u) ν from hInt₂).congr ?_
      filter_upwards [ae_time_triangle_interior t] with u hu
      have he : (fun s => ‖F (s,u)‖) = fun s => F (s,u) := by
        funext s
        exact Real.norm_of_nonneg (hFn (s,u))
      rw [he, hInner u hu]
  refine ⟨hI, ?_⟩
  change (∫ z, F z ∂(ν.prod ν)) = _
  rw [integral_prod_symm _ hI]
  calc
    _ = ∫ u, fractionalK (a+b) (t-u)*fractionalK c u ∂ν := by
      apply integral_congr_ae
      filter_upwards [ae_time_triangle_interior t] with u hu
      exact hInner u hu
    _ = _ := fractionalK_convolution_add (add_pos ha hb) hc ht

section Bounds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- Finite positive fractional-kernel envelopes suffice for absolute
integrability of the Volterra triangle, including Banach-valued inputs. -/
theorem fractional_power_triangle_absolute_integrable
    {ι κ : Type*} {β t : ℝ} {f : ℝ → ℝ} {g : ℝ → E}
    (hβ : 0 < β) (ht : 0 < t) (hf : Measurable f) (hg : StronglyMeasurable g)
    (I : Finset ι) (J : Finset κ)
    (a p : ι → ℝ) (c q : κ → ℝ)
    (ha : ∀ i ∈ I, 0 < a i) (hc : ∀ j ∈ J, 0 < c j)
    (hfB : ∀ s ∈ Ioc 0 t, |f s| ≤ ∑ i ∈ I, p i * fractionalK (a i) s)
    (hgB : ∀ s ∈ Ioc 0 t, ‖g s‖ ≤ ∑ j ∈ J, q j * fractionalK (c j) s) :
    Integrable (fun z : ℝ × ℝ => |f (t-z.1)*fractionalK β (z.1-z.2)| * ‖g z.2‖)
      ((volume.restrict (Ioc 0 t)).prod (volume.restrict (Ioc 0 t))) := by
  let ν := volume.restrict (Ioc 0 t)
  let F (s : ℝ) := ∑ i ∈ I, p i * fractionalK (a i) s
  let G (s : ℝ) := ∑ j ∈ J, q j * fractionalK (c j) s
  let B (z : ℝ × ℝ) := (F (t-z.1)*fractionalK β (z.1-z.2))*G z.2
  have hBI : Integrable B (ν.prod ν) := by
    let h (i : ι) (j : κ) (z : ℝ × ℝ) :=
      (p i*q j)*(fractionalK (a i) (t-z.1)*fractionalK β (z.1-z.2)*fractionalK (c j) z.2)
    have hi (i : ι) (hi : i ∈ I) (j : κ) (hj : j ∈ J) :
        Integrable (h i j) (ν.prod ν) :=
      ((fractionalK_triangle_integrable_and_integral (ha i hi) hβ (hc j hj) ht).1).const_mul _
    have he : B = fun z => ∑ i ∈ I, ∑ j ∈ J, h i j z := by
      funext z
      unfold B F G
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [h]
      ring
    rw [he]
    exact integrable_finsetSum I (fun i hiI => integrable_finsetSum J (hi i hiI))
  have hfm : Measurable (fun z : ℝ × ℝ => f (t-z.1)*fractionalK β (z.1-z.2)) :=
    (hf.comp (measurable_const.sub measurable_fst)).mul
      ((fractionalK_measurable β).comp (measurable_fst.sub measurable_snd))
  refine hBI.mono' ((continuous_abs.measurable.comp hfm).mul (hg.norm.measurable.comp measurable_snd)).aestronglyMeasurable ?_
  have hfst : ∀ᵐ z ∂ν.prod ν, z.1 ∈ Ioo (0 : ℝ) t :=
    (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := ν)).tendsto_ae (ae_time_triangle_interior t)
  have hsnd : ∀ᵐ z ∂ν.prod ν, z.2 ∈ Ioc (0 : ℝ) t :=
    (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := ν)).tendsto_ae (ae_restrict_mem measurableSet_Ioc)
  filter_upwards [hfst, hsnd] with z hz₁ hz₂
  have hz' : t-z.1 ∈ Ioc 0 t := ⟨sub_pos.mpr hz₁.2, sub_le_self t hz₁.1.le⟩
  have hK := triangular_fractionalK_nonneg hβ (z.1-z.2)
  have h1 : |f (t-z.1)| ≤ F (t-z.1) := hfB _ hz'
  have h2 : ‖g z.2‖ ≤ G z.2 := hgB _ hz₂
  rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _)), abs_mul, abs_of_nonneg hK]
  exact mul_le_mul (mul_le_mul_of_nonneg_right h1 hK) h2 (norm_nonneg _)
    (mul_nonneg ((abs_nonneg _).trans h1) hK)

theorem fractional_power_triangle_smul_integrable
    {ι κ : Type*} {β t : ℝ} {f : ℝ → ℝ} {g : ℝ → E}
    (hβ : 0 < β) (ht : 0 < t) (hf : Measurable f) (hg : StronglyMeasurable g)
    (I : Finset ι) (J : Finset κ)
    (a p : ι → ℝ) (c q : κ → ℝ)
    (ha : ∀ i ∈ I, 0 < a i) (hc : ∀ j ∈ J, 0 < c j)
    (hfB : ∀ s ∈ Ioc 0 t, |f s| ≤ ∑ i ∈ I, p i * fractionalK (a i) s)
    (hgB : ∀ s ∈ Ioc 0 t, ‖g s‖ ≤ ∑ j ∈ J, q j * fractionalK (c j) s) :
    Integrable (fun z : ℝ × ℝ => (f (t-z.1)*fractionalK β (z.1-z.2)) • g z.2)
      ((volume.restrict (Ioc 0 t)).prod (volume.restrict (Ioc 0 t))) := by
  have hfm : Measurable (fun z : ℝ × ℝ => f (t-z.1)*fractionalK β (z.1-z.2)) :=
    (hf.comp (measurable_const.sub measurable_fst)).mul
      ((fractionalK_measurable β).comp (measurable_fst.sub measurable_snd))
  refine (integrable_norm_iff (hfm.stronglyMeasurable.smul
    (hg.comp_measurable measurable_snd)).aestronglyMeasurable).mp ?_
  exact (fractional_power_triangle_absolute_integrable hβ ht hf hg I J a p c q ha hc hfB hgB).congr
    (ae_of_all _ fun z => by
      change |f (t-z.1)*fractionalK β (z.1-z.2)| * ‖g z.2‖ =
        ‖(f (t-z.1)*fractionalK β (z.1-z.2)) • g z.2‖
      rw [norm_smul, Real.norm_eq_abs])

/-- Bochner associativity under finite positive-order fractional envelopes. -/
theorem volterra_fractional_smul_assoc_of_power_bounds [CompleteSpace E]
    {ι κ : Type*} {β t : ℝ} {f : ℝ → ℝ} {g : ℝ → E}
    (hβ : 0 < β) (ht : 0 < t) (hf : Measurable f) (hg : StronglyMeasurable g)
    (I : Finset ι) (J : Finset κ)
    (a p : ι → ℝ) (c q : κ → ℝ)
    (ha : ∀ i ∈ I, 0 < a i) (hc : ∀ j ∈ J, 0 < c j)
    (hfB : ∀ s ∈ Ioc 0 t, |f s| ≤ ∑ i ∈ I, p i * fractionalK (a i) s)
    (hgB : ∀ s ∈ Ioc 0 t, ‖g s‖ ≤ ∑ j ∈ J, q j * fractionalK (c j) s) :
    volterraSmulConvolution f (volterraSmulConvolution (fractionalK β) g) t =
      volterraSmulConvolution (volterraConvolution f (fractionalK β)) g t :=
  volterra_smul_convolution_assoc (fun x hx => by simp [fractionalK, hx])
    (fractional_power_triangle_smul_integrable hβ ht hf hg I J a p c q ha hc hfB hgB)

private theorem triangular_fractionalK_as_power {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    Real.Gamma a * fractionalK a x = x^(a-1) := by
  rw [fractionalK, ite_eq_right (not_le.mpr hx)]
  field_simp [(Real.Gamma_pos_of_pos ha).ne']

private theorem triangular_fractionalK_one {x : ℝ} (hx : 0 < x) :
    fractionalK 1 x = 1 := by
  simp [fractionalK, not_le.mpr hx, Real.Gamma_one]

private theorem triangular_fractionalK_eq_inverse (α : ℝ) :
    fractionalK (1-α) = fractionalL α := by
  funext x
  simp only [fractionalK, fractionalL, show 1-α-1 = -α by ring]

/-- The affine-transform triangle with the two Riccati drift powers
and an input bounded by a constant plus the inverse kernel. -/
theorem riccati_affine_triangle_smul_integrable
    {α t A B C D : ℝ} {f : ℝ → ℝ} {g : ℝ → E}
    (hα : 1/2 < α) (hα' : α < 1) (ht : 0 < t)
    (hf : Measurable f) (hg : StronglyMeasurable g)
    (hfB : ∀ s ∈ Ioc 0 t, |f s| ≤ A*s^(α-1)+B*s^(2*α-2))
    (hgB : ∀ s ∈ Ioc 0 t, ‖g s‖ ≤ C+D*fractionalL α s) :
    Integrable (fun z : ℝ × ℝ => (f (t-z.1)*fractionalK α (z.1-z.2)) • g z.2)
      ((volume.restrict (Ioc 0 t)).prod (volume.restrict (Ioc 0 t))) := by
  have hα₀ : 0 < α := by linarith
  have hα₂ : 0 < 2*α-1 := by linarith
  let a (i : Fin 2) := if i = 0 then α else 2*α-1
  let p (i : Fin 2) := if i = 0 then A * Real.Gamma α else B * Real.Gamma (2*α-1)
  let c (i : Fin 2) := if i = 0 then 1 else 1-α
  let q (i : Fin 2) := if i = 0 then C else D
  apply fractional_power_triangle_smul_integrable hα₀ ht hf hg
    (Finset.univ : Finset (Fin 2)) (Finset.univ : Finset (Fin 2)) a p c q
  · intro i _
    dsimp [a]
    split <;> assumption
  · intro j _
    dsimp [c]
    split
    · exact zero_lt_one
    · exact sub_pos.mpr hα'
  · intro s hs
    have he : (∑ i : Fin 2, p i * fractionalK (a i) s) = A*s^(α-1)+B*s^(2*α-2) := by
      simp only [Fin.sum_univ_two, a, p, ite_true,
        ite_eq_right (show (1 : Fin 2) ≠ 0 by decide)]
      rw [mul_assoc, triangular_fractionalK_as_power hα₀ hs.1, mul_assoc,
        triangular_fractionalK_as_power hα₂ hs.1, show 2*α-1-1 = 2*α-2 by ring]
    exact (hfB s hs).trans_eq he.symm
  · intro s hs
    have he : (∑ j : Fin 2, q j * fractionalK (c j) s) = C+D*fractionalL α s := by
      simp only [Fin.sum_univ_two, c, q, ite_true,
        ite_eq_right (show (1 : Fin 2) ≠ 0 by decide),
        triangular_fractionalK_one hs.1, triangular_fractionalK_eq_inverse, mul_one]
    exact (hgB s hs).trans_eq he.symm

/-- The Riccati envelopes justify reassociation of the affine transform. -/
theorem volterra_affine_smul_assoc_of_riccati_bounds [CompleteSpace E]
    {α t A B C D : ℝ} {f : ℝ → ℝ} {g : ℝ → E}
    (hα : 1/2 < α) (hα' : α < 1) (ht : 0 < t)
    (hf : Measurable f) (hg : StronglyMeasurable g)
    (hfB : ∀ s ∈ Ioc 0 t, |f s| ≤ A*s^(α-1)+B*s^(2*α-2))
    (hgB : ∀ s ∈ Ioc 0 t, ‖g s‖ ≤ C+D*fractionalL α s) :
    volterraSmulConvolution f (volterraSmulConvolution (fractionalK α) g) t =
      volterraSmulConvolution (volterraConvolution f (fractionalK α)) g t :=
  volterra_smul_convolution_assoc (fun x hx => by simp [fractionalK, hx])
    (riccati_affine_triangle_smul_integrable hα hα' ht hf hg hfB hgB)

end Bounds

/-- Scalar specialization for ordinary affine-transform integrals. -/
theorem volterra_affine_assoc_of_riccati_bounds
    {α t A B C D : ℝ} {f g : ℝ → ℝ}
    (hα : 1/2 < α) (hα' : α < 1) (ht : 0 < t)
    (hf : Measurable f) (hg : Measurable g)
    (hfB : ∀ s ∈ Ioc 0 t, |f s| ≤ A*s^(α-1)+B*s^(2*α-2))
    (hgB : ∀ s ∈ Ioc 0 t, |g s| ≤ C+D*fractionalL α s) :
    volterraConvolution f (volterraConvolution (fractionalK α) g) t =
      volterraConvolution (volterraConvolution f (fractionalK α)) g t := by
  simpa only [volterraSmulConvolution, volterraConvolution, smul_eq_mul] using
    volterra_affine_smul_assoc_of_riccati_bounds hα hα' ht hf hg.stronglyMeasurable hfB
      (by simpa only [Real.norm_eq_abs] using hgB)

#print axioms fractionalK_triangle_integrable_and_integral
#print axioms fractional_power_triangle_absolute_integrable
#print axioms volterra_fractional_smul_assoc_of_power_bounds
#print axioms riccati_affine_triangle_smul_integrable
#print axioms volterra_affine_smul_assoc_of_riccati_bounds
#print axioms volterra_affine_assoc_of_riccati_bounds

end RoughHeston
