import FractionalKernelL1

open MeasureTheory Filter Set
open scoped MeasureTheory Topology

namespace RoughHeston

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A causal Volterra integral with a scalar kernel and a Banach-valued input. -/
noncomputable def volterraSmulConvolution (k : ℝ → ℝ) (f : ℝ → E) (t : ℝ) : E :=
  ∫ s in Ioc (0 : ℝ) t, k (t - s) • f s

/-- Reassociate the two scalar kernels using Bochner Fubini on the time rectangle. -/
theorem volterra_smul_convolution_assoc {l k : ℝ → ℝ} {f : ℝ → E} {t : ℝ}
    (hk : ∀ x ≤ 0, k x = 0)
    (hI : Integrable (fun z : ℝ × ℝ => (l (t - z.1) * k (z.1 - z.2)) • f z.2)
      ((volume.restrict (Ioc 0 t)).prod (volume.restrict (Ioc 0 t)))) :
    volterraSmulConvolution l (volterraSmulConvolution k f) t =
      volterraSmulConvolution (volterraConvolution l k) f t := by
  classical
  have hleft (s : ℝ) (hs : s ∈ Ioc 0 t) :
      l (t - s) • volterraSmulConvolution k f s =
        ∫ u in Ioc (0 : ℝ) t, (l (t - s) * k (s - u)) • f u := by
    unfold volterraSmulConvolution
    have hsub : Ioc 0 s ⊆ Ioc 0 t := Ioc_subset_Ioc_right hs.2
    have hz (u : ℝ) (hu : u ∈ Ioc 0 t \ Ioc 0 s) :
        (l (t - s) * k (s - u)) • f u = 0 := by
      have hus : s ≤ u := by
        by_contra! h
        exact hu.2 ⟨hu.1.1, h.le⟩
      rw [hk _ (sub_nonpos.mpr hus), mul_zero, zero_smul]
    have hext := setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (μ := volume) measurableSet_Ioc hsub hz
    rw [hext, ← integral_smul]
    exact integral_congr_ae (Eventually.of_forall fun _ => (mul_smul _ _ _).symm)
  have hright (u : ℝ) (hu : u ∈ Ioc 0 t) :
      (∫ s in Ioc (0 : ℝ) t, (l (t - s) * k (s - u)) • f u) =
        volterraConvolution l k (t - u) • f u := by
    rw [integral_smul_const, volterra_shifted_kernel_integral hk hu]
  calc
    _ = ∫ s in Ioc (0 : ℝ) t, ∫ u in Ioc (0 : ℝ) t,
        (l (t - s) * k (s - u)) • f u := setIntegral_congr_fun measurableSet_Ioc hleft
    _ = ∫ u in Ioc (0 : ℝ) t, ∫ s in Ioc (0 : ℝ) t,
        (l (t - s) * k (s - u)) • f u := integral_integral_swap hI
    _ = _ := setIntegral_congr_fun measurableSet_Ioc hright

omit [CompleteSpace E] in
/-- A Banach-valued input has integrable fractional Volterra triangle
whenever its norm is integrable on the horizon. -/
theorem fractional_volterra_smul_triangle_integrable {α t : ℝ} {f : ℝ → E}
    (hα₀ : 0 < α) (hα₁ : α < 1) (hf : StronglyMeasurable f)
    (hfint : IntegrableOn f (Ioc 0 t)) :
    Integrable (fun z : ℝ × ℝ =>
      (fractionalL α (t - z.1) * fractionalK α (z.1 - z.2)) • f z.2)
      ((volume.restrict (Ioc 0 t)).prod (volume.restrict (Ioc 0 t))) := by
  have hc : Measurable (fun z : ℝ × ℝ =>
      fractionalL α (t - z.1) * fractionalK α (z.1 - z.2)) :=
    ((fractionalL_measurable α).comp (measurable_const.sub measurable_fst)).mul
      ((fractionalK_measurable α).comp (measurable_fst.sub measurable_snd))
  have hsm := hc.stronglyMeasurable.smul (hf.comp_measurable measurable_snd)
  refine (integrable_norm_iff hsm.aestronglyMeasurable).mp ?_
  refine (fractional_volterra_triangle_integrable hα₀ hα₁
    hf.norm.measurable hfint.norm).congr (Eventually.of_forall fun z => ?_)
  change fractionalL α (t - z.1) * fractionalK α (z.1 - z.2) * ‖f z.2‖ =
    ‖(fractionalL α (t - z.1) * fractionalK α (z.1 - z.2)) • f z.2‖
  have hnK (u : ℝ) : 0 ≤ fractionalK α u := by
    unfold fractionalK
    split
    · exact le_rfl
    · exact div_nonneg (Real.rpow_nonneg (le_of_lt (lt_of_not_ge ‹¬u ≤ 0›)) _)
        (Real.Gamma_pos_of_pos hα₀).le
  have hnL (u : ℝ) : 0 ≤ fractionalL α u := by
    unfold fractionalL
    split
    · exact le_rfl
    · exact div_nonneg (Real.rpow_nonneg (le_of_lt (lt_of_not_ge ‹¬u ≤ 0›)) _)
        (Real.Gamma_pos_of_pos (sub_pos.mpr hα₁)).le
  rw [norm_smul, Real.norm_of_nonneg (mul_nonneg (hnL _) (hnK _))]

/-- Fractional inversion of the drift convolution in a Banach space. -/
theorem fractional_volterra_smul_inverts_drift {α t : ℝ} {f : ℝ → E}
    (hα₀ : 0 < α) (hα₁ : α < 1) (hf : StronglyMeasurable f)
    (hfint : IntegrableOn f (Ioc 0 t)) :
    volterraSmulConvolution (fractionalL α) (volterraSmulConvolution (fractionalK α) f) t =
      ∫ s in Ioc (0 : ℝ) t, f s := by
  rw [volterra_smul_convolution_assoc (fun x hx => by simp [fractionalK, hx])
    (fractional_volterra_smul_triangle_integrable hα₀ hα₁ hf hfint)]
  unfold volterraSmulConvolution
  rw [← setIntegral_congr_set (Ioo_ae_eq_Ioc : Ioo (0 : ℝ) t =ᵐ[volume] Ioc 0 t),
    ← setIntegral_congr_set (Ioo_ae_eq_Ioc : Ioo (0 : ℝ) t =ᵐ[volume] Ioc 0 t)]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro s hs
  change volterraConvolution (fractionalL α) (fractionalK α) (t - s) • f s = f s
  rw [fractional_causal_kernel_inverse hα₀ hα₁ (sub_pos.mpr hs.2), one_smul]

/-- Fractional convolution by the inverse kernel is injective on
continuous Banach-valued paths on a positive finite horizon. -/
theorem fractionalL_smul_zero_implies_path_zero {α T : ℝ} {f : ℝ → E}
    (hα₀ : 0 < α) (hα₁ : α < 1) (hT : 0 < T) (hf : StronglyMeasurable f)
    (hfc : ContinuousOn f (Icc 0 T))
    (hzero : ∀ t ∈ Icc 0 T, volterraSmulConvolution (fractionalL α) f t = 0) :
    ∀ t ∈ Icc 0 T, f t = 0 := by
  have hK : fractionalK (1 - α) = fractionalL α := by
    funext t
    simp only [fractionalK, fractionalL, show 1 - α - 1 = -α by ring]
  have hL : fractionalL (1 - α) = fractionalK α := by
    funext t
    simp only [fractionalL, fractionalK, show -(1 - α) = α - 1 by ring,
      show 1 - (1 - α) = α by ring]
  have hi (t : ℝ) (ht : t ∈ Icc 0 T) : IntervalIntegrable f volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1 (hfc.mono (Icc_subset_Icc le_rfl ht.2))
  have hprim (t : ℝ) (ht : t ∈ Icc 0 T) : (∫ s in (0 : ℝ)..t, f s) = 0 := by
    have hfin := (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).1 (hi t ht)
    have hidentity := fractional_volterra_smul_inverts_drift (α := 1 - α)
      (sub_pos.mpr hα₁) (by linarith : 1 - α < 1) hf hfin
    rw [hK, hL] at hidentity
    rw [intervalIntegral.integral_of_le ht.1, ← hidentity]
    unfold volterraSmulConvolution
    calc
      _ = ∫ _ in Ioc (0 : ℝ) t, (0 : E) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro s hs
        change fractionalK α (t - s) • volterraSmulConvolution (fractionalL α) f s = 0
        rw [hzero s ⟨hs.1.le, hs.2.trans ht.2⟩, smul_zero]
      _ = 0 := integral_zero _ _
  have hint : EqOn f (fun _ : ℝ => (0 : E)) (Ioo 0 T) := by
    intro t ht
    have hmem : Ioo 0 T ∈ 𝓝 t := Ioo_mem_nhds ht.1 ht.2
    have hfc' : ContinuousAt f t :=
      (hfc t (Ioo_subset_Icc_self ht)).continuousAt (Icc_mem_nhds ht.1 ht.2)
    have hd := intervalIntegral.integral_hasDerivAt_right (hi t (Ioo_subset_Icc_self ht))
      hf.stronglyMeasurableAtFilter hfc'
    have he : (fun t => ∫ s in (0 : ℝ)..t, f s) =ᶠ[𝓝 t] fun _ => (0 : E) :=
      Filter.Eventually.mono hmem (fun u hu => hprim u (Ioo_subset_Icc_self hu))
    exact hd.unique ((hasDerivAt_const t (0 : E)).congr_of_eventuallyEq he)
  exact hint.of_subset_closure hfc continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo hT.ne])


end RoughHeston

#print axioms RoughHeston.volterra_smul_convolution_assoc
#print axioms RoughHeston.fractional_volterra_smul_triangle_integrable
#print axioms RoughHeston.fractional_volterra_smul_inverts_drift

#print axioms RoughHeston.fractionalL_smul_zero_implies_path_zero
