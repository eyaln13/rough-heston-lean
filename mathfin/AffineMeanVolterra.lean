import FractionalPowerTriangle
import BanachHestonInversion
import AffineTestPrimitive

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RoughHeston

private theorem affine_fractionalK_one {x : ℝ} (hx : 0 < x) :
    fractionalK 1 x = 1 := by
  simp [fractionalK, not_le.mpr hx, Real.Gamma_one]

private theorem integral_eq_causal_unit_convolution (g : ℝ → ℝ) (t : ℝ) :
    (∫ s in Ioc (0:ℝ) t,g s)=volterraConvolution (fractionalK 1) g t := by
  unfold volterraConvolution
  rw [← restrict_Ioo_eq_restrict_Ioc]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro s hs
  change g s = fractionalK 1 (t-s)*g s
  rw [affine_fractionalK_one (sub_pos.mpr hs.2),one_mul]

private theorem affine_fractional_assoc_of_continuous_bound
    {α β t : ℝ} {g : ℝ → ℝ} (hα : 0 < α) (hβ : 0 < β) (ht : 0<t)
    (hgm : Measurable g) (hgc : ContinuousOn g (Icc 0 t)) :
    volterraConvolution (fractionalK α) (volterraConvolution (fractionalK β) g) t =
      volterraConvolution (volterraConvolution (fractionalK α) (fractionalK β)) g t := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hgc
  let I : Finset Unit := {()}
  have hL (s : ℝ) (hs : s∈Ioc 0 t) :
      |fractionalK α s| ≤ ∑ i ∈ I, (fun _ : Unit => (1:ℝ)) i*fractionalK ((fun _ : Unit => α) i) s := by
    have hn : 0≤fractionalK α s := by
      rw [fractionalK,ite_eq_right (not_le.mpr hs.1)]
      exact div_nonneg (Real.rpow_nonneg hs.1.le _) (Real.Gamma_pos_of_pos hα).le
    simp [I,abs_of_nonneg hn]
  have hR (s : ℝ) (hs : s∈Ioc 0 t) :
      ‖g s‖ ≤ ∑ i ∈ I, (fun _ : Unit => C) i*fractionalK ((fun _ : Unit => (1:ℝ)) i) s := by
    simpa only [I,Finset.sum_singleton,affine_fractionalK_one hs.1,mul_one] using
      hC s (Ioc_subset_Icc_self hs)
  have ha := volterra_fractional_smul_assoc_of_power_bounds hβ ht
    (fractionalK_measurable α) hgm.stronglyMeasurable I I (fun _ => α) (fun _ => 1)
    (fun _ => 1) (fun _ => C) (fun _ _ => hα) (fun _ _ => zero_lt_one) hL hR
  simpa only [volterraSmulConvolution,volterraConvolution,smul_eq_mul] using ha

private theorem affine_fractionalK_comp {α β : ℝ} (hα : 0<α) (hβ : 0<β) :
    volterraConvolution (fractionalK α) (fractionalK β)=fractionalK (α+β) := by
  funext t
  by_cases ht : 0<t
  · exact fractionalK_convolution_add hα hβ ht
  · simp [volterraConvolution,fractionalK,le_of_not_gt ht]

/-- Inverting the tilted first-moment equation yields the forward
Volterra mean equation on the open preterminal interval. -/
theorem affine_mean_volterra_of_inverse
    {α T v₀ b : ℝ} {f k : ℝ → ℝ} (hα : 0<α) (hα' : α<1)
    (hfm : Measurable f) (hkm : Measurable k)
    (hf : ContinuousOn f (Ico 0 T)) (hk : ContinuousOn k (Ico 0 T))
    (hinv : ∀ s ∈ Ioo 0 T, volterraConvolution (fractionalL α) f s =
      ∫ r in Ioc (0:ℝ) s,b+v₀*fractionalL α r-k r*f r) :
    ∀ s ∈ Ioo (0:ℝ) T, f s = v₀+volterraConvolution (fractionalK α) (fun r => b-k r*f r) s := by
  intro s hs
  let g (r : ℝ) := f r-v₀
  let G (r : ℝ) := b-k r*f r
  let K := fractionalK α
  let L := fractionalK (1-α)
  let J := fractionalK 1
  let U := (s+T)/2
  have hU : s<U := by dsimp [U]; linarith [hs.2]
  have hUT : U<T := by dsimp [U]; linarith [hs.2]
  have hUU : Icc (0:ℝ) U ⊆ Ico 0 T := fun r hr => ⟨hr.1,hr.2.trans_lt hUT⟩
  have hL : L=fractionalL α := by
    funext r
    simp only [L,fractionalK,fractionalL,show 1-α-1 = -α by ring]
  have hgm : Measurable g := hfm.sub_const v₀
  have hGc : ContinuousOn G (Icc 0 U) :=
    continuousOn_const.sub ((hk.mono hUU).mul (hf.mono hUU))
  have hGm : Measurable G := (hkm.mul hfm).const_sub b
  have hgc : ContinuousOn g (Icc 0 U) := (hf.mono hUU).sub continuousOn_const
  have hLg (t : ℝ) (ht : t ∈ Ioo (0:ℝ) U) :
      volterraConvolution L g t=volterraConvolution J G t := by
    let W (r : ℝ) := fractionalL α (t-r)
    have hW : IntegrableOn W (Ioc 0 t) := fractionalL_reflected_integrableOn_Ioc hα' ht.1.le
    have hLConst : (∫ r in Ioc (0:ℝ) t,W r)=∫ r in Ioc (0:ℝ) t, fractionalL α r := by
      rw [← intervalIntegral.integral_of_le ht.1.le,← intervalIntegral.integral_of_le ht.1.le]
      dsimp [W]
      rw [intervalIntegral.integral_comp_sub_left, sub_self,sub_zero]
    obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((hf.mono hUU).mono (Icc_subset_Icc_right ht.2.le))
    have hWf : IntegrableOn (fun r => W r*f r) (Ioc 0 t) := by
      refine (hW.norm.mul_const B).mono' (((fractionalL_measurable α).comp
        (measurable_const.sub measurable_id)).mul hfm).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hB r (Ioc_subset_Icc_self hr)) (norm_nonneg _)
    have hG : IntegrableOn G (Ioc 0 t) :=
      ((hGc.mono (Icc_subset_Icc_right ht.2.le)).intervalIntegrable_of_Icc ht.1.le).1
    have hAdd := integral_add hG ((fractionalL_integrableOn_Ioc hα' t).const_mul v₀)
    rw [← integral_eq_causal_unit_convolution G t,hL]
    unfold volterraConvolution
    change (∫ r in Ioc (0:ℝ) t,W r*(f r-v₀))=(∫ r in Ioc (0:ℝ) t,G r)
    simp_rw [mul_sub]
    rw [integral_sub hWf (hW.mul_const v₀),integral_mul_const,hLConst]
    have hi := hinv t ⟨ht.1,ht.2.trans hUT⟩
    change (∫ r in Ioc (0:ℝ) t,W r*f r)=
      (∫ r in Ioc (0:ℝ) t,b+v₀*fractionalL α r-k r*f r) at hi
    rw [hi]
    have hRe (r : ℝ) : b+v₀*fractionalL α r-k r*f r=G r+v₀*fractionalL α r := by
      dsimp [G]
      ring
    simp_rw [hRe]
    rw [hAdd,integral_const_mul]
    ring
  have hPrimitive (t : ℝ) (ht : t∈Ioo (0:ℝ) U) :
      (∫ r in Ioc (0:ℝ) t,g r)=
      ∫ r in Ioc (0:ℝ) t,volterraConvolution K G r := by
    have hsub : Icc (0:ℝ) t ⊆ Icc 0 U := Icc_subset_Icc_right ht.2.le
    rw [integral_eq_causal_unit_convolution,integral_eq_causal_unit_convolution]
    have hKL : volterraConvolution K L=J := by
      change volterraConvolution (fractionalK α) (fractionalK (1-α)) = fractionalK 1
      rw [affine_fractionalK_comp hα (sub_pos.mpr hα'),show α+(1-α)=1 by ring]
    have hKJ : volterraConvolution K J=volterraConvolution J K := by
      change volterraConvolution (fractionalK α) (fractionalK 1) = volterraConvolution (fractionalK 1) (fractionalK α)
      rw [affine_fractionalK_comp hα zero_lt_one,affine_fractionalK_comp zero_lt_one hα,add_comm α 1]
    have h1 := affine_fractional_assoc_of_continuous_bound hα (sub_pos.mpr hα') ht.1 hgm (hgc.mono hsub)
    have h2 := affine_fractional_assoc_of_continuous_bound hα zero_lt_one ht.1 hGm (hGc.mono hsub)
    have h3 := affine_fractional_assoc_of_continuous_bound zero_lt_one hα ht.1 hGm (hGc.mono hsub)
    change volterraConvolution K (volterraConvolution L g) t=volterraConvolution (volterraConvolution K L) g t at h1
    change volterraConvolution K (volterraConvolution J G) t=volterraConvolution (volterraConvolution K J) G t at h2
    change volterraConvolution J (volterraConvolution K G) t=volterraConvolution (volterraConvolution J K) G t at h3
    calc
      _ = volterraConvolution K (volterraConvolution L g) t := by
        rw [hKL] at h1
        exact h1.symm
      _ = volterraConvolution K (volterraConvolution J G) t := by
        unfold volterraConvolution
        apply setIntegral_congr_fun measurableSet_Ioc
        intro r hr
        change K (t-r)*volterraConvolution L g r = K (t-r)*volterraConvolution J G r
        rw [hLg r ⟨hr.1,hr.2.trans_lt ht.2⟩]
      _ = _ := by rw [h2,hKJ,← h3]
  have hKGc : ContinuousOn (volterraConvolution K G) (Icc 0 U) := by
    have h := continuousOn_volterra_forcing (hs.1.trans hU).le (fractionalK_measurable α)
      (fractionalK_integrableOn_Ioc hα U) hGc
    convert h using 1
    funext t
    rfl
  have hgcAt := hgc.continuousAt (Icc_mem_nhds hs.1 hU)
  have hKGAt := hKGc.continuousAt (Icc_mem_nhds hs.1 hU)
  have hInt (G : ℝ → ℝ) (h : ContinuousOn G (Icc 0 U)) :
      IntervalIntegrable G volume 0 s :=
    (h.mono (Icc_subset_Icc_right hU.le)).intervalIntegrable_of_Icc hs.1.le
  have hgsm : StronglyMeasurableAtFilter g (𝓝 s) volume :=
    hgm.stronglyMeasurable.stronglyMeasurableAtFilter
  have hKsm : StronglyMeasurableAtFilter (volterraConvolution K G) (𝓝 s) volume :=
    AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem
      (hKGc.aestronglyMeasurable (μ := volume) measurableSet_Icc) (Icc_mem_nhds hs.1 hU)
  have hgD := intervalIntegral.integral_hasDerivAt_right (hInt g hgc) hgsm hgcAt
  have hKGD := intervalIntegral.integral_hasDerivAt_right (hInt _ hKGc) hKsm hKGAt
  have heq : (fun t => ∫ r in (0:ℝ)..t,g r) =ᶠ[𝓝 s]
      fun t => ∫ r in (0:ℝ)..t,volterraConvolution K G r := by
    filter_upwards [Ioo_mem_nhds hs.1 hU] with t ht
    simpa only [intervalIntegral.integral_of_le ht.1.le] using hPrimitive t ht
  have hEnd := (hgD.congr_of_eventuallyEq heq.symm).unique hKGD
  change f s-v₀=volterraConvolution K G s at hEnd
  linarith

#print axioms affine_mean_volterra_of_inverse

end RoughHeston
