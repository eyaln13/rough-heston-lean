import OrthogonalDeterministicConvolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology Interval InnerProductSpace

namespace RoughHeston

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

private theorem l2_inner_product_integral (f g : Lp ℝ 2 μ) :
    ⟪f,g⟫_ℝ=∫ ω,f ω*g ω ∂μ := by
  rw [L2.inner_def]
  congr 1
  funext ω
  change g ω*f ω=f ω*g ω
  ring

private theorem primitive_pairing_zero_imp {U : ℝ→Ω→ℝ} {Z : Ω→ℝ} {T : ℝ}
    (hU : Measurable (Function.uncurry U)) (hU₂ : ∀ r,MemLp (U r) 2 μ)
    {C : ℝ} (hC : 0≤C) (hUC : ∀ r∈Icc (0:ℝ) T,(∫ ω,(U r ω)^2 ∂μ)≤C)
    (hZ : Measurable Z) (hZ₂ : MemLp Z 2 μ)
    (u : ℝ→Lp ℝ 2 μ) (hu : ContinuousOn u (Icc 0 T))
    (hue : ∀ r∈Icc (0:ℝ) T,⇑(u r)=ᵐ[μ] U r)
    (hzero : ∀ t∈Ioo (0:ℝ) T,(∫ ω,(∫ r in (0:ℝ)..t,U r ω)*Z ω ∂μ)=0)
    {s : ℝ} (hs : s∈Ioo (0:ℝ) T) :
    (∫ ω,U s ω*Z ω ∂μ)=0 := by
  let f (r : ℝ) := ∫ ω,U r ω*Z ω ∂μ
  let z := hZ₂.toLp Z
  have hfc : ContinuousOn f (Icc 0 T) := by
    refine (hu.inner continuousOn_const (g := fun _ => z)).congr ?_
    intro r hr
    change f r = ⟪u r,z⟫_ℝ
    rw [l2_inner_product_integral]
    exact integral_congr_ae ((hue r hr).symm.mul hZ₂.coeFn_toLp.symm)
  have hfm : Measurable f :=
    (hU.mul (hZ.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable
  have hprim (t : ℝ) (ht : t∈Ioo (0:ℝ) T) : (∫ r in (0:ℝ)..t,f r)=0 := by
    have ht' : 0≤t := ht.1.le
    have hν : ∀ᵐ r ∂volume.restrict (Ioc (0:ℝ) t),(∫ ω,(U r ω)^2 ∂μ)≤C := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact hUC r ⟨hr.1.le,hr.2.trans ht.2.le⟩
    simpa only [one_mul,← intervalIntegral.integral_of_le ht',f] using
      (deterministic_weighted_path_pairing (ν := volume.restrict (Ioc (0:ℝ) t))
        hU hZ hZ₂ (measurable_const (a := (1:ℝ))) (integrable_const 1) hU₂ hC hν).symm.trans
          (by simpa only [one_mul,← intervalIntegral.integral_of_le ht'] using hzero t ht)
  have hfcAt : ContinuousAt f s :=
    (hfc s (Ioo_subset_Icc_self hs)).continuousAt (Icc_mem_nhds hs.1 hs.2)
  have hfi : IntervalIntegrable f volume 0 s :=
    ((hfc.mono (Icc_subset_Icc_right hs.2.le))).intervalIntegrable_of_Icc hs.1.le
  have hd := intervalIntegral.integral_hasDerivAt_right hfi
    hfm.stronglyMeasurable.stronglyMeasurableAtFilter hfcAt
  have he : (fun t => ∫ r in (0:ℝ)..t,f r)=ᶠ[𝓝 s] fun _ => (0:ℝ) :=
    Filter.Eventually.mono (Ioo_mem_nhds hs.1 hs.2) (fun t ht => hprim t ht)
  exact hd.unique ((hasDerivAt_const s (0:ℝ)).congr_of_eventuallyEq he)

private theorem subtract_mean_pairing {X Y : Ω→ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    (∫ ω,X ω*(Y ω-(∫ z,Y z ∂μ)) ∂μ) =
      (∫ ω,X ω*Y ω ∂μ)-(∫ ω,X ω ∂μ)*(∫ ω,Y ω ∂μ) := by
  let c := ∫ ω,Y ω ∂μ
  have hXY : Integrable (fun ω => X ω*Y ω) μ := hX.integrable_mul hY
  have hXc := (hX.integrable one_le_two).mul_const c
  simp_rw [mul_sub]
  rw [integral_sub hXY hXc,integral_mul_const]

/-- If the integrated coordinates have zero mixed covariance for all
observation pairs, differentiating twice gives the same for the original
coordinates. The differentiations use continuity of time sections in L². -/
theorem zero_mixed_covariance_of_orthogonal_primitives {T : ℝ} {U V : ℝ→Ω→ℝ}
    (hU : Measurable (Function.uncurry U)) (hV : Measurable (Function.uncurry V))
    (hU₂ : ∀ r,MemLp (U r) 2 μ) (hV₂ : ∀ r,MemLp (V r) 2 μ)
    {C D : ℝ} (hC : 0≤C) (hD : 0≤D)
    (hUC : ∀ r∈Icc (0:ℝ) T,(∫ ω,(U r ω)^2 ∂μ)≤C)
    (hVD : ∀ r∈Icc (0:ℝ) T,(∫ ω,(V r ω)^2 ∂μ)≤D)
    (u v : ℝ→Lp ℝ 2 μ) (hu : ContinuousOn u (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hue : ∀ r∈Icc (0:ℝ) T,⇑(u r)=ᵐ[μ] U r)
    (hve : ∀ r∈Icc (0:ℝ) T,⇑(v r)=ᵐ[μ] V r)
    (hA : ∀ s∈Ioo (0:ℝ) T,MemLp (fun ω => ∫ r in (0:ℝ)..s,U r ω) 2 μ)
    (hB : ∀ t∈Ioo (0:ℝ) T,MemLp (fun ω => ∫ r in (0:ℝ)..t,V r ω) 2 μ)
    (hAB : ∀ s∈Ioo (0:ℝ) T,∀ t∈Ioo (0:ℝ) T,
      (∫ ω,(∫ r in (0:ℝ)..s,U r ω)*(∫ r in (0:ℝ)..t,V r ω) ∂μ) =
        (∫ ω,(∫ r in (0:ℝ)..s,U r ω) ∂μ)*(∫ ω,(∫ r in (0:ℝ)..t,V r ω) ∂μ))
    {s t : ℝ} (hs : s∈Ioo (0:ℝ) T) (ht : t∈Ioo (0:ℝ) T) :
    (∫ ω,U s ω*V t ω ∂μ)=(∫ ω,U s ω ∂μ)*(∫ ω,V t ω ∂μ) := by
  have hfirst (b : ℝ) (hb : b∈Ioo (0:ℝ) T) :
      (∫ ω,U s ω*(∫ r in (0:ℝ)..b,V r ω) ∂μ)=
        (∫ ω,U s ω ∂μ)*(∫ ω,(∫ r in (0:ℝ)..b,V r ω) ∂μ) := by
    let B (ω : Ω) := ∫ r in (0:ℝ)..b,V r ω
    let c := ∫ ω,B ω ∂μ
    have hb₂ : MemLp B 2 μ := hB b hb
    have hbM : Measurable B := by
      dsimp [B]
      simp_rw [intervalIntegral.integral_of_le hb.1.le]
      exact hV.stronglyMeasurable.integral_prod_left'.measurable
    have htest (a : ℝ) (ha : a∈Ioo (0:ℝ) T) :
        (∫ ω,(∫ r in (0:ℝ)..a,U r ω)*(B ω-c) ∂μ)=0 := by
      rw [subtract_mean_pairing (hA a ha) hb₂]
      exact sub_eq_zero.mpr (hAB a ha b hb)
    have hz := primitive_pairing_zero_imp hU hU₂ hC hUC (hbM.sub_const c)
      (hb₂.sub (memLp_const c)) u hu hue htest hs
    rw [subtract_mean_pairing (hU₂ s) hb₂] at hz
    exact sub_eq_zero.mp hz
  let c := ∫ ω,U s ω ∂μ
  have hUm : Measurable (U s) := hU.comp (measurable_const.prodMk measurable_id)
  have htest (b : ℝ) (hb : b∈Ioo (0:ℝ) T) :
      (∫ ω,(∫ r in (0:ℝ)..b,V r ω)*(U s ω-c) ∂μ)=0 := by
    rw [subtract_mean_pairing (hB b hb) (hU₂ s)]
    rw [mul_comm (∫ ω,(∫ r in (0:ℝ)..b,V r ω) ∂μ)]
    simp_rw [mul_comm (∫ r in (0:ℝ)..b,V r _) (U s _)]
    exact sub_eq_zero.mpr (hfirst b hb)
  have hz := primitive_pairing_zero_imp hV hV₂ hD hVD (hUm.sub_const c)
    ((hU₂ s).sub (memLp_const c)) v hv hve htest ht
  rw [subtract_mean_pairing (hV₂ t) (hU₂ s),mul_comm (∫ ω,V t ω ∂μ)] at hz
  simpa only [mul_comm (V t _) (U s _)] using sub_eq_zero.mp hz

#print axioms zero_mixed_covariance_of_orthogonal_primitives

end RoughHeston
