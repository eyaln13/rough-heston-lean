import DensityChargeRiccati
import VolterraMomentBound

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RoughHeston

private theorem density_kernel_nonneg {α : ℝ} (hα : 0 < α) (s : ℝ) :
    0 ≤ fractionalK α s := by
  by_cases hs : s ≤ 0
  · simp [fractionalK, hs]
  · rw [fractionalK, ite_eq_right hs]
    exact div_nonneg (Real.rpow_nonneg (lt_of_not_ge hs).le _) (Real.Gamma_pos_of_pos hα).le

private theorem density_convolution_sub_div {α t T l : ℝ} {f g : ℝ → ℝ}
    (hα : 0 < α) (ht : t ∈ Icc 0 T) (hf : Continuous f) (hg : Continuous g) :
    volterraConvolution (fractionalK α) (fun s => (f s-g s)/l) t =
      (volterraConvolution (fractionalK α) f t-volterraConvolution (fractionalK α) g t)/l := by
  unfold volterraConvolution
  have hEq (s : ℝ) : fractionalK α (t-s)*((f s-g s)/l) =
    (fractionalK α (t-s)*f s-fractionalK α (t-s)*g s)/l := by ring
  simp_rw [hEq]
  rw [integral_div, integral_sub (density_conv_integrable hα ht hf)
    (density_conv_integrable hα ht hg)]

private theorem density_convolution_parameter_congr {α t T : ℝ} {f g : ℝ → ℝ}
    (ht : t ∈ Icc 0 T) (h : EqOn f g (Icc 0 T)) :
    volterraConvolution (fractionalK α) f t = volterraConvolution (fractionalK α) g t := by
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s hs
  change fractionalK α (t-s)*f s = fractionalK α (t-s)*g s
  rw [h ⟨hs.1.le, hs.2.trans ht.2⟩]

private theorem density_conv_norm_affine_bound {α T t A B : ℝ} {f v : ℝ → ℝ}
    (hα : 0 < α) (ht : t ∈ Icc 0 T) (hf : Continuous f) (hv : Continuous v)
    (hbound : ∀ s ∈ Icc 0 T, ‖f s‖ ≤ A+B*‖v s‖) :
    ‖volterraConvolution (fractionalK α) f t‖ ≤
      (t^α/Real.Gamma (α+1))*A+
        B*volterraConvolution (fractionalK α) (fun s => ‖v s‖) t := by
  let k (s : ℝ) := fractionalK α (t-s)
  have hvn : Continuous (fun s => ‖v s‖) := hv.norm
  have hiA := (density_conv_integrable (g := fun _ => A) hα ht continuous_const)
  have hiB := (density_conv_integrable hα ht hvn).const_mul B
  have hInt : (∫ s in Ioc (0 : ℝ) t, ‖k s*f s‖) ≤
      ∫ s in Ioc (0 : ℝ) t, k s*A+B*(k s*‖v s‖) := by
    refine setIntegral_mono_on (density_conv_integrable hα ht hf).norm
      (hiA.add hiB) measurableSet_Ioc ?_
    intro s hs
    have hk : 0 ≤ k s := density_kernel_nonneg hα _
    rw [norm_mul, Real.norm_of_nonneg hk]
    have h := mul_le_mul_of_nonneg_left (hbound s ⟨hs.1.le, hs.2.trans ht.2⟩) hk
    convert h using 1
    ring
  unfold volterraConvolution
  apply (norm_integral_le_integral_norm _).trans
  rw [integral_add hiA hiB, integral_mul_const, integral_const_mul, density_fractionalK_mass hα ht.1]
    at hInt
  exact hInt

private theorem density_uniform_volterra_norm_bound {ι : Type*} {α T M A B : ℝ}
    {v f : ι → ℝ → ℝ} (hα : 0 < α) (hT : 0 ≤ T) (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hv : ∀ i, Continuous (v i)) (hf : ∀ i, Continuous (f i))
    (hv0 : ∀ i, ‖v i 0‖ ≤ M)
    (heq : ∀ i t, t ∈ Icc 0 T → v i t = v i 0+volterraConvolution (fractionalK α) (f i) t)
    (hbound : ∀ i s, s ∈ Icc 0 T → ‖f i s‖ ≤ A+B*‖v i s‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i t, t ∈ Icc 0 T → ‖v i t‖ ≤ C := by
  let L := M+(T^α/Real.Gamma (α+1))*A+B
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hg := Real.Gamma_pos_of_pos (show 0 < α+1 by linarith)
  have hI : IntervalIntegrable (fractionalK α) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr (fractionalK_integrableOn_Ioc hα T)
  obtain ⟨C, hC⟩ := uniform_volterra_moment_bound
    (h := fun i s => ‖v i s‖) hT hL hI (fractionalK_measurable α)
    (fun s _ => density_kernel_nonneg hα s) (fun i => (hv i).norm.measurable)
    (fun _ _ _ => norm_nonneg _) (fun i => isCompact_Icc.bddAbove_image (hv i).norm.continuousOn)
    (fun i t ht => by
      let Z := volterraConvolution (fractionalK α) (fun s => ‖v i s‖) t
      have hZ : 0 ≤ Z := integral_nonneg_of_ae
        (ae_of_all _ fun s => mul_nonneg (density_kernel_nonneg hα (t-s)) (norm_nonneg _))
      have hmass : t^α/Real.Gamma (α+1) ≤ T^α/Real.Gamma (α+1) :=
        div_le_div_of_nonneg_right (Real.rpow_le_rpow ht.1 ht.2 hα.le) hg.le
      have hMb : M+(T^α/Real.Gamma (α+1))*A ≤ L := le_add_of_nonneg_right hB
      have hLb : B ≤ L := le_add_of_nonneg_left (by positivity)
      calc
        ‖v i t‖ ≤ ‖v i 0‖+‖volterraConvolution (fractionalK α) (f i) t‖ := by
          conv_lhs => rw [heq i t ht]
          exact norm_add_le _ _
        _ ≤ M+((t^α/Real.Gamma (α+1))*A+B*Z) := add_le_add (hv0 i)
          (density_conv_norm_affine_bound hα ht (hf i) (hv i) (hbound i))
        _ ≤ L*(1+Z) := by
          rw [mul_add, mul_one, ← add_assoc]
          exact add_le_add ((add_le_add (le_refl M)
            (mul_le_mul_of_nonneg_right hmass hA)).trans hMb)
            (mul_le_mul_of_nonneg_right hLb hZ))
  exact ⟨max C 0, le_max_right _ _, fun i t ht => (hC i t ht).trans (le_max_left _ _)⟩

/-- The linearized Riccati equation gives the right derivative in the
initial density parameter, with an error bound uniform on the horizon.
Existence of the continuous family and of the continuous linear solution
is assumed in this estimate. -/
theorem density_riccati_sensitivity_right
    {α T q κ a B : ℝ} {w : ℝ → ℝ → ℝ} {k : ℝ → ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hw : ∀ l ∈ Icc (0 : ℝ) 1, Continuous (w l))
    (hwb : ∀ l ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 T, ‖w l t‖ ≤ B)
    (hwvol : ∀ l ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 T,
      w l t = l+volterraConvolution (fractionalK α)
        (fun s => q+κ*l-κ*w l s-a*(w l s)^2) t)
    (hk : Continuous k)
    (hkvol : ∀ t ∈ Icc 0 T, k t = 1+volterraConvolution (fractionalK α)
      (fun s => κ-(κ+2*a*w 0 s)*k s) t) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ l ∈ Ioc (0 : ℝ) 1, ∀ t ∈ Icc 0 T,
      ‖(w l t-w 0 t)/l-k t‖ ≤ C*l) ∧
    ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun l => w l t) (k t) (Ici 0) 0 := by
  let U := Ioc (0:ℝ) 1
  let F (l s : ℝ) := q+κ*l-κ*w l s-a*(w l s)^2
  let H (s : ℝ) := κ-(κ+2*a*w 0 s)*k s
  let D (l : U) (s : ℝ) := (w l s-w 0 s)/(l : ℝ)
  let P (l : U) (s : ℝ) := κ-(κ+a*(w l s+w 0 s))*D l s
  let E (l : U) (s : ℝ) := (D l s-k s)/(l : ℝ)
  let G (l : U) (s : ℝ) := -(κ+2*a*w 0 s)*E l s-a*(D l s)^2
  let L := ‖κ‖+2*‖a‖*B
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hz : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hcc (l : U) : (l : ℝ) ∈ Icc 0 1 := Ioc_subset_Icc_self l.property
  have hF (l : ℝ) (hl : l ∈ Icc 0 1) : Continuous (F l) :=
    (continuous_const.sub (continuous_const.mul (hw l hl))).sub
      (continuous_const.mul ((hw l hl).pow 2))
  have hH : Continuous H := continuous_const.sub
    ((continuous_const.add (continuous_const.mul (hw 0 hz))).mul hk)
  have hD (l : U) : Continuous (D l) := ((hw l (hcc l)).sub (hw 0 hz)).div_const _
  have hP (l : U) : Continuous (P l) := continuous_const.sub
    ((continuous_const.add (continuous_const.mul ((hw l (hcc l)).add (hw 0 hz)))).mul (hD l))
  have hE (l : U) : Continuous (E l) := ((hD l).sub hk).div_const _
  have hG (l : U) : Continuous (G l) :=
    (((continuous_const.add (continuous_const.mul (hw 0 hz))).neg).mul (hE l)).sub
      (continuous_const.mul ((hD l).pow 2))
  have hDvol (l : U) (t : ℝ) (ht : t ∈ Icc 0 T) :
      D l t = 1+volterraConvolution (fractionalK α) (P l) t := by
    have hl : 0 < (l : ℝ) := l.property.1
    have hP' : EqOn (fun s => (F l s-F 0 s)/(l : ℝ)) (P l) (Icc 0 T) := by
      intro s _
      dsimp [F, P, D]
      field_simp [ne_of_gt hl]
      ring
    rw [← density_convolution_parameter_congr ht hP',
      density_convolution_sub_div hα ht (hF l (hcc l)) (hF 0 hz)]
    change (w l t-w 0 t)/(l : ℝ) = _
    rw [hwvol l (hcc l) t ht, hwvol 0 hz t ht]
    change ((l : ℝ)+volterraConvolution (fractionalK α) (F l) t -
      (0+volterraConvolution (fractionalK α) (F 0) t))/(l : ℝ) = _
    field_simp [ne_of_gt hl]
    ring
  have hEvol (l : U) (t : ℝ) (ht : t ∈ Icc 0 T) :
      E l t = volterraConvolution (fractionalK α) (G l) t := by
    have hl : 0 < (l : ℝ) := l.property.1
    have hG' : EqOn (fun s => (P l s-H s)/(l : ℝ)) (G l) (Icc 0 T) := by
      intro s _
      dsimp [P, H, G, D, E]
      field_simp [ne_of_gt hl]
      ring
    rw [← density_convolution_parameter_congr ht hG',
      density_convolution_sub_div hα ht (hP l) hH]
    change (D l t-k t)/(l : ℝ) = _
    rw [hDvol l t ht, hkvol t ht]
    change ((1+volterraConvolution (fractionalK α) (P l) t)-
      (1+volterraConvolution (fractionalK α) H t))/(l : ℝ) = _
    ring
  have hPnorm (l : U) (s : ℝ) (hs : s ∈ Icc 0 T) : ‖P l s‖ ≤ ‖κ‖+L*‖D l s‖ := by
    have hW : ‖w l s+w 0 s‖ ≤ 2*B :=
      (norm_add_le _ _).trans ((add_le_add (hwb l (hcc l) s hs) (hwb 0 hz s hs)).trans_eq (by ring))
    have hK : ‖κ+a*(w l s+w 0 s)‖ ≤ L := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
      exact (add_le_add le_rfl (mul_le_mul_of_nonneg_left hW (norm_nonneg a))).trans_eq (by dsimp [L]; ring)
    exact (norm_sub_le _ _).trans (by rw [norm_mul]; gcongr)
  have hD0 (l : U) : D l 0 = 1 := by
    simpa [volterraConvolution] using hDvol l 0 ⟨le_rfl, hT⟩
  obtain ⟨C, hC, hDnorm⟩ := density_uniform_volterra_norm_bound hα hT zero_le_one (norm_nonneg κ) hL
    hD hP (fun l => by simp [hD0 l]) (fun l t ht => by rw [hD0 l]; exact hDvol l t ht) hPnorm
  have hGnorm (l : U) (s : ℝ) (hs : s ∈ Icc 0 T) :
      ‖G l s‖ ≤ ‖a‖*C^2+L*‖E l s‖ := by
    have hK : ‖κ+2*a*w 0 s‖ ≤ L := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, Real.norm_of_nonneg (show 0≤(2:ℝ) by norm_num)]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hwb 0 hz s hs) (by positivity))
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_neg, norm_mul, norm_pow, add_comm]
    exact add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hDnorm l s hs) 2)
      (norm_nonneg a)) (mul_le_mul_of_nonneg_right hK (norm_nonneg _))
  have hE0 (l : U) : E l 0 = 0 := by
    simpa [volterraConvolution] using hEvol l 0 ⟨le_rfl, hT⟩
  obtain ⟨C', hC', hEnorm⟩ := density_uniform_volterra_norm_bound hα hT le_rfl
    (show 0≤‖a‖*C^2 by positivity) hL hE hG (fun l => by simp [hE0 l])
    (fun l t ht => by rw [hE0 l, zero_add]; exact hEvol l t ht) hGnorm
  have hUniform (l : ℝ) (hl : l ∈ Ioc 0 1) (t : ℝ) (ht : t ∈ Icc 0 T) :
      ‖(w l t-w 0 t)/l-k t‖ ≤ C'*l := by
    have hb := hEnorm ⟨l, hl⟩ t ht
    change ‖((w l t-w 0 t)/l-k t)/l‖ ≤ C' at hb
    rw [norm_div, Real.norm_of_nonneg hl.1.le] at hb
    exact (div_le_iff₀ hl.1).mp hb
  refine ⟨⟨C', hC', hUniform⟩, ?_⟩
  intro t ht
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hside : Ici (0 : ℝ) \ {0} = Ioi 0 := by ext l; simp
  rw [hside, tendsto_iff_norm_sub_tendsto_zero]
  have hsmall : Tendsto (fun l : ℝ => C'*l) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hc : Continuous (fun l : ℝ => C'*l) := continuous_const.mul continuous_id
    have hl : Tendsto (fun l : ℝ => C'*l) (𝓝 0) (𝓝 (C' * 0)) := hc.continuousAt
    simpa only [mul_zero] using hl.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hsmall
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)] with l hl h1
  have hll : l ∈ Ioc (0:ℝ) 1 := ⟨hl, (show l < 1 from h1).le⟩
  simpa [slope_def_field] using hUniform l hll t ht

#print axioms density_riccati_sensitivity_right

end RoughHeston
