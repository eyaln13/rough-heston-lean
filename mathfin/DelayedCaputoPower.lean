import ClusterDensitySensitivity

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RoughHeston

/-- The fractional time primitive of a constant density starting at a
deterministic delay. -/
noncomputable def delayedCaputoPower (α d A : ℝ) (t : ℝ) : ℝ :=
  A * ((max 0 (t-d))^α / Real.Gamma (α+1))

theorem continuous_delayedCaputoPower {α d A : ℝ} (hα : 0 < α) :
    Continuous (delayedCaputoPower α d A) := by
  refine continuous_const.mul (((Real.continuous_rpow_const hα.le).comp ?_).div_const _)
  exact continuous_const.max (continuous_id.sub continuous_const)

private theorem delayedCaputoPower_is_convolution {α d A t : ℝ}
    (hα : 0 < α) (hd : 0 ≤ d) (_ht : 0 ≤ t) :
    delayedCaputoPower α d A t = volterraConvolution (fractionalK α)
      ((Ioi d).indicator (fun _ => A)) t := by
  unfold volterraConvolution
  have he : EqOn (fun s : ℝ => fractionalK α (t-s)*((Ioi d).indicator (fun _ => A)) s)
      ((Ioi d).indicator (fun s => fractionalK α (t-s)*A)) (Ioc 0 t) := by
    intro s _
    by_cases h : s ∈ Ioi d <;> simp [Set.indicator, h]
  rw [setIntegral_congr_fun measurableSet_Ioc he, setIntegral_indicator measurableSet_Ioi,
    Ioc_inter_Ioi, sup_eq_right.mpr hd]
  rcases le_total t d with htd | hdt
  · rw [Ioc_eq_empty_of_le htd, setIntegral_empty]
    simp [delayedCaputoPower, max_eq_left (sub_nonpos.mpr htd), Real.zero_rpow hα.ne']
  · let f (s : ℝ) := fractionalK α (t-s)*A
    change delayedCaputoPower α d A t = ∫ s in Ioc d t, f s
    have hs := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := t-d) f d
    rw [zero_add, sub_add_cancel, intervalIntegral.integral_of_le hdt,
      intervalIntegral.integral_of_le (sub_nonneg.mpr hdt)] at hs
    rw [← hs]
    have hf : EqOn (fun s => f (s+d)) (fun s => fractionalK α (t-d-s)*A) (Ioc 0 (t-d)) := by
      intro s _
      dsimp [f]
      rw [show t-(s+d)=t-d-s by ring]
    rw [setIntegral_congr_fun measurableSet_Ioc hf, integral_mul_const,
      density_fractionalK_mass hα (sub_nonneg.mpr hdt)]
    simp only [delayedCaputoPower, max_eq_right (sub_nonneg.mpr hdt), mul_comm]

/-- The delayed fractional power has constant Caputo derivative after
its starting time. -/
theorem delayedCaputoPower_memory {α d A t : ℝ}
    (hα : 0 < α) (hα' : α < 1) (hd : 0 ≤ d) (ht : d < t) :
    IntervalIntegrable (fun u => (α*u^(-α-1)/Real.Gamma (1-α))*
      (delayedCaputoPower α d A t-delayedCaputoPower α d A (t-u))) volume 0 t ∧
    fractionalMemory α (delayedCaputoPower α d A 0) (delayedCaputoPower α d A) t = A := by
  let g := delayedCaputoPower α d A
  have hgc : Continuous g := continuous_delayedCaputoPower hα
  have hg₀ : g 0 = 0 := by
    change A*((max 0 ((0:ℝ)-d))^α/Real.Gamma (α+1)) = 0
    rw [max_eq_left (sub_nonpos.mpr hd), Real.zero_rpow hα.ne']
    simp
  have hgcd : ContDiffAt ℝ 1 g t := by
    have hp : ContDiffAt ℝ 1 (fun x : ℝ => (x-d)^α) t :=
      (Real.contDiffAt_rpow_const_of_ne (sub_pos.mpr ht).ne').comp t (contDiffAt_id.sub contDiffAt_const)
    have hh : ContDiffAt ℝ 1 (fun x : ℝ => A*((x-d)^α/Real.Gamma (α+1))) t :=
      contDiffAt_const.mul (hp.div contDiffAt_const (Real.Gamma_pos_of_pos (by linarith)).ne')
    apply hh.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with s hs
    have hs' : d < s := hs
    simp only [g, delayedCaputoPower, max_eq_right (sub_nonneg.mpr hs'.le)]
  let f : ℝ → ℝ := (Ioi d).indicator (fun _ => A)
  have hfm : Measurable f := measurable_const.indicator measurableSet_Ioi
  have hPrim (s : ℝ) (hs : d < s) : volterraConvolution (fractionalL α) g s = A*(s-d) := by
    have hs₀ := hd.trans_lt hs
    have hi : IntegrableOn f (Ioc 0 s) := by
      unfold f
      exact (integrable_const A).indicator measurableSet_Ioi
    have he := (fractional_rl_inverse_of_point_charge (q := 0) hα hα' hs₀ hfm hi
      (w := g) (fun v hv => by
        simp only [zero_mul,zero_add]
        exact delayedCaputoPower_is_convolution hα hd hv.1.le)).2
    rw [he, zero_add]
    change (∫ v in Ioc (0 : ℝ) s, (Ioi d).indicator (fun _ => A) v) = _
    rw [setIntegral_indicator measurableSet_Ioi, Ioc_inter_Ioi, sup_eq_right.mpr hd,
      setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hs.le), mul_comm]
  have hDeriv : HasDerivAt (volterraConvolution (fractionalL α) g) A t := by
    have hl : HasDerivAt (fun s : ℝ => A*(s-d)) A t := by
      convert ((hasDerivAt_id t).sub_const d).const_mul A using 1
      · funext s
        dsimp
      · ring
    apply hl.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact hPrim s hs
  obtain ⟨hi,hD⟩ := fractional_rl_hasDerivAt_memory hα hα' (hd.trans_lt ht) hgc.measurable
    (hgc.intervalIntegrable 0 t).1 hgcd
  refine ⟨hi, ?_⟩
  change fractionalMemory α (g 0) g t = A
  rw [hg₀, ← hD.deriv, hDeriv.deriv]

/-- The Caputo memory operator is additive under subtraction of paths
and insensitive to a common constant offset in the path and initial value. -/
theorem fractionalMemory_affine_sub {α t C : ℝ} {f g : ℝ → ℝ}
    (hf : IntervalIntegrable (fun u => (α*u^(-α-1)/Real.Gamma (1-α))*(f t-f (t-u))) volume 0 t)
    (hg : IntervalIntegrable (fun u => (α*u^(-α-1)/Real.Gamma (1-α))*(g t-g (t-u))) volume 0 t) :
    let p := fun s => C+f s-g s
    IntervalIntegrable (fun u => (α*u^(-α-1)/Real.Gamma (1-α))*(p t-p (t-u))) volume 0 t ∧
    fractionalMemory α (p 0) p t = fractionalMemory α (f 0) f t - fractionalMemory α (g 0) g t := by
  dsimp
  have hfun : (fun u : ℝ => (α*u^(-α-1)/Real.Gamma (1-α))*
      ((C+f t-g t)-(C+f (t-u)-g (t-u)))) =
      (fun u : ℝ => (α*u^(-α-1)/Real.Gamma (1-α))*(f t-f (t-u))) -
      (fun u : ℝ => (α*u^(-α-1)/Real.Gamma (1-α))*(g t-g (t-u))) := by
    funext s
    simp only [Pi.sub_apply]
    ring
  constructor
  · rw [hfun]
    exact hf.sub hg
  · unfold fractionalMemory
    rw [hfun]
    have he : intervalIntegral
        ((fun u : ℝ => (α*u^(-α-1)/Real.Gamma (1-α))*(f t-f (t-u))) -
          (fun u : ℝ => (α*u^(-α-1)/Real.Gamma (1-α))*(g t-g (t-u))))
        0 t volume =
        (∫ u in (0 : ℝ)..t, (α*u^(-α-1)/Real.Gamma (1-α))*(f t-f (t-u))) -
        (∫ u in (0 : ℝ)..t, (α*u^(-α-1)/Real.Gamma (1-α))*(g t-g (t-u))) :=
      intervalIntegral.integral_sub hf hg
    rw [he]
    ring

#print axioms delayedCaputoPower_memory
#print axioms fractionalMemory_affine_sub

end RoughHeston
