import HestonKernelMomentBound

/-! The Heston kernel sections form a strongly measurable family in
one fixed predictable L² space. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped MeasureTheory ProbabilityTheory Topology NNReal ENNReal

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℝ≥0 m} {V : ℝ≥0 → Ω → ℝ}

private noncomputable def taper (n : ℕ) (x : ℝ) : ℝ :=
  min 1 (((n : ℝ) + 1) * max x 0)

private theorem taper_nonneg (n : ℕ) (x : ℝ) : 0 ≤ taper n x :=
  le_min zero_le_one (mul_nonneg (by positivity) (le_max_right _ _))

private noncomputable def taperedWeight (α : ℝ) (u : ℝ≥0)
    (V : ℝ≥0 → Ω → ℝ) (n : ℕ) (z : ℝ≥0 × Ω) : ℝ :=
  taper n ((u : ℝ) - z.1) * hestonCutoffWeight α u V n z.1 z.2

private theorem taperedWeight_predictable (α : ℝ) (u : ℝ≥0)
    (hV : IsStronglyPredictable 𝒢 V) (n : ℕ) :
    StronglyMeasurable[𝒢.predictable] (taperedWeight α u V n) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := 𝒢.predictable
  have htime : Measurable (fun z : ℝ≥0 × Ω => (u : ℝ) - (z.1 : ℝ)) :=
    measurable_const.sub (measurable_subtype_coe.comp (measurable_fst_jointPredictable 𝒢))
  have htaper : Measurable (fun z : ℝ≥0 × Ω => taper n ((u : ℝ) - z.1)) :=
    measurable_const.min (measurable_const.mul (htime.max measurable_const))
  exact htaper.stronglyMeasurable.mul (heston_cutoffWeight_predictable α u hV n)

private theorem taperedWeight_bound (α : ℝ) (hα : 0 < α) (hα' : α ≤ 1)
    (u : ℝ≥0) (V : ℝ≥0 → Ω → ℝ) (n : ℕ) (z : ℝ≥0 × Ω) :
    ‖taperedWeight α u V n z‖ ≤ hestonKernel α ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1) := by
  rw [taperedWeight, norm_mul, Real.norm_of_nonneg (taper_nonneg _ _)]
  have h := mul_le_mul_of_nonneg_right (min_le_left (1 : ℝ) (((n : ℝ) + 1) * max ((u : ℝ) - z.1) 0))
    (norm_nonneg (hestonCutoffWeight α u V n z.1 z.2))
  exact h.trans (by simpa only [one_mul] using heston_cutoffWeight_bound hα hα' u V n z.1 z.2)

private theorem continuous_taperedWeight_parameter (α : ℝ) (V : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (z : ℝ≥0 × Ω) : Continuous (fun u : ℝ≥0 => taperedWeight α u V n z) := by
  let x (u : ℝ≥0) := (u : ℝ) - (z.1 : ℝ)
  let k (u : ℝ≥0) := max ((n : ℝ) + 1)⁻¹ (x u)
  have hx : Continuous x := continuous_subtype_val.sub continuous_const
  have hk : Continuous k := continuous_const.max hx
  have hp (u : ℝ≥0) : 0 < k u :=
    (inv_pos.mpr (by positivity : 0 < (n : ℝ) + 1)).trans_le (le_max_left _ _)
  have hkernel : Continuous (fun u : ℝ≥0 => hestonKernel α (k u)) := by
    have he : (fun u : ℝ≥0 => hestonKernel α (k u)) =
        fun u => k u ^ (α - 1) / Real.Gamma α := by
      funext u
      exact ite_eq_left (hp u)
    rw [he]
    exact (hk.rpow_const (fun u => Or.inl (hp u).ne')).div_const _
  have htaper : Continuous (fun u : ℝ≥0 => taper n (x u)) :=
    continuous_const.min (continuous_const.mul (hx.max continuous_const))
  exact htaper.mul (hkernel.mul continuous_const)

private theorem taperedWeight_le (α : ℝ) (hα : 0 < α) (hα' : α ≤ 1)
    (u : ℝ≥0) (V : ℝ≥0 → Ω → ℝ) (n : ℕ) (z : ℝ≥0 × Ω) :
    0 ≤ taperedWeight α u V n z ∧
      taperedWeight α u V n z ≤ hestonConvolutionWeight α u V z.1 z.2 := by
  let x : ℝ := (u : ℝ) - z.1
  by_cases hx : 0 < x
  · let r : ℝ := (n : ℝ) + 1
    let k := max r⁻¹ x
    let q := min (Real.sqrt (V z.1 z.2)) r
    have hq : 0 ≤ q := le_min (Real.sqrt_nonneg _) (by dsimp [r]; positivity)
    have hk : 0 < k := hx.trans_le (le_max_right _ _)
    have hΓ := (Real.Gamma_pos_of_pos hα).le
    have hkp : 0 ≤ hestonKernel α k := by
      rw [hestonKernel, ite_eq_left hk]
      exact div_nonneg (Real.rpow_nonneg hk.le _) hΓ
    have hle : hestonKernel α k ≤ hestonKernel α x := by
      simp only [hestonKernel, ite_eq_left hk, ite_eq_left hx]
      exact div_le_div_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hx (le_max_right _ _) (sub_nonpos.mpr hα')) hΓ
    have hterm : 0 ≤ hestonKernel α k * q := mul_nonneg hkp hq
    change 0 ≤ taper n x * (hestonKernel α k * q) ∧
      taper n x * (hestonKernel α k * q) ≤ hestonKernel α x * Real.sqrt (V z.1 z.2)
    refine ⟨mul_nonneg (taper_nonneg _ _) hterm, ?_⟩
    calc
      _ ≤ 1 * (hestonKernel α k * q) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) hterm
      _ ≤ _ := by
        rw [one_mul]
        exact mul_le_mul hle (min_le_left _ _) hq (hkp.trans hle)
  · change 0 ≤ taper n x * _ ∧ taper n x * _ ≤ hestonKernel α x * _
    simp [taper, max_eq_right (not_lt.mp hx), hestonKernel, hx]

private theorem taperedWeight_eventually_eq (α : ℝ) (u : ℝ≥0)
    (V : ℝ≥0 → Ω → ℝ) (z : ℝ≥0 × Ω) :
    ∀ᶠ n : ℕ in atTop, taperedWeight α u V n z = hestonConvolutionWeight α u V z.1 z.2 := by
  let x : ℝ := (u : ℝ) - z.1
  by_cases hx : 0 < x
  · have hr : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_mono (fun _ => le_add_of_nonneg_right zero_le_one) tendsto_natCast_atTop_atTop
    have hi : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hr
    filter_upwards [hi.eventually_lt_const hx,
      hr.eventually (eventually_ge_atTop (Real.sqrt (V z.1 z.2)))] with n hn hVn
    have hp : 0 < (n : ℝ) + 1 := by positivity
    have hOne : 1 ≤ ((n : ℝ) + 1) * x := by
      rw [mul_comm]
      exact (div_le_iff₀ hp).mp (by simpa only [one_div] using hn.le : 1 / ((n : ℝ) + 1) ≤ x)
    change taper n x * (hestonKernel α (max ((n : ℝ) + 1)⁻¹ x) *
      min (Real.sqrt (V z.1 z.2)) ((n : ℝ) + 1)) = hestonKernel α x * Real.sqrt (V z.1 z.2)
    simp only [taper, max_eq_left hx.le, min_eq_left hOne, max_eq_right hn.le,
      min_eq_left hVn, one_mul]
  · filter_upwards with n
    change taper n x * _ = hestonKernel α x * _
    simp [taper, max_eq_right (not_lt.mp hx), hestonKernel, hx]

private theorem tendsto_toLp_two_of_dominated_sq {S ι : Type*}
    {mS : MeasurableSpace S} {ν : Measure S} {l : Filter ι} [l.IsCountablyGenerated]
    {g : ι → S → ℝ} {f : S → ℝ} (hg : ∀ i, MemLp (g i) 2 ν) (hf : MemLp f 2 ν)
    {d : S → ℝ} (hd : Integrable d ν)
    (hb : ∀ i, ∀ᵐ z ∂ν, (g i z - f z) ^ 2 ≤ d z)
    (hlim : ∀ᵐ z ∂ν, Tendsto (fun i => g i z) l (𝓝 (f z))) :
    Tendsto (fun i => (hg i).toLp (g i)) l (𝓝 (hf.toLp f)) := by
  have hm (i : ι) : AEStronglyMeasurable (fun z => (g i z - f z) ^ 2) ν :=
    ((hg i).aestronglyMeasurable.sub hf.aestronglyMeasurable).pow 2
  have hdom (i : ι) : ∀ᵐ z ∂ν, ‖(g i z - f z) ^ 2‖ ≤ d z :=
    (hb i).mono fun _ hz => by simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hz
  have hlim' : ∀ᵐ z ∂ν, Tendsto (fun i => (g i z - f z) ^ 2) l (𝓝 ((0 : S → ℝ) z)) :=
    hlim.mono fun z hz => by
      simpa only [Pi.zero_apply, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
        (hz.sub (tendsto_const_nhds (x := f z))).pow 2
  have hsq : Tendsto (fun i => ∫ z, (g i z - f z) ^ 2 ∂ν) l (𝓝 0) := by
    simpa only [Pi.zero_apply, integral_zero] using tendsto_integral_filter_of_dominated_convergence
      d (Eventually.of_forall hm) (Eventually.of_forall hdom) hd hlim'
  have he (i : ι) : Real.sqrt (∫ z, (g i z - f z) ^ 2 ∂ν) =
      dist ((hg i).toLp (g i)) (hf.toLp f) := by
    rw [← dist_toLp_two_sq (hg i) hf, Real.sqrt_sq dist_nonneg]
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [Function.comp_def, he, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hsq

/-- A section of the Heston weight as an element of the predictable L²
space with the common horizon T. -/
noncomputable def hestonKernelFamilyLp [IsFiniteMeasure μ] {α : ℝ} {T : ℝ≥0}
    (hα : 1 / 2 < α) (hVp : IsStronglyPredictable 𝒢 V)
    (hVnonneg : ∀ s ω, 0 ≤ V s ω) (hVint : ∀ s, Integrable (V s) μ)
    {C : ℝ} (hmean : ∀ s, (∫ ω, V s ω ∂μ) ≤ C) (u : Icc (0 : ℝ≥0) T) :
    Lp ℝ 2 (jointPredictableMeasure 𝒢 μ T) :=
  (heston_convolution_weight_memLp_two_joint_horizon hα u.property.2 hVp hVnonneg hVint hmean).toLp
    (Function.uncurry (hestonConvolutionWeight α u V))

theorem hestonKernelFamilyLp_ae [IsFiniteMeasure μ] {α : ℝ} {T : ℝ≥0}
    (hα : 1 / 2 < α) (hVp : IsStronglyPredictable 𝒢 V)
    (hVnonneg : ∀ s ω, 0 ≤ V s ω) (hVint : ∀ s, Integrable (V s) μ)
    {C : ℝ} (hmean : ∀ s, (∫ ω, V s ω ∂μ) ≤ C) (u : Icc (0 : ℝ≥0) T) :
    ⇑(hestonKernelFamilyLp hα hVp hVnonneg hVint hmean u)
      =ᵐ[jointPredictableMeasure 𝒢 μ T] Function.uncurry (hestonConvolutionWeight α u V) :=
  MemLp.coeFn_toLp (heston_convolution_weight_memLp_two_joint_horizon hα u.property.2
    hVp hVnonneg hVint hmean)

/-- Strong measurability of the kernel sections on the fixed horizon. -/
theorem hestonKernelFamilyLp_stronglyMeasurable [IsFiniteMeasure μ] {α : ℝ} {T : ℝ≥0}
    (hα : 1 / 2 < α) (hα' : α ≤ 1) (hVp : IsStronglyPredictable 𝒢 V)
    (hVnonneg : ∀ s ω, 0 ≤ V s ω) (hVint : ∀ s, Integrable (V s) μ)
    {C : ℝ} (hmean : ∀ s, (∫ ω, V s ω ∂μ) ≤ C) :
    StronglyMeasurable (hestonKernelFamilyLp (T := T) hα hVp hVnonneg hVint hmean) := by
  have hα₀ : 0 < α := by linarith
  let ν := jointPredictableMeasure 𝒢 μ T
  let b (n : ℕ) := hestonKernel α ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1)
  let g (n : ℕ) (u : Icc (0 : ℝ≥0) T) := taperedWeight α (u : ℝ≥0) V n
  have hg (n : ℕ) (u : Icc (0 : ℝ≥0) T) : MemLp (g n u) 2 ν :=
    MemLp.of_bound (taperedWeight_predictable α u hVp n).aestronglyMeasurable _
      (Eventually.of_forall (taperedWeight_bound α hα₀ hα' u V n))
  let G (n : ℕ) (u : Icc (0 : ℝ≥0) T) := (hg n u).toLp (g n u)
  have hG (n : ℕ) : Continuous (G n) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    change Tendsto (G n) (𝓝 u) (𝓝 (G n u))
    apply tendsto_toLp_two_of_dominated_sq (hg n) (hg n u)
      (integrable_const ((b n + b n) ^ 2))
    · intro v
      filter_upwards with z
      rw [← sq_abs (g n v z - g n u z)]
      apply pow_le_pow_left₀ (abs_nonneg _) _ 2
      rw [← Real.norm_eq_abs]
      exact (norm_sub_le _ _).trans
        (add_le_add (taperedWeight_bound α hα₀ hα' v V n z)
          (taperedWeight_bound α hα₀ hα' u V n z))
    · exact Eventually.of_forall fun z =>
        ((continuous_taperedWeight_parameter α V n z).comp continuous_subtype_val).tendsto u
  apply stronglyMeasurable_of_tendsto atTop (fun n => (hG n).stronglyMeasurable)
  apply tendsto_pi_nhds.mpr
  intro u
  let f := Function.uncurry (hestonConvolutionWeight α u V)
  have hf : MemLp f 2 ν :=
    heston_convolution_weight_memLp_two_joint_horizon hα u.property.2 hVp hVnonneg hVint hmean
  change Tendsto (fun n => G n u) atTop (𝓝 (hf.toLp f))
  apply tendsto_toLp_two_of_dominated_sq (fun n => hg n u) hf hf.integrable_sq
  · intro n
    filter_upwards with z
    obtain ⟨h₀, h₁⟩ := taperedWeight_le α hα₀ hα' u V n z
    change 0 ≤ g n u z at h₀
    change g n u z ≤ f z at h₁
    rw [← sq_abs (g n u z - f z), abs_of_nonpos (sub_nonpos.mpr h₁), neg_sub]
    exact pow_le_pow_left₀ (sub_nonneg.mpr h₁) (sub_le_self _ h₀) 2
  · refine Eventually.of_forall fun z => ?_
    have he : (fun n => g n u z) =ᶠ[atTop] fun _ : ℕ => f z :=
      taperedWeight_eventually_eq α u V z
    exact tendsto_const_nhds.congr' he.symm

end RoughHeston

#print axioms RoughHeston.hestonKernelFamilyLp_ae
#print axioms RoughHeston.hestonKernelFamilyLp_stronglyMeasurable
