import DensityChargeGlobal
import DensityChargeSensitivity
import CaputoMeanEquation

open MeasureTheory Set Filter
open scoped Topology Interval NNReal

namespace RoughHeston

private noncomputable def weightedFractionalKernel (α : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  Real.exp (-(n : ℝ)*s)*fractionalK α s

private theorem weightedFractionalKernel_measurable (α : ℝ) (n : ℕ) :
    Measurable (weightedFractionalKernel α n) :=
  (Real.continuous_exp.comp (show Continuous (fun s : ℝ => -(n : ℝ)*s) from
    continuous_const.mul continuous_id)).measurable.mul (fractionalK_measurable α)

private theorem weightedFractionalKernel_nonneg {α : ℝ} (hα : 0 < α) (n : ℕ) (s : ℝ) :
    0 ≤ weightedFractionalKernel α n s := by
  refine mul_nonneg (Real.exp_pos _).le ?_
  by_cases hs : s ≤ 0
  · simp [fractionalK, hs]
  · rw [fractionalK, ite_eq_right hs]
    exact div_nonneg (Real.rpow_nonneg (lt_of_not_ge hs).le _) (Real.Gamma_pos_of_pos hα).le

private theorem weightedFractionalKernel_integrable {α T : ℝ} (hα : 0 < α) (n : ℕ) :
    IntegrableOn (weightedFractionalKernel α n) (Ioc 0 T) := by
  refine (fractionalK_integrableOn_Ioc hα T).mono'
    (weightedFractionalKernel_measurable α n).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hk : 0 ≤ fractionalK α s := by
    simp [fractionalK, not_le.mpr hs.1, Real.rpow_nonneg hs.1.le,
      (Real.Gamma_pos_of_pos hα).le, div_nonneg]
  rw [Real.norm_of_nonneg (weightedFractionalKernel_nonneg hα n s)]
  exact mul_le_of_le_one_left hk
    (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) hs.1.le))

private theorem tendsto_weightedFractionalKernel_mass {α T : ℝ} (hα : 0 < α) :
    Tendsto (fun n : ℕ => ∫ r in Ioc (0 : ℝ) T, weightedFractionalKernel α n r) atTop (𝓝 0) := by
  suffices h : Tendsto (fun n : ℕ => ∫ r in Ioc (0 : ℝ) T, weightedFractionalKernel α n r)
      atTop (𝓝 (∫ _r : ℝ in Ioc (0 : ℝ) T, (0 : ℝ))) by simpa only [integral_zero] using h
  apply tendsto_integral_of_dominated_convergence (fractionalK α)
    (fun n => (weightedFractionalKernel_measurable α n).aestronglyMeasurable)
    (fractionalK_integrableOn_Ioc hα T)
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hK : 0 ≤ fractionalK α r := by
      rw [fractionalK, ite_eq_right (not_le.mpr hr.1)]
      exact div_nonneg (Real.rpow_nonneg hr.1.le _) (Real.Gamma_pos_of_pos hα).le
    rw [Real.norm_of_nonneg (weightedFractionalKernel_nonneg hα n r)]
    exact mul_le_of_le_one_left hK
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) hr.1.le))
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hx : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hy : Tendsto (fun n : ℕ => -(n : ℝ)*r) atTop atBot := by
      have he := hx.const_mul_atTop_of_neg (show -r < 0 by linarith [hr.1])
      convert he using 1
      funext n
      ring
    have hlim := (Real.tendsto_exp_atBot.comp hy).mul_const (fractionalK α r)
    simpa only [weightedFractionalKernel, Function.comp_def, zero_mul] using hlim

/-- Continuous affine linear fractional Volterra equations have a
solution on every finite horizon. The contraction uses a decaying
exponential weight on continuous paths. -/
theorem exists_linear_fractional_volterra
    {α T initial force : ℝ} {rate : ℝ → ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (hrate : Continuous rate) :
    ∃ k : ℝ → ℝ, Continuous k ∧
      ∀ t ∈ Icc 0 T, k t = initial + volterraConvolution (fractionalK α)
        (fun s => force-rate s*k s) t := by
  obtain ⟨L₀,hL₀⟩ := isCompact_Icc.bddAbove_image (K := Icc (0:ℝ) T) hrate.norm.continuousOn
  let L := max L₀ 0
  have hL : 0 ≤ L := le_max_right _ _
  have hRate (s : ℝ) (hs : s ∈ Icc 0 T) : ‖rate s‖ ≤ L :=
    (hL₀ ⟨s,hs,rfl⟩).trans (le_max_left _ _)
  have hh := (tendsto_weightedFractionalKernel_mass (T := T) hα).const_mul L
  rw [mul_zero] at hh
  have hgood := hh.eventually (Iio_mem_nhds (show (0:ℝ)<1/2 by norm_num))
  obtain ⟨n, hn⟩ := hgood.exists
  have hsmall : L*(∫ r in Ioc (0:ℝ) T, weightedFractionalKernel α n r) ≤ 1/2 :=
    (show L*(∫ r in Ioc (0:ℝ) T, weightedFractionalKernel α n r) < 1/2 from hn).le
  let K := weightedFractionalKernel α n
  have hKm : Measurable K := weightedFractionalKernel_measurable α n
  have hKi : IntegrableOn K (Ioc 0 T) := weightedFractionalKernel_integrable hα n
  let X := C(Icc (0 : ℝ) T, ℝ)
  let U (φ : X) := riccatiTimeExtension hT φ
  have hU (φ : X) : Continuous (U φ) := continuous_riccatiTimeExtension hT φ
  let g (φ : X) (s : ℝ) := force*Real.exp (-(n : ℝ)*s)-rate s*U φ s
  have hExpNeg : Continuous (fun s : ℝ => Real.exp (-(n : ℝ)*s)) :=
    Real.continuous_exp.comp (show Continuous (fun s : ℝ => -(n : ℝ)*s) from continuous_const.mul continuous_id)
  have hg (φ : X) : Continuous (g φ) := (continuous_const.mul hExpNeg).sub (hrate.mul (hU φ))
  let A (t : ℝ) := initial*Real.exp (-(n : ℝ)*t)
  have hA : Continuous A := continuous_const.mul hExpNeg
  have hContinuous (φ : X) : ContinuousOn (volterraConvolution K (g φ)) (Icc 0 T) := by
    have he : volterraSmulConvolution K (g φ) = volterraConvolution K (g φ) := by
      funext t
      simp only [volterraSmulConvolution, volterraConvolution, smul_eq_mul]
    rw [← he]
    exact continuousOn_volterra_forcing hT hKm hKi (hg φ).continuousOn
  let P (φ : X) : X := ⟨fun t => A t+volterraConvolution K (g φ) t,
    (hA.continuousOn.add (hContinuous φ)).domRestrict⟩
  have hLip (φ ψ : X) : ‖P φ-P ψ‖ ≤ (1/2)*‖φ-ψ‖ := by
    refine (ContinuousMap.norm_le _ (by positivity)).mpr ?_
    intro t
    let j (s : ℝ) := K (t-s)
    have ht : (t : ℝ) ∈ Icc 0 T := t.property
    have hIt : IntegrableOn K (Ioc 0 (t : ℝ)) := hKi.mono_set (Ioc_subset_Ioc_right ht.2)
    have hj : IntegrableOn j (Ioc 0 (t : ℝ)) := by
      have hi := ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr hIt).symm.comp_sub_left (t : ℝ)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mp
        (by simpa only [sub_zero, sub_self] using hi)
    have hj₀ (s : ℝ) : 0 ≤ j s := weightedFractionalKernel_nonneg hα n _
    have hjMass : ∫ s in Ioc (0 : ℝ) (t : ℝ), j s =
        ∫ s in Ioc (0 : ℝ) (t : ℝ), K s := by
      have he := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := (t : ℝ)) K (t : ℝ)
      simpa only [j, sub_self, sub_zero, intervalIntegral.integral_of_le ht.1] using he
    have hgi (χ : X) : IntegrableOn (fun s => j s*g χ s) (Ioc 0 (t : ℝ)) := by
      obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image (K := Icc (0:ℝ) T) (hg χ).norm.continuousOn
      refine (hj.norm.mul_const B).mono'
        (((hKm.comp (measurable_const.sub measurable_id)).mul (hg χ).measurable).aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hB ⟨s,⟨hs.1.le,hs.2.trans ht.2⟩,rfl⟩) (norm_nonneg _)
    have hpoint (s : ℝ) (hs : s ∈ Ioc 0 (t : ℝ)) : ‖g φ s-g ψ s‖ ≤ L*‖φ-ψ‖ := by
      change ‖(force*Real.exp (-(n:ℝ)*s)-rate s*U φ s) -
        (force*Real.exp (-(n:ℝ)*s)-rate s*U ψ s)‖ ≤ _
      rw [show (force*Real.exp (-(n:ℝ)*s)-rate s*U φ s) -
        (force*Real.exp (-(n:ℝ)*s)-rate s*U ψ s) =
          -(rate s*(U φ s-U ψ s)) by ring, norm_neg, norm_mul]
      exact mul_le_mul (hRate s ⟨hs.1.le,hs.2.trans ht.2⟩)
        (ContinuousMap.norm_coe_le_norm (φ-ψ) _) (norm_nonneg _) hL
    change ‖(A t+volterraConvolution K (g φ) t)-(A t+volterraConvolution K (g ψ) t)‖ ≤ _
    rw [add_sub_add_left_eq_sub]
    unfold volterraConvolution
    change ‖(∫ s in Ioc (0 : ℝ) (t : ℝ), j s*g φ s) -
      (∫ s in Ioc (0 : ℝ) (t : ℝ), j s*g ψ s)‖ ≤ _
    rw [← integral_sub (hgi φ) (hgi ψ)]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hbound := setIntegral_mono_on ((hgi φ).sub (hgi ψ)).norm
      (hj.mul_const (L*‖φ-ψ‖)) measurableSet_Ioc (fun s hs => by
        change ‖j s*g φ s-j s*g ψ s‖ ≤ j s*(L*‖φ-ψ‖)
        rw [← mul_sub, norm_mul, Real.norm_of_nonneg (hj₀ s)]
        exact mul_le_mul_of_nonneg_left (hpoint s hs) (hj₀ s))
    rw [integral_mul_const, hjMass] at hbound
    refine hbound.trans ?_
    calc
      _ ≤ (∫ s in Ioc (0 : ℝ) T, K s)*(L*‖φ-ψ‖) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hL (norm_nonneg _))
        exact setIntegral_mono_set hKi (ae_of_all _ (weightedFractionalKernel_nonneg hα n))
          (Ioc_subset_Ioc_right ht.2).eventuallyLE
      _ = (L*(∫ s in Ioc (0 : ℝ) T, K s))*‖φ-ψ‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
  have hP : ContractingWith (1/2 : ℝ≥0) P := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun φ ψ => ?_⟩
    have h := hLip φ ψ
    rw [← dist_eq_norm (P φ) (P ψ), ← dist_eq_norm φ ψ] at h
    simpa only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using h
  let φ := ContractingWith.fixedPoint P hP
  let k (s : ℝ) := Real.exp ((n : ℝ)*s)*U φ s
  have hFix : P φ = φ := hP.fixedPoint_isFixedPt
  have hExpPos : Continuous (fun s : ℝ => Real.exp ((n : ℝ)*s)) :=
    Real.continuous_exp.comp (show Continuous (fun s : ℝ => (n : ℝ)*s) from continuous_const.mul continuous_id)
  refine ⟨k, hExpPos.mul (hU φ), ?_⟩
  intro t ht
  have hE := congrArg (fun ψ : X => ψ ⟨t,ht⟩) hFix.symm
  change φ ⟨t,ht⟩ = A t+volterraConvolution K (g φ) t at hE
  have hUt : U φ t = φ ⟨t,ht⟩ := riccatiTimeExtension_apply_of_mem hT φ ⟨t,ht⟩
  have hExp (s : ℝ) : Real.exp ((n:ℝ)*s) * Real.exp (-(n:ℝ)*s) = 1 := by
    rw [← Real.exp_add, show (n:ℝ)*s+ -(n:ℝ)*s = 0 by ring, Real.exp_zero]
  calc
    k t = Real.exp ((n : ℝ)*t)*(A t+volterraConvolution K (g φ) t) := by
      dsimp [k]
      rw [hUt, hE]
    _ = initial + Real.exp ((n : ℝ)*t)*volterraConvolution K (g φ) t := by
      have hAt : Real.exp ((n : ℝ)*t)*A t = initial := by
        unfold A
        rw [mul_left_comm, hExp, mul_one]
      rw [mul_add, hAt]
    _ = _ := by
      congr 1
      unfold volterraConvolution
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      change Real.exp ((n:ℝ)*t)*(Real.exp (-(n:ℝ)*(t-s))*fractionalK α (t-s)*
        (force*Real.exp (-(n:ℝ)*s)-rate s*U φ s)) =
          fractionalK α (t-s)*(force-rate s*(Real.exp ((n:ℝ)*s)*U φ s))
      rw [show (-(n:ℝ)*(t-s)) = -(n:ℝ)*t+(n:ℝ)*s by ring, Real.exp_add]
      have hExpT := hExp t
      have hExpS := hExp s
      calc
        _ = (Real.exp ((n:ℝ)*t)*Real.exp (-(n:ℝ)*t))*fractionalK α (t-s)*
            (force*(Real.exp ((n:ℝ)*s)*Real.exp (-(n:ℝ)*s))-rate s*(Real.exp ((n:ℝ)*s)*U φ s)) := by ring
        _ = _ := by rw [hExpT, hExpS, one_mul, mul_one]

#print axioms exists_linear_fractional_volterra

end RoughHeston
