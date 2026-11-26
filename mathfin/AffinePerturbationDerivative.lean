import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

open MeasureTheory Set Filter
open scoped Topology

namespace RoughHeston

private theorem affine_exp_difference_norm_le {K x : ℝ} (hK : 0 ≤ K) (hx : x ≤ K) :
    ‖Real.exp x-1‖ ≤ Real.exp K*‖x‖ := by
  have hDer (x : ℝ) (hx : x∈Iic K) :
      HasDerivWithinAt Real.exp (Real.exp x) (Iic K) x :=
    (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hB (x : ℝ) (hx : x∈Iic K) : ‖Real.exp x‖ ≤ Real.exp K := by
    rw [Real.norm_of_nonneg (Real.exp_pos x).le]
    exact Real.exp_le_exp.mpr hx
  simpa only [Real.exp_zero,sub_zero] using
    (convex_Iic K).norm_image_sub_le_of_norm_hasDerivWithin_le hDer hB hK hx

/-- Differentiating the expectation of the one-sided perturbed
exponential recovers the weighted first moment. A lower bound on X
and nonnegative A give a deterministic bound on the exponent. -/
theorem integral_mul_eq_zero_of_affine_exp_perturbation
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {D X A : Ω → ℝ} {K B : ℝ}
    (hK : 0 ≤ K) (hD : AEStronglyMeasurable D μ) (hDb : ∀ᵐ ω ∂μ, ‖D ω‖ ≤ B)
    (hXi : Integrable X μ) (hAi : Integrable A μ)
    (hX : ∀ᵐ ω ∂μ, -K ≤ X ω) (hA : ∀ᵐ ω ∂μ, 0 ≤ A ω)
    (hEq : ∀ ε ∈ Icc (0:ℝ) 1,
      (∫ ω, D ω*Real.exp (-ε*X ω-ε^2*A ω/2) ∂μ) = ∫ ω,D ω ∂μ) :
    (∫ ω, D ω*X ω ∂μ) = 0 := by
  let R (ε : ℝ) (ω : Ω) := -ε*X ω-ε^2*A ω/2
  let J (ε : ℝ) (ω : Ω) := D ω*Real.exp (R ε ω)
  let S (ε : ℝ) (ω : Ω) := (J ε ω-D ω)/ε
  have hR (ε : ℝ) (hε : ε∈Icc (0:ℝ) 1) (ω : Ω) (hx : -K≤X ω) (ha : 0≤A ω) :
      R ε ω ≤ K := by
    have hl := mul_le_mul_of_nonneg_left (neg_le_neg hx) hε.1
    have hu := mul_le_mul_of_nonneg_right hε.2 hK
    have hn : 0 ≤ ε^2*A ω/2 := by positivity
    dsimp [R]
    linarith only [show ε*(-X ω) ≤ ε*K by simpa only [neg_neg] using hl,hu,hn]
  have hJm (ε : ℝ) : AEStronglyMeasurable (J ε) μ := by
    have h := hD.mul (Real.continuous_exp.comp_aestronglyMeasurable
      ((hXi.aestronglyMeasurable.const_mul (-ε)).sub
        ((hAi.aestronglyMeasurable.const_mul (ε^2)).mul_const (2:ℝ)⁻¹)))
    convert h using 1
    funext ω
    simp [J,R,Pi.sub_apply,Pi.mul_apply,div_eq_mul_inv]
  have hJi (ε : ℝ) (hε : ε∈Icc (0:ℝ) 1) : Integrable (J ε) μ := by
    refine (integrable_const (B*Real.exp K)).mono' (hJm ε) ?_
    filter_upwards [hX,hA,hDb] with ω hx ha hd
    exact (norm_mul _ _).trans_le (mul_le_mul hd
      (by rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact Real.exp_le_exp.mpr (hR ε hε ω hx ha))
      (norm_nonneg _) ((norm_nonneg _).trans hd))
  have hDi : Integrable D μ := (integrable_const B).mono' hD hDb
  have hUnit : ∀ᶠ ε in 𝓝[>] (0:ℝ), ε∈Ioc (0:ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)] with ε hε he
    exact ⟨hε,(show ε<1 from he).le⟩
  let Q (ω : Ω) := (B*Real.exp K)*(‖X ω‖+‖A ω‖/2)
  have hQi : Integrable Q μ :=
    (hXi.norm.add (hAi.norm.div_const 2)).const_mul _
  have hSm : ∀ᶠ ε in 𝓝[>] (0:ℝ), AEStronglyMeasurable (S ε) μ :=
    Eventually.of_forall fun ε => by
      simpa only [S,Pi.sub_apply,div_eq_mul_inv] using ((hJm ε).sub hD).mul_const ε⁻¹
  have hSB : ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ᵐ ω ∂μ, ‖S ε ω‖ ≤ Q ω := by
    filter_upwards [hUnit] with ε hε
    filter_upwards [hX,hA,hDb] with ω hx ha hd
    have hRn : ‖R ε ω‖ ≤ ε*(‖X ω‖+‖A ω‖/2) := by
      have hT := norm_sub_le (-ε*X ω) (ε^2*A ω/2)
      rw [norm_mul,norm_neg,Real.norm_of_nonneg hε.1.le,norm_div,norm_mul,
        Real.norm_of_nonneg (sq_nonneg ε),Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2)] at hT
      refine hT.trans ?_
      have he : ε^2 ≤ ε := by nlinarith [mul_le_mul_of_nonneg_left hε.2 hε.1.le]
      nlinarith [mul_le_mul_of_nonneg_right he (norm_nonneg (A ω))]
    have hh := affine_exp_difference_norm_le hK (hR ε (Ioc_subset_Icc_self hε) ω hx ha)
    have hnD : 0≤B := (norm_nonneg _).trans hd
    have hDn : ‖D ω*(Real.exp (R ε ω)-1)‖ ≤
        B*(Real.exp K*(ε*(‖X ω‖+‖A ω‖/2))) := by
      rw [norm_mul]
      exact mul_le_mul hd (hh.trans (mul_le_mul_of_nonneg_left hRn (Real.exp_pos _).le))
        (norm_nonneg _) hnD
    change ‖(D ω*Real.exp (R ε ω)-D ω)/ε‖ ≤ Q ω
    rw [← mul_sub_one, norm_div, Real.norm_of_nonneg hε.1.le]
    exact (div_le_iff₀ hε.1).mpr (hDn.trans_eq (by ring))
  have hSLim : ∀ᵐ ω ∂μ, Tendsto (fun ε => S ε ω) (𝓝[>] (0:ℝ))
      (𝓝 (-(D ω*X ω))) := ae_of_all _ fun ω => by
    have hR' : HasDerivAt (fun ε => R ε ω) (-X ω) 0 := by
      have h1 := (hasDerivAt_id (0:ℝ)).neg.mul_const (X ω)
      have h2 := (((hasDerivAt_id (0:ℝ)).pow 2).mul_const (A ω)).div_const 2
      convert h1.sub h2 using 1
      · funext ε
        simp [R,Pi.sub_apply]
      · simp
    have he : HasDerivAt (fun ε => J ε ω) (-(D ω*X ω)) 0 := by
      have h := ((Real.hasDerivAt_exp (R 0 ω)).comp 0 hR').const_mul (D ω)
      simpa [R,J,Function.comp_def,mul_neg] using h
    have hh := he.hasDerivWithinAt (s := Ici 0)
    rw [hasDerivWithinAt_iff_tendsto_slope, show Ici (0:ℝ) \ {0} = Ioi 0 by ext z; simp] at hh
    refine hh.congr (fun ε => ?_)
    rw [slope_def_field,sub_zero]
    simp [S,J,R]
  have hlim := tendsto_integral_filter_of_dominated_convergence Q hSm hSB hQi hSLim
  have hEq0 : (fun ε => ∫ ω,S ε ω ∂μ) =ᶠ[𝓝[>] (0:ℝ)] fun _ => 0 := by
    filter_upwards [hUnit] with ε hε
    dsimp only [S]
    rw [integral_div,integral_sub (hJi ε (Ioc_subset_Icc_self hε)) hDi]
    exact (congrArg (fun x : ℝ => (x-(∫ ω,D ω ∂μ))/ε)
      (hEq ε (Ioc_subset_Icc_self hε))).trans (by simp)
  have he := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hEq0.symm)
  rw [integral_neg] at he
  linarith

#print axioms integral_mul_eq_zero_of_affine_exp_perturbation

end RoughHeston
