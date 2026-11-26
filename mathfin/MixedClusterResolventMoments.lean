import OrthogonalJointResolventRows
import JointHorizonExtension

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝒢 : Filtration ℝ≥0 m}

private theorem centered_noise_mixed_product {Z W : Ω → ℝ}
    (hZ : MemLp Z 2 μ) (hW : MemLp W 2 μ) {c d σ : ℝ}
    (hZ₀ : (∫ ω,Z ω ∂μ)=0) (hW₀ : (∫ ω,W ω ∂μ)=0)
    (hZW₀ : (∫ ω,Z ω*W ω ∂μ)=0) :
    (∫ ω,(c+σ*Z ω)*(d+σ*W ω) ∂μ)=c*d := by
  have hZi := hZ.integrable (by norm_num)
  have hWi := hW.integrable (by norm_num)
  have hZWi : Integrable (fun ω => Z ω*W ω) μ := hZ.integrable_mul hW
  have hi₁ : Integrable (fun _ : Ω => c*d) μ := integrable_const _
  have hi₂ := hWi.const_mul (c*σ)
  have hi₃ := hZi.const_mul (d*σ)
  have hi₄ := hZWi.const_mul (σ^2)
  have he : (fun ω => (c+σ*Z ω)*(d+σ*W ω)) =
      fun ω => c*d + (c*σ)*W ω + (d*σ)*Z ω + σ^2*(Z ω*W ω) := by
    funext ω
    ring
  have hs₄ := integral_add ((hi₁.add hi₂).add hi₃) hi₄
  have hs₃ := integral_add (hi₁.add hi₂) hi₃
  simp only [Pi.add_apply] at hs₄ hs₃
  rw [he,hs₄,hs₃,
    integral_add hi₁ hi₂,integral_const_mul (c*σ) W,integral_const_mul (d*σ) Z,
    integral_const_mul (σ^2) (fun ω => Z ω*W ω),hZW₀,hZ₀,hW₀]
  simp

/-- Mixed physical observation times are allowed. Each resolvent integrand
is integrated against its own dedicated driver, with the zero extension used
to compare the two integrals on one horizon. -/
theorem mixed_cluster_resolvent_moments {T s t : ℝ≥0} {X Y : ℝ≥0 → Ω → ℝ}
    (hs : s≤T) (ht : t≤T)
    (hX : Martingale X 𝒢 μ) (hY : Martingale Y 𝒢 μ)
    (hXY : Martingale (fun r => X r*Y r) 𝒢 μ)
    (hX₂ : ∀ r,MemLp (X r) 2 μ) (hY₂ : ∀ r,MemLp (Y r) 2 μ)
    (hXC : Martingale (fun r ω => X r ω^2-((min r T:ℝ≥0):ℝ)) 𝒢 μ)
    (hYC : Martingale (fun r ω => Y r ω^2-((min r T:ℝ≥0):ℝ)) 𝒢 μ)
    (f : Lp ℝ 2 (jointPredictableMeasure 𝒢 μ s))
    (g : Lp ℝ 2 (jointPredictableMeasure 𝒢 μ t))
    {A B : Ω → ℝ} {c d σ : ℝ}
    (hA : A =ᵐ[μ] fun ω => c+σ*jointItoIntegralCLM (M := fun r => X (min r s)) s
      (fun r => hX₂ (min r s)) f ω)
    (hB : B =ᵐ[μ] fun ω => d+σ*jointItoIntegralCLM (M := fun r => Y (min r t)) t
      (fun r => hY₂ (min r t)) g ω) :
    MemLp A 2 μ ∧ MemLp B 2 μ ∧ (∫ ω,A ω ∂μ)=c ∧ (∫ ω,B ω ∂μ)=d ∧
      (∫ ω,A ω*B ω ∂μ)=c*d := by
  rw [jointItoIntegralCLM_cross_horizon 𝒢 μ hs hX₂ hX hXC] at hA
  rw [jointItoIntegralCLM_cross_horizon 𝒢 μ ht hY₂ hY hYC] at hB
  let Z := jointItoIntegralCLM T hX₂ (jointBandExtend 𝒢 μ hs f)
  let W := jointItoIntegralCLM T hY₂ (jointBandExtend 𝒢 μ ht g)
  have hZ : MemLp Z 2 μ := Lp.memLp Z
  have hW : MemLp W 2 μ := Lp.memLp W
  have hZ₀ : (∫ ω,Z ω ∂μ)=0 := integral_jointItoIntegralCLM_eq_zero T hX₂ hX hXC _
  have hW₀ : (∫ ω,W ω ∂μ)=0 := integral_jointItoIntegralCLM_eq_zero T hY₂ hY hYC _
  have hZW₀ : (∫ ω,Z ω*W ω ∂μ)=0 :=
    orthogonal_jointItoIntegralCLM_cross T hX hY hXY hX₂ hY₂ hXC hYC _ _
  have hmean {U : Ω → ℝ} {I : Lp ℝ 2 μ} {a : ℝ}
      (hU : U =ᵐ[μ] fun ω => a+σ*I ω) (hI : (∫ ω,I ω ∂μ)=0) :
      MemLp U 2 μ ∧ (∫ ω,U ω ∂μ)=a := by
    have hn : MemLp (fun ω => σ*I ω) 2 μ := (Lp.memLp I).const_mul σ
    refine ⟨((memLp_const a).add hn).ae_eq hU.symm,?_⟩
    rw [integral_congr_ae hU,integral_add (integrable_const a) (hn.integrable (by norm_num)),
      integral_const_mul,hI]
    simp
  obtain ⟨hA₂,hA₀⟩ := hmean (I := Z) hA hZ₀
  obtain ⟨hB₂,hB₀⟩ := hmean (I := W) hB hW₀
  refine ⟨hA₂,hB₂,hA₀,hB₀,(integral_congr_ae (hA.mul hB)).trans ?_⟩
  exact centered_noise_mixed_product hZ hW hZ₀ hW₀ hZW₀

#print axioms mixed_cluster_resolvent_moments

end RoughHeston
