import CanonicalPulseCoordinates
import UniformBoundaryAcrossLaws

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
local notation "Ω" => CanonicalPath T (CoupledPhysicalState ι)
local notation "𝒢" => canonicalPathNaturalFiltration T (E := CoupledPhysicalState ι)

/-- Positive-time inverse equation for the regular version of a
canonical physical row, retaining the initial fractional input. -/
theorem canonicalRegularVariance_inverse_ae_of_centered
    {α κ : ℝ} (hα' : α<1)
    {v : Option ι→ℝ} (P : ProbabilityMeasure Ω)
    (hI : ∀ᵐ p ∂(P:Measure Ω),p∈canonicalPhysicalInitialSet T v)
    (hN : ∀ᵐ p ∂(P:Measure Ω),p∈canonicalPhysicalNonnegative (ι := ι) T)
    (i : Option ι) {β : ℝ≥0→ℝ} {B : ℝ} (hβ : Measurable β) (hβB : ∀ t,‖β t‖≤B)
    (hInv : ∀ᵐ p ∂(P:Measure Ω),∀ t≤T,
      volterraConvolution (fractionalL α) (fun r => canonicalPhysicalVariance T i r.toNNReal p-v i) (t:ℝ) =
        canonicalPhysicalResidual T i t p +
          ∫ r in (0:ℝ)..(t:ℝ),β r.toNNReal-κ*canonicalPhysicalVariance T i r.toNNReal p):
    ∀ᵐ p ∂(P:Measure Ω),∀ s∈Ioc (0:ℝ) (T:ℝ),
      canonicalPhysicalResidual T i s.toNNReal p =
        volterraConvolution (fractionalL α)
          (fun r => canonicalRegularVariance T i (v i) r.toNNReal p) s +
        ∫ r in Ioc (0:ℝ) s,κ*canonicalRegularVariance T i (v i) r.toNNReal p-
          (β r.toNNReal+(v i)*fractionalL α r) := by
  filter_upwards [hInv,
    canonicalRegularVariance_ae_paths hI hN i] with p hp hV s hs
  let V (r : ℝ) := canonicalRegularVariance T i (v i) r.toNNReal p
  have hVraw (r : ℝ) : canonicalPhysicalVariance T i r.toNNReal p=V r := (hV _).symm
  have hVc : Continuous V := by
    exact ((canonicalPhysicalVariance_time_continuous i p).comp continuous_real_toNNReal).congr hVraw
  have hst : s.toNNReal≤T := Real.toNNReal_le_iff_le_coe.mpr hs.2
  have hEq := hp s.toNNReal hst
  rw [Real.coe_toNNReal s hs.1.le] at hEq
  simp_rw [hVraw] at hEq
  rw [intervalIntegral.integral_of_le hs.1.le] at hEq
  have hLi := fractionalL_integrableOn_Ioc hα' s
  have hLref := fractionalL_reflected_integrableOn_Ioc hα' hs.1.le
  obtain ⟨hVi,hLVi⟩ := cluster_affine_payoff_integrability_of_continuous hα' hs.1.le hVc
  have hbI : IntegrableOn (fun r : ℝ => β r.toNNReal) (Ioc 0 s) := by
    refine (integrableOn_const (C := B) (by simp [Real.volume_Ioc] : volume (Ioc (0:ℝ) s)≠∞)).mono'
      (hβ.comp continuous_real_toNNReal.measurable).aestronglyMeasurable ?_
    exact ae_of_all _ fun r => hβB r.toNNReal
  have hLvol : (∫ r in Ioc (0:ℝ) s, fractionalL α (s-r)) = ∫ r in Ioc (0:ℝ) s,fractionalL α r := by
    rw [← intervalIntegral.integral_of_le hs.1.le,← intervalIntegral.integral_of_le hs.1.le,
      intervalIntegral.integral_comp_sub_left,sub_self,sub_zero]
  unfold volterraConvolution at hEq ⊢
  simp_rw [mul_sub] at hEq
  rw [integral_sub hLVi (hLref.mul_const (v i)),integral_mul_const,hLvol,
    integral_sub hbI (hVi.const_mul κ),integral_const_mul] at hEq
  change canonicalPhysicalResidual T i s.toNNReal p =
    (∫ r in Ioc (0:ℝ) s,fractionalL α (s-r)*V r) +
      ∫ r in Ioc (0:ℝ) s,κ*V r-(β r.toNNReal+(v i)*fractionalL α r)
  have hAdd := integral_add hbI (hLi.const_mul (v i))
  have hsub := integral_sub (hVi.const_mul κ) (hbI.add (hLi.const_mul (v i)))
  simp only [Pi.add_apply] at hsub
  rw [hsub,
    hAdd,integral_const_mul,integral_const_mul]
  linarith


theorem canonicalRegularVariance_inverse_ae
    (hT : 0<T) {α κ : ℝ} (hα : 0<α) (hα' : α<1)
    {v : Option ι→ℝ} (P : ProbabilityMeasure Ω)
    (hI : ∀ᵐ p ∂(P:Measure Ω),p∈canonicalPhysicalInitialSet T v)
    (hN : ∀ᵐ p ∂(P:Measure Ω),p∈canonicalPhysicalNonnegative (ι := ι) T)
    (i : Option ι) {β : ℝ≥0→ℝ} {B : ℝ} (hβ : Measurable β) (hβB : ∀ t,‖β t‖≤B)
    (hEq : ∀ t : CanonicalPathTime T,canonicalPhysicalIntegratedError T (v i) κ i hβ hβB
      (hestonKernel α) t=ᵐ[(P:Measure Ω)] 0) :
    ∀ᵐ p ∂(P:Measure Ω),∀ s∈Ioc (0:ℝ) (T:ℝ),
      canonicalPhysicalResidual T i s.toNNReal p =
        volterraConvolution (fractionalL α)
          (fun r => canonicalRegularVariance T i (v i) r.toNNReal p) s +
        ∫ r in Ioc (0:ℝ) s,κ*canonicalRegularVariance T i (v i) r.toNNReal p-
          (β r.toNNReal+(v i)*fractionalL α r) :=
  canonicalRegularVariance_inverse_ae_of_centered hα' P hI hN i hβ hβB
    (ae_canonicalPhysical_inverse_of_integrated hT hα hα' i hβ hβB P hEq)

/-- The constant-immigration companion of the fixed mesh is a genuine
input to the boundary proposition in the same canonical filtration. -/
theorem canonicalCompanion_boundaryProcess_of_inverse
    {α κ σ b : ℝ} (hα' : α<1)
    {v : Option ι→ℝ} (hv : 0≤v none) (P : ProbabilityMeasure Ω)
    (hI : ∀ᵐ p ∂(P:Measure Ω),p∈canonicalPhysicalInitialSet T v)
    (hN : ∀ᵐ p ∂(P:Measure Ω),p∈canonicalPhysicalNonnegative (ι := ι) T)
    (hInv : ∀ᵐ p ∂(P:Measure Ω),∀ t≤T,
      volterraConvolution (fractionalL α) (fun r => canonicalPhysicalVariance T none r.toNNReal p-v none) (t:ℝ) =
        canonicalPhysicalResidual T none t p +
          ∫ r in (0:ℝ)..(t:ℝ),b-κ*canonicalPhysicalVariance T none r.toNNReal p)
    (hM : Martingale (canonicalPhysicalResidual T none) 𝒢 (P:Measure Ω))
    (hM₂ : ∀ t,MemLp (canonicalPhysicalResidual T none t) 2 (P:Measure Ω))
    (hC : Martingale (canonicalPhysicalCompensatedProduct T σ none none) 𝒢 (P:Measure Ω))
    {B₂ : ℝ} (hB₂ : 0≤B₂)
    (hV₂ : ∀ t≤T,MemLp (canonicalPhysicalVariance T none t) 2 (P:Measure Ω))
    (hVB : ∀ t≤T,(∫ p,(canonicalPhysicalVariance T none t p)^2 ∂(P:Measure Ω))≤B₂) :
    HestonBoundaryProcess (P:Measure Ω) 𝒢 T α κ (σ^2/2) b (v none)
      (canonicalPhysicalResidual T none) (canonicalRegularVariance T none (v none))
      (canonicalPhysicalCompensator T σ none none) := by
  let μ := (P:Measure Ω)
  let V := canonicalRegularVariance T (none : Option ι) (v none)
  obtain ⟨hVc,hVn,hV0⟩ := canonicalRegularVariance_continuous_nonnegative_initial (T := T) (none : Option ι) hv
  have hVr (t : ℝ≥0) : V t =ᵐ[μ] canonicalPhysicalVariance T none t :=
    (canonicalRegularVariance_ae_paths hI hN none).mono fun p hp => hp t
  have hVi (t : ℝ≥0) (ht : t≤T) : Integrable (V t) μ :=
    ((hV₂ t ht).integrable one_le_two).congr (hVr t).symm
  have hVSi (t : ℝ≥0) (ht : t≤T) : Integrable (fun p => (V t p)^2) μ :=
    (hV₂ t ht).integrable_sq.congr ((hVr t).pow_const 2).symm
  have hVS (t : ℝ≥0) (ht : t≤T) : (∫ p,(V t p)^2 ∂μ)≤B₂ :=
    (integral_congr_ae ((hVr t).pow_const 2)).trans_le (hVB t ht)
  have hVF (t : ℝ≥0) (ht : t≤T) : (∫ p,V t p ∂μ)≤1+B₂ := by
    have h1 : Integrable (fun _ : Ω => (1:ℝ)) μ := integrable_const 1
    have hi := integral_mono (hVi t ht) (h1.add (hVSi t ht)) (fun p => by
      change V t p≤1+(V t p)^2
      nlinarith [sq_nonneg (V t p-1)])
    simp only [Pi.add_apply] at hi
    rw [integral_add h1 (hVSi t ht),integral_const,probReal_univ,one_smul] at hi
    exact hi.trans (add_le_add le_rfl (hVS t ht))
  refine ⟨hM,hM₂,canonicalPhysicalResidual_time_continuous none,canonicalPhysicalResidual_zero_ae hI none,
    canonicalRegularVariance_adapted none _,hVc,hVn,(fun p => (hV0 p).le),ae_of_all _ hV0,
    hVi,hVSi,⟨1+B₂,by positivity,hVF⟩,⟨B₂,hB₂,hVS⟩,hC,
    canonicalPhysical_diagonal_clock_integrable σ none hM₂ hC,?_,?_,?_⟩
  · exact fun s t hst => ae_of_all _ fun p => canonicalPhysical_diagonal_monotone σ none p hst
  · intro t ht
    filter_upwards [canonicalPhysical_diagonal_clock_regular_ae hI hN σ none] with p hp
    change canonicalPhysicalCompensator T σ none none t p =
      ∫ r in (0:ℝ)..(t:ℝ), (2*(σ^2/2))*canonicalRegularVariance T none (v none) r.toNNReal p
    rw [show 2*(σ^2/2)=σ^2 by ring]
    exact hp t ht
  · exact canonicalRegularVariance_inverse_ae_of_centered hα' P hI hN none measurable_const (fun _ => le_rfl) hInv

theorem canonicalCompanion_boundaryProcess
    (hT : 0<T) {α κ σ b : ℝ} (hα : 0<α) (hα' : α<1)
    {v : Option ι→ℝ} (hv : 0≤v none) (P : ProbabilityMeasure Ω)
    (hI : ∀ᵐ p ∂(P:Measure Ω),p∈canonicalPhysicalInitialSet T v)
    (hN : ∀ᵐ p ∂(P:Measure Ω),p∈canonicalPhysicalNonnegative (ι := ι) T)
    (hEq : ∀ t : CanonicalPathTime T,canonicalPhysicalIntegratedError T (v none) κ none
      (b := fun _ => b) (B := ‖b‖) measurable_const (fun _ => le_rfl) (hestonKernel α) t=ᵐ[(P:Measure Ω)] 0)
    (hM : Martingale (canonicalPhysicalResidual T none) 𝒢 (P:Measure Ω))
    (hM₂ : ∀ t,MemLp (canonicalPhysicalResidual T none t) 2 (P:Measure Ω))
    (hC : Martingale (canonicalPhysicalCompensatedProduct T σ none none) 𝒢 (P:Measure Ω))
    {B₂ : ℝ} (hB₂ : 0≤B₂)
    (hV₂ : ∀ t≤T,MemLp (canonicalPhysicalVariance T none t) 2 (P:Measure Ω))
    (hVB : ∀ t≤T,(∫ p,(canonicalPhysicalVariance T none t p)^2 ∂(P:Measure Ω))≤B₂) :
    HestonBoundaryProcess (P:Measure Ω) 𝒢 T α κ (σ^2/2) b (v none)
      (canonicalPhysicalResidual T none) (canonicalRegularVariance T none (v none))
      (canonicalPhysicalCompensator T σ none none) :=
  canonicalCompanion_boundaryProcess_of_inverse hα' hv P hI hN
    (ae_canonicalPhysical_inverse_of_integrated hT hα hα' none measurable_const (fun _ => le_rfl) P hEq)
    hM hM₂ hC hB₂ hV₂ hVB

#print axioms canonicalCompanion_boundaryProcess_of_inverse
#print axioms canonicalRegularVariance_inverse_ae
#print axioms canonicalCompanion_boundaryProcess

end RoughHeston
