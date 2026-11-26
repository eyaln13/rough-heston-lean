import CanonicalIntegratedPulseResolvent
import DeterministicPathIntegralL2
import DifferentiateOrthogonalPrimitives
import PathLpContinuityFromFourthMoments
import VolterraMomentBound
import EulerObservableMoments

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
local notation "Path" => CanonicalPath T (CoupledPhysicalState ι)

omit [Fintype ι] [DecidableEq ι] in
private theorem canonical_joint_physical_eval :
    Continuous (fun z : ℝ × Path => canonicalPathEval T z.1.toNNReal z.2) := by
  have ht : Continuous (fun r : ℝ => canonicalEvalTime T r.toNNReal) :=
    (continuous_real_toNNReal.min continuous_const).subtype_mk _
  exact continuous_eval.comp (continuous_snd.prodMk (ht.comp continuous_fst))

omit [Fintype ι] [DecidableEq ι] in
private theorem canonical_joint_residual (i : Option ι) :
    Continuous (fun z : ℝ × Path => canonicalPhysicalResidual T i z.1.toNNReal z.2) :=
  ((continuous_apply i).comp continuous_snd).comp canonical_joint_physical_eval

private theorem reflected_resolvent_memLp_two {α s : ℝ} (hα : 1/2<α) (hs : 0≤s)
    {R : ℝ→ℝ} (hR : Measurable R)
    {Rbound : ℝ} (hRb : ∀ r∈Ioc (0:ℝ) s,|R r|≤Rbound*fractionalK α r) :
    MemLp (fun r => R (s-r)) 2 (volume.restrict (Ioc 0 s)) := by
  have hα₀ : 0<α := by linarith
  have hKp (r : ℝ) : 0≤fractionalK α r := by
    unfold fractionalK
    split <;> first | exact le_rfl | exact div_nonneg (Real.rpow_nonneg (by linarith) _) (Real.Gamma_pos_of_pos hα₀).le
  have hiK : IntegrableOn (fun r => (fractionalK α r)^2) (Ioc (0:ℝ) s) := by
    refine (intervalIntegrable_fractionalK_add_sq hα hs).1.mono'
      ((fractionalK_measurable α).pow_const 2).aestronglyMeasurable ?_
    exact ae_of_all _ fun r => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact le_add_of_nonneg_left (hKp r)
  have hiR : IntegrableOn (fun r => (R r)^2) (Ioc (0:ℝ) s) := by
    refine (hiK.const_mul (Rbound^2)).mono' (hR.pow_const 2).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [Real.norm_of_nonneg (sq_nonneg _),← sq_abs (R r)]
    have hh := pow_le_pow_left₀ (abs_nonneg _) (hRb r hr) 2
    simpa only [mul_pow,mul_comm] using hh
  have hRi := ((intervalIntegrable_iff_integrableOn_Ioc_of_le hs).2 hiR).comp_sub_left s
  have hRi' : IntegrableOn (fun r => (R (s-r))^2) (Ioc (0:ℝ) s) := by
    simpa only [sub_zero,sub_self] using hRi.2
  exact (memLp_two_iff_integrable_sq
    (hR.comp (measurable_const.sub measurable_id)).aestronglyMeasurable).2 hRi'

namespace FractionalFixedMeshLaw

variable {α κ σ : ℝ} {v : Option ι→ℝ} {β : Option ι→ℝ≥0→ℝ}
  (L : FractionalFixedMeshLaw T α κ σ v β)

private theorem residual_uniform_second :
    ∃ C : ℝ,0≤C ∧ ∀ i t,(∫ p,(canonicalPhysicalResidual T i t p)^2 ∂(L.law:Measure Path))≤C := by
  obtain ⟨C,hC,hq⟩ := L.residualFourthMoments
  refine ⟨1+C.toReal,by positivity,?_⟩
  intro i t
  let X := canonicalPhysicalResidual T i t
  have hm := memLp_and_integral_norm_pow_of_lintegral (p := 4) (by decide)
    (continuous_canonicalPhysicalResidual T i t).measurable (b := C.toReal) ENNReal.toReal_nonneg (by
      simpa only [ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm,ENNReal.ofReal_toReal hC] using hq i t)
  have hM : MemLp X 4 (L.law:Measure Path) := by
    simpa only [Nat.cast_ofNat] using hm.1
  have he (p : Path) : ‖X p‖^4=(X p)^4 := by
    rw [Real.norm_eq_abs,← abs_pow,abs_of_nonneg (by positivity : 0≤(X p)^4)]
  have hfour : (∫ p,(X p)^4 ∂(L.law:Measure Path)) ≤ C.toReal := by
    have hb : (∫ p,‖X p‖^4 ∂(L.law:Measure Path)) ≤ C.toReal := hm.2
    simpa only [he] using hb
  exact (integral_sq_le_one_add_integral_pow_four hM).2.trans (add_le_add_right hfour _)

private theorem residual_centered (i : Option ι) (t : ℝ≥0) :
    (∫ p,canonicalPhysicalResidual T i t p ∂(L.law:Measure Path))=0 := by
  have he := (L.residualMartingale i).setIntegral_eq (show (0:ℝ≥0)≤t from zero_le) MeasurableSet.univ
  rw [Measure.restrict_univ,integral_congr_ae (canonicalPhysicalResidual_zero_ae L.starts i),integral_zero] at he
  exact he.symm

/-- The original-law expectation of the integrated pulse is exactly
the deterministic resolvent of its physical immigration primitive. -/
theorem integrated_pulse_mean {i : ι} (hi : v (some i)=0)
    (hα : 1/2<α) (hα' : α<1) {R : ℝ→ℝ} (hR : Measurable R)
    {Rbound : ℝ} (hRb : ∀ r∈Ioc (0:ℝ) (T:ℝ),|R r|≤Rbound*fractionalK α r)
    (hRes : ∀ r∈Ioc (0:ℝ) (T:ℝ),R r=fractionalK α r-κ*volterraConvolution (fractionalK α) R r)
    {B : ℝ} (hβ : Measurable (β (some i))) (hB : ∀ t,‖β (some i) t‖≤B)
    {s : ℝ} (hs : s∈Icc (0:ℝ) (T:ℝ)) :
    (∫ p,canonicalVariancePrimitive T (some i) s p ∂(L.law:Measure Path)) =
      volterraConvolution R (physicalImmigrationPrimitive (β (some i))) s := by
  let μ := (L.law:Measure Path)
  let M (r : ℝ) := canonicalPhysicalResidual T (some i) r.toNNReal
  let ν := volume.restrict (Ioc (0:ℝ) s)
  let k (r : ℝ) := R (s-r)
  let X (p : Path) := ∫ r,k r*M r p ∂ν
  let c := volterraConvolution R (physicalImmigrationPrimitive (β (some i))) s
  have hα₀ : 0<α := by linarith
  have hAi : canonicalVariancePrimitive T (some i) s =ᵐ[μ] fun p => c+X p :=
    (L.canonicalPulse_integrated_resolvent hi hα₀ hα' hR hRb hRes hβ hB).mono fun _ hp => hp s hs
  have hk : Measurable k := hR.comp (measurable_const.sub measurable_id)
  have hk₂ : MemLp k 2 ν := reflected_resolvent_memLp_two hα hs.1 hR
    (fun r hr => hRb r ⟨hr.1,hr.2.trans hs.2⟩)
  obtain ⟨C,hC,hMC⟩ := L.residual_uniform_second
  have hM := (canonical_joint_residual (T := T) (some i)).measurable
  have hM₂ (r : ℝ) : MemLp (M r) 2 μ := L.residual_memLp r.toNNReal
  have hMC' : ∀ᵐ r ∂ν,(∫ p,(M r p)^2 ∂μ)≤C := ae_of_all _ fun r => hMC _ r.toNNReal
  have hX₂ : MemLp X 2 μ := weighted_path_memLp_two hM hk hk₂ hM₂ hC hMC'
  have hx : (∫ p,X p ∂μ)=0 := by
    have h := deterministic_weighted_path_pairing hM (measurable_const (a := (1:ℝ)))
      (memLp_const (1:ℝ)) hk (hk₂.integrable one_le_two) hM₂ hC hMC'
    simp only [mul_one] at h
    change (∫ p,X p ∂μ)=∫ r,k r*(∫ p,M r p ∂μ) ∂ν at h
    have hz (r : ℝ) : (∫ p,M r p ∂μ)=0 := L.residual_centered _ _
    simpa only [hz,mul_zero,integral_zero] using h
  rw [integral_congr_ae hAi,integral_add (integrable_const c) (hX₂.integrable one_le_two),hx]
  simp [μ,c]

/-- The integrated physical cluster coordinates have exactly zero mixed
covariance. The proof uses the original residuals and ordinary Fubini. -/
theorem integrated_pulse_mixed_covariance {i j : ι} (hij : i≠j)
    (hi : v (some i)=0) (hj : v (some j)=0)
    (hα : 1/2<α) (hα' : α<1) {R : ℝ→ℝ} (hR : Measurable R)
    {Rbound : ℝ} (hRb : ∀ r∈Ioc (0:ℝ) (T:ℝ),|R r|≤Rbound*fractionalK α r)
    (hRes : ∀ r∈Ioc (0:ℝ) (T:ℝ),R r=fractionalK α r-κ*volterraConvolution (fractionalK α) R r)
    {B : ℝ} (hβ : ∀ i,Measurable (β i)) (hB : ∀ i t,‖β i t‖≤B)
    {s t : ℝ} (hs : s∈Icc (0:ℝ) (T:ℝ)) (ht : t∈Icc (0:ℝ) (T:ℝ)) :
    let μ := (L.law:Measure Path)
    let A := canonicalVariancePrimitive T (some i) s
    let D := canonicalVariancePrimitive T (some j) t
    MemLp A 2 μ ∧ MemLp D 2 μ ∧
      (∫ p,A p*D p ∂μ)=(∫ p,A p ∂μ)*(∫ p,D p ∂μ) := by
  let μ := (L.law:Measure Path)
  let A := canonicalVariancePrimitive T (some i) s
  let D := canonicalVariancePrimitive T (some j) t
  let M (r : ℝ) := canonicalPhysicalResidual T (some i) r.toNNReal
  let N (r : ℝ) := canonicalPhysicalResidual T (some j) r.toNNReal
  let ν := volume.restrict (Ioc (0:ℝ) s)
  let ν' := volume.restrict (Ioc (0:ℝ) t)
  let k (r : ℝ) := R (s-r)
  let l (r : ℝ) := R (t-r)
  let X (p : Path) := ∫ r,k r*M r p ∂ν
  let Y (p : Path) := ∫ r,l r*N r p ∂ν'
  let c := volterraConvolution R (physicalImmigrationPrimitive (β (some i))) s
  let d := volterraConvolution R (physicalImmigrationPrimitive (β (some j))) t
  have hα₀ : 0<α := by linarith
  have hAi : A=ᵐ[μ] fun p => c+X p :=
    (L.canonicalPulse_integrated_resolvent hi hα₀ hα' hR hRb hRes (hβ _) (hB _)).mono fun _ hp => hp s hs
  have hDj : D=ᵐ[μ] fun p => d+Y p :=
    (L.canonicalPulse_integrated_resolvent hj hα₀ hα' hR hRb hRes (hβ _) (hB _)).mono fun _ hp => hp t ht
  have hk : Measurable k := hR.comp (measurable_const.sub measurable_id)
  have hl : Measurable l := hR.comp (measurable_const.sub measurable_id)
  have hk₂ : MemLp k 2 ν := reflected_resolvent_memLp_two hα hs.1 hR
    (fun r hr => hRb r ⟨hr.1,hr.2.trans hs.2⟩)
  have hl₂ : MemLp l 2 ν' := reflected_resolvent_memLp_two hα ht.1 hR
    (fun r hr => hRb r ⟨hr.1,hr.2.trans ht.2⟩)
  obtain ⟨C,hC,hMC⟩ := L.residual_uniform_second
  have hM := (canonical_joint_residual (T := T) (some i)).measurable
  have hN := (canonical_joint_residual (T := T) (some j)).measurable
  have hM₂ (r : ℝ) : MemLp (M r) 2 μ := L.residual_memLp r.toNNReal
  have hN₂ (r : ℝ) : MemLp (N r) 2 μ := L.residual_memLp r.toNNReal
  have hMC' : ∀ᵐ r ∂ν,(∫ p,(M r p)^2 ∂μ)≤C := ae_of_all _ fun r => hMC _ r.toNNReal
  have hNC' : ∀ᵐ r ∂ν',(∫ p,(N r p)^2 ∂μ)≤C := ae_of_all _ fun r => hMC _ r.toNNReal
  have hX₂ : MemLp X 2 μ := weighted_path_memLp_two hM hk hk₂ hM₂ hC hMC'
  have hY₂ : MemLp Y 2 μ := weighted_path_memLp_two hN hl hl₂ hN₂ hC hNC'
  have hmi (r u : ℝ) : (∫ p,M r p*N u p ∂μ)=0 := by
    exact orthogonal_martingale_mixed_time_mean_zero (L.residualMartingale (some i))
      (L.residualMartingale (some j)) (canonical_cluster_residual_product_martingale hij (L.productMartingale _ _))
      (fun r => L.residual_memLp r) (fun r => L.residual_memLp r)
      (canonicalPhysicalResidual_zero_ae L.starts (some i)) _ _
  have hXY : (∫ p,X p*Y p ∂μ)=0 :=
    orthogonal_deterministic_weighted_paths hM hN hk hl (hk₂.integrable one_le_two)
      (hl₂.integrable one_le_two) hM₂ hN₂ hC hC hMC' hNC' hY₂ hmi
  have hx : (∫ p,X p ∂μ)=0 := by
    have h := deterministic_weighted_path_pairing hM (measurable_const (a := (1:ℝ)))
      (memLp_const (1:ℝ)) hk (hk₂.integrable one_le_two) hM₂ hC hMC'
    simp only [mul_one] at h
    change (∫ p,X p ∂μ)=∫ r,k r*(∫ p,M r p ∂μ) ∂ν at h
    have hz (r : ℝ) : (∫ p,M r p ∂μ)=0 := L.residual_centered _ _
    simpa only [hz,mul_zero,integral_zero] using h
  have hy : (∫ p,Y p ∂μ)=0 := by
    have h := deterministic_weighted_path_pairing hN (measurable_const (a := (1:ℝ)))
      (memLp_const (1:ℝ)) hl (hl₂.integrable one_le_two) hN₂ hC hNC'
    simp only [mul_one] at h
    change (∫ p,Y p ∂μ)=∫ r,l r*(∫ p,N r p ∂μ) ∂ν' at h
    have hz (r : ℝ) : (∫ p,N r p ∂μ)=0 := L.residual_centered _ _
    simpa only [hz,mul_zero,integral_zero] using h
  have hXi := hX₂.integrable one_le_two
  have hYi := hY₂.integrable one_le_two
  have hAm : (∫ p,A p ∂μ)=c := by
    rw [integral_congr_ae hAi,integral_add (integrable_const c) hXi,hx]
    simp [μ]
  have hDm : (∫ p,D p ∂μ)=d := by
    rw [integral_congr_ae hDj,integral_add (integrable_const d) hYi,hy]
    simp [μ]
  refine ⟨((memLp_const c).add hX₂).ae_eq hAi.symm,((memLp_const d).add hY₂).ae_eq hDj.symm,?_⟩
  change (∫ p,A p*D p ∂μ)=(∫ p,A p ∂μ)*(∫ p,D p ∂μ)
  have hp : (fun p => A p*D p) =ᵐ[μ] fun p => (c+X p)*(d+Y p) := hAi.mul hDj
  rw [hAm,hDm,integral_congr_ae hp]
  have he : (fun p => (c+X p)*(d+Y p)) = fun p => c*d+c*Y p+d*X p+X p*Y p := by
    funext p
    ring
  have h₁ : Integrable (fun _ : Path => c*d) μ := integrable_const _
  have h₂ := hYi.const_mul c
  have h₃ := hXi.const_mul d
  have h₄ : Integrable (fun p => X p*Y p) μ := hX₂.integrable_mul hY₂
  have he₄ := integral_add ((h₁.add h₂).add h₃) h₄
  have he₃ := integral_add (h₁.add h₂) h₃
  simp only [Pi.add_apply] at he₄ he₃
  rw [he,he₄,he₃,integral_add h₁ h₂,integral_const_mul c Y,integral_const_mul d X,hx,hy,hXY]
  simp [μ]

end FractionalFixedMeshLaw

#print axioms FractionalFixedMeshLaw.integrated_pulse_mean
#print axioms FractionalFixedMeshLaw.integrated_pulse_mixed_covariance

end RoughHeston
