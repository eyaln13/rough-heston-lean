import AffineBoundaryAtom
import CaputoMeanComparison
import CaputoPowerBound

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace RoughHeston

/-- The finite-charge Riccati comparison and continuous tilted mean
equation yield the uniform conditional backward moment estimate. -/
theorem affine_boundary_backward_mean
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {V : ℝ → Ω → ℝ} {w : ℕ → ℝ → ℝ} {α κ a lo hi b B D : ℝ}
    (hα : 1/2<α) (hα' : α<1) (hκ : 0≤κ) (ha : 0<a)
    (hlo : 0<lo) (hB : 0≤B)
    (hVm : ∀ t,Measurable (V t)) (hVnn : ∀ t ω,0≤V t ω)
    (hVi : ∀ t∈Icc 0 hi,Integrable (V t) μ)
    (hVB : ∀ t∈Icc 0 hi,(∫ ω,V t ω ∂μ)≤B)
    (hw : ∀ (n : ℕ) (t : ℝ), PointChargeRiccatiOn α (n:ℝ) (-κ) (-a) t (w n))
    (hAff : ∀ t∈Icc lo hi, ∀ n, Real.exp (-D) ≤ (∫ ω,laplaceBoundaryWeight (V t) n ω ∂μ))
    (hMean : ∀ t∈Icc lo hi, ∀ n,
      let f (r : ℝ) := ∫ ω,V r ω ∂laplaceBoundaryTilt μ (V t) n
      ContinuousOn f (Ico 0 t) ∧
      ∀ s ∈ Ioo (0:ℝ) t, f s = f 0+
        volterraConvolution (fractionalK α) (fun r => b-(κ+2*a*w n (t-r))*f r) s) :
    ∃ p ∈ Ioo (2*α-1) α, ∃ C : ℝ, 0<C ∧
      ∀ t ∈ Icc lo hi, ∀ u ∈ Ioc (0:ℝ) t,
        (∫ ω,V (t-u) ω ∂boundaryConditionedMeasure μ {ω | V t ω=0})≤C*u^p := by
  obtain ⟨p,hp,hpg⟩ := exists_backwardPowerCoefficient_gap hα hα' ha
  have hp₀ : 0<p := (show 0<2*α-1 by linarith).trans hp.1
  have hpc : caputoCoefficient α p < boundaryCoefficient α := by
    rw [← two_mul_singularRiccatiCoefficient hα' ha]
    exact hpg
  obtain ⟨c,hc,d,hd,N,hN,hR⟩ :=
    exists_global_riccati_uniform_boundary_lower hα hα' ha hκ (half_pos hlo) hpc
  let K := B/Real.exp (-D)
  have hK : 0≤K := div_nonneg hB (Real.exp_pos _).le
  obtain ⟨A,hA,hComp⟩ := caputo_mean_le_backwardPower_of_volterra (b := b) hα hα' hp₀ hp.2 hc hK hd.1
  let C := max A (K/d^p)
  have hC : 0<C := hA.trans_le (le_max_left _ _)
  refine ⟨p,hp,C,hC,?_⟩
  intro t ht u hu
  let f (n : ℕ) (r : ℝ) := ∫ ω,V r ω ∂laplaceBoundaryTilt μ (V t) n
  have hdt : d<t := hd.2.trans_lt ((half_lt_self hlo).trans_le ht.1)
  have ht₀ : 0<t := hlo.trans_le ht.1
  have hKf (n : ℕ) (r : ℝ) (hr : r ∈ Icc 0 t) : f n r ≤ K := by
    have hr' : r∈Icc 0 hi := ⟨hr.1,hr.2.trans ht.2⟩
    let P := laplaceBoundaryWeight (V t) n
    have hPm : Measurable P := ((hVm t).const_mul (-(n:ℝ))).exp
    have hP0 (ω : Ω) : 0≤P ω := (Real.exp_pos _).le
    have hP1 (ω : Ω) : P ω≤1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (hVnn _ _))
    have hInt : Integrable (fun ω => P ω*V r ω) μ :=
      (hVi r hr').bdd_mul hPm.aestronglyMeasurable
        (ae_of_all _ fun ω => by simpa only [Real.norm_of_nonneg (hP0 ω)] using hP1 ω)
    have hNum : (∫ ω,P ω*V r ω ∂μ)≤B :=
      (integral_mono hInt (hVi r hr') (fun ω => mul_le_of_le_one_left (hVnn _ _) (hP1 ω))).trans
        (hVB r hr')
    have hPos : 0<(∫ ω,P ω ∂μ) := (Real.exp_pos _).trans_le (hAff t ht n)
    change (∫ ω,V r ω ∂laplaceBoundaryTilt μ (V t) n)≤K
    rw [laplaceBoundaryTilt_integral _ _ (hVm t)]
    exact (div_le_div_of_nonneg_right hNum hPos.le).trans
      (div_le_div_of_nonneg_left hB (Real.exp_pos _) (hAff t ht n))
  have hAtom : 0<μ {ω | V t ω=0} := by
    have hh := ge_of_tendsto (tendsto_laplaceBoundary_atom (hVm t) (ae_of_all _ (hVnn t)))
      (Eventually.of_forall (hAff t ht))
    exact (ENNReal.toReal_pos_iff.mp ((Real.exp_pos _).trans_le hh)).1
  have htu : t-u∈Icc (0:ℝ) t := ⟨sub_nonneg.mpr hu.2,sub_le_self _ hu.1.le⟩
  apply boundaryConditionalMean_le_of_laplaceTilt (hVm t) (ae_of_all _ (hVnn t))
    (hVi (t-u) ⟨htu.1,htu.2.trans ht.2⟩) hAtom
  by_cases hud : d≤u
  · exact Eventually.of_forall fun n => (hKf n (t-u) htu).trans (by
      have hdPow : 0<d^p := Real.rpow_pos_of_pos hd.1 _
      have hPow : d^p≤u^p := Real.rpow_le_rpow hd.1.le hud hp₀.le
      calc
        K = (K/d^p)*d^p := (div_mul_cancel₀ _ hdPow.ne').symm
        _ ≤ C*d^p := mul_le_mul_of_nonneg_right (le_max_right _ _) hdPow.le
        _ ≤ C*u^p := mul_le_mul_of_nonneg_left hPow hC.le)
  · have hPow : 0<u^(2*α-1) := Real.rpow_pos_of_pos hu.1 _
    obtain ⟨n₀,hn₀⟩ := exists_nat_ge ((N:ℝ)/u^(2*α-1))
    filter_upwards [eventually_ge_atTop n₀] with n hn
    have hnR : (N:ℝ)≤(n:ℝ)*u^(2*α-1) :=
      (div_le_iff₀ hPow).mp (hn₀.trans (Nat.cast_le.mpr hn))
    let k (r : ℝ) := κ+2*a*w n (t-r)
    have hkc (r : ℝ) (hr : r∈Ico 0 t) : ContDiffAt ℝ 1 k r :=
      contDiffAt_const.add (contDiffAt_const.mul ((hw n t).contDiffAt_pos _ (sub_pos.mpr hr.2)
        |>.comp r (contDiffAt_const.sub contDiffAt_id)))
    have hkC : ContinuousOn k (Ico 0 t) := fun r hr => (hkc r hr).continuousAt.continuousWithinAt
    have hkl (r : ℝ) (hr : r ∈ Icc (t-d) (t-u)) : c*(t-r)^(-α)≤k r := by
      have h₁ : u≤t-r := by linarith [hr.2]
      have h₂ : t-r≤d := by linarith [hr.1]
      have hh := hR hu.1 h₁ h₂ hnR (hw n (t-r))
      dsimp [k]
      linarith
    have hmean := hMean t ht n
    have hh := hComp (T := t) (S := t-u) hdt (sub_lt_self _ hu.1)
      hmean.1 hkC (fun r hr => hkc r ⟨hr.1.le,hr.2⟩)
      (fun r hr => hKf n r ⟨hr.1,hr.2.trans (sub_le_self _ hd.1.le)⟩)
      hkl hmean.2 (t-u) ⟨sub_le_sub_left (le_of_not_ge hud) _,le_rfl⟩
    have hh' : f n (t-u) < A*u^p := by
      simpa only [sub_sub_cancel] using hh
    exact hh'.le.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg hu.1.le _))

#print axioms affine_boundary_backward_mean

end RoughHeston
