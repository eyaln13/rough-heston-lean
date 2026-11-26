import FocalBandMoment
import FocalIncrementKernelBounds
import FocalBandScaling

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston.GirsanovPort
open SHEStochastic

noncomputable def focalNoiseIncrementConstant (α δ σ A C D : ℝ) (n : ℕ) : ℝ :=
  let m := (2^n:ℕ)
  let β := 2*α-1
  let q := β-2*δ
  let z := α-1+(m:ℝ)*q
  let E₁ := (|σ| * (2*A+C))^2
  let E₂ := (|σ| * A)^2
  (2:ℝ)^(2*m-1)*
    (focalBandMomentFactor α q n*E₁^m*D*2^z+
      focalBandMomentFactor α β n*E₂^m*D*2^z)

private theorem bandFactor_nonneg {α q : ℝ} (hα : 0<α) (hq : 0<q) (n : ℕ) :
    0 ≤ focalBandMomentFactor α q n := by
  have h1 := Real.Gamma_pos_of_pos (by linarith : 0 < 1+q)
  have h2 := Real.Gamma_pos_of_pos (add_pos hα hq)
  have h3 := Real.Gamma_pos_of_pos hα
  have h4 := Real.Gamma_pos_of_pos hq
  dsimp [focalBandMomentFactor]; rw [Real.Gamma_one]; positivity

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {T : ℝ≥0} {B U : ℝ≥0 → Ω → ℝ}

theorem focal_noise_increment_power_bound
    {α δ σ A C D S ε : ℝ} (hα : 1/2<α) (hα' : α<1) (hδ : 0≤δ)
    (hq : 0<2*α-1-2*δ) (hS : 0<S) (hε : 0≤ε)
    (hA : 0≤A) (hC : 0≤C) (hD : 0≤D) (n : ℕ)
    (hz : 0≤α-1+((2^n:ℕ):ℝ)*(2*α-1-2*δ))
    {a b : ℝ≥0} (hab : a<b) (hbT : b≤T) (hT : (T:ℝ)≤2*S)
    (hb : MathFinBridge.BrownianOn P F T B)
    (hnull : ∀ N : Set Ω, MeasurableSet N → P N=0 → MeasurableSet[F 0] N)
    (hB₂ : ∀ t, MemLp (B t) 2 P) (hB : Martingale B F P)
    (hclock : Martingale (fun t ω => B t ω^2-((min t T:ℝ≥0):ℝ)) F P)
    (hU : Measurable (Function.uncurry U)) (hU₀ : ∀ s ω, 0≤U s ω)
    {R : ℝ → ℝ} (hR : Measurable R) (hzero : ∀ x≤0, R x=0)
    (hpoint : ∀ x∈Ioc 0 (T:ℝ), |R x|≤A*x^(α-1))
    (hinc : ∀ x h, 0<x → 0≤h → x+h≤(T:ℝ) → |R (x+h)-R x|≤C*x^(α-2)*h)
    (f : Lp ℝ 2 (jointPredictableMeasure F P T))
    (hf : f =ᵐ[jointPredictableMeasure F P T] fun z =>
      σ*(R ((b:ℝ)-(z.1:ℝ))-R ((a:ℝ)-(z.1:ℝ)))*Real.sqrt (U z.1 z.2))
    (hprev : ∀ᵐ t ∂hestonTimeMeasure T, Integrable (fun ω => U t ω^(2^n:ℕ)) P ∧
      (∫ ω, U t ω^(2^n:ℕ) ∂P) ≤ (D*ε*S^((((2^n:ℕ):ℝ)-1)*(2*α-1)))*(t:ℝ)^(α-1)) :
    let p := 2*(2^n:ℕ)
    let I := jointItoIntegralCLM T hB₂ f
    MemLp (fun ω => I ω) (p:ℝ≥0∞) P ∧
      (∫ ω, ‖I ω‖^p ∂P) ≤ focalNoiseIncrementConstant α δ σ A C D n*
        (ε*S^((p:ℝ)*(2*α-1)-α-(p:ℝ)*δ)*((b:ℝ)-(a:ℝ))^((p:ℝ)*δ)) := by
  let m := (2^n:ℕ)
  let β := 2*α-1
  let q := β-2*δ
  let Δ := (b:ℝ)-(a:ℝ)
  let z := α-1+(m:ℝ)*q
  let D' := D*ε*S^(((m:ℝ)-1)*β)
  let A₁ := (|σ| * (2*A+C))^2
  let A₂ := (|σ| * A)^2
  have hβ : 0<β := by dsimp [β]; linarith
  have hal : 0<α := by linarith
  have hh : 0<Δ := sub_pos.mpr (show (a:ℝ)<(b:ℝ) from hab)
  have hD' : 0≤D' := by dsimp [D']; positivity
  have hA₁ : 0≤A₁ := sq_nonneg _
  have hA₂ : 0≤A₂ := sq_nonneg _
  obtain ⟨u,v,hef,hu,hv⟩ := cluster_split_increment_row hab.le hzero f hf
  obtain ⟨hpu,hpv⟩ := cluster_resolvent_increment_row_bounds hα'.le hδ (by linarith) hA hC hpoint hinc hab (show (b:ℝ)≤(T:ℝ) from hbT) (σ:=σ)
  obtain ⟨hui,huM⟩ := focal_noise_on_band_power_bound (show (0:ℝ≥0)≤a from zero_le) (hab.le.trans hbT) hal hα'.le hq
    (mul_nonneg hA₁ (Real.rpow_nonneg hh.le _)) hD' n hb hnull hB₂ hB hclock hU hU₀
    (pastResolventDifference_measurable hR a b) (fun t ht => indicator_of_notMem ht _) hpu u hu hprev
  obtain ⟨hvi,hvM⟩ := focal_noise_on_band_power_bound hab.le hbT hal hα'.le hβ hA₂ hD' n
    hb hnull hB₂ hB hclock hU hU₀ (newResolventWeight_measurable hR a b)
    (fun t ht => indicator_of_notMem ht _) hpv v hv hprev
  have he : (fun ω => jointItoIntegralCLM T hB₂ f ω) =ᵐ[P]
      ((fun ω => jointItoIntegralCLM T hB₂ u ω)+(fun ω => jointItoIntegralCLM T hB₂ v ω)) := by
    rw [hef,map_add]; exact Lp.coeFn_add _ _
  have haS : (a:ℝ)≤2*S := (show (a:ℝ)≤(b:ℝ) from hab.le).trans ((show (b:ℝ)≤(T:ℝ) from hbT).trans hT)
  have hhS : Δ≤2*S := (sub_le_self _ a.coe_nonneg).trans ((show (b:ℝ)≤(T:ℝ) from hbT).trans hT)
  have hOld := (cluster_band_scaling (m:=m) (bandFactor_nonneg hal hq n) hA₁ hD hε hS hh a.coe_nonneg haS hhS rfl hz).1
  have hNew := (cluster_band_scaling (m:=m) (bandFactor_nonneg hal hβ n) hA₂ hD hε hS hh a.coe_nonneg haS hhS rfl hz).2
  simp only [NNReal.coe_zero,sub_zero] at huM
  obtain ⟨hi,hM⟩ := cluster_integral_sum_moment hui hvi he (huM.trans hOld) (hvM.trans hNew)
  refine ⟨hi,hM.trans_eq ?_⟩
  simp only [Nat.cast_mul,Nat.cast_ofNat]
  dsimp only [focalNoiseIncrementConstant,m,β,q,Δ,z,D',A₁,A₂]
  ring

#print axioms focal_noise_increment_power_bound

end RoughHeston.GirsanovPort
