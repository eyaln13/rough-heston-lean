import HestonRealKernelNoiseMoment
import ClusterTimeWindowBeta

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston.GirsanovPort
open SHEStochastic

noncomputable def focalBandMomentFactor (α q : ℝ) (n : ℕ) : ℝ :=
  let J := Real.Gamma 1*Real.Gamma q/Real.Gamma (1+q)
  let G := Real.Gamma α*Real.Gamma q/Real.Gamma (α+q)
  (NativeScalarBDG.constant n:ℝ)*J^((((2^n:ℕ):ℝ))-1)*G

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {T : ℝ≥0} {B U : ℝ≥0 → Ω → ℝ}

/-- Kernel noise supported on one time window. The lower-order moment
may grow as t^(α−1) at birth. The window may start at any later time. -/
theorem focal_noise_on_band_power_bound {a b : ℝ≥0} (hle : a≤b) (hbT : b≤T)
    {α q A D σ : ℝ} (ha : 0<α) (ha' : α≤1) (hq : 0<q)
    (hA : 0≤A) (hD : 0≤D) (n : ℕ)
    (hb : MathFinBridge.BrownianOn P F T B)
    (hnull : ∀ N : Set Ω, MeasurableSet N → P N=0 → MeasurableSet[F 0] N)
    (hB₂ : ∀ t, MemLp (B t) 2 P) (hB : Martingale B F P)
    (hclock : Martingale (fun t ω => B t ω^2-((min t T:ℝ≥0):ℝ)) F P)
    (hU : Measurable (Function.uncurry U)) (hU₀ : ∀ s ω, 0≤U s ω)
    {k : ℝ≥0 → ℝ} (hk : Measurable k)
    (hz : ∀ t, t∉Ioc a b → k t=0)
    (hlocal : ∀ t∈Ioo a b, (σ*k t)^2 ≤ A*((b:ℝ)-(t:ℝ))^(q-1))
    (u : Lp ℝ 2 (jointPredictableMeasure F P T))
    (hu : u =ᵐ[jointPredictableMeasure F P T] fun z => σ*k z.1*Real.sqrt (U z.1 z.2))
    (hprev : ∀ᵐ t ∂hestonTimeMeasure T, Integrable (fun ω => U t ω^(2^n:ℕ)) P ∧
      (∫ ω, U t ω^(2^n:ℕ) ∂P) ≤ D*(t:ℝ)^(α-1)) :
    let N := jointItoIntegralCLM T hB₂ u
    MemLp (fun ω => N ω) ((2*2^n:ℕ):ℝ≥0∞) P ∧
      (∫ ω, ‖N ω‖^(2*2^n:ℕ) ∂P) ≤ focalBandMomentFactor α q n *
        A^(2^n:ℕ)*D*((b:ℝ)-(a:ℝ))^(α-1+((2^n:ℕ):ℝ)*q) := by
  rcases eq_or_lt_of_le hle with he | hab
  · subst b
    have hzero : u=0 := by
      apply Lp.ext
      filter_upwards [hu,Lp.coeFn_zero ℝ 2 (jointPredictableMeasure F P T)] with z h h0
      rw [h,hz z.1 (by simp),mul_zero,zero_mul,h0]; rfl
    rw [hzero,map_zero]
    let p := (2*2^n:ℕ)
    have he : (fun ω => (0:Lp ℝ 2 P) ω)=ᵐ[P] fun _ => (0:ℝ) := Lp.coeFn_zero _ _ _
    have hi : MemLp (fun ω => (0:Lp ℝ 2 P) ω) (p:ℝ≥0∞) P :=
      (memLp_const (0:ℝ)).ae_eq he.symm
    refine ⟨hi,?_⟩
    have hi₀ : (∫ ω, ‖(0:Lp ℝ 2 P) ω‖^(2*2^n:ℕ) ∂P)=0 := by
      have h' := integral_congr_ae (he.mono fun ω h => congrArg (fun z : ℝ => ‖z‖^(2*2^n:ℕ)) h)
      simpa using h'
    rw [hi₀]
    have h1 := Real.Gamma_pos_of_pos (by linarith : 0<1+q)
    have h2 := Real.Gamma_pos_of_pos (add_pos ha hq)
    have h3 := Real.Gamma_pos_of_pos ha
    have h4 := Real.Gamma_pos_of_pos hq
    simp only [focalBandMomentFactor,Real.Gamma_one,sub_self]; positivity
  let m := (2^n:ℕ)
  let d : ℝ := (m:ℝ)-1
  let L := (b:ℝ)-(a:ℝ)
  let J := Real.Gamma 1*Real.Gamma q/Real.Gamma (1+q)
  let G := Real.Gamma α*Real.Gamma q/Real.Gamma (α+q)
  let w (t : ℝ≥0) := (σ*k t)^2
  let c (t : ℝ≥0) := D*(t:ℝ)^(α-1)
  have hp : 0<L := sub_pos.mpr (show (a:ℝ)<(b:ℝ) from hab)
  have hd : 0≤d := sub_nonneg.mpr (by exact_mod_cast Nat.one_le_pow n 2 (by decide))
  have hJ : 0≤J := div_nonneg (mul_nonneg (Real.Gamma_pos_of_pos zero_lt_one).le
    (Real.Gamma_pos_of_pos hq).le) (Real.Gamma_pos_of_pos (by linarith)).le
  have hG : 0≤G := div_nonneg (mul_nonneg (Real.Gamma_pos_of_pos ha).le
    (Real.Gamma_pos_of_pos hq).le) (Real.Gamma_pos_of_pos (add_pos ha hq)).le
  have hw : Measurable w := by dsimp [w]; fun_prop
  have hc : Measurable c := by dsimp [c]; fun_prop
  have hzero (t) (ht : t∉Ioc a b) : w t=0 := by simp [w,hz t ht]
  obtain ⟨hwi,hwb⟩ := heston_time_window_beta_bound hab hbT (p:=1) (by norm_num) hq hA hw hzero
    (fun s hs => ⟨sq_nonneg _, by simpa only [sub_self,Real.rpow_zero,one_mul] using hlocal s hs⟩)
  have hwb' : (∫ t,w t ∂hestonTimeMeasure T) ≤ A*(L^q*J) := by
    simpa only [show 1+q-1=q by ring] using hwb
  obtain ⟨hwci,hwcb⟩ := heston_time_window_beta_bound hab hbT ha hq (mul_nonneg hA hD)
    (hw.mul hc) (fun s hs => by simp only [Pi.mul_apply,hzero s hs,zero_mul])
    (fun s hs => by
      have hsa : 0 < (s:ℝ)-(a:ℝ) := sub_pos.mpr (show (a:ℝ)<(s:ℝ) from hs.1)
      have hh := Real.rpow_le_rpow_of_nonpos hsa (sub_le_self (s:ℝ) a.coe_nonneg) (sub_nonpos.mpr ha')
      have hdiff := Real.rpow_nonneg (show 0≤(b:ℝ)-(s:ℝ) from sub_nonneg.mpr hs.2.le) (q-1)
      have hn : 0≤c s := mul_nonneg hD (Real.rpow_nonneg s.coe_nonneg _)
      refine ⟨mul_nonneg (sq_nonneg _) hn,?_⟩
      have h := mul_le_mul (hlocal s hs) (mul_le_mul_of_nonneg_left hh hD) hn (mul_nonneg hA hdiff)
      refine h.trans_eq ?_; ring)
  obtain ⟨hm,hbound⟩ := heston_sqrt_row_real_moment hb hnull hB₂ hB hclock n hk hU hU₀
    u hu hprev hwi hwci
  refine ⟨hm, hbound.trans ?_⟩
  have h2 := mul_le_mul (Real.rpow_le_rpow (integral_nonneg fun s => sq_nonneg (σ*k s)) hwb' hd) hwcb
    (integral_nonneg fun s => mul_nonneg (sq_nonneg _) (mul_nonneg hD (Real.rpow_nonneg s.coe_nonneg _)))
    (Real.rpow_nonneg (mul_nonneg hA (mul_nonneg (Real.rpow_nonneg hp.le _) hJ)) _)
  refine (mul_le_mul_of_nonneg_left h2 (NNReal.coe_nonneg (NativeScalarBDG.constant n))).trans_eq ?_
  have hAp : A^d*A=A^m := by
    calc
      _ = A^d*A^(1:ℝ) := by rw [Real.rpow_one]
      _ = A^(d+1) := (Real.rpow_add_of_nonneg hA hd zero_le_one).symm
      _ = A^m := by dsimp only [d]; rw [sub_add_cancel,Real.rpow_natCast]
  have hLp : (L^q)^d*L^(α+q-1)=L^(α-1+(m:ℝ)*q) := by
    rw [←Real.rpow_mul hp.le,←Real.rpow_add hp]; congr 1; dsimp [d]; ring
  change _*( (A*(L^q*J))^d*((A*D)*(L^(α+q-1)*G))) = _
  rw [Real.mul_rpow hA (mul_nonneg (Real.rpow_nonneg hp.le _) hJ),
    Real.mul_rpow (Real.rpow_nonneg hp.le _) hJ]
  change _ = ((NativeScalarBDG.constant n:ℝ)*J^d*G)*A^m*D*L^(α-1+(m:ℝ)*q)
  rw [←hAp,←hLp]; ring

#print axioms focal_noise_on_band_power_bound

end RoughHeston.GirsanovPort
