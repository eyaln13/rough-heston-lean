import ClusterKernelMoment

/-! The small immigration factor in moments of every dyadic order,
obtained on the original clock. -/

open MeasureTheory Set Filter
open scoped Topology

namespace RoughHeston

/-- The two bounds for the deterministic rectangular input retain a
single copy of the immigration mass at every positive integer power. -/
theorem pulse_input_power_profile {m : ℕ} (hm : 0 < m)
    {I s e t α β A D : ℝ} (hI : 0 ≤ I) (hs : 0 < s)
    (hA : 0 ≤ A) (hf : I ≤ D*e*t^(α-1)) (hg : I ≤ A*s^β) :
    I^m ≤ D*A^(m-1)*e*t^(α-1)*s^(((m:ℝ)-1)*β) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  rw [pow_succ]
  have hpow := pow_le_pow_left₀ hI hg n
  have h := mul_le_mul hpow hf hI (pow_nonneg (mul_nonneg hA (Real.rpow_nonneg hs.le _)) _)
  simp only [Nat.succ_sub_one,Nat.cast_succ,add_sub_cancel_right] at *
  rw [mul_pow] at h
  rw [mul_comm (n:ℝ) β,Real.rpow_mul hs.le,Real.rpow_natCast]
  linarith only [h]

/-- One stochastic moment-doubling step with its actual time-dependent
input bound. The upper limit 2s covers the whole observation block. -/
theorem cluster_noise_doubling_profile {α β s t ε C : ℝ} (m : ℕ)
    (hα : 1/2 < α) (hb : β = 2*α-1) (hs : 0 < s) (ht : 0 < t) (hts : t ≤ 2*s)
    (hε : 0 ≤ ε) (hC : 0 ≤ C) {f : ℝ → ℝ} (hf : Measurable f)
    (hn : ∀ u ∈ Ioc 0 t, 0 ≤ f u)
    (hbound : ∀ u ∈ Ioc 0 t, f u ≤ C*ε*u^(α-1)*s^(((m:ℝ)-1)*β)) :
    t^(β*((m:ℝ)-1))*(∫ u in Ioc 0 t,(t-u)^(β-1)*f u) ≤
      (Real.Gamma α*Real.Gamma β/Real.Gamma (α+β))*C*2^((m:ℝ)*β)*
        ε*t^(α-1)*s^((2*(m:ℝ)-1)*β) := by
  subst β
  let β := 2*α-1
  have hb : 0 < β := by dsimp [β]; linarith
  have ha : 0 < α := by linarith
  let D := C*ε*s^(((m:ℝ)-1)*β)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let w (u : ℝ) := (t-u)^(β-1)
  have hg : IntegrableOn (fun u : ℝ => w u*(D*u^(α-1))) (Ioc 0 t) := by
    have h := ((real_beta_weight_scaled ha hb ht).1).const_mul D
    apply h.congr
    exact ae_of_all _ fun u => by dsimp [w]; ring
  have hpoint (u : ℝ) (hu : u ∈ Ioc 0 t) : w u*f u ≤ w u*(D*u^(α-1)) := by
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (sub_nonneg.mpr hu.2) _)
    dsimp [D]
    linarith only [hbound u hu]
  have hi : IntegrableOn (fun u => w u*f u) (Ioc 0 t) := by
    apply hg.mono' ((by fun_prop : Measurable w).mul hf).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with u hu
    change ‖w u * f u‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (show 0 ≤ w u from Real.rpow_nonneg (sub_nonneg.mpr hu.2) _) (hn u hu))]
    exact hpoint u hu
  have hcomp := mul_le_mul_of_nonneg_left
    (integral_mono_ae hi hg (ae_restrict_of_forall_mem measurableSet_Ioc hpoint))
    (Real.rpow_nonneg ht.le (β*((m:ℝ)-1)))
  have hex := cluster_beta_moment_step hα ht (m:ℝ) D
  have hcore : t^(β*((m:ℝ)-1))*(∫ u in Ioc 0 t,w u*f u) ≤
      Real.Gamma α*Real.Gamma β/Real.Gamma (α+β)*D*t^(α-1+(m:ℝ)*β) := hcomp.trans_eq hex
  let G := Real.Gamma α*Real.Gamma β/Real.Gamma (α+β)
  have hG : 0 ≤ G := div_nonneg (mul_nonneg (Real.Gamma_pos_of_pos ha).le
    (Real.Gamma_pos_of_pos hb).le) (Real.Gamma_pos_of_pos (add_pos ha hb)).le
  have htime := Real.rpow_le_rpow ht.le hts (mul_nonneg m.cast_nonneg hb.le)
  have he : s^(((m:ℝ)-1)*β)*s^((m:ℝ)*β)=s^((2*(m:ℝ)-1)*β) := by
    rw [← Real.rpow_add hs]; congr 1; ring
  refine hcore.trans ?_
  rw [Real.rpow_add ht]
  calc
    (G*D)*(t^(α-1)*t^((m:ℝ)*β)) ≤ (G*D)*(t^(α-1)*(2*s)^((m:ℝ)*β)) := by gcongr
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hs.le, ← he]
      dsimp [D,G,β]
      ring

/-- Uniform moment induction on the original time scale for a family of
pulses. The index may include the birth, mesh and reference age. The
recursion is the direct kernel moment estimate at each fixed age. -/
theorem cluster_dyadic_order_moments {ι : Type*} {α β A D C₀ : ℝ}
    (hα : 1/2 < α) (hβ : β=2*α-1) (hA : 0 ≤ A) (hD : 0 ≤ D) (hC₀ : 0 ≤ C₀)
    {e s : ι → ℝ} (hs : ∀ i, 0 < s i) (he : ∀ i, 0 ≤ e i)
    {I : ι → ℝ → ℝ} (hI : ∀ i t, 0 < t → t ≤ 2*s i →
      0 ≤ I i t ∧ I i t ≤ D*e i*t^(α-1) ∧ I i t ≤ A*(s i)^β)
    {f : ℕ → ι → ℝ → ℝ} (hf : ∀ k i, Measurable (f k i))
    (hn : ∀ k i t, 0 < t → t ≤ 2*s i → 0 ≤ f k i t)
    (hbase : ∀ i t, 0 < t → t ≤ 2*s i → f 0 i t ≤ C₀*e i*t^(α-1))
    {B : ℕ → ℝ} (hB : ∀ k, 0 ≤ B k)
    (hstep : ∀ k i t, 0 < t → t ≤ 2*s i →
      f (k+1) i t ≤ B k*((I i t)^(2*(2^k:ℕ)) +
        t^(β*((((2^k:ℕ):ℝ))-1))*(∫ u in Ioc 0 t,(t-u)^(β-1)*f k i u))) :
    ∀ k, ∃ C : ℝ, 0 ≤ C ∧ ∀ i t, 0 < t → t ≤ 2*s i →
      f k i t ≤ C*e i*t^(α-1)*(s i)^(((((2^k:ℕ):ℝ))-1)*β) := by
  have ha : 0 < α := by linarith
  have hb : 0 < β := by linarith
  let G := Real.Gamma α*Real.Gamma β/Real.Gamma (α+β)
  have hG : 0 ≤ G := div_nonneg (mul_nonneg (Real.Gamma_pos_of_pos ha).le
    (Real.Gamma_pos_of_pos hb).le) (Real.Gamma_pos_of_pos (add_pos ha hb)).le
  intro k
  induction k with
  | zero =>
    exact ⟨C₀,hC₀,fun i t ht hts => by simpa using hbase i t ht hts⟩
  | succ k ih =>
    obtain ⟨C,hC,hm⟩ := ih
    let m := (2^k:ℕ)
    have hmp : 0 < m := pow_pos (by decide) _
    let L := D*A^(2*m-1)+G*C*(2:ℝ)^((m:ℝ)*β)
    have hL : 0 ≤ L := by dsimp [L]; positivity
    refine ⟨B k*L,mul_nonneg (hB k) hL,?_⟩
    intro i t ht hts
    obtain ⟨hi,hi0,hi1⟩ := hI i t ht hts
    have hd := pulse_input_power_profile (m := 2*m) (by positivity) hi (hs i) hA hi0 hi1
    have hN := cluster_noise_doubling_profile m hα hβ (hs i) ht hts (he i) hC (hf k i)
      (fun u hu => hn k i u hu.1 (hu.2.trans hts)) (fun u hu => hm i u hu.1 (hu.2.trans hts))
    have h := (hstep k i t ht hts).trans (mul_le_mul_of_nonneg_left (add_le_add hd hN) (hB k))
    have heq : (2^(k+1):ℕ)=2*m := by simp [m,pow_succ,Nat.mul_comm]
    rw [heq]
    dsimp only [G,L]
    simp only [Nat.cast_mul,Nat.cast_ofNat] at h ⊢
    linarith only [h]

#print axioms cluster_dyadic_order_moments

#print axioms pulse_input_power_profile
#print axioms cluster_noise_doubling_profile

end RoughHeston
