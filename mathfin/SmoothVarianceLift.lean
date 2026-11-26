import TimeDomainExponentialResolvent
import Mathlib.Analysis.Normed.Group.Constructions

open MeasureTheory Set
open scoped Interval BigOperators

namespace RoughHeston

/-- The exponential memory coordinate of the clipped variance path. -/
noncomputable def exponentialVarianceMemory (rate : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, Real.exp (-(rate * (t - s))) * max (f s) 0

theorem exponentialVarianceMemory_eq_integratingFactor (rate : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    exponentialVarianceMemory rate f t =
      Real.exp (-(rate * t)) * (∫ s in (0 : ℝ)..t, Real.exp (rate * s) * max (f s) 0) := by
  rw [exponentialVarianceMemory, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  change Real.exp (-(rate * (t - s))) * max (f s) 0 =
    Real.exp (-(rate * t)) * (Real.exp (rate * s) * max (f s) 0)
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

private theorem hasDerivAt_exp_neg_mul (rate t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.exp (-(rate * u)))
      (Real.exp (-(rate * t)) * (-rate)) t := by
  have h : HasDerivAt (fun u : ℝ => -(rate * u)) (-rate) t := by
    simpa only [id_eq, neg_mul, mul_one] using (hasDerivAt_id t).const_mul (-rate)
  exact h.exp

/-- Each exponential memory coordinate solves its first-order ODE. -/
theorem exponentialVarianceMemory_hasDerivAt {f : ℝ → ℝ} (hf : Continuous f) (rate t : ℝ) :
    HasDerivAt (exponentialVarianceMemory rate f)
      (max (f t) 0 - rate * exponentialVarianceMemory rate f t) t := by
  let g (s : ℝ) := Real.exp (rate * s) * max (f s) 0
  have hg : Continuous g := (continuous_const.mul continuous_id).rexp.mul (hf.max continuous_const)
  have hi : HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, g s) (g t) t :=
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  have he := hasDerivAt_exp_neg_mul rate t
  have H := he.fun_mul hi
  have hfn : exponentialVarianceMemory rate f =
      fun u => Real.exp (-(rate * u)) * (∫ s in (0 : ℝ)..u, g s) :=
    funext (exponentialVarianceMemory_eq_integratingFactor rate f)
  rw [hfn]
  convert H using 1
  simp only [g]
  have hmul : Real.exp (-(rate * t)) * Real.exp (rate * t) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [← mul_assoc (Real.exp (-(rate * t))) (Real.exp (rate * t)), hmul, one_mul]
  ring

theorem exponentialVarianceMemory_zero (rate : ℝ) (f : ℝ → ℝ) : exponentialVarianceMemory rate f 0 = 0 := by
  simp [exponentialVarianceMemory]

/-- The memory remains nonnegative at every nonnegative time. -/
theorem exponentialVarianceMemory_nonneg (rate : ℝ) (f : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ exponentialVarianceMemory rate f t :=
  intervalIntegral.integral_nonneg_of_forall ht (fun s =>
    mul_nonneg (Real.exp_pos (-(rate * (t - s)))).le (le_max_right (f s) 0))

/-- A solution of the memory ODE started at zero agrees with the explicit
memory on the whole horizon. In particular its positive state condition
follows from the ODE itself. -/
theorem exponentialVarianceMemory_eq_of_ode {f m : ℝ → ℝ} {T rate : ℝ}
    (hf : Continuous f) (hm₀ : m 0 = 0)
    (hm : ∀ s ∈ Icc (0 : ℝ) T, HasDerivAt m (max (f s) 0 - rate * m s) s) :
    ∀ t ∈ Icc (0 : ℝ) T, m t = exponentialVarianceMemory rate f t := by
  intro t ht
  let d (s : ℝ) := Real.exp (rate * s) * (m s - exponentialVarianceMemory rate f s)
  have hd (s : ℝ) (hs : s ∈ [[(0 : ℝ), t]]) : HasDerivAt d 0 s := by
    rw [uIcc_of_le ht.1] at hs
    have hs' : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
    have he : HasDerivAt (fun u : ℝ => Real.exp (rate * u)) (Real.exp (rate * s) * rate) s := by
      simpa only [id_eq, mul_one] using ((hasDerivAt_id s).const_mul rate).exp
    convert he.fun_mul ((hm s hs').sub (exponentialVarianceMemory_hasDerivAt hf rate s)) using 1
    simp only [Pi.sub_apply]
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (intervalIntegrable_const (c := (0 : ℝ)) (a := 0) (b := t) (μ := volume))
  have h₀ : d 0 = 0 := by simp [d, hm₀, exponentialVarianceMemory_zero]
  have hdt : d t = 0 := by simpa only [intervalIntegral.integral_zero, h₀, sub_zero] using h.symm
  exact sub_eq_zero.mp ((mul_eq_zero.mp hdt).resolve_left (Real.exp_pos _).ne')

/-- Drift of the lifted variance and memory vector. -/
noncomputable def smoothVarianceLiftDrift {ι : Type*} [Fintype ι]
    (K₀ κ v : ℝ) (b ℓ : ℝ → ℝ) (q rate : ι → ℝ) (t : ℝ)
    (z : ℝ × (ι → ℝ)) : ℝ × (ι → ℝ) :=
  (K₀ * (b t + v * ℓ t - (κ + ℓ 0) * max z.1 0 + ∑ i, q i * rate i * z.2 i),
    fun i => max z.1 0 - rate i * z.2 i)

/-- The drift is continuous in all state variables at each fixed time. -/
theorem smoothVarianceLiftDrift_continuous {ι : Type*} [Fintype ι]
    (K₀ κ v : ℝ) (b ℓ : ℝ → ℝ) (q rate : ι → ℝ) (t : ℝ) :
    Continuous (smoothVarianceLiftDrift K₀ κ v b ℓ q rate t) := by
  unfold smoothVarianceLiftDrift
  have hpos : Continuous (fun z : ℝ × (ι → ℝ) => max z.1 0) :=
    continuous_fst.max continuous_const
  have hz (i : ι) : Continuous (fun z : ℝ × (ι → ℝ) => z.2 i) :=
    (continuous_apply i).comp continuous_snd
  have hsum : Continuous (fun z : ℝ × (ι → ℝ) => ∑ i, q i * rate i * z.2 i) :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (hz i)
  exact (continuous_const.mul ((continuous_const.sub (continuous_const.mul hpos)).add hsum)).prodMk
    (continuous_pi fun i => hpos.sub (continuous_const.mul (hz i)))

/-- At a nonpositive variance state, occupied nonnegative memories and
nonnegative inputs make the drift point toward the nonnegative half-line. -/
theorem smoothVarianceLiftDrift_fst_nonneg {ι : Type*} [Fintype ι]
    {K₀ κ v : ℝ} {b ℓ : ℝ → ℝ} {q rate : ι → ℝ} {t : ℝ} {z : ℝ × (ι → ℝ)}
    (hK₀ : 0 ≤ K₀) (hv : 0 ≤ v) (hb : 0 ≤ b t) (hℓ : 0 ≤ ℓ t)
    (hq : ∀ i, 0 ≤ q i) (hrate : ∀ i, 0 ≤ rate i) (hz : z.1 ≤ 0) (hm : ∀ i, 0 ≤ z.2 i) :
    0 ≤ (smoothVarianceLiftDrift K₀ κ v b ℓ q rate t z).1 := by
  simp only [smoothVarianceLiftDrift, max_eq_right hz, mul_zero, sub_zero]
  exact mul_nonneg hK₀ (add_nonneg (add_nonneg hb (mul_nonneg hv hℓ))
    (Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (hq i) (hrate i)) (hm i)))

/-- Clipping the variance makes any square-root diffusion row vanish at a
nonpositive variance coordinate. -/
theorem smoothVarianceLift_diffusion_zero {z σ ρ : ℝ} (hz : z ≤ 0) :
    σ * Real.sqrt (max z 0) * ρ = 0 := by
  simp [max_eq_right hz]

/-- Replacing the history term by the exponential memory coordinates gives
exactly the history-dependent term in the lifted variance drift. -/
theorem exponentialVarianceMemory_sum_eq_history {ι : Type*} [Fintype ι]
    (q rate : ι → ℝ) {f : ℝ → ℝ} (hf : Continuous f) (t : ℝ) :
    let ℓ (u : ℝ) := ∑ i, q i * Real.exp (-(rate i * u))
    (∫ s in (0 : ℝ)..t, -(deriv ℓ (t - s)) * max (f s) 0) =
      ∑ i, q i * rate i * exponentialVarianceMemory (rate i) f t := by
  dsimp only
  have hderiv (u : ℝ) : -(deriv (fun v : ℝ => ∑ i, q i * Real.exp (-(rate i * v))) u) =
      ∑ i, q i * rate i * Real.exp (-(rate i * u)) := by
    have hd : HasDerivAt (fun v : ℝ => ∑ i, q i * Real.exp (-(rate i * v)))
        (∑ i, -(q i * rate i * Real.exp (-(rate i * u)))) u := by
      refine HasDerivAt.fun_sum fun i _ => ?_
      convert (hasDerivAt_exp_neg_mul (rate i) u).const_mul (q i) using 1
      ring
    rw [hd.deriv, Finset.sum_neg_distrib, neg_neg]
  simp_rw [hderiv, Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [exponentialVarianceMemory, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    ring
  · intro i _
    apply Continuous.intervalIntegrable
    fun_prop

/-- The lifted drift has uniform linear growth on a time set where the
input and the resolvent density are bounded. The state norm is the sup norm. -/
theorem smoothVarianceLiftDrift_linear_growth {ι : Type*} [Fintype ι]
    (K₀ κ v : ℝ) (b ℓ : ℝ → ℝ) (q rate : ι → ℝ) {S : Set ℝ} {B L : ℝ}
    (hB₀ : 0 ≤ B) (hL₀ : 0 ≤ L) (hb : ∀ t ∈ S, ‖b t‖ ≤ B) (hℓ : ∀ t ∈ S, ‖ℓ t‖ ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ S, ∀ z : ℝ × (ι → ℝ),
      ‖smoothVarianceLiftDrift K₀ κ v b ℓ q rate t z‖ ≤ C * (1 + ‖z‖) := by
  let C₀ := ‖K₀‖ * (B + ‖v‖ * L)
  let C₁ := ‖K₀‖ * (‖κ + ℓ 0‖ + ∑ i, ‖q i * rate i‖)
  let C₂ := 1 + ∑ i, ‖rate i‖
  let C := C₀ + C₁ + C₂ + 1
  have hC₀ : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  have hC₁ : 0 ≤ C₁ := by dsimp only [C₁]; positivity
  have hC₂ : 0 ≤ C₂ := by dsimp only [C₂]; positivity
  have hC : 0 < C := by dsimp only [C]; linarith
  have hle₀ : C₀ ≤ C := by dsimp only [C]; linarith
  have hle₁ : C₁ ≤ C := by dsimp only [C]; linarith
  have hle₂ : C₂ ≤ C := by dsimp only [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro t ht z
  let u := max z.1 0
  let R := ‖z‖
  have hR : 0 ≤ R := norm_nonneg _
  have hu : ‖u‖ ≤ R := by
    by_cases hz : z.1 ≤ 0
    · simpa only [u, max_eq_right hz, norm_zero] using hR
    · simpa only [u, max_eq_left (le_of_not_ge hz)] using (norm_fst_le z)
  have hm (i : ι) : ‖z.2 i‖ ≤ R := (norm_le_pi_norm z.2 i).trans (norm_snd_le z)
  have hsum : ‖∑ i, q i * rate i * z.2 i‖ ≤ (∑ i, ‖q i * rate i‖) * R := by
    calc
      _ ≤ ∑ i, ‖q i * rate i * z.2 i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖q i * rate i‖ * R := Finset.sum_le_sum fun i _ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hm i) (norm_nonneg _)
      _ = _ := (Finset.sum_mul _ _ _).symm
  have hconst : ‖b t + v * ℓ t‖ ≤ B + ‖v‖ * L := by
    exact (norm_add_le _ _).trans (add_le_add (hb t ht) (by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hℓ t ht) (norm_nonneg _)))
  have hU : ‖(κ + ℓ 0) * u‖ ≤ ‖κ + ℓ 0‖ * R := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hu (norm_nonneg _)
  have hinside : ‖b t + v * ℓ t - (κ + ℓ 0) * u + ∑ i, q i * rate i * z.2 i‖ ≤
      B + ‖v‖ * L + (‖κ + ℓ 0‖ + ∑ i, ‖q i * rate i‖) * R := by
    calc
      _ ≤ (‖b t + v * ℓ t‖ + ‖(κ + ℓ 0) * u‖) + ‖∑ i, q i * rate i * z.2 i‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ B + ‖v‖ * L + ‖κ + ℓ 0‖ * R + (∑ i, ‖q i * rate i‖) * R :=
        add_le_add (add_le_add hconst hU) hsum
      _ = _ := by ring
  apply norm_prod_le_iff.mpr
  constructor
  · change ‖K₀ * (b t + v * ℓ t - (κ + ℓ 0) * u + ∑ i, q i * rate i * z.2 i)‖ ≤ C * (1 + R)
    rw [norm_mul]
    calc
      _ ≤ ‖K₀‖ * (B + ‖v‖ * L + (‖κ + ℓ 0‖ + ∑ i, ‖q i * rate i‖) * R) :=
        mul_le_mul_of_nonneg_left hinside (norm_nonneg _)
      _ = C₀ + C₁ * R := by dsimp only [C₀, C₁]; ring
      _ ≤ C + C * R := add_le_add hle₀ (mul_le_mul_of_nonneg_right hle₁ hR)
      _ = _ := by ring
  · apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC.le (by positivity : 0 ≤ 1 + R))).mpr
    intro i
    change ‖u - rate i * z.2 i‖ ≤ C * (1 + R)
    have hi : ‖rate i‖ ≤ ∑ j, ‖rate j‖ :=
      Finset.single_le_sum (fun j _ => norm_nonneg (rate j)) (Finset.mem_univ i)
    calc
      _ ≤ ‖u‖ + ‖rate i‖ * ‖z.2 i‖ := by simpa only [norm_mul] using norm_sub_le u (rate i * z.2 i)
      _ ≤ R + (∑ j, ‖rate j‖) * R := add_le_add hu (mul_le_mul hi (hm i) (norm_nonneg _) (by positivity))
      _ = C₂ * R := by dsimp only [C₂]; ring
      _ ≤ C * R := mul_le_mul_of_nonneg_right hle₂ hR
      _ ≤ C * (1 + R) := mul_le_mul_of_nonneg_left (by linarith) hC.le

end RoughHeston

#print axioms RoughHeston.exponentialVarianceMemory_hasDerivAt
#print axioms RoughHeston.exponentialVarianceMemory_nonneg
#print axioms RoughHeston.smoothVarianceLiftDrift_continuous
#print axioms RoughHeston.smoothVarianceLiftDrift_fst_nonneg
#print axioms RoughHeston.smoothVarianceLift_diffusion_zero

#print axioms RoughHeston.exponentialVarianceMemory_sum_eq_history
#print axioms RoughHeston.smoothVarianceLiftDrift_linear_growth

#print axioms RoughHeston.exponentialVarianceMemory_eq_of_ode
