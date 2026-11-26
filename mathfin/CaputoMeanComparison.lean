import CaputoPowerEvaluation
import CaputoMeanEquation

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RoughHeston

private theorem fractionalMemory_sub
    {α t : ℝ} {g f : ℝ → ℝ}
    (hg : IntervalIntegrable (fun u =>
      (α*u^(-α-1)/Real.Gamma (1-α))*(g t-g (t-u))) volume 0 t)
    (hf : IntervalIntegrable (fun u =>
      (α*u^(-α-1)/Real.Gamma (1-α))*(f t-f (t-u))) volume 0 t) :
    IntervalIntegrable (fun u => (α*u^(-α-1)/Real.Gamma (1-α))*
      ((g t-f t)-(g (t-u)-f (t-u)))) volume 0 t ∧
    fractionalMemory α (g 0-f 0) (fun s => g s-f s) t =
      fractionalMemory α (g 0) g t - fractionalMemory α (f 0) f t := by
  have he (u : ℝ) :
      (α*u^(-α-1)/Real.Gamma (1-α))*((g t-f t)-(g (t-u)-f (t-u))) =
      (α*u^(-α-1)/Real.Gamma (1-α))*(g t-g (t-u)) -
      (α*u^(-α-1)/Real.Gamma (1-α))*(f t-f (t-u)) := by ring
  constructor
  · simp_rw [he]
    exact hg.sub hf
  unfold fractionalMemory
  dsimp only
  simp_rw [he]
  rw [intervalIntegral.integral_sub hg hf]
  ring

/-- A uniformly bounded preterminal mean solving the Caputo equation
is bounded by a backward power wherever its killing coefficient has
the stated lower bound. The comparison constant is independent of the
terminal cutoff. -/
theorem caputo_mean_le_backwardPower {α p c C b d : ℝ}
    (hα : 0 < α) (hα' : α < 1) (hp : 0 < p) (hpα : p < α)
    (hc : caputoCoefficient α p < c) (hC : 0 ≤ C) (hd : 0 < d) :
    ∃ A : ℝ, 0 < A ∧
      ∀ {T S : ℝ} {f k : ℝ → ℝ}, d < T → S < T →
        ContinuousOn f (Icc (T-d) S) →
        (∀ t ∈ Icc 0 (T-d), f t ≤ C) →
        (∀ t ∈ Icc (T-d) S, c*(T-t)^(-α) ≤ k t) →
        (∀ t ∈ Icc (T-d) S, IntervalIntegrable (fun u =>
          (α*u^(-α-1)/Real.Gamma (1-α))*(f t-f (t-u))) volume 0 t) →
        (∀ t ∈ Icc (T-d) S, fractionalMemory α (f 0) f t + k t*f t = b) →
        ∀ t ∈ Icc (T-d) S, f t < A*(T-t)^p := by
  let D := c-caputoCoefficient α p
  let A := max ((C+1)/d^p) ((b+1)/(D*d^(p-α)))
  have hD : 0 < D := sub_pos.mpr hc
  have hdP : 0 < d^p := Real.rpow_pos_of_pos hd _
  have hdQ : 0 < d^(p-α) := Real.rpow_pos_of_pos hd _
  have hA : 0 < A := (div_pos (by linarith) hdP).trans_le (le_max_left _ _)
  have hA₁ : C+1 ≤ A*d^p := (div_le_iff₀ hdP).mp (le_max_left _ _)
  have hA₂ : b+1 ≤ A*(D*d^(p-α)) :=
    (div_le_iff₀ (mul_pos hD hdQ)).mp (le_max_right _ _)
  refine ⟨A, hA, ?_⟩
  intro T S f k hTd hST hfc hstart hkl hfi heq
  let g (t : ℝ) := A*(T-t)^p
  have hgc : Continuous g := continuous_const.mul
    ((Real.continuous_rpow_const hp.le).comp (continuous_const.sub continuous_id))
  have hstart' (t : ℝ) (ht : t ∈ Icc 0 (T-d)) : 0 < g t-f t := by
    have ht' : d ≤ T-t := by linarith [ht.2]
    have hcomp := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hd.le ht' hp.le) hA.le
    have hf := hstart t ht
    change 0 < A*(T-t)^p-f t
    linarith only [hcomp, hA₁, hf]
  have ha : 0 < T-d := sub_pos.mpr hTd
  have hgap := fractional_first_contact_comparison hα hα'
    (hstart' 0 ⟨le_rfl, ha.le⟩).le ha
    (hgc.continuousOn.sub hfc) (fun s hs => hstart' s (Ioc_subset_Icc_self hs)) ?_
  · intro t ht
    exact sub_pos.mp (hgap t ht)
  · intro t ht hz
    have ht₀ := ha.trans_le ht.1
    have htT := ht.2.trans_lt hST
    have hpos : 0 < T-t := sub_pos.mpr htT
    have hcont : ContDiffAt ℝ 1 g t := contDiffAt_const.mul
      ((Real.contDiffAt_rpow_const_of_ne hpos.ne').comp t (contDiffAt_const.sub contDiffAt_id))
    have hgi : IntegrableOn g (Ioc 0 t) := (hgc.intervalIntegrable 0 t).1
    have hI := (fractional_rl_hasDerivAt_memory hα hα' ht₀ hgc.measurable hgi hcont).1
    obtain ⟨hint, hmem⟩ := fractionalMemory_sub hI (hfi t ht)
    refine ⟨hint, ?_⟩
    change 0 ≤ fractionalMemory α (g 0 - f 0) (fun s => g s - f s) t
    rw [hmem]
    have hDg := backwardPower_caputo_lower_bound hα hα' hp hpα ht₀ htT
    have hs : fractionalMemory α (g 0) g t =
        A*fractionalMemory α (T^p) (fun v => (T-v)^p) t := by
      have he (u : ℝ) : (α*u^(-α-1)/Real.Gamma (1-α))*(g t-g (t-u)) =
        A*((α*u^(-α-1)/Real.Gamma (1-α))*((T-t)^p-(T-(t-u))^p)) := by
        dsimp [g]
        ring
      unfold fractionalMemory
      dsimp only
      simp_rw [he]
      rw [intervalIntegral.integral_const_mul]
      dsimp [g]
      rw [sub_zero]
      ring
    have hkg := mul_le_mul_of_nonneg_right (hkl t ht)
      (mul_nonneg hA.le (Real.rpow_nonneg hpos.le p))
    have he₁ : A*(-caputoCoefficient α p*(T-t)^(p-α)) + c*(T-t)^(-α)*g t =
        A*(D*(T-t)^(p-α)) := by
      change A*(-caputoCoefficient α p*(T-t)^(p-α)) +
        c*(T-t)^(-α)*(A*(T-t)^p) = _
      have he₀ : (T-t)^(-α)*(T-t)^p = (T-t)^(p-α) := by
        rw [← Real.rpow_add hpos, show -α+p=p-α by ring]
      rw [show c*(T-t)^(-α)*(A*(T-t)^p) =
        c*A*((T-t)^(-α)*(T-t)^p) by ring, he₀]
      dsimp [D]
      ring
    have hsmall : T-t ≤ d := by linarith [ht.1]
    have hnear := Real.rpow_le_rpow_of_nonpos hpos hsmall (sub_nonpos.mpr hpα.le)
    have htime := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnear hD.le) hA.le
    change g t-f t = 0 at hz
    have hz' : g t = f t := sub_eq_zero.mp hz
    change c*(T-t)^(-α)*g t ≤ k t*g t at hkg
    rw [hz'] at hkg he₁
    linarith only [heq t ht, add_le_add (mul_le_mul_of_nonneg_left hDg hA.le) hkg,
      hs, he₁, htime, hA₂]


/-- The backward comparison applies directly to a continuous solution
of the preterminal Volterra mean equation. -/
theorem caputo_mean_le_backwardPower_of_volterra {α p c C b d : ℝ}
    (hα : 1/2 < α) (hα' : α < 1) (hp : 0 < p) (hpα : p < α)
    (hc : caputoCoefficient α p < c) (hC : 0 ≤ C) (hd : 0 < d) :
    ∃ A : ℝ, 0 < A ∧
      ∀ {T S : ℝ} {f k : ℝ → ℝ}, d < T → S < T →
        ContinuousOn f (Ico 0 T) → ContinuousOn k (Ico 0 T) →
        (∀ s ∈ Ioo 0 T, ContDiffAt ℝ 1 k s) →
        (∀ t ∈ Icc 0 (T-d), f t ≤ C) →
        (∀ t ∈ Icc (T-d) S, c*(T-t)^(-α) ≤ k t) →
        (∀ s ∈ Ioo 0 T, f s = f 0 +
          volterraConvolution (fractionalK α) (fun u => b-k u*f u) s) →
        ∀ t ∈ Icc (T-d) S, f t < A*(T-t)^p := by
  have hα₀ : 0 < α := by linarith
  obtain ⟨A, hA, hbound⟩ := caputo_mean_le_backwardPower (b := b)
    hα₀ hα' hp hpα hc hC hd
  refine ⟨A, hA, ?_⟩
  intro T S f k hTd hST hf hk hk₁ hstart hkl hvol
  have hsub (t : ℝ) (ht : t ∈ Icc (T-d) S) : t ∈ Ioo 0 T :=
    ⟨(sub_pos.mpr hTd).trans_le ht.1, ht.2.trans_lt hST⟩
  have heq (t : ℝ) (ht : t ∈ Icc (T-d) S) :=
    caputo_mean_equation_of_volterra hα hα' (hsub t ht) hf hk hk₁ hvol
  refine hbound hTd hST (hf.mono ?_) hstart hkl (fun t ht => (heq t ht).2.1) ?_
  · intro t ht
    exact ⟨(hsub t ht).1.le, (hsub t ht).2⟩
  · intro t ht
    rw [(heq t ht).2.2, sub_add_cancel]

end RoughHeston

#print axioms RoughHeston.caputo_mean_le_backwardPower

#print axioms RoughHeston.caputo_mean_le_backwardPower_of_volterra
