import SmoothCoupledDrift

/-! Deterministic cancellation identifying the first-kind resolvent
of a finite exponential variance lift. -/

open MeasureTheory Set
open scoped Interval

namespace RoughHeston

variable {η : Type*} [Fintype η]

/-- The inverse associated with the atom at zero and the finite
exponential density, evaluated on the centered path. -/
noncomputable def smoothExponentialInverse (K₀ ℓ₀ : ℝ) (q rate : η → ℝ)
    (v : ℝ) (V : ℝ → ℝ) (t : ℝ) : ℝ :=
  (V t-v)/K₀ + ∫ r in (0 : ℝ)..t, smoothExponentialResolvent ℓ₀ q rate (t-r)*(V r-v)

theorem integral_exponentialVarianceMemory_deriv {V : ℝ → ℝ} (hV : Continuous V)
    (rate t : ℝ) :
    (∫ r in (0 : ℝ)..t, (max (V r) 0 - rate*exponentialVarianceMemory rate V r)) =
      exponentialVarianceMemory rate V t := by
  have hC : Continuous (exponentialVarianceMemory rate V) :=
    continuous_iff_continuousAt.2 fun r => (exponentialVarianceMemory_hasDerivAt hV rate r).continuousAt
  have hi : Continuous (fun r => max (V r) 0 - rate*exponentialVarianceMemory rate V r) :=
    (hV.max continuous_const).sub (continuous_const.mul hC)
  simpa only [exponentialVarianceMemory_zero, sub_zero] using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r _ => exponentialVarianceMemory_hasDerivAt hV rate r) (hi.intervalIntegrable (μ := volume) 0 t))

/-- The drift, with its memory terms, cancels upon applying the first-kind
resolvent. Here the variance path is nonnegative on the integration interval. -/
theorem smoothExponentialInverse_eq_rescaled_martingale {K₀ κ ℓ₀ v t M : ℝ}
    (hK : K₀ ≠ 0) (ht : 0 ≤ t) (q rate : η → ℝ) {V β : ℝ → ℝ}
    (hV : Continuous V) (hV₀ : ∀ r ∈ Icc 0 t, 0 ≤ V r)
    (hβ : IntervalIntegrable β volume 0 t)
    (hLift : V t =
      v + K₀ * (∫ r in (0 : ℝ)..t,
        β r + v*smoothExponentialResolvent ℓ₀ q rate r -
          (κ+smoothExponentialResolvent ℓ₀ q rate 0)*V r +
          ∑ j, q j*rate j*exponentialVarianceMemory (rate j) V r) + M) :
    smoothExponentialInverse K₀ ℓ₀ q rate v V t =
      M/K₀ + ∫ r in (0 : ℝ)..t, (β r - κ*V r) := by
  let L := smoothExponentialResolvent ℓ₀ q rate
  let m (j : η) := exponentialVarianceMemory (rate j) V
  have hL : Continuous L := continuous_smoothExponentialResolvent ℓ₀ q rate
  have hm (j : η) : Continuous (m j) :=
    continuous_iff_continuousAt.2 fun r => (exponentialVarianceMemory_hasDerivAt hV (rate j) r).continuousAt
  have hVi := hV.intervalIntegrable (μ := volume) 0 t
  have hLi := hL.intervalIntegrable (μ := volume) 0 t
  have hLflip : Continuous (fun r : ℝ => L (t-r)) :=
    hL.comp (continuous_const.sub continuous_id : Continuous (fun r : ℝ => t-r))
  have hmem (j : η) :
      rate j*(∫ r in (0 : ℝ)..t, m j r) = (∫ r in (0 : ℝ)..t, V r) - m j t := by
    have e := integral_exponentialVarianceMemory_deriv hV (rate j) t
    change (∫ r in (0 : ℝ)..t, (max (V r) 0 - rate j*m j r)) = m j t at e
    rw [intervalIntegral.integral_congr (g := fun r => V r - rate j*m j r) (fun r hr => by
      rw [uIcc_of_le ht] at hr
      rw [max_eq_left (hV₀ r hr)]),
      intervalIntegral.integral_sub hVi ((hm j).intervalIntegrable (μ := volume) 0 t |>.const_mul _),
      intervalIntegral.integral_const_mul] at e
    linarith
  have hExp (j : η) :
      (∫ r in (0 : ℝ)..t, Real.exp (-(rate j*(t-r))) * V r) = m j t := by
    unfold m exponentialVarianceMemory
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le ht] at hr
    simp only [max_eq_left (hV₀ r hr)]
  have hprod :
      (∫ r in (0 : ℝ)..t, L (t-r)*V r) =
        ℓ₀*(∫ r in (0 : ℝ)..t, V r) + ∑ j, q j*m j t := by
    have hExpC (j : η) : Continuous (fun r : ℝ => Real.exp (-(rate j*(t-r))) * V r) := by fun_prop
    have hSum : IntervalIntegrable (fun r : ℝ => ∑ j, q j*(Real.exp (-(rate j*(t-r))) * V r))
        volume 0 t := (continuous_finsetSum _ fun j _ => continuous_const.mul (hExpC j)).intervalIntegrable (μ := volume) 0 t
    calc
      _ = ∫ r in (0 : ℝ)..t, (ℓ₀*V r + ∑ j, q j*(Real.exp (-(rate j*(t-r))) * V r)) := by
        apply intervalIntegral.integral_congr
        intro r _
        simp [L, smoothExponentialResolvent, add_mul, Finset.sum_mul, mul_assoc]
      _ = _ := by
        rw [intervalIntegral.integral_add (hVi.const_mul _) hSum, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_finsetSum]
        · congr 1
          exact Finset.sum_congr rfl fun j _ => by rw [intervalIntegral.integral_const_mul, hExp j]
        · intro j _
          exact (hExpC j).intervalIntegrable (μ := volume) 0 t |>.const_mul _
  have hFlip : (∫ r in (0 : ℝ)..t, L (t-r)) = ∫ r in (0 : ℝ)..t, L r := by
    simpa only [sub_self, sub_zero] using
      (intervalIntegral.integral_comp_sub_left (f := L) (a := 0) (b := t) t)
  have hConvolution :
      (∫ r in (0 : ℝ)..t, L (t-r)*(V r-v)) =
        ℓ₀*(∫ r in (0 : ℝ)..t, V r) + (∑ j, q j*m j t) -
          v*(∫ r in (0 : ℝ)..t, L r) := by
    have hc : (∫ r in (0 : ℝ)..t, L (t-r)*v) = v*(∫ r in (0 : ℝ)..t, L r) := by
      simp_rw [mul_comm (L _) v]
      rw [intervalIntegral.integral_const_mul, hFlip]
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub, hprod, hc]
    · exact (hLflip.mul hV).intervalIntegrable (μ := volume) 0 t
    · exact (hLflip.mul continuous_const).intervalIntegrable (μ := volume) 0 t
  have hsum :
      (∫ r in (0 : ℝ)..t, ∑ j, q j*rate j*m j r) =
        (∑ j, q j)*(∫ r in (0 : ℝ)..t, V r) - (∑ j, q j*m j t) := by
    rw [intervalIntegral.integral_finsetSum]
    · simp_rw [mul_assoc (q _) (rate _), intervalIntegral.integral_const_mul, hmem, mul_sub,
        Finset.sum_sub_distrib, ← Finset.sum_mul]
    · intro j _
      exact (hm j).intervalIntegrable (μ := volume) 0 t |>.const_mul _
  have hAtZero : L 0 = ℓ₀ + ∑ j, q j := by simp [L, smoothExponentialResolvent]
  change V t = v + K₀ * (∫ r in (0 : ℝ)..t,
    β r + v*L r - (κ+L 0)*V r + ∑ j, q j*rate j*m j r) + M at hLift
  have hd : IntervalIntegrable (fun r => ∑ j, q j*rate j*m j r) volume 0 t :=
    (continuous_finsetSum _ fun j _ => continuous_const.mul (hm j)).intervalIntegrable (μ := volume) 0 t
  rw [intervalIntegral.integral_add
      ((hβ.add (hLi.const_mul _)).sub (hVi.const_mul _)) hd,
    intervalIntegral.integral_sub (hβ.add (hLi.const_mul _)) (hVi.const_mul _),
    intervalIntegral.integral_add hβ (hLi.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hsum, hAtZero] at hLift
  unfold smoothExponentialInverse
  change (V t-v)/K₀ + (∫ r in (0 : ℝ)..t, L (t-r)*(V r-v)) = _
  rw [hConvolution, intervalIntegral.integral_sub hβ (hVi.const_mul _),
    intervalIntegral.integral_const_mul]
  have e : V t-v = K₀ * ((∫ r in (0 : ℝ)..t, β r) + v*(∫ r in (0 : ℝ)..t, L r) -
      (κ+ℓ₀+(∑ j, q j))*(∫ r in (0 : ℝ)..t, V r) +
      ((∑ j, q j)*(∫ r in (0 : ℝ)..t, V r) - (∑ j, q j*m j t))) + M := by
    nlinarith [hLift]
  rw [e, add_div, mul_div_cancel_left₀ _ hK]
  ring

#print axioms RoughHeston.integral_exponentialVarianceMemory_deriv
#print axioms RoughHeston.smoothExponentialInverse_eq_rescaled_martingale

end RoughHeston
