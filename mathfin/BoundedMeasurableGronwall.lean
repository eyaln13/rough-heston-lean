import IntegralGronwallBound

/-! Integral absorption for bounded measurable moment functions. -/

open Set MeasureTheory

namespace RoughHeston

private theorem integral_exp_const_mul {kExp t : ℝ} (hRate : kExp ≠ 0) :
    (∫ u in (0 : ℝ)..t, Real.exp (kExp * u)) = (Real.exp (kExp * t) - 1) / kExp := by
  have hcont : Continuous (fun u : ℝ => Real.exp (kExp * u)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hderiv (u : ℝ) :
      HasDerivAt (fun u : ℝ => Real.exp (kExp * u) / kExp) (Real.exp (kExp * u)) u := by
    convert (((hasDerivAt_id u).const_mul kExp).exp.div_const kExp) using 1 <;> simp [hRate]
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hderiv u) (hcont.intervalIntegrable 0 t)
  rw [he, mul_zero, Real.exp_zero]
  ring

/-- A bounded measurable nonnegative function satisfying a linear
integral inequality has a bound independent of its initial crude bound. -/
theorem le_uniform_exp_of_bounded_measurable_integral_inequality {f : ℝ → ℝ}
    (hf : Measurable f) {A K T L : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hT : 0 ≤ T) (hLf : ∀ t ∈ Icc 0 T, 0 ≤ f t ∧ f t ≤ L)
    (hbound : ∀ t ∈ Icc 0 T, f t ≤ A + K * (∫ u in 0..t, f u))
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    f t ≤ 2 * A * Real.exp ((2*K+1) * T) := by
  let kExp := 2*K+1
  let g (u : ℝ) := Real.exp (-(kExp*u)) * f u
  let S := sSup (g '' Icc 0 T)
  have hRate : 0 < kExp := by dsimp [kExp]; positivity
  have hSet : (g '' Icc 0 T).Nonempty := ⟨g 0, mem_image_of_mem g ⟨le_rfl, hT⟩⟩
  have hexp_le_one (u : ℝ) (hu : 0 ≤ u) : Real.exp (-(kExp*u)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr (mul_nonneg hRate.le hu))
  have hG : BddAbove (g '' Icc 0 T) := by
    refine ⟨L, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    change Real.exp (-(kExp*u)) * f u ≤ L
    exact ((mul_le_mul_of_nonneg_right (hexp_le_one u hu.1) (hLf u hu).1).trans_eq (one_mul _)).trans
      (hLf u hu).2
  have hGS (u : ℝ) (hu : u ∈ Icc 0 T) : g u ≤ S :=
    le_csSup hG (mem_image_of_mem g hu)
  have hS0 : 0 ≤ S := (mul_nonneg (Real.exp_pos _).le (hLf 0 ⟨le_rfl, hT⟩).1).trans
    (hGS 0 ⟨le_rfl, hT⟩)
  have hfUpper (u : ℝ) (hu : u ∈ Icc 0 T) : f u ≤ S * Real.exp (kExp*u) := by
    have hh := mul_le_mul_of_nonneg_right (hGS u hu) (Real.exp_pos (kExp*u)).le
    have he : Real.exp (-(kExp*u)) * Real.exp (kExp*u) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc
      _ = f u * 1 := by simp
      _ = f u * (Real.exp (-(kExp*u)) * Real.exp (kExp*u)) := by rw [he]
      _ = g u * Real.exp (kExp*u) := by dsimp [g]; ring
      _ ≤ _ := hh
  have hStep (u : ℝ) (hu : u ∈ Icc 0 T) : g u ≤ A + (K / kExp) * S := by
    have hInt : IntervalIntegrable f volume 0 u := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hu.1]
      have hbounded : ∀ᵐ x ∂volume.restrict (Ioc 0 u), ‖f x‖ ≤ L := by
        filter_upwards [ae_restrict_mem (μ := volume) (s := Ioc 0 u) measurableSet_Ioc] with x hx
        have hy := hLf x ⟨hx.1.le, hx.2.trans hu.2⟩
        rw [Real.norm_of_nonneg hy.1]
        exact hy.2
      exact (integrable_const L).mono' hf.stronglyMeasurable.aestronglyMeasurable hbounded
    have hExp : Continuous (fun r : ℝ => S * Real.exp (kExp*r)) :=
      continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    have hI : (∫ r in 0..u, f r) ≤ S * ((Real.exp (kExp*u) - 1) / kExp) := by
      have h := intervalIntegral.integral_mono_on hu.1 hInt (hExp.intervalIntegrable 0 u)
        (fun r hr => hfUpper r ⟨hr.1, hr.2.trans hu.2⟩)
      rwa [intervalIntegral.integral_const_mul, integral_exp_const_mul hRate.ne'] at h
    let e := Real.exp (-(kExp*u))
    have he : 0 ≤ e := (Real.exp_pos _).le
    have he1 : e ≤ 1 := hexp_le_one u hu.1
    have heE : e * Real.exp (kExp*u) = 1 := by
      dsimp [e]
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have heMul : e * ((Real.exp (kExp*u) - 1) / kExp) = (1 - e) / kExp := by
      rw [← mul_div_assoc, mul_sub, heE, mul_one]
    have hFrac : (1 - e) / kExp ≤ 1 / kExp :=
      div_le_div_of_nonneg_right (sub_le_self _ he) hRate.le
    calc
      _ ≤ e * (A + K * (∫ r in 0..u, f r)) :=
        mul_le_mul_of_nonneg_left (hbound u hu) he
      _ ≤ e * (A + K * (S * ((Real.exp (kExp*u) - 1) / kExp))) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hI hK)) he
      _ = e * A + (K*S) * (e * ((Real.exp (kExp*u) - 1) / kExp)) := by ring
      _ ≤ A + (K / kExp) * S := by
        rw [heMul]
        have h := mul_le_mul_of_nonneg_left hFrac (mul_nonneg hK hS0)
        have hA' : e*A ≤ A :=
          (mul_le_mul_of_nonneg_right he1 hA).trans_eq (one_mul _)
        have heq : (K*S) * (1 / kExp) = (K / kExp) * S := by ring
        rw [heq] at h
        exact add_le_add hA' h
  have hS : S ≤ A + (K / kExp) * S := csSup_le hSet (by
    rintro _ ⟨u, hu, rfl⟩
    exact hStep u hu)
  have hRat : K / kExp ≤ 1/2 := (div_le_iff₀ hRate).2 (by dsimp [kExp]; linarith)
  have hS2 : S ≤ 2*A := by
    have h := mul_le_mul_of_nonneg_right hRat hS0
    linarith
  calc
    _ ≤ S * Real.exp (kExp*t) := hfUpper t ht
    _ ≤ 2*A * Real.exp (kExp*t) := mul_le_mul_of_nonneg_right hS2 (Real.exp_pos _).le
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hRate.le)) (by positivity)

#print axioms RoughHeston.le_uniform_exp_of_bounded_measurable_integral_inequality

end RoughHeston
