import FractionalResolventLocalBounds
import FractionalConvolutionRegularity

open MeasureTheory Filter Set
open scoped Topology

namespace RoughHeston

/-- The mean value estimate also applies to the negative exponent α−1. -/
theorem cluster_real_power_increment {p x h : ℝ} (hp : p≤1) (hx : 0<x) (hh : 0≤h) :
    |(x+h)^p-x^p| ≤ (|p| *x^(p-1))*h := by
  have hd := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun u : ℝ => u^p) (f' := fun u => p*u^(p-1))
    (fun u (hu : u∈Icc x (x+h)) =>
      (Real.hasDerivAt_rpow_const (x:=u) (p:=p) (Or.inl (hx.trans_le hu.1).ne')).hasDerivWithinAt)
    (C := |p| *x^(p-1))
    (fun u (hu : u∈Ico x (x+h)) => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (Real.rpow_nonneg (hx.le.trans hu.1) _)]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hx hu.1 (sub_nonpos.mpr hp))
        (abs_nonneg _)) (x+h) ⟨le_add_of_nonneg_right hh, le_rfl⟩
  simpa only [Real.norm_eq_abs,add_sub_cancel_left] using hd

/-- Uniform Lipschitz control away from the singularity, with its
correct dependence on the distance x to the singularity. -/
theorem fractionalResolvent_kernel_increment_bound {α K H : ℝ}
    (ha : 0<α) (ha' : α<1) (hK : 0≤K) (hH : 0<H) :
    ∃ C : ℝ, 0≤C ∧ ∀ κ x h : ℝ, |κ|≤K → 0<x → 0≤h → x+h≤H →
      |fractionalSecondKindResolvent α κ (x+h)-fractionalSecondKindResolvent α κ x| ≤
        C*x^(α-2)*h := by
  let Z := H^α
  let L := 1+K*Z
  have hZ : 0 ≤ Z := Real.rpow_nonneg hH.le _
  have hL : 1 ≤ L := by dsimp [L]; linarith [mul_nonneg hK hZ]
  obtain ⟨A,hA,hLip⟩ := fractionalResolventProfile_lipschitz_on ha hL
  let P := fractionalResolventProfile α
  let B := A*L+|P 0|
  have hB : 0≤B := add_nonneg (mul_nonneg hA (by linarith)) (abs_nonneg _)
  refine ⟨|α-1| *B+A*K*|α| *Z, by positivity,?_⟩
  intro κ x h hk hx hh hxh
  let y := x+h
  have hxy : x≤y := le_add_of_nonneg_right hh
  have hy : 0<y := hx.trans_le hxy
  have hpow (s : ℝ) (hs : 0≤s) (hsH : s≤H) := Real.rpow_le_rpow hs hsH ha.le
  have hz (s : ℝ) (hs : 0≤s) (hsH : s≤H) : |-κ*s^α|≤L := by
    rw [abs_mul,abs_neg,abs_of_nonneg (Real.rpow_nonneg hs _)]
    exact (mul_le_mul hk (hpow s hs hsH) (Real.rpow_nonneg hs _) hK).trans
      (show K*Z≤L by dsimp [L]; linarith)
  let X := -κ*x^α
  let Y := -κ*y^α
  have hX := hz x hx.le (hxy.trans hxh)
  have hY := hz y hy.le hxh
  have hBY : |P Y| ≤ B := by
    have hl := hLip Y 0 hY (by simp; linarith)
    simp only [sub_zero] at hl
    calc
      _ = |(P Y-P 0)+P 0| := by rw [sub_add_cancel]
      _ ≤ |P Y-P 0|+|P 0| := abs_add_le _ _
      _ ≤ _ := by dsimp [B]; simpa only [sub_zero] using
        add_le_add (hl.trans (mul_le_mul_of_nonneg_left hY hA)) (le_refl |P 0|)
  have harg : |Y-X| ≤ K*((|α| *x^(α-1))*h) := by
    have he : Y-X = -κ*(y^α-x^α) := by dsimp [Y,X]; ring
    rw [he, abs_mul,abs_neg]
    exact mul_le_mul hk (cluster_real_power_increment ha'.le hx hh) (abs_nonneg _) hK
  have hprof : |P Y-P X| ≤ A*(K*((|α| *x^(α-1))*h)) :=
    (hLip Y X hY hX).trans (mul_le_mul_of_nonneg_left harg hA)
  have hlead := cluster_real_power_increment (p:=α-1) (by linarith) hx hh
  have hcross : x^(α-1)*x^(α-1) ≤ x^(α-2)*Z := by
    have he : x^(α-1)*x^(α-1) = x^(α-2)*x^α := by
      rw [←Real.rpow_add hx,←Real.rpow_add hx]; congr 1; ring
    rw [he]
    exact mul_le_mul_of_nonneg_left (hpow x hx.le (hxy.trans hxh)) (Real.rpow_nonneg hx.le _)
  rw [fractionalSecondKindResolvent_factor hy, fractionalSecondKindResolvent_factor hx]
  change |y^(α-1)*P Y-x^(α-1)*P X|≤_
  rw [show y^(α-1)*P Y-x^(α-1)*P X =
    (y^(α-1)-x^(α-1))*P Y+x^(α-1)*(P Y-P X) by ring]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul,abs_mul,abs_of_nonneg (Real.rpow_nonneg hx.le _)]
  have hfirst := mul_le_mul hlead hBY (abs_nonneg _) (by positivity)
  have hsecond := mul_le_mul_of_nonneg_left hprof (Real.rpow_nonneg hx.le (α-1))
  have hlast := mul_le_mul_of_nonneg_left hcross
    (show 0≤A*K*|α| *h by positivity)
  dsimp [y] at hfirst ⊢
  rw [show α-1-1=α-2 by ring] at hfirst
  linarith only [hfirst,hsecond,hlast]

#print axioms cluster_real_power_increment
#print axioms fractionalResolvent_kernel_increment_bound

end RoughHeston
