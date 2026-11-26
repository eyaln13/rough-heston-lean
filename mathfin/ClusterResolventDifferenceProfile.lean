import ClusterResolventIncrements
import ClusterKernelBetaBound

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston

/-- Interpolating the size and the Lipschitz bounds leaves an
integrable squared singularity when δ is below the Hurst index. -/
theorem cluster_kernel_difference_power {R : ℝ → ℝ} {α δ A C H : ℝ}
    (ha : α≤1) (hd : 0≤δ) (hd' : δ≤1)
    (hA : 0≤A) (hC : 0≤C)
    (hpoint : ∀ x ∈ Ioc 0 H, |R x|≤A*x^(α-1))
    (hinc : ∀ x h, 0<x → 0≤h → x+h≤H → |R (x+h)-R x|≤C*x^(α-2)*h)
    {x h : ℝ} (hx : 0<x) (hh : 0<h) (hH : x+h≤H) :
    |R (x+h)-R x| ≤ (2*A+C)*h^δ*x^(α-1-δ) := by
  have hxh := le_add_of_nonneg_right (a:=x) hh.le
  have h1 : 0≤h^δ := Real.rpow_nonneg hh.le _
  have h2 : 0≤x^(α-1-δ) := Real.rpow_nonneg hx.le _
  by_cases hle : h≤x
  · have hp := Real.rpow_le_rpow hh.le hle (sub_nonneg.mpr hd')
    have hxpow : x^(α-2)*x^(1-δ)=x^(α-1-δ) := by rw [←Real.rpow_add hx]; congr 1; ring
    have hhpow : h^δ*h^(1-δ)=h := by rw [←Real.rpow_add hh,show δ+(1-δ)=1 by ring,Real.rpow_one]
    calc
      _ ≤ C*x^(α-2)*h := hinc x h hx hh.le hH
      _ = C*h^δ*x^(α-2)*h^(1-δ) := by
        conv_lhs => rw [←hhpow]
        ring
      _ ≤ C*h^δ*x^(α-2)*x^(1-δ) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = C*h^δ*x^(α-1-δ) := by rw [←hxpow]; ring
      _ ≤ _ := by gcongr; linarith
  · have hge := (lt_of_not_ge hle).le
    have p := abs_sub (R (x+h)) (R x)
    have hs := add_le_add (hpoint _ ⟨hx.trans_le hxh,hH⟩) (hpoint _ ⟨hx,hxh.trans hH⟩)
    have hdec := Real.rpow_le_rpow_of_nonpos hx hxh (sub_nonpos.mpr ha)
    have hpow := Real.rpow_le_rpow hx.le hge hd
    have he : x^(α-1)=x^δ*x^(α-1-δ) := by rw [←Real.rpow_add hx]; congr 1; ring
    calc
      _ ≤ |R (x+h)|+|R x| := p
      _ ≤ A*(x+h)^(α-1)+A*x^(α-1) := hs
      _ ≤ 2*A*x^(α-1) := by linarith only [mul_le_mul_of_nonneg_left hdec hA]
      _ = 2*A*x^δ*x^(α-1-δ) := by rw [he]; ring
      _ ≤ 2*A*h^δ*x^(α-1-δ) := by gcongr
      _ ≤ _ := by gcongr; linarith

#print axioms cluster_kernel_difference_power

end RoughHeston
