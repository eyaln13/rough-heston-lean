import RiemannLiouvilleMemory
import Mathlib.Analysis.Calculus.ContDiff.RCLike

open MeasureTheory Set Filter
open scoped Interval Topology

namespace RoughHeston

/-- The Caputo derivative of the backward power has the lower bound
used in the conditional-mean comparison. -/
theorem backwardPower_caputo_lower_bound {α p T s : ℝ}
    (hα : 0 < α) (hα' : α < 1) (hp : 0 < p) (hpα : p < α)
    (hs : 0 < s) (hsT : s < T) :
    -(caputoCoefficient α p) * (T-s) ^ (p-α) ≤
      fractionalMemory α (T ^ p) (fun v => (T-v) ^ p) s := by
  let B : ContDiffBump (0 : ℝ) :=
    ⟨(2*s+T)/3, (s+2*T)/3, by linarith, by linarith⟩
  let g (v : ℝ) := (T-v) ^ p
  let G (v : ℝ) := B v * (g v - g 0)
  have hgc (v : ℝ) (hv : v < T) : ContDiffAt ℝ 1 g v :=
    (Real.contDiffAt_rpow_const_of_ne (sub_pos.mpr hv).ne').comp v (contDiffAt_const.sub contDiffAt_id)
  have hG : ContDiff ℝ 1 G := by
    apply contDiff_iff_contDiffAt.mpr
    intro v
    by_cases hv : v < T
    · exact (B.contDiff.contDiffAt (x := v)).mul ((hgc v hv).sub contDiffAt_const)
    · have hthin : B.rOut < dist v 0 := by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (by linarith)]
        change (s+2*T)/3 < v
        linarith
      have he : ∀ᶠ z in 𝓝 v, B.rOut < dist z 0 :=
        continuousAt_const.eventually_lt (continuousAt_id.dist continuousAt_const) hthin
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [he] with z hz
      simp [G, B.zero_of_le_dist hz.le]
  have hGcap : HasCompactSupport G := B.hasCompactSupport.mul_right
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hGcap hG (by simp)
  have hloc (v : ℝ) (hv : v ∈ Icc 0 s) :
      G =ᶠ[𝓝 v] fun z => g z - g 0 := by
    have hthin : dist v 0 < B.rIn := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hv.1]
      change v < (2*s+T)/3
      linarith [hv.2]
    have he : ∀ᶠ z in 𝓝 v, dist z 0 < B.rIn :=
      (continuousAt_id.dist continuousAt_const).eventually_lt continuousAt_const hthin
    filter_upwards [he] with z hz
    simp [G, B.one_of_mem_closedBall (Metric.mem_closedBall.mpr hz.le)]
  have hd (v : ℝ) (hv : v ∈ Icc 0 s) : deriv G v = -p * (T-v) ^ (p-1) := by
    have hvT : v < T := hv.2.trans_lt hsT
    have hh := (Real.hasDerivAt_rpow_const (x := T-v) (p := p)
      (Or.inl (sub_pos.mpr hvT).ne')).comp v
        ((hasDerivAt_const v T).sub (hasDerivAt_id v))
    have hd' : HasDerivAt (fun z => g z - g 0) (-p * (T-v) ^ (p-1)) v := by
      simpa [g, neg_mul] using hh.sub_const (g 0)
    exact (hd'.congr_of_eventuallyEq (hloc v hv)).deriv
  have hGval (v : ℝ) (hv : v ∈ Icc 0 s) : G v = g v - g 0 := (hloc v hv).eq_of_nhds
  have hG0 : G 0 = 0 := by rw [hGval 0 ⟨le_rfl, hs.le⟩, sub_self]
  have hM : fractionalMemory α 0 G s = fractionalMemory α (g 0) g s := by
    unfold fractionalMemory
    rw [hGval s ⟨hs.le, le_rfl⟩, sub_zero]
    congr 1
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hs.le] at hu
    dsimp only
    rw [hGval (s-u) ⟨sub_nonneg.mpr hu.2, sub_le_self _ hu.1⟩]
    ring
  have hS := fractional_memory_integral_of_deriv hα hα' hs hG hK hG0
  have heq : fractionalMemory α (g 0) g s =
      -(p / Real.Gamma (1-α)) *
        ∫ u in Ioc (0 : ℝ) s, u ^ (-α) * ((T-s)+u) ^ (p-1) := by
    rw [← hM, ← hS, intervalIntegral.integral_of_le hs.le, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    dsimp only
    rw [hd (s-u) ⟨sub_nonneg.mpr hu.2, sub_le_self _ hu.1.le⟩,
      fractionalL, ite_eq_right (not_le.mpr hu.1), show T-(s-u) = T-s+u by ring]
    ring
  have hg0 : g 0 = T ^ p := by simp [g]
  rw [hg0] at heq
  change _ ≤ fractionalMemory α (T ^ p) g s
  rw [heq, ← intervalIntegral.integral_of_le hs.le]
  exact caputo_terminal_power_bound hα' hp hpα (sub_pos.mpr hsT) hs.le

end RoughHeston

#print axioms RoughHeston.backwardPower_caputo_lower_bound
