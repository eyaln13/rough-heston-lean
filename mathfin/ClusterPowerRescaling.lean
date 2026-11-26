import ClusterMomentInduction

namespace RoughHeston

/-- Combine the two beta integrals on one physical age block. All
dependence on the observation time, pulse mass and reference age is explicit. -/
theorem cluster_age_noise_power_scaling {α β e S t A D G J : ℝ}
    {m : ℕ} (hb : 0 ≤ β) (he : 0 ≤ e)
    (hS : 0 < S) (ht : 0 < t) (htS : t ≤ 2*S)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hG : 0 ≤ G) (hJ : 0 ≤ J) :
    (A*(t^β*J))^((m:ℝ)-1) *
      ((A*(D*e*S^(((m:ℝ)-1)*β)))*(t^(α+β-1)*G)) ≤
      (((A*J)^((m:ℝ)-1)*A*D*G)*2^((m:ℝ)*β))*
        e*t^(α-1)*S^((2*(m:ℝ)-1)*β) := by
  let d : ℝ := (m:ℝ)-1
  have h1 : (A*(t^β*J))^d = (A*J)^d*t^(β*d) := by
    rw [show A*(t^β*J) = (A*J)*t^β by ring,
      Real.mul_rpow (mul_nonneg hA hJ) (Real.rpow_nonneg ht.le _), ← Real.rpow_mul ht.le]
  have h2 : t^(β*d)*t^(α+β-1) = t^(α-1)*t^((m:ℝ)*β) := by
    rw [← Real.rpow_add ht, ← Real.rpow_add ht]; congr 1; dsimp [d]; ring
  have h3 : S^(d*β)*S^((m:ℝ)*β) = S^((2*(m:ℝ)-1)*β) := by
    rw [← Real.rpow_add hS]; congr 1; dsimp [d]; ring
  have h4 := Real.rpow_le_rpow ht.le htS (mul_nonneg m.cast_nonneg hb)
  rw [Real.mul_rpow (by norm_num : 0 ≤ (2:ℝ)) hS.le] at h4
  let L := (A*J)^d*(A*D*G)*e*t^(α-1)*S^(d*β)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  change (A*(t^β*J))^d * ((A*(D*e*S^(d*β)))*(t^(α+β-1)*G)) ≤ _
  rw [h1]
  calc
    _ = ((A*J)^d*A*D*G*e*S^(d*β))*(t^(β*d)*t^(α+β-1)) := by ring
    _ = L*t^((m:ℝ)*β) := by rw [h2]; dsimp [L]; ring
    _ ≤ L*(2^((m:ℝ)*β)*S^((m:ℝ)*β)) := mul_le_mul_of_nonneg_left h4 hL
    _ = _ := by rw [← h3]; dsimp [L,d]; ring

#print axioms cluster_age_noise_power_scaling

end RoughHeston
