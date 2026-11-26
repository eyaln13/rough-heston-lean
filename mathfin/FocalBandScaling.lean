import ClusterPowerRescaling

namespace RoughHeston

/-- Put the two observation-window bounds on the same time scale. -/
theorem cluster_band_scaling {α β δ C A D e S h a : ℝ} {m : ℕ}
    (hC : 0≤C) (hA : 0≤A) (hD : 0≤D) (he : 0≤e) (hS : 0<S) (hh : 0<h)
    (ha : 0≤a) (haS : a≤2*S) (hhS : h≤2*S) (hb : β=2*α-1)
    (hz : 0≤α-1+(m:ℝ)*(β-2*δ)) :
    let z := α-1+(m:ℝ)*(β-2*δ)
    let W := e*S^((2*(m:ℝ))*β-α-(2*(m:ℝ))*δ)*h^((2*(m:ℝ))*δ)
    (C*(A*h^(2*δ))^m*(D*e*S^(((m:ℝ)-1)*β))*a^z ≤ (C*A^m*D*2^z)*W) ∧
    (C*A^m*(D*e*S^(((m:ℝ)-1)*β))*h^(α-1+(m:ℝ)*β) ≤ (C*A^m*D*2^z)*W) := by
  let z := α-1+(m:ℝ)*(β-2*δ)
  let k := 2*(m:ℝ)*δ
  let b := ((m:ℝ)-1)*β
  have htotal : b+z=2*(m:ℝ)*β-α-2*(m:ℝ)*δ := by dsimp [b,z]; rw [hb]; ring
  have hxp : S^b*S^z=S^(2*(m:ℝ)*β-α-2*(m:ℝ)*δ) := by rw [←Real.rpow_add hS,htotal]
  have hp : (h^(2*δ))^m=h^k := by rw [←Real.rpow_mul_natCast hh.le]; congr 1; dsimp [k]; ring
  have hnew : h^(α-1+(m:ℝ)*β)=h^k*h^z := by rw [←Real.rpow_add hh]; congr 1; dsimp [k,z]; ring
  have hcase {x : ℝ} (hx : 0≤x) (hxS : x≤2*S) :
      (C*A^m*D*e*S^b*h^k)*x^z ≤ (C*A^m*D*2^z)*(e*S^(2*(m:ℝ)*β-α-2*(m:ℝ)*δ)*h^k) := by
    have hlt := Real.rpow_le_rpow hx hxS hz
    rw [Real.mul_rpow (by norm_num : 0≤(2:ℝ)) hS.le] at hlt
    have hn : 0 ≤ C*A^m*D*e*S^b*h^k := by positivity
    refine (mul_le_mul_of_nonneg_left hlt hn).trans_eq ?_
    rw [←hxp]; ring
  dsimp only
  constructor
  · rw [mul_pow,hp]; convert hcase ha haS using 1 <;> dsimp [b,k,z] <;> ring
  · rw [hnew]; convert hcase hh.le hhS using 1 <;> dsimp [b,k,z] <;> ring

#print axioms cluster_band_scaling

end RoughHeston
