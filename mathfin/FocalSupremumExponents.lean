import ClusterMomentInduction

namespace RoughHeston

/-- The dyadic order is chosen once for the roughness parameter. -/
theorem exists_focal_block_moment_order {α : ℝ} (hα : 1/2<α) (hα' : α<1) :
    let β := 2*α-1
    ∃ (δ : ℝ) (n : ℕ), 0<δ ∧ 0<β-2*δ ∧
      1<((2*2^n:ℕ):ℝ)*δ ∧
      0≤α-1+((2^n:ℕ):ℝ)*(β-2*δ) ∧ α≤((2*2^n:ℕ):ℝ)*β := by
  let β := 2*α-1
  have hβ : 0<β := by dsimp [β]; linarith
  let δ := β/4
  have hd : 0<δ := by dsimp [δ]; positivity
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (2/δ) (by norm_num : (1:ℝ)<2)
  have hnp : 2<(2:ℝ)^n*δ := (div_lt_iff₀ hd).mp hn
  refine ⟨δ,n,hd,by dsimp [δ]; linarith,?_,?_,?_⟩
  all_goals push_cast
  all_goals dsimp only [δ,β] at hnp ⊢
  all_goals nlinarith only [hnp,hα,hα']

#print axioms exists_focal_block_moment_order

end RoughHeston
