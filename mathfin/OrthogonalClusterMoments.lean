import StochasticCovariation

open MeasureTheory Set Filter
open scoped Topology ProbabilityTheory

namespace RoughHeston

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

private theorem cluster_integrable_mul {U V : Ω → ℝ}
    (hU : MemLp U 2 μ) (hV : MemLp V 2 μ) : Integrable (U * V) μ :=
  memLp_one_iff_integrable.mp (show MemLp (U * V) 1 μ from hU.mul hV)

private theorem cluster_integral_grid_zero [Preorder ι] [IsFiniteMeasure μ]
    {𝒢 : Filtration ι m} (grid : ℕ →o ι) {X : ι → Ω → ℝ}
    (hX : Martingale X 𝒢 μ) (hX₂ : ∀ t, MemLp (X t) 2 μ) {a : ℕ → Ω → ℝ}
    (ha : ∀ k, StronglyMeasurable[𝒢 (grid k)] (a k))
    (haTop : ∀ k, MemLp (a k) ⊤ μ) (n : ℕ) :
    (∫ ω, gridIntegral grid a X n ω ∂μ) = 0 := by
  have hM := grid_integral_martingale grid hX hX₂ ha haTop
  have he := hM.setIntegral_eq (Nat.zero_le n) (s := univ) MeasurableSet.univ
  simpa only [Measure.restrict_univ, gridIntegral, runningSum_zero, Pi.zero_apply, integral_zero]
    using he.symm

private theorem cluster_integral_mul_zero_of_L2_limits {U V : Ω → ℝ}
    {Un Vn : ℕ → Ω → ℝ} (hU : MemLp U 2 μ) (hV : MemLp V 2 μ)
    (hUn : ∀ n, MemLp (Un n) 2 μ) (hVn : ∀ n, MemLp (Vn n) 2 μ)
    (hlU : Tendsto (fun n => eLpNorm (Un n - U) 2 μ) atTop (𝓝 0))
    (hlV : Tendsto (fun n => eLpNorm (Vn n - V) 2 μ) atTop (𝓝 0))
    (hzero : ∀ n, (∫ ω, Un n ω * Vn n ω ∂μ) = 0) :
    (∫ ω, U ω * V ω ∂μ) = 0 := by
  have ht := tendsto_integral_of_L1' (U * V)
    (Eventually.of_forall (fun n => cluster_integrable_mul (hUn n) (hVn n)))
    (product_L1_limit_of_L2_limits hU hV hUn hVn hlU hlV)
  have ht₀ : Tendsto (fun n => ∫ ω, Un n ω * Vn n ω ∂μ) atTop (𝓝 0) := by
    simp only [hzero]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique ht ht₀

/-- Mean-square limits of simple integrals against orthogonal martingales
are centered and have zero cross expectation. The integrals use common grids
and can use different bounded predictable weights on every grid. -/
theorem orthogonal_grid_limits_mean_and_cross [Preorder ι] [IsFiniteMeasure μ]
    {𝒢 : Filtration ι m} (grid : ℕ → ℕ →o ι) (length : ℕ → ℕ)
    {X Y : ι → Ω → ℝ} (hX : Martingale X 𝒢 μ) (hY : Martingale Y 𝒢 μ)
    (hXY : Martingale (fun t => X t * Y t) 𝒢 μ)
    (hX₂ : ∀ t, MemLp (X t) 2 μ) (hY₂ : ∀ t, MemLp (Y t) 2 μ)
    {a b : ℕ → ℕ → Ω → ℝ}
    (ha : ∀ n k, StronglyMeasurable[𝒢 (grid n k)] (a n k))
    (hb : ∀ n k, StronglyMeasurable[𝒢 (grid n k)] (b n k))
    (haTop : ∀ n k, MemLp (a n k) ⊤ μ) (hbTop : ∀ n k, MemLp (b n k) ⊤ μ)
    {U V : Ω → ℝ} (hU : MemLp U 2 μ) (hV : MemLp V 2 μ)
    (hlU : Tendsto (fun n => eLpNorm (gridIntegral (grid n) (a n) X (length n) - U) 2 μ)
      atTop (𝓝 0))
    (hlV : Tendsto (fun n => eLpNorm (gridIntegral (grid n) (b n) Y (length n) - V) 2 μ)
      atTop (𝓝 0)) :
    (∫ ω, U ω ∂μ) = 0 ∧ (∫ ω, V ω ∂μ) = 0 ∧ (∫ ω, U ω * V ω ∂μ) = 0 := by
  have hUn n := grid_integral_memLp_two (grid n) hX₂ (haTop n) (length n)
  have hVn n := grid_integral_memLp_two (grid n) hY₂ (hbTop n) (length n)
  have hconst : MemLp (fun _ : Ω => (1 : ℝ)) 2 μ := memLp_const _
  have hclim : Tendsto (fun _ : ℕ => eLpNorm ((fun _ : Ω => (1 : ℝ)) - fun _ => 1) 2 μ)
      atTop (𝓝 0) := by simpa only [sub_self, eLpNorm_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  refine ⟨?_, ?_, cluster_integral_mul_zero_of_L2_limits hU hV hUn hVn hlU hlV ?_⟩
  · simpa only [mul_one] using
      cluster_integral_mul_zero_of_L2_limits hU hconst hUn (fun _ => hconst) hlU hclim
        (fun n => by
          simpa only [mul_one] using
            cluster_integral_grid_zero (grid n) hX hX₂ (ha n) (haTop n) (length n))
  · simpa only [mul_one] using
      cluster_integral_mul_zero_of_L2_limits hV hconst hVn (fun _ => hconst) hlV hclim
        (fun n => by
          simpa only [mul_one] using
            cluster_integral_grid_zero (grid n) hY hY₂ (hb n) (hbTop n) (length n))
  · intro n
    have h := grid_integral_cross_isometry (grid n) hX hY
      (C := fun _ => 0) (by simpa only [sub_zero] using hXY) hX₂ hY₂
      (ha n) (hb n) (haTop n) (hbTop n) (length n)
    simpa using h

private theorem cluster_gridIntegral_truncate [Preorder ι] (grid : ℕ →o ι)
    (a : ℕ → Ω → ℝ) (X : ι → Ω → ℝ) (r n : ℕ) :
    gridIntegral grid (fun k => if k < r then a k else 0) X n =
      gridIntegral grid a X (min n r) := by
  induction n with
  | zero => simp [gridIntegral]
  | succ n ih =>
    rw [gridIntegral_succ, ih]
    by_cases hn : n < r
    · rw [ite_eq_left hn, min_eq_left hn.le, min_eq_left hn, gridIntegral_succ]
    · simp only [ite_eq_right hn, zero_mul, add_zero]
      rw [min_eq_right (by omega : r ≤ n), min_eq_right (by omega : r ≤ n + 1)]

/-- The two limits may concern different observation times. Each sum ends
at its own grid index, and it is extended by zero weights on the remaining
cells of the common grid. The deterministic weights may depend on both the
observation time and the partition index. -/
theorem orthogonal_deterministic_grid_limits_mean_and_cross [Preorder ι] [IsFiniteMeasure μ]
    {𝒢 : Filtration ι m} (grid : ℕ → ℕ →o ι) (r s : ℕ → ℕ)
    {X Y : ι → Ω → ℝ} (hX : Martingale X 𝒢 μ) (hY : Martingale Y 𝒢 μ)
    (hXY : Martingale (fun t => X t * Y t) 𝒢 μ)
    (hX₂ : ∀ t, MemLp (X t) 2 μ) (hY₂ : ∀ t, MemLp (Y t) 2 μ)
    (a b : ℕ → ℕ → ℝ) {U V : Ω → ℝ} (hU : MemLp U 2 μ) (hV : MemLp V 2 μ)
    (hlU : Tendsto (fun n => eLpNorm (gridIntegral (grid n) (fun k _ => a n k) X (r n) - U) 2 μ)
      atTop (𝓝 0))
    (hlV : Tendsto (fun n => eLpNorm (gridIntegral (grid n) (fun k _ => b n k) Y (s n) - V) 2 μ)
      atTop (𝓝 0)) :
    (∫ ω, U ω ∂μ) = 0 ∧ (∫ ω, V ω ∂μ) = 0 ∧ (∫ ω, U ω * V ω ∂μ) = 0 := by
  let a' (n k : ℕ) (_ : Ω) := if k < r n then a n k else 0
  let b' (n k : ℕ) (_ : Ω) := if k < s n then b n k else 0
  have heqa (n : ℕ) : gridIntegral (grid n) (a' n) X (max (r n) (s n)) =
      gridIntegral (grid n) (fun k _ => a n k) X (r n) := by
    have he : a' n = fun k => if k < r n then (fun _ : Ω => a n k) else 0 := by
      funext k ω
      by_cases hk : k < r n <;> simp [a', hk]
    rw [he, cluster_gridIntegral_truncate, min_eq_right (le_max_left _ _)]
  have heqb (n : ℕ) : gridIntegral (grid n) (b' n) Y (max (r n) (s n)) =
      gridIntegral (grid n) (fun k _ => b n k) Y (s n) := by
    have he : b' n = fun k => if k < s n then (fun _ : Ω => b n k) else 0 := by
      funext k ω
      by_cases hk : k < s n <;> simp [b', hk]
    rw [he, cluster_gridIntegral_truncate, min_eq_right (le_max_right _ _)]
  exact orthogonal_grid_limits_mean_and_cross grid (fun n => max (r n) (s n))
    hX hY hXY hX₂ hY₂ (a := a') (b := b')
    (fun _ _ => stronglyMeasurable_const) (fun _ _ => stronglyMeasurable_const)
    (fun _ _ => memLp_const _) (fun _ _ => memLp_const _) hU hV
    (by simpa only [heqa] using hlU) (by simpa only [heqb] using hlV)

/-- Markov's inequality applied to the product of two nonnegative counts. -/
theorem joint_exceedance_le_product_moment [IsFiniteMeasure μ] {A B : Ω → ℝ}
    (hA : 0 ≤ᵐ[μ] A) (hB : 0 ≤ᵐ[μ] B) (hAB : Integrable (A * B) μ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    μ.real {ω | a ≤ A ω ∧ b ≤ B ω} ≤ (∫ ω, A ω * B ω ∂μ) / (a * b) := by
  have hprod : 0 ≤ᵐ[μ] A * B := by
    filter_upwards [hA, hB] with ω h₁ h₂
    exact mul_nonneg h₁ h₂
  apply (le_div_iff₀ (mul_pos ha hb)).mpr
  rw [mul_comm]
  refine (mul_le_mul_of_nonneg_left (measureReal_mono ?_) (mul_pos ha hb).le).trans
    (mul_meas_ge_le_integral_of_nonneg hprod hAB (a * b))
  intro ω hω
  exact mul_le_mul hω.1 hω.2 hb.le (ha.le.trans hω.1)

/-- A pair of nonnegative counts with centered orthogonal noise terms
satisfies the off-diagonal bound in terms of their deterministic means. -/
theorem joint_cluster_exceedance_le_of_orthogonal_noise [IsProbabilityMeasure μ]
    {U V : Ω → ℝ} (hU : MemLp U 2 μ) (hV : MemLp V 2 μ)
    (hUmean : (∫ ω, U ω ∂μ) = 0) (hVmean : (∫ ω, V ω ∂μ) = 0)
    (hcross : (∫ ω, U ω * V ω ∂μ) = 0)
    {c d a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 ≤ᵐ[μ] fun ω => c + U ω) (hd : 0 ≤ᵐ[μ] fun ω => d + V ω) :
    μ.real {ω | a ≤ c + U ω ∧ b ≤ d + V ω} ≤ (c * d) / (a * b) := by
  have hU' : MemLp (fun ω => c + U ω) 2 μ := (memLp_const c).add hU
  have hV' : MemLp (fun ω => d + V ω) 2 μ := (memLp_const d).add hV
  have hUi := hU.integrable (by norm_num)
  have hVi := hV.integrable (by norm_num)
  have hi : Integrable (fun ω => U ω * V ω) μ := cluster_integrable_mul hU hV
  have hdet : Integrable (fun _ : Ω => c * d) μ := integrable_const _
  have hcdV : Integrable (fun ω => c * d + c * V ω) μ := hdet.add (hVi.const_mul c)
  have hcdVU : Integrable (fun ω => c * d + c * V ω + U ω * d) μ := hcdV.add (hUi.mul_const d)
  have he : (∫ ω, (c + U ω) * (d + V ω) ∂μ) = c * d := by
    have hsplit : (fun ω => (c + U ω) * (d + V ω)) =
        fun ω => c * d + c * V ω + U ω * d + U ω * V ω := by
      funext ω
      ring
    rw [hsplit, integral_add hcdVU hi, integral_add hcdV (hUi.mul_const d),
      integral_add hdet (hVi.const_mul c), integral_const_mul c V, integral_mul_const d U,
      hUmean, hVmean, hcross]
    simp
  simpa only [he] using joint_exceedance_le_product_moment hc hd
    (cluster_integrable_mul hU' hV') ha hb

#print axioms orthogonal_grid_limits_mean_and_cross
#print axioms orthogonal_deterministic_grid_limits_mean_and_cross
#print axioms joint_cluster_exceedance_le_of_orthogonal_noise

end RoughHeston
