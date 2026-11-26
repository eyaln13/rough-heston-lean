import Verification

open Filter
open scoped Topology BigOperators

namespace RoughHeston

variable {ι : Type*} [Fintype ι]

/-- The mass of the nonnegative parts of the cluster coordinates. -/
noncomputable def clusterMass (x : ι → ℝ) : ℝ :=
  ∑ i, max 0 (x i)

noncomputable def clusterAmplitude (x : ι → ℝ) (i : ι) : ℝ :=
  Real.sqrt (max 0 (x i))

/-- The direction of the shared Brownian coordinate, extended by zero
when every cluster is zero. -/
noncomputable def clusterDirection (x : ι → ℝ) (i : ι) : ℝ :=
  clusterAmplitude x i / Real.sqrt (clusterMass x)

noncomputable def clusterSharedCoefficient (σ : ℝ) (x : ι → ℝ) (i : ι) : ℝ :=
  σ * clusterAmplitude x i * clusterDirection x i

noncomputable def clusterAuxiliaryCoefficient [DecidableEq ι] (σ : ℝ) (x : ι → ℝ) (i j : ι) : ℝ :=
  σ * clusterAmplitude x i * ((if i = j then 1 else 0) -
    clusterDirection x i * clusterDirection x j)

private theorem clusterMass_nonneg (x : ι → ℝ) : 0 ≤ clusterMass x :=
  Finset.sum_nonneg fun _ _ => le_max_left _ _

private theorem coordinate_le_clusterMass (x : ι → ℝ) (i : ι) :
    max 0 (x i) ≤ clusterMass x :=
  Finset.single_le_sum (fun j _ => le_max_left 0 (x j)) (Finset.mem_univ i)

private theorem amplitude_eq_zero_of_mass_eq_zero {x : ι → ℝ} (hx : clusterMass x = 0) (i : ι) :
    clusterAmplitude x i = 0 := by
  have h := (coordinate_le_clusterMass x i).trans_eq hx
  rw [clusterAmplitude, le_antisymm h (le_max_left _ _), Real.sqrt_zero]

private theorem continuous_clusterMass : Continuous (clusterMass : (ι → ℝ) → ℝ) :=
  continuous_finsetSum _ fun _ _ => continuous_const.max (continuous_apply _)

omit [Fintype ι] in
private theorem continuous_clusterAmplitude (i : ι) :
    Continuous (fun x : ι → ℝ => clusterAmplitude x i) :=
  Real.continuous_sqrt.comp (continuous_const.max (continuous_apply _))

private theorem continuousAt_clusterDirection {x : ι → ℝ} (hx : clusterMass x ≠ 0) (i : ι) :
    ContinuousAt (fun y : ι → ℝ => clusterDirection y i) x :=
  (continuous_clusterAmplitude i).continuousAt.div
    (Real.continuous_sqrt.comp continuous_clusterMass).continuousAt
    (Real.sqrt_pos.2 (lt_of_le_of_ne (clusterMass_nonneg _) (Ne.symm hx))).ne'

private theorem clusterDirection_nonneg (x : ι → ℝ) (i : ι) : 0 ≤ clusterDirection x i :=
  div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

private theorem clusterDirection_le_one (x : ι → ℝ) (i : ι) : clusterDirection x i ≤ 1 := by
  by_cases hx : clusterMass x = 0
  · simp [clusterDirection, hx]
  · apply (div_le_one (Real.sqrt_pos.2
      (lt_of_le_of_ne (clusterMass_nonneg _) (Ne.symm hx)))).2
    exact Real.sqrt_le_sqrt (coordinate_le_clusterMass x i)

private theorem abs_clusterDirection_le_one (x : ι → ℝ) (i : ι) :
    |clusterDirection x i| ≤ 1 := by
  rw [abs_of_nonneg (clusterDirection_nonneg x i)]
  exact clusterDirection_le_one x i

private theorem clusterDirection_sq_sum {x : ι → ℝ} (hx : clusterMass x ≠ 0) :
    ∑ i, clusterDirection x i ^ 2 = 1 := by
  simp only [clusterDirection, div_pow, clusterAmplitude,
    Real.sq_sqrt (le_max_left (0 : ℝ) _), Real.sq_sqrt (clusterMass_nonneg x), ← Finset.sum_div]
  exact div_self hx

/-- At zero total cluster mass the shared coefficient is continuous
because its absolute value is bounded by the vanishing cluster amplitude. -/
theorem continuous_clusterSharedCoefficient (σ : ℝ) (i : ι) :
    Continuous (fun x : ι → ℝ => clusterSharedCoefficient σ x i) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : clusterMass x = 0
  · change Tendsto (fun y => clusterSharedCoefficient σ y i) (𝓝 x)
      (𝓝 (clusterSharedCoefficient σ x i))
    rw [show clusterSharedCoefficient σ x i = 0 by
      simp [clusterSharedCoefficient, amplitude_eq_zero_of_mass_eq_zero hx i]]
    apply squeeze_zero_norm (a := fun y => |σ| * clusterAmplitude y i)
    · intro y
      rw [Real.norm_eq_abs, clusterSharedCoefficient, abs_mul, abs_mul,
        abs_of_nonneg (show 0 ≤ clusterAmplitude y i from Real.sqrt_nonneg _)]
      exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg σ) (Real.sqrt_nonneg _)) (abs_clusterDirection_le_one y i)
    · have hb := (continuous_clusterAmplitude i).continuousAt (x := x).tendsto
      rw [amplitude_eq_zero_of_mass_eq_zero hx i] at hb
      simpa only [mul_zero] using (tendsto_const_nhds (x := |σ|)).mul hb
  · exact (continuousAt_const.mul (continuous_clusterAmplitude i).continuousAt).mul
      (continuousAt_clusterDirection hx i)

/-- The auxiliary directions have the same continuity, including on
the face where all cluster amplitudes vanish. -/
theorem continuous_clusterAuxiliaryCoefficient [DecidableEq ι] (σ : ℝ) (i j : ι) :
    Continuous (fun x : ι → ℝ => clusterAuxiliaryCoefficient σ x i j) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : clusterMass x = 0
  · change Tendsto (fun y => clusterAuxiliaryCoefficient σ y i j) (𝓝 x)
      (𝓝 (clusterAuxiliaryCoefficient σ x i j))
    rw [show clusterAuxiliaryCoefficient σ x i j = 0 by
      simp [clusterAuxiliaryCoefficient, amplitude_eq_zero_of_mass_eq_zero hx i]]
    apply squeeze_zero_norm (a := fun y => |σ| * clusterAmplitude y i * 2)
    · intro y
      rw [Real.norm_eq_abs, clusterAuxiliaryCoefficient, abs_mul, abs_mul,
        abs_of_nonneg (show 0 ≤ clusterAmplitude y i from Real.sqrt_nonneg _)]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg σ) (Real.sqrt_nonneg _))
      have hij : |clusterDirection y i * clusterDirection y j| ≤ 1 := by
        rw [abs_mul]
        exact (mul_le_mul (abs_clusterDirection_le_one y i) (abs_clusterDirection_le_one y j)
          (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
      have hδ : |(if i = j then (1 : ℝ) else 0)| ≤ 1 := by split <;> norm_num
      exact (abs_sub _ _).trans (by linarith)
    · have hb := (continuous_clusterAmplitude i).continuousAt (x := x).tendsto
      rw [amplitude_eq_zero_of_mass_eq_zero hx i] at hb
      simpa only [mul_zero, zero_mul] using
        ((tendsto_const_nhds (x := |σ|)).mul hb).mul (tendsto_const_nhds (x := (2 : ℝ)))
  · exact (continuousAt_const.mul (continuous_clusterAmplitude i).continuousAt).mul
      (continuousAt_const.sub ((continuousAt_clusterDirection hx i).mul
        (continuousAt_clusterDirection hx j)))

/-- Taking covariance of two rows gives orthogonal cluster noise and
the prescribed quadratic variation of each nonnegative coordinate. -/
theorem clusterDiffusion_covariance [DecidableEq ι] (σ : ℝ) (x : ι → ℝ) (i j : ι) :
    clusterSharedCoefficient σ x i * clusterSharedCoefficient σ x j +
      ∑ k, clusterAuxiliaryCoefficient σ x i k * clusterAuxiliaryCoefficient σ x j k =
      if i = j then σ ^ 2 * max 0 (x i) else 0 := by
  by_cases hx : clusterMass x = 0
  · simp [clusterSharedCoefficient, clusterAuxiliaryCoefficient,
      amplitude_eq_zero_of_mass_eq_zero hx, (coordinate_le_clusterMass x i).trans_eq hx |>.antisymm
        (le_max_left 0 (x i))]
  · let a (k : ι) := σ * clusterAmplitude x k
    let u := clusterDirection x
    let q (l k : ι) : ℝ := (if l = k then 1 else 0) - u l * u k
    have he (k : ι) : (a i * q i k) * (a j * q j k) =
        (a i * a j) * (q i k * q j k) := by ring
    change a i * u i * (a j * u j) + ∑ k, (a i * q i k) * (a j * q j k) = _
    simp_rw [he, ← Finset.mul_sum]
    rw [show a i * u i * (a j * u j) = (a i * a j) * (u i * u j) by ring,
      ← mul_add, cluster_projection u (clusterDirection_sq_sum hx)]
    split
    · rename_i h
      subst j
      rw [mul_one, ← sq]
      simp only [a, clusterAmplitude, mul_pow, Real.sq_sqrt (le_max_left (0 : ℝ) _)]
    · rw [mul_zero]

/-- The shared coefficient gives the prescribed covariation with the
competitor; the ratio has the zero extension at zero total mass. -/
theorem clusterDiffusion_competitor_covariance (σ : ℝ) (x : ι → ℝ) (y : ℝ) (i : ι) :
    clusterSharedCoefficient σ x i * (σ * Real.sqrt (max 0 y)) =
      σ ^ 2 * (max 0 (x i) * Real.sqrt (max 0 y) / Real.sqrt (clusterMass x)) := by
  unfold clusterSharedCoefficient clusterDirection clusterAmplitude
  calc
    _ = σ ^ 2 * ((Real.sqrt (max 0 (x i))) ^ 2 *
        Real.sqrt (max 0 y) / Real.sqrt (clusterMass x)) := by ring
    _ = _ := by rw [Real.sq_sqrt (le_max_left (0 : ℝ) _)]

end RoughHeston

#print axioms RoughHeston.continuous_clusterSharedCoefficient
#print axioms RoughHeston.continuous_clusterAuxiliaryCoefficient
#print axioms RoughHeston.clusterDiffusion_covariance
#print axioms RoughHeston.clusterDiffusion_competitor_covariance
