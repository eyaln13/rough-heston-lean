import ClusterRiccatiQuantitative

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RoughHeston

/-- The slope of the density Riccati solution in its initial value
decays at the large-charge rate on bounded time intervals. -/
theorem exists_cluster_riccati_sensitivity_decay
    {α κ a H : ℝ} (hα : 1/2 < α) (hα' : α < 1) (hκ : 0 ≤ κ) (ha : 0 < a) (hH : 0 < H) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q u T : ℝ} {w k : ℝ → ℝ},
      1 ≤ q → 0 < u → u ≤ H → u < T → 1 ≤ Real.sqrt q*u^α →
      Continuous w → w 0 = 0 → (∀ s ∈ Ioc 0 u, 0 ≤ w s) →
      (∀ s ∈ Icc 0 T, w s = w 0 +
        volterraConvolution (fractionalK α) (fun v => q+(-κ)*w v+(-a)*w v^2) s) →
      Continuous k → (∀ s ∈ Icc 0 u, k s ≤ 1) →
      (∀ s ∈ Icc 0 T, k s = 1+
        volterraConvolution (fractionalK α) (fun v => κ-(κ+2*a*w v)*k v) s) →
      k u ≤ C/(Real.sqrt q*u^α) := by
  obtain ⟨c,hc,hLower⟩ := exists_cluster_riccati_lower_constant hα hα' hκ ha.le
  have hα₀ : 0 < α := by linarith
  let G := Real.Gamma (α+1)
  have hG : 0 < G := Real.Gamma_pos_of_pos (by linarith)
  let D := 2*a*c
  have hD : 0 < D := by dsimp [D]; positivity
  let C := (κ*H^α+G*(2:ℝ)^α)/D
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro q u T w k hq hu huH huT hqScale hw hw₀ hwPos hwVol hk hkB hkVol
  let R := D*Real.sqrt q
  have hq' : 0 < Real.sqrt q := Real.sqrt_pos.mpr (zero_lt_one.trans_le hq)
  have hR : 0 < R := mul_pos hD hq'
  let rate (s : ℝ) := κ+2*a*w s
  have hr : Continuous rate := continuous_const.add (continuous_const.mul hw)
  have hr₁ (s : ℝ) (hs : s ∈ Ioo 0 T) : ContDiffAt ℝ 1 rate s :=
    contDiffAt_const.add (contDiffAt_const.mul
      (density_riccati_caputo_of_volterra hα hα' hs hw hwVol).1)
  have hrR (s : ℝ) (hs : s ∈ Icc (u/2) u) : R ≤ rate s := by
    have h := hLower hq hu huT hqScale hw hw₀ hwPos hwVol s hs
    have h' := mul_le_mul_of_nonneg_left h (show 0 ≤ 2*a by positivity)
    have hb : R ≤ 2*a*w s := by simpa only [R,D,mul_assoc] using h'
    exact hb.trans (le_add_of_nonneg_left hκ : 2*a*w s ≤ κ+2*a*w s)
  have hK := density_linearized_riccati_endpoint_bound hα hα' hκ hu huT hR hr hr₁ hrR hk hkB hkVol
  have hup : 0 < u^α := Real.rpow_pos_of_pos hu _
  have hTwo : 0 < (2:ℝ)^α := by positivity
  refine hK.trans ?_
  calc
    _ = (κ*u^α+G*(2:ℝ)^α)/(D*Real.sqrt q*u^α) := by
      rw [Real.div_rpow hu.le (by norm_num : (0:ℝ)≤2)]
      change (κ+G/(u^α/(2:ℝ)^α))/R = _
      dsimp [R]
      field_simp
    _ ≤ _ := by
      change _ ≤ ((κ*H^α+G*(2:ℝ)^α)/D)/(Real.sqrt q*u^α)
      rw [div_div, ← mul_assoc]
      exact div_le_div_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hu.le huH hα₀.le) hκ) le_rfl) (mul_nonneg (mul_nonneg hD.le hq'.le) hup.le)

/-- If an age is in the last half of the observation interval, a
charge above the squared scale satisfies the large-charge conditions. -/
theorem cluster_sensitivity_charge_threshold {α H s u q : ℝ}
    (hα : 0 < α) (_hH : 0 < H) (hs : 0 < s) (hsH : s ≤ H)
    (hu : u ∈ Icc (s/2) s)
    (hq : max (H^(2*α)) ((2:ℝ)^(2*α)) / s^(2*α) ≤ q) :
    1 ≤ q ∧ 1 ≤ Real.sqrt q*u^α := by
  have hs₂ : 0 < s^(2*α) := Real.rpow_pos_of_pos hs _
  have hu₀ : 0 < u := (half_pos hs).trans_le hu.1
  have hsα := Real.rpow_pos_of_pos hs α
  have huα := Real.rpow_pos_of_pos hu₀ α
  have hsq : s^(2*α) = (s^α)^2 := by
    rw [mul_comm, Real.rpow_mul hs.le, Real.rpow_two]
  have hTwo : (2:ℝ)^(2*α) = ((2:ℝ)^α)^2 := by
    rw [mul_comm, Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), Real.rpow_two]
  have hq₁ : 1 ≤ q := by
    refine le_trans ?_ hq
    apply (le_div_iff₀ hs₂).mpr
    rw [one_mul]
    exact (Real.rpow_le_rpow hs.le hsH (by positivity)).trans (le_max_left _ _)
  refine ⟨hq₁,?_⟩
  have hTwoq : (2:ℝ)^(2*α)/s^(2*α) ≤ q :=
    (div_le_div_of_nonneg_right (le_max_right _ _) hs₂.le).trans hq
  rw [hTwo,hsq,← div_pow] at hTwoq
  have hSq := Real.sqrt_le_sqrt hTwoq
  have hK : (2:ℝ)^α / s^α ≤ Real.sqrt q := by
    rwa [Real.sqrt_sq (by positivity)] at hSq
  have hD : s^α/(2:ℝ)^α ≤ u^α := by
    rw [← Real.div_rpow hs.le (by norm_num : (0:ℝ) ≤ 2)]
    exact Real.rpow_le_rpow (half_pos hs).le hu.1 hα.le
  have hProd := mul_le_mul hK hD (by positivity) (Real.sqrt_nonneg q)
  have he : ((2:ℝ)^α/s^α)*(s^α/(2:ℝ)^α) = 1 := by field_simp
  rwa [he] at hProd

#print axioms exists_cluster_riccati_sensitivity_decay
#print axioms cluster_sensitivity_charge_threshold

end RoughHeston
