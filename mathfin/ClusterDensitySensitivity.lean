import LinearFractionalRiccati

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RoughHeston

private theorem positivity_from_initial_and_caputo_contact
    {α T : ℝ} {f : ℝ → ℝ} (hα : 0 < α) (hα' : α < 1) (hf : Continuous f)
    (hf₀ : 0 < f 0)
    (hcontact : ∀ s ∈ Ioo 0 T, f s = 0 →
      IntervalIntegrable (fun u => (α*u^(-α-1)/Real.Gamma (1-α))*(f s-f (s-u))) volume 0 s ∧
      0 ≤ fractionalMemory α (f 0) f s) :
    ∀ t ∈ Ioo 0 T, 0 < f t := by
  obtain ⟨r,hr,hnear⟩ := Metric.eventually_nhds_iff.mp
    (continuousAt_const.eventually_lt hf.continuousAt hf₀)
  let d := r/2
  have hd : 0 < d := div_pos hr (by norm_num)
  have hstart (s : ℝ) (hs : s ∈ Ioc 0 d) : 0 < f s := by
    apply hnear
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1.le]
    exact hs.2.trans_lt (by dsimp [d]; linarith)
  intro t ht
  by_cases htd : t ≤ d
  · exact hstart t ⟨ht.1,htd⟩
  exact fractional_first_contact_comparison hα hα' hf₀.le hd hf.continuousOn hstart
    (fun s hs => hcontact s ⟨hd.trans_le hs.1,hs.2.trans_lt ht.2⟩) t ⟨le_of_not_ge htd,le_rfl⟩

/-- The derivative equation for the density charge preserves the
bounds zero and one when the rate is bounded below by the forcing. -/
theorem density_linearized_riccati_bounds
    {α κ T : ℝ} {rate k : ℝ → ℝ}
    (hα : 1/2 < α) (hα' : α < 1) (hT : 0 < T) (hκ : 0 ≤ κ)
    (hr : Continuous rate) (hr₁ : ∀ t ∈ Ioo 0 T, ContDiffAt ℝ 1 rate t)
    (hrκ : ∀ t ∈ Ioo 0 T, κ ≤ rate t) (hk : Continuous k)
    (hV : ∀ t ∈ Icc 0 T, k t = 1+volterraConvolution (fractionalK α)
      (fun s => κ-rate s*k s) t) :
    ∀ t ∈ Ico 0 T, 0 < k t ∧ k t ≤ 1 := by
  have hα₀ : 0 < α := by linarith
  have h0 : k 0 = 1 := by simpa [volterraConvolution] using hV 0 ⟨le_rfl,hT.le⟩
  have hCaputo (t : ℝ) (ht : t ∈ Ioo 0 T) :
      IntervalIntegrable (fun u => (α*u^(-α-1)/Real.Gamma (1-α))*(k t-k (t-u))) volume 0 t ∧
      fractionalMemory α (k 0) k t = κ-rate t*k t := by
    exact (caputo_mean_equation_of_volterra hα hα' ht hk.continuousOn hr.continuousOn hr₁
      (fun s hs => by rw [h0]; exact hV s (Ioo_subset_Icc_self hs))).2
  have hpos := positivity_from_initial_and_caputo_contact hα₀ hα' hk
    (show 0 < k 0 by rw [h0]; exact zero_lt_one) (fun s hs he => by
      obtain ⟨hI,hC⟩ := hCaputo s hs
      exact ⟨hI, by rw [hC, he, mul_zero, sub_zero]; exact hκ⟩)
  intro t ht
  rcases eq_or_lt_of_le ht.1 with he | hp
  · subst t
    rw [h0]
    exact ⟨zero_lt_one,le_rfl⟩
  have ht' : t ∈ Ioo 0 T := ⟨hp, ht.2⟩
  refine ⟨hpos t ht', ?_⟩
  by_contra! htk
  let ε := (k t-1)/2
  have hε : 0 < ε := div_pos (sub_pos.mpr htk) (by norm_num)
  let g (s : ℝ) := 1+ε-k s
  have hgc : Continuous g := continuous_const.sub hk
  have hgi : 0 < g 0 := by dsimp [g]; rw [h0]; linarith
  have hGPos : 0 < g t := positivity_from_initial_and_caputo_contact hα₀ hα' hgc hgi
    (fun s hs hz => by
      have hEq : k s = 1+ε := (sub_eq_zero.mp hz).symm
      obtain ⟨hInt,hCap⟩ := hCaputo s hs
      have hΔ (u : ℝ) : (α*u^(-α-1)/Real.Gamma (1-α))*(g s-g (s-u)) =
          -((α*u^(-α-1)/Real.Gamma (1-α))*(k s-k (s-u))) := by dsimp [g]; ring
      have hMem : fractionalMemory α (g 0) g s = -fractionalMemory α (k 0) k s := by
        unfold fractionalMemory
        simp_rw [hΔ]
        rw [intervalIntegral.integral_neg]
        dsimp [g]
        ring
      refine ⟨?_, ?_⟩
      · have hF : (fun u : ℝ => (α*u^(-α-1)/Real.Gamma (1-α))*(g s-g (s-u))) =
            -(fun u : ℝ => (α*u^(-α-1)/Real.Gamma (1-α))*(k s-k (s-u))) := funext hΔ
        rw [hF]
        exact hInt.neg
      · rw [hMem, hCap, hEq]
        exact neg_nonneg.mpr (sub_nonpos.mpr ((hrκ s hs).trans
          (le_mul_of_one_le_right (hκ.trans (hrκ s hs)) (le_add_of_nonneg_right hε.le))))) t ht'
  dsimp [g, ε] at hGPos
  linarith

/-- Actual density-charge solutions and their initial-value derivative
on a fixed horizon, with the derivative bounded between zero and one. -/
theorem exists_cluster_density_riccati_with_sensitivity_data
    {α q κ a T : ℝ}
    (hα : 1/2 < α) (hα' : α < 1) (hq : 0 < q) (hκ : 0 ≤ κ) (ha : 0 < a) (hT : 0 ≤ T) :
    ∃ (w : ℝ → ℝ → ℝ) (k : ℝ → ℝ), Continuous k ∧
      (∀ l ∈ Icc (0 : ℝ) 1, Continuous (w l)) ∧
      (∀ l ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 T,
        w l t = l+volterraConvolution (fractionalK α)
          (fun s => q+κ*l-κ*w l s-a*(w l s)^2) t) ∧
      (∀ t ∈ Icc 0 T, k t = 1+volterraConvolution (fractionalK α)
        (fun s => κ-(κ+2*a*w 0 s)*k s) t) ∧
      (∀ t ∈ Icc 0 T, 0 ≤ w 0 t) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ l ∈ Ioc (0 : ℝ) 1, ∀ t ∈ Icc 0 T,
        ‖(w l t-w 0 t)/l-k t‖ ≤ C*l) ∧
      ∀ t ∈ Icc 0 T, (0 < k t ∧ k t ≤ 1) ∧
        HasDerivWithinAt (fun l => w l t) (k t) (Ici 0) 0 := by
  have hα₀ : 0 < α := by linarith
  let H := T+1
  have hTH : T < H := lt_add_one T
  have hH : 0 < H := hT.trans_lt hTH
  obtain ⟨B,w,hB,hw,hwB,hwV⟩ := exists_cluster_density_riccati_family hα hα' hq hκ ha H
  have hl₀ : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl,zero_le_one⟩
  have hw₀ : w 0 0 = 0 := by simpa [volterraConvolution] using hwV 0 hl₀ 0 ⟨le_rfl,hH.le⟩
  have hWV : ∀ t ∈ Icc 0 H, w 0 t = w 0 0 + volterraConvolution (fractionalK α)
      (fun s => q+(-κ)*w 0 s+(-a)*(w 0 s)^2) t := by
    simpa only [hw₀, mul_zero, add_zero, neg_mul, sub_eq_add_neg] using hwV 0 hl₀
  let R := 1+q/a
  have hR : 0 < R := add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg hq.le ha.le)
  have hR₁ : 1 ≤ R := le_add_of_nonneg_right (div_nonneg hq.le ha.le)
  have hR₂ : q ≤ a*R^2 := by
    have hs : q/a ≤ R := by dsimp [R]; linarith
    have hRquad : R ≤ R^2 := by nlinarith [mul_nonneg hR.le (sub_nonneg.mpr hR₁)]
    exact ((div_le_iff₀ ha).mp (hs.trans hRquad)).trans_eq (mul_comm _ _)
  have hRbar : q+(-κ)*R+(-a)*R^2 ≤ 0 := by
    have hn := mul_nonneg hκ hR.le
    linarith
  have hWPos (t : ℝ) (ht : t ∈ Ioo 0 H) : 0 < w 0 t :=
    (density_riccati_pos_lt_constant hα hα' hH hq (hw 0 hl₀)
      (by rw [hw₀]) (by rw [hw₀]; exact hR) hRbar hWV t ht).1
  let rate (s : ℝ) := κ+2*a*w 0 s
  have hr : Continuous rate := continuous_const.add (continuous_const.mul (hw 0 hl₀))
  obtain ⟨k,hk,hkV⟩ := exists_linear_fractional_volterra
    (force := κ) (initial := 1) hα₀ hH.le hr
  have hr₁ (t : ℝ) (ht : t ∈ Ioo 0 H) : ContDiffAt ℝ 1 rate t :=
    contDiffAt_const.add (contDiffAt_const.mul
      (density_riccati_caputo_of_volterra hα hα' ht (hw 0 hl₀) hWV).1)
  have hrκ (t : ℝ) (ht : t ∈ Ioo 0 H) : κ ≤ rate t :=
    le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num) ha.le) (hWPos t ht).le)
  have hKb := density_linearized_riccati_bounds hα hα' hH hκ hr hr₁ hrκ hk hkV
  have hsub : Icc (0 : ℝ) T ⊆ Icc 0 H := Icc_subset_Icc_right hTH.le
  have hsub' : Icc (0 : ℝ) T ⊆ Ico 0 H := fun _ ht => ⟨ht.1,ht.2.trans_lt hTH⟩
  obtain ⟨⟨C,hC,hUC⟩,hD⟩ := density_riccati_sensitivity_right hα₀ hH.le hB hw hwB hwV hk hkV
  have hNN (t : ℝ) (ht : t ∈ Icc 0 T) : 0 ≤ w 0 t := by
    rcases eq_or_lt_of_le ht.1 with hz | hp
    · subst t
      rw [hw₀]
    · exact (hWPos t ⟨hp,ht.2.trans_lt hTH⟩).le
  exact ⟨w,k,hk,hw,fun l hl t ht => hwV l hl t (hsub ht),
    (fun t ht => hkV t (hsub ht)), hNN,
    ⟨C,hC,fun l hl t ht => hUC l hl t (hsub ht)⟩,
    fun t ht => ⟨hKb t (hsub' ht),hD t (hsub ht)⟩⟩

/-- Density-charge solutions and their right derivative on a fixed horizon. -/
theorem exists_cluster_density_riccati_with_sensitivity
    {α q κ a T : ℝ}
    (hα : 1/2 < α) (hα' : α < 1) (hq : 0 < q) (hκ : 0 ≤ κ) (ha : 0 < a) (hT : 0 ≤ T) :
    ∃ (w : ℝ → ℝ → ℝ) (k : ℝ → ℝ), Continuous k ∧
      (∀ l ∈ Icc (0 : ℝ) 1, Continuous (w l)) ∧
      (∀ l ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 T,
        w l t = l+volterraConvolution (fractionalK α)
          (fun s => q+κ*l-κ*w l s-a*(w l s)^2) t) ∧
      (∀ t ∈ Icc 0 T, k t = 1+volterraConvolution (fractionalK α)
        (fun s => κ-(κ+2*a*w 0 s)*k s) t) ∧
      ∀ t ∈ Icc 0 T, (0 < k t ∧ k t ≤ 1) ∧
        HasDerivWithinAt (fun l => w l t) (k t) (Ici 0) 0 := by
  obtain ⟨w,k,hk,hw,hwV,hkV,_,_,hD⟩ :=
    exists_cluster_density_riccati_with_sensitivity_data hα hα' hq hκ ha hT
  exact ⟨w,k,hk,hw,hwV,hkV,hD⟩

#print axioms density_linearized_riccati_bounds
#print axioms exists_cluster_density_riccati_with_sensitivity_data
#print axioms exists_cluster_density_riccati_with_sensitivity

end RoughHeston
