import DelayedCaputoPower

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RoughHeston

private theorem contact_comparison_positive_at
    {α t : ℝ} {g : ℝ → ℝ}
    (hα : 0 < α) (hα' : α < 1) (ht : 0 < t) (hg : Continuous g)
    (h0 : 0 < g 0)
    (hContact : ∀ s ∈ Ioc 0 t, g s = 0 →
      IntervalIntegrable (fun u => (α*u^(-α-1)/Real.Gamma (1-α))*(g s-g (s-u))) volume 0 s ∧
      0 ≤ fractionalMemory α (g 0) g s) : 0 < g t := by
  obtain ⟨r,hr,hnear⟩ := Metric.eventually_nhds_iff.mp
    (continuousAt_const.eventually_lt hg.continuousAt h0)
  let d := r/2
  have hd : 0 < d := div_pos hr (by norm_num)
  have hstart (s : ℝ) (hs : s ∈ Ioc 0 d) : 0 < g s := by
    apply hnear
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1.le]
    exact hs.2.trans_lt (by dsimp [d]; linarith)
  by_cases htd : t ≤ d
  · exact hstart t ⟨ht,htd⟩
  exact fractional_first_contact_comparison hα hα' h0.le hd hg.continuousOn hstart
    (fun s hs => hContact s ⟨hd.trans_le hs.1,hs.2⟩) t ⟨le_of_not_ge htd,le_rfl⟩

/-- A power subsolution for the unshifted density Riccati equation.
The constant offset in the comparison disappears by taking it to zero. -/
theorem density_riccati_lower_by_power
    {α q κ a T u A M : ℝ} {w : ℝ → ℝ}
    (hα : 1/2 < α) (hα' : α < 1) (hκ : 0 ≤ κ) (ha : 0 ≤ a)
    (_hu : 0 < u) (huT : u < T) (hA : 0 ≤ A) (_hM : 0 ≤ M)
    (hHeight : A*(u^α/Real.Gamma (α+1)) ≤ M) (hReaction : A+κ*M+a*M^2 ≤ q)
    (hw : Continuous w) (hw₀ : w 0 = 0) (hwpos : ∀ s ∈ Ioc 0 u, 0 ≤ w s)
    (hV : ∀ s ∈ Icc 0 T, w s = w 0 +
      volterraConvolution (fractionalK α) (fun v => q+(-κ)*w v+(-a)*w v^2) s) :
    ∀ t ∈ Ioc 0 u, delayedCaputoPower α 0 A t ≤ w t := by
  have hα₀ : 0 < α := by linarith
  have hΓ := Real.Gamma_pos_of_pos (show 0 < α+1 by linarith)
  let p := delayedCaputoPower α 0 A
  have hp : Continuous p := continuous_delayedCaputoPower hα₀
  have hp₀ : p 0 = 0 := by simp [p, delayedCaputoPower, Real.zero_rpow hα₀.ne']
  have hPBound (s : ℝ) (hs : s ∈ Ioc 0 u) : p s ≤ M := by
    rw [show p s = A*(s^α/Real.Gamma (α+1)) by simp [p, delayedCaputoPower, hs.1.le] ]
    exact (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
      (Real.rpow_le_rpow hs.1.le hs.2 hα₀.le) hΓ.le) hA).trans hHeight
  intro t ht
  by_contra! hbad
  let e := (p t-w t)/2
  have he : 0 < e := div_pos (sub_pos.mpr hbad) (by norm_num)
  let g (s : ℝ) := e+w s-p s
  have hg : Continuous g := (continuous_const.add hw).sub hp
  have hg₀ : 0 < g 0 := by simpa [g, hw₀, hp₀] using he
  have htrue := contact_comparison_positive_at hα₀ hα' ht.1 hg hg₀ (fun s hs hz => by
    obtain ⟨_,hwi,hwMem⟩ := density_riccati_caputo_of_volterra hα hα'
      (show s ∈ Ioo 0 T from ⟨hs.1,hs.2.trans_lt (ht.2.trans_lt huT)⟩) hw hV
    obtain ⟨hpi,hpMem⟩ := delayedCaputoPower_memory
      (A := A) hα₀ hα' (d := 0) le_rfl hs.1
    obtain ⟨hgi,hgMem⟩ := fractionalMemory_affine_sub (C := e) hwi hpi
    refine ⟨hgi, ?_⟩
    change 0 ≤ fractionalMemory α ((fun x => e+w x-p x) 0) (fun x => e+w x-p x) s
    rw [hgMem, hwMem, hpMem]
    have hsu : s ∈ Ioc 0 u := ⟨hs.1,hs.2.trans ht.2⟩
    have hwp : w s ≤ p s := by dsimp [g] at hz; linarith
    have hwb : w s ≤ M := hwp.trans (hPBound s hsu)
    have hlin := mul_le_mul_of_nonneg_left hwb hκ
    have hquad := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hwpos s hsu) hwb 2) ha
    simp only [neg_mul]
    linarith)
  dsimp [g,e] at htrue
  linarith

/-- A quantitative lower level on the final half of an observation
interval, with constants independent of the positive density charge. -/
theorem exists_cluster_riccati_lower_constant
    {α κ a : ℝ} (hα : 1/2 < α) (hα' : α < 1) (hκ : 0 ≤ κ) (ha : 0 ≤ a) :
    ∃ c : ℝ, 0 < c ∧ ∀ {q u T : ℝ} {w : ℝ → ℝ},
      1 ≤ q → 0 < u → u < T → 1 ≤ Real.sqrt q*u^α → Continuous w → w 0 = 0 →
      (∀ s ∈ Ioc 0 u, 0 ≤ w s) →
      (∀ s ∈ Icc 0 T, w s = w 0 +
        volterraConvolution (fractionalK α) (fun v => q+(-κ)*w v+(-a)*w v^2) s) →
      ∀ t ∈ Icc (u/2) u, c*Real.sqrt q ≤ w t := by
  have hα₀ : 0 < α := by linarith
  let G := Real.Gamma (α+1)
  have hG : 0 < G := Real.Gamma_pos_of_pos (by linarith)
  let c₀ := 1/(1+G+κ+a)
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  have hc₀₁ : c₀ ≤ 1 := by
    change 1/(1+G+κ+a) ≤ 1
    exact (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hc₀G : c₀*(G+κ+a) ≤ 1 := by
    have hEq : c₀*(1+G+κ+a) = 1 := by
      dsimp [c₀]
      field_simp
    nlinarith only [hEq,hc₀]
  refine ⟨c₀/(2:ℝ)^α, div_pos hc₀ (by positivity), ?_⟩
  intro q u T w hq hu huT hscale hw hw₀ hwpos hV t ht
  let r := Real.sqrt q
  have hr : 0 < r := Real.sqrt_pos.2 (zero_lt_one.trans_le hq)
  have hrq : r^2 = q := Real.sq_sqrt (zero_le_one.trans hq)
  have hr₁ : 1 ≤ r := by
    have h := Real.sqrt_le_sqrt hq
    simpa [r] using h
  have hrle : r ≤ q := by nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hr₁)]
  have huα : 0 < u^α := Real.rpow_pos_of_pos hu _
  have hd : r/u^α ≤ q := (div_le_iff₀ huα).mpr (by
    have h := mul_le_mul_of_nonneg_left hscale hr.le
    change r*1 ≤ r*(r*u^α) at h
    rwa [mul_one, ← mul_assoc, ← pow_two, hrq] at h)
  let M := c₀*r
  let A := M*G/u^α
  have hM : 0 ≤ M := mul_nonneg hc₀.le hr.le
  have hA : 0 ≤ A := div_nonneg (mul_nonneg hM hG.le) huα.le
  have hAM : A*(u^α/G) = M := by
    dsimp [A]
    field_simp
  have hR : A+κ*M+a*M^2 ≤ q := by
    have h₁ : A ≤ c₀*G*q := by
      convert mul_le_mul_of_nonneg_left hd (mul_nonneg hc₀.le hG.le) using 1
      dsimp [A,M]
      ring
    have h₂ : κ*M ≤ c₀*κ*q := by
      convert mul_le_mul_of_nonneg_left hrle (mul_nonneg hc₀.le hκ) using 1
      dsimp [M]
      ring
    have h₃ : a*M^2 ≤ c₀*a*q := by
      calc
        _ = (a*c₀^2)*q := by dsimp [M]; rw [mul_pow, hrq]; ring
        _ ≤ _ := by
          have hsq : c₀^2 ≤ c₀ := by nlinarith [mul_nonneg hc₀.le (sub_nonneg.mpr hc₀₁)]
          convert mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq ha)
            (zero_le_one.trans hq) using 1
          ring
    calc
      _ ≤ c₀*G*q+c₀*κ*q+c₀*a*q := add_le_add (add_le_add h₁ h₂) h₃
      _ = c₀*(G+κ+a)*q := by ring
      _ ≤ q := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc₀G (zero_le_one.trans hq)
  have ht₀ : 0 < t := (half_pos hu).trans_le ht.1
  have hwt := density_riccati_lower_by_power hα hα' hκ ha hu huT hA hM hAM.le
    hR hw hw₀ hwpos hV t ⟨ht₀,ht.2⟩
  refine le_trans ?_ hwt
  calc
    (c₀/(2:ℝ)^α)*Real.sqrt q = A*((u/2)^α/G) := by
      rw [Real.div_rpow hu.le (by norm_num : (0:ℝ) ≤ 2)]
      dsimp [A,M,r]
      field_simp
    _ ≤ delayedCaputoPower α 0 A t := by
      rw [show delayedCaputoPower α 0 A t = A*(t^α/G) by
        simp [delayedCaputoPower, ht₀.le, G] ]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
        (Real.rpow_le_rpow (by linarith) ht.1 hα₀.le) hG.le) hA

/-- Once a positive rate lower bound holds over the last half interval,
a delayed decreasing power gives a quantitative bound at the endpoint. -/
theorem density_linearized_riccati_endpoint_bound
    {α κ T u R : ℝ} {rate k : ℝ → ℝ}
    (hα : 1/2 < α) (hα' : α < 1) (hκ : 0 ≤ κ) (hu : 0 < u) (huT : u < T) (hR : 0 < R)
    (hr : Continuous rate) (hr₁ : ∀ t ∈ Ioo 0 T, ContDiffAt ℝ 1 rate t)
    (hrR : ∀ t ∈ Icc (u/2) u, R ≤ rate t) (hk : Continuous k)
    (hkB : ∀ t ∈ Icc 0 u, k t ≤ 1)
    (hV : ∀ t ∈ Icc 0 T, k t = 1+volterraConvolution (fractionalK α)
      (fun s => κ-rate s*k s) t) :
    k u ≤ (κ+Real.Gamma (α+1)/(u/2)^α)/R := by
  have hα₀ : 0 < α := by linarith
  have hΓ := Real.Gamma_pos_of_pos (show 0 < α+1 by linarith)
  let d := u/2
  have hd : 0 < d := half_pos hu
  have hdu : d < u := by dsimp [d]; linarith
  have hdα : 0 < d^α := Real.rpow_pos_of_pos hd _
  let e := (κ+Real.Gamma (α+1)/d^α)/R
  have he : 0 < e := div_pos (add_pos_of_nonneg_of_pos hκ (div_pos hΓ hdα)) hR
  change k u ≤ e
  by_cases he₁ : 1 ≤ e
  · exact (hkB u ⟨hu.le,le_rfl⟩).trans he₁
  have he₁' : e < 1 := lt_of_not_ge he₁
  let A := (1-e)*Real.Gamma (α+1)/d^α
  have hA : 0 ≤ A := div_nonneg (mul_nonneg (sub_nonneg.mpr he₁'.le) hΓ.le) hdα.le
  have hAR : κ+A ≤ R*e := by
    have hE : R*e = κ+Real.Gamma (α+1)/d^α := by dsimp [e]; field_simp
    rw [hE]
    apply add_le_add le_rfl
    exact div_le_div_of_nonneg_right (by linarith [mul_nonneg he.le hΓ.le]) hdα.le
  let p := delayedCaputoPower α d (-A)
  have hp : Continuous p := continuous_delayedCaputoPower hα₀
  have hPZero (s : ℝ) (hs : s ≤ d) : p s = 0 := by
    simp [p, delayedCaputoPower, max_eq_left (sub_nonpos.mpr hs), Real.zero_rpow hα₀.ne']
  have hPmax (s : ℝ) (hs : s ∈ Icc d u) : -(1-e) ≤ p s := by
    have hh : s-d ≤ d := by dsimp [d] at *; linarith [hs.2]
    have hpow := div_le_div_of_nonneg_right
      (Real.rpow_le_rpow (sub_nonneg.mpr hs.1) hh hα₀.le) hΓ.le
    have heq : (-A)*(d^α/Real.Gamma (α+1)) = -(1-e) := by dsimp [A]; field_simp
    calc
      _ = (-A)*(d^α/Real.Gamma (α+1)) := heq.symm
      _ ≤ p s := by
        rw [show p s = (-A)*((s-d)^α/Real.Gamma (α+1)) by
          simp [p, delayedCaputoPower, max_eq_right (sub_nonneg.mpr hs.1)] ]
        exact mul_le_mul_of_nonpos_left hpow (neg_nonpos.mpr hA)
  have hPu : p u = -(1-e) := by
    have h : u-d = d := by dsimp [d]; ring
    simp only [p, delayedCaputoPower, h, max_eq_right hd.le]
    dsimp [A]
    field_simp
  have hk0 : k 0 = 1 := by simpa [volterraConvolution] using hV 0 ⟨le_rfl,(hu.trans huT).le⟩
  by_contra! hku
  let δ := (k u-e)/2
  have hδ : 0 < δ := half_pos (sub_pos.mpr hku)
  let g (s : ℝ) := (1+δ)+p s-k s
  have hg : Continuous g := (continuous_const.add hp).sub hk
  have hg0 : 0 < g 0 := by dsimp [g]; rw [hPZero 0 hd.le, hk0]; linarith
  have hPast (s : ℝ) (hs : s ∈ Icc 0 d) : 0 < g s := by
    have hK := hkB s ⟨hs.1,hs.2.trans hdu.le⟩
    dsimp [g]
    rw [hPZero s hs.2]
    linarith
  have hgd : 0 < g d := hPast d ⟨hd.le,le_rfl⟩
  obtain ⟨z,hz,hnear⟩ := Metric.eventually_nhds_iff.mp
    (continuousAt_const.eventually_lt (hg.continuousAt (x := d)) hgd)
  let b := min u (d+z/2)
  have hdb : d < b := lt_min hdu (by linarith)
  have hb₀ := hd.trans hdb
  have hbu : b ≤ u := min_le_left _ _
  have hStart (s : ℝ) (hs : s ∈ Ioc 0 b) : 0 < g s := by
    rcases le_or_gt s d with hsd | hds
    · exact hPast s ⟨hs.1.le,hsd⟩
    apply hnear
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hds.le)]
    have h := hs.2.trans (min_le_right u (d+z/2))
    linarith
  have hgu := fractional_first_contact_comparison hα₀ hα' hg0.le hb₀ hg.continuousOn hStart
    (fun s hs hs0 => by
      have hds : d < s := hdb.trans_le hs.1
      have hsu : s ∈ Icc d u := ⟨hds.le,hs.2⟩
      have hsT : s ∈ Ioo 0 T := ⟨hd.trans hds,hs.2.trans_lt huT⟩
      obtain ⟨_, hki, hkMem⟩ := caputo_mean_equation_of_volterra hα hα' hsT
        hk.continuousOn hr.continuousOn hr₁
        (fun v hv => by rw [hk0]; exact hV v (Ioo_subset_Icc_self hv))
      obtain ⟨hpi,hpMem⟩ := delayedCaputoPower_memory (A := -A) hα₀ hα' hd.le hds
      obtain ⟨hgi,hgMem⟩ := fractionalMemory_affine_sub (C := 1+δ) hpi hki
      refine ⟨hgi, ?_⟩
      change 0 ≤ fractionalMemory α ((fun x => (1+δ)+p x-k x) 0) (fun x => (1+δ)+p x-k x) s
      rw [hgMem,hpMem,hkMem]
      have hkLower : e ≤ k s := by
        have hh := hPmax s hsu
        dsimp [g] at hs0
        linarith
      have hProd := mul_le_mul (hrR s hsu) hkLower he.le (hR.le.trans (hrR s hsu))
      linarith) u ⟨hbu,le_rfl⟩
  dsimp [g,δ] at hgu
  rw [hPu] at hgu
  linarith

#print axioms density_riccati_lower_by_power
#print axioms exists_cluster_riccati_lower_constant
#print axioms density_linearized_riccati_endpoint_bound

end RoughHeston
