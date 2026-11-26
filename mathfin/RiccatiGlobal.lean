import RiccatiEndpointFill

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RoughHeston

/-- Global existence for a positive point charge and nonpositive linear
and quadratic drift. The solution satisfies the same weighted asymptotic
as the local solution and stays between zero and its point-charge kernel. -/
theorem exists_global_fractional_riccati_point_charge
    {α q b c : ℝ} (hα : 1/2 < α) (hα' : α < 1) (hq : 0 < q)
    (hb : b ≤ 0) (hc : c ≤ 0) :
    ∃ w : ℝ → ℝ, (∀ T : ℝ, PointChargeRiccatiOn α q b c T w) ∧
      ∀ t > 0, 0 < w t ∧ w t ≤ q * fractionalK α t := by
  classical
  have hα₀ : 0 < α := by linarith
  obtain ⟨T₀, w₀, hT₀, hm₀, hc₀, _, hv₀, hl₀⟩ :=
    exists_local_fractional_riccati_point_charge hα q b c
  have hloc₀ : ContinuousPointChargeOn α q b c T₀ w₀ := ⟨hm₀, hc₀, hv₀, hl₀⟩
  let S : Set ℝ := {T | 0 < T ∧ ∃ w, ContinuousPointChargeOn α q b c T w}
  have hS₀ : T₀ ∈ S := ⟨hT₀, w₀, hloc₀⟩
  have hS : S.Nonempty := ⟨T₀, hS₀⟩
  let U : Set ℝ := ⋃ T ∈ S, Ioo 0 T
  have hU_def (t : ℝ) : t ∈ U ↔ ∃ T ∈ S, t ∈ Ioo 0 T := by
    simp only [U, mem_iUnion, exists_prop]
  have hU_open : IsOpen U := isOpen_biUnion fun _ _ => isOpen_Ioo
  have choose_local (t : U) : ∃ T, ∃ v, (t : ℝ) ∈ Ioo 0 T ∧
      ContinuousPointChargeOn α q b c T v := by
    obtain ⟨T, hT, ht⟩ := (hU_def t).mp t.property
    have hT' : T ∈ S := hT
    obtain ⟨_, v, hv⟩ := hT'
    exact ⟨T, v, ht, hv⟩
  choose horizon V htime hV using choose_local
  let w (t : ℝ) := if ht : t ∈ U then V ⟨t, ht⟩ t else 0
  have hmatch {T : ℝ} {v : ℝ → ℝ} (hT : T ∈ S)
      (hv : ContinuousPointChargeOn α q b c T v) : EqOn w v (Ioo 0 T) := by
    intro t ht
    have htU : t ∈ U := (hU_def t).mpr ⟨T, hT, ht⟩
    change (if h : t ∈ U then V ⟨t,h⟩ t else 0) = v t
    rw [dite_eq_left htU]
    exact (hV ⟨t, htU⟩).eq_of_lt_horizons hα hα' hq hb hc hv
      ht.1 (htime ⟨t, htU⟩).2 ht.2
  have hwcont : ContinuousOn w U := by
    intro t ht
    obtain ⟨T, hT, htT⟩ := (hU_def t).mp ht
    have hT' : T ∈ S := hT
    obtain ⟨_, v, hv⟩ := hT'
    have hIoo : ∀ᶠ s in 𝓝 t, s ∈ Ioo 0 T := Ioo_mem_nhds htT.1 htT.2
    have hnear : ∀ᶠ s in 𝓝 t, w s = v s := hIoo.mono fun s hs => hmatch hT hv hs
    exact ((hv.continuousOn.continuousAt (Ioi_mem_nhds htT.1)).congr_of_eventuallyEq hnear).continuousWithinAt
  have hzero {t : ℝ} (ht : t ∉ U) : w t = 0 := dite_eq_right ht
  have hwm : Measurable w := by
    apply measurable_of_restrict_of_restrict_compl hU_open.measurableSet
    · exact (continuousOn_iff_continuous_domRestrict.mp hwcont).measurable
    · have hconst : (Uᶜ.domRestrict w) = fun _ => (0 : ℝ) := by
        funext t
        exact hzero t.property
      rw [hconst]
      exact measurable_const
  have hwvol (t : ℝ) (ht : t ∈ U) : w t = q*fractionalK α t +
      volterraConvolution (fractionalK α) (fun s => b*w s+c*w s^2) t := by
    obtain ⟨T, hT, htT⟩ := (hU_def t).mp ht
    have hT' : T ∈ S := hT
    obtain ⟨_, v, hv⟩ := hT'
    rw [hmatch hT hv htT, hv.volterra t ⟨htT.1, htT.2.le⟩]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    change fractionalK α (t-s)*(b*v s+c*v s^2) = fractionalK α (t-s)*(b*w s+c*w s^2)
    rw [hmatch hT hv (show s ∈ Ioo 0 T from ⟨hs.1, hs.2.trans_lt htT.2⟩)]
  have hwlim : Tendsto (fun s => s^(1-α)*w s) (𝓝[>] 0) (𝓝 (q/Real.Gamma α)) := by
    refine hl₀.congr' ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hT₀)] with s hs hst
    rw [hmatch hS₀ hloc₀ (show s ∈ Ioo 0 T₀ from ⟨hs, hst⟩)]
  have hwbound (t : ℝ) (ht : t ∈ U) : 0 < w t ∧ w t ≤ q*fractionalK α t := by
    obtain ⟨T, hT, htT⟩ := (hU_def t).mp ht
    have hT' : T ∈ S := hT
    obtain ⟨_, v, hv⟩ := hT'
    rw [hmatch hT hv htT]
    exact hv.pos_le_charge_kernel hα hα' hq hb hc htT
  have hS_unbounded : ¬ BddAbove S := by
    intro hS_bdd
    let A := sSup S
    have hA₀ : T₀ ≤ A := le_csSup hS_bdd hS₀
    have hA : 0 < A := hT₀.trans_le hA₀
    have hU : U = Ioo 0 A := by
      ext t
      constructor
      · intro ht
        obtain ⟨T, hT, htT⟩ := (hU_def t).mp ht
        exact ⟨htT.1, htT.2.trans_le (le_csSup hS_bdd hT)⟩
      · intro ht
        obtain ⟨T, hT, htT⟩ := exists_lt_of_lt_csSup hS ht.2
        exact (hU_def t).mpr ⟨T, hT, ht.1, htT⟩
    let d := T₀/2
    have hd : 0 < d := by dsimp [d]; linarith
    have hdT : d < T₀ := by dsimp [d]; linarith
    have hdA := hdT.trans_le hA₀
    let B := q * fractionalK α d
    have hB : 0 ≤ B := by
      dsimp [B, fractionalK]
      rw [ite_eq_right (not_le.mpr hd)]
      positivity
    have hTail (s : ℝ) (hs : s ∈ Ioc d A) : ‖w s‖ ≤ B := by
      rcases lt_or_eq_of_le hs.2 with hsa | hsa
      · have hsU : s ∈ U := hU.symm ▸ (show s ∈ Ioo 0 A from ⟨hd.trans hs.1, hsa⟩)
        obtain ⟨hsp, hsb⟩ := hwbound s hsU
        have hk : fractionalK α s ≤ fractionalK α d := by
          simp only [fractionalK, ite_eq_right (not_le.mpr (hd.trans hs.1)), ite_eq_right (not_le.mpr hd)]
          exact div_le_div_of_nonneg_right
            (Real.rpow_le_rpow_of_nonpos hd hs.1.le (by linarith))
            (Real.Gamma_pos_of_pos hα₀).le
        simpa [Real.norm_of_nonneg hsp.le] using hsb.trans (mul_le_mul_of_nonneg_left hk hq.le)
      · subst s
        rw [hzero (by simp [hU]), norm_zero]
        exact hB
    have hOldIntegrable : IntegrableOn (fun s => b*w s+c*w s^2) (Ioc 0 d) := by
      have ⟨hi₁, hi₂⟩ := integrableOn_riccati_powers_of_weighted_asymptotic hα hd hm₀ hc₀ hl₀
      refine ((hi₁.const_mul b).add (hi₂.const_mul c)).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      change b*w₀ s+c*w₀ s^2 = b*w s+c*w s^2
      rw [hmatch hS₀ hloc₀ (show s ∈ Ioo 0 T₀ from ⟨hs.1, hs.2.trans_lt hdT⟩)]
    obtain ⟨W, hWm, hWc, hWw, hWv⟩ :=
      exists_point_charge_riccati_endpoint hα₀ hα' hd hdA hwm (hU ▸ hwcont) hB hTail
        hOldIntegrable (fun t ht => hwvol t (hU.symm ▸ ht))
    have hWlim : Tendsto (fun s => s^(1-α)*W s) (𝓝[>] 0) (𝓝 (q/Real.Gamma α)) := by
      refine hwlim.congr' ?_
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hA)] with t ht
      rw [hWw (show t ∈ Iio A from ht)]
    have ⟨hWi₁, hWi₂⟩ := integrableOn_riccati_powers_of_weighted_asymptotic hα hA hWm hWc hWlim
    obtain ⟨e, he, F, hFm, hFc, hFW, hFv⟩ := exists_point_charge_riccati_continuation
      hα₀ hα' hA (zero_lt_one) hWm (hWc.mono Ioc_subset_Ioi_self)
      ((hWi₁.const_mul b).add (hWi₂.const_mul c)) hWv
    have hFlim : Tendsto (fun s => s^(1-α)*F s) (𝓝[>] 0) (𝓝 (q/Real.Gamma α)) := by
      refine hWlim.congr' ?_
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hA)] with t ht
      rw [hFW (show t ∈ Iic A from (show t < A from ht).le)]
    have hAS : A+e ∈ S := ⟨add_pos hA he.1, F, hFm, hFc, hFv, hFlim⟩
    exact (not_le_of_gt (lt_add_of_pos_right A he.1)) (le_csSup hS_bdd hAS)
  have hU_pos : U = Ioi 0 := by
    ext t
    constructor
    · intro ht
      obtain ⟨_, _, ht⟩ := (hU_def t).mp ht
      exact ht.1
    · intro ht
      obtain ⟨T, hT, htT⟩ := not_bddAbove_iff.mp hS_unbounded t
      exact (hU_def t).mpr ⟨T, hT, ht, htT⟩
  exact ⟨w, fun _ => PointChargeRiccatiOn.of_global_volterra hα hα' hwm (hU_pos ▸ hwcont)
      (fun t ht => hwvol t (hU_pos.symm ▸ ht)) hwlim,
    fun t ht => hwbound t (hU_pos.symm ▸ ht)⟩

/-- Positive-charge global solutions agree at every positive time. -/
theorem eqOn_global_fractional_riccati_point_charge
    {α q b c : ℝ} {v w : ℝ → ℝ}
    (hα : 1/2 < α) (hα' : α < 1) (hq : 0 < q) (hb : b ≤ 0) (hc : c ≤ 0)
    (hv : ∀ T : ℝ, PointChargeRiccatiOn α q b c T v)
    (hw : ∀ T : ℝ, PointChargeRiccatiOn α q b c T w) : EqOn v w (Ioi 0) := by
  intro t ht
  exact point_charge_riccati_eqOn_of_nonpositive_drift hα hα' (show 0 < t from ht)
    hq hb hc (hv t) (hw t) ⟨ht, le_rfl⟩

#print axioms exists_global_fractional_riccati_point_charge
#print axioms eqOn_global_fractional_riccati_point_charge

end RoughHeston
