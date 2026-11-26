import DensityChargeRiccati

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RoughHeston

private theorem density_global_kernel_nonneg {α : ℝ} (hα : 0 < α) (x : ℝ) :
    0 ≤ fractionalK α x := by
  by_cases hx : x ≤ 0
  · simp [fractionalK, hx]
  · rw [fractionalK, ite_eq_right hx]
    exact div_nonneg (Real.rpow_nonneg (lt_of_not_ge hx).le _) (Real.Gamma_pos_of_pos hα).le

private theorem density_closed_interval_bounds
    {α l d b c A B : ℝ} {w : ℝ → ℝ}
    (hα : 1/2 < α) (hα' : α < 1) (hA : 0 < A) (hd : 0 < d) (hw : Continuous w)
    (h0 : w 0 = l) (hl : 0 ≤ l) (hlB : l < B) (hB : d+b*B+c*B^2 ≤ 0)
    (hV : ∀ s ∈ Icc 0 A, w s = l +
      volterraConvolution (fractionalK α) (fun u => d+b*w u+c*w u^2) s) :
    ∀ s ∈ Icc 0 A, 0 ≤ w s ∧ w s ≤ B := by
  have hIn := density_riccati_pos_lt_constant hα hα' hA hd hw (h0 ▸ hl) (h0 ▸ hlB) hB
    (by simpa only [h0] using hV)
  intro s hs
  rcases eq_or_lt_of_le hs.1 with hsz | hs₀
  · subst s
    exact ⟨h0.symm ▸ hl, h0.symm ▸ hlB.le⟩
  rcases lt_or_eq_of_le hs.2 with hsA | hsa
  · exact ⟨(hIn s ⟨hs₀, hsA⟩).1.le, (hIn s ⟨hs₀, hsA⟩).2.le⟩
  · subst s
    have hLim : Tendsto w (𝓝[<] A) (𝓝 (w A)) :=
      hw.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hnear : ∀ᶠ u in 𝓝[<] A, 0 ≤ w u ∧ w u ≤ B := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hA)] with u hu hu₀
      exact ⟨(hIn u ⟨hu₀,hu⟩).1.le, (hIn u ⟨hu₀,hu⟩).2.le⟩
    exact ⟨ge_of_tendsto hLim (hnear.mono fun _ hu => hu.1),
      le_of_tendsto hLim (hnear.mono fun _ hu => hu.2)⟩

private theorem extend_density_riccati_one_step
    {α l d b c A H B M ε : ℝ} {w : ℝ → ℝ}
    (hα : 0 < α) (hα' : α < 1) (hA : 0 < A) (hAH : A ≤ H)
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hB : 0 ≤ B) (hM : 0 ≤ M) (hw : Continuous w)
    (hb : ∀ s ∈ Icc 0 A, ‖w s‖ ≤ B)
    (hMineq : ‖l‖ + (‖d‖+‖b‖*B+‖c‖*B^2) * ((H+1)^α/Real.Gamma (α+1)) +
      ‖d‖*(1/Real.Gamma (α+1)) ≤ M)
    (hsmall : (‖b‖+2*‖c‖*(2*M+1))*(ε^α/Real.Gamma (α+1)) ≤ 1/2)
    (hV : ∀ s ∈ Icc 0 A, w s = l +
      volterraConvolution (fractionalK α) (fun u => d+b*w u+c*w u^2) s) :
    ∃ W : ℝ → ℝ, Continuous W ∧
      ∀ s ∈ Icc 0 (A+ε), W s = l +
        volterraConvolution (fractionalK α) (fun u => d+b*W u+c*W u^2) s := by
  let F (s : ℝ) := d+b*w s+c*w s^2
  have hF : Continuous F := (continuous_const.add (continuous_const.mul hw)).add
    (continuous_const.mul (hw.pow 2))
  let C := ‖d‖+‖b‖*B+‖c‖*B^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hFb (s : ℝ) (hs : s ∈ Icc 0 A) : ‖F s‖ ≤ C := by
    refine (norm_add_le _ _).trans ?_
    calc
      ‖d+b*w s‖+‖c*w s^2‖ ≤ ‖d‖+‖b*w s‖+‖c*w s^2‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ ≤ C := by
        rw [norm_mul, norm_mul, norm_pow]
        exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hb s hs) (norm_nonneg b)))
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hb s hs) 2) (norm_nonneg c))
  let G (x : ℝ) := l + riccatiShiftedHistory α 0 A F x + d*(x^α/Real.Gamma (α+1))
  have hGc : ContinuousOn G (Icc 0 ε) := by
    refine (continuousOn_const.add (continuousOn_riccatiShiftedHistory hα hα' hA hF.measurable
      (hF.intervalIntegrable 0 A).1 hF.continuousOn)).add ?_
    exact (continuous_const.mul ((Real.continuous_rpow_const hα.le).div_const _)).continuousOn
  have hGb (x : ℝ) (hx : x ∈ Icc 0 ε) : ‖G x‖ ≤ M := by
    let t := A+x
    have ht₀ : 0 ≤ t := add_nonneg hA.le hx.1
    have ht : t ∈ Icc 0 (H+1) := ⟨ht₀, add_le_add hAH (hx.2.trans hε₁)⟩
    let k (s : ℝ) := fractionalK α (t-s)
    have hkI := density_conv_integrable (g := fun _ => (1 : ℝ)) hα ht continuous_const
    simp only [mul_one] at hkI
    have hFI := density_conv_integrable hα ht hF
    have hSub : Ioc (0 : ℝ) A ⊆ Ioc 0 t := Ioc_subset_Ioc_right (le_add_of_nonneg_right hx.1)
    have hFIA : IntegrableOn (fun s => k s*F s) (Ioc 0 A) := hFI.mono_set hSub
    have hkIA : IntegrableOn k (Ioc 0 A) := hkI.mono_set hSub
    have hNorm : ‖riccatiShiftedHistory α 0 A F x‖ ≤ C*((H+1)^α/Real.Gamma (α+1)) := by
      simp only [riccatiShiftedHistory, zero_mul, zero_add]
      change ‖∫ s in Ioc (0 : ℝ) A, k s*F s‖ ≤ _
      refine (norm_integral_le_integral_norm _).trans ?_
      have hcI := setIntegral_mono_on hFIA.norm (hkIA.const_mul C) measurableSet_Ioc (fun s hs => by
        have hkn : 0 ≤ k s := density_global_kernel_nonneg hα _
        rw [norm_mul, Real.norm_of_nonneg hkn]
        exact (mul_le_mul_of_nonneg_left (hFb s (Ioc_subset_Icc_self hs)) hkn).trans_eq (mul_comm _ _))
      rw [integral_const_mul] at hcI
      refine hcI.trans (mul_le_mul_of_nonneg_left ?_ hC)
      have hbI := setIntegral_mono_set hkI (ae_of_all _ fun s => density_global_kernel_nonneg hα (t-s))
        hSub.eventuallyLE
      change (∫ s in Ioc (0 : ℝ) A, k s) ≤ _ 
      change (∫ s in Ioc (0 : ℝ) A, k s) ≤ ∫ s in Ioc (0 : ℝ) t, fractionalK α (t-s) at hbI
      rw [density_fractionalK_mass hα ht₀] at hbI
      exact hbI.trans (div_le_div_of_nonneg_right (Real.rpow_le_rpow ht₀ ht.2 hα.le)
        (Real.Gamma_pos_of_pos (by linarith)).le)
    have hMass : x^α/Real.Gamma (α+1) ≤ 1/Real.Gamma (α+1) := by
      refine div_le_div_of_nonneg_right ?_ (Real.Gamma_pos_of_pos (by linarith)).le
      simpa only [Real.one_rpow] using Real.rpow_le_rpow hx.1 (hx.2.trans hε₁) hα.le
    have hMx : 0 ≤ x^α/Real.Gamma (α+1) :=
      div_nonneg (Real.rpow_nonneg hx.1 _) (Real.Gamma_pos_of_pos (by linarith)).le
    calc
      ‖G x‖ ≤ ‖l+riccatiShiftedHistory α 0 A F x‖ + ‖d*(x^α/Real.Gamma (α+1))‖ := norm_add_le _ _
      _ ≤ ‖l‖ + C*((H+1)^α/Real.Gamma (α+1)) + ‖d‖*(1/Real.Gamma (α+1)) := by
        rw [norm_mul, Real.norm_of_nonneg hMx]
        exact add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl hNorm))
          (mul_le_mul_of_nonneg_left hMass (norm_nonneg _))
      _ ≤ M := hMineq
  obtain ⟨y, hy, _, hyV⟩ := exists_forced_riccati_on_small_interval hα hε hM hGc hGb hsmall
  have hy₀ : y 0 = w A := by
    have he := hyV 0 ⟨le_rfl, hε.le⟩
    rw [hV A ⟨hA.le, le_rfl⟩]
    simpa [G, riccatiShiftedHistory, volterraConvolution, F, Real.zero_rpow hα.ne'] using he
  let W (s : ℝ) := if s ≤ A then w s else y (s-A)
  have hLeft (s : ℝ) (hs : s ≤ A) : W s = w s := ite_eq_left hs
  have hRight (s : ℝ) (hs : A ≤ s) : W s = y (s-A) := by
    rcases lt_or_eq_of_le hs with has | hes
    · exact ite_eq_right (not_le.mpr has)
    · subst s
      rw [hLeft A le_rfl, sub_self, hy₀]
  have hW : Continuous W := by
    rw [← continuousOn_univ, ← (Iic_union_Ici (a := A)),
      continuousOn_union_iff_of_isClosed isClosed_Iic isClosed_Ici]
    exact ⟨hw.continuousOn.congr (fun s hs => hLeft s hs),
      (hy.comp (continuous_id.sub continuous_const)).continuousOn.congr (fun s hs => hRight s hs)⟩
  refine ⟨W, hW, ?_⟩
  intro t ht
  by_cases hta : t ≤ A
  · rw [hLeft t hta, hV t ⟨ht.1, hta⟩]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    change fractionalK α (t-s)*F s = fractionalK α (t-s)*(d+b*W s+c*W s^2)
    rw [hLeft s (hs.2.trans hta)]
  · have ha : A < t := lt_of_not_ge hta
    have hx : t-A ∈ Icc 0 ε := ⟨sub_nonneg.mpr ha.le, by linarith [ht.2]⟩
    let f (s : ℝ) := fractionalK α (t-s)*(d+b*W s+c*W s^2)
    have hFcont : Continuous (fun s => d+b*W s+c*W s^2) :=
      (continuous_const.add (continuous_const.mul hW)).add (continuous_const.mul (hW.pow 2))
    have hf : IntegrableOn f (Ioc 0 t) := density_conv_integrable hα ht hFcont
    have hSplit : (∫ s in Ioc (0 : ℝ) t, f s) = (∫ s in Ioc (0 : ℝ) A, f s) +
        (∫ s in Ioc A t, f s) := by
      rw [← Ioc_union_Ioc_eq_Ioc hA.le ha.le]
      exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
        (hf.mono_set (Ioc_subset_Ioc_right ha.le)) (hf.mono_set (Ioc_subset_Ioc_left hA.le))
    have hOld : (∫ s in Ioc (0 : ℝ) A, f s) = riccatiShiftedHistory α 0 A F (t-A) := by
      simp only [riccatiShiftedHistory, zero_mul, zero_add]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      change fractionalK α (t-s)*(d+b*W s+c*W s^2) = fractionalK α (A+(t-A)-s)*F s
      rw [hLeft s hs.2, show A+(t-A)-s=t-s by ring]
    have hNew : (∫ s in Ioc A t, f s) = d*((t-A)^α/Real.Gamma (α+1)) +
        volterraConvolution (fractionalK α) (fun s => b*y s+c*y s^2) (t-A) := by
      have hShift := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := t-A) f A
      rw [zero_add, sub_add_cancel, intervalIntegral.integral_of_le ha.le,
        intervalIntegral.integral_of_le hx.1] at hShift
      rw [← hShift]
      let k (s : ℝ) := fractionalK α (t-A-s)
      have he : EqOn (fun s : ℝ => f (s+A)) (fun s => k s*d+k s*(b*y s+c*y s^2))
          (Ioc 0 (t-A)) := by
        intro s hs
        dsimp [f, k]
        rw [hRight (s+A) (by linarith [hs.1]),
          show s+A-A=s by ring, show t-(s+A)=t-A-s by ring]
        ring
      rw [setIntegral_congr_fun measurableSet_Ioc he]
      have hK : IntegrableOn k (Ioc 0 (t-A)) := by
        simpa only [mul_one] using (density_conv_integrable (g := fun _ => (1 : ℝ)) hα hx continuous_const)
      have hPoly : Continuous (fun s => b*y s+c*y s^2) :=
        (continuous_const.mul hy).add (continuous_const.mul (hy.pow 2))
      rw [integral_add (hK.mul_const d) (density_conv_integrable hα hx hPoly), integral_mul_const]
      change (∫ s in Ioc (0 : ℝ) (t-A), fractionalK α (t-A-s))*d +
        volterraConvolution (fractionalK α) (fun s => b*y s+c*y s^2) (t-A) = _
      rw [density_fractionalK_mass hα hx.1, mul_comm d]
    rw [hRight t ha.le, hyV (t-A) hx]
    change G (t-A)+volterraConvolution (fractionalK α) (fun s => b*y s+c*y s^2) (t-A)
      = l+∫ s in Ioc (0 : ℝ) t, f s
    rw [hSplit, hOld, hNew]
    dsimp [G]
    ring

/-- Every finite horizon admits a continuous density-charge solution when
a constant upper barrier lies above the initial value. -/
theorem exists_density_riccati_on_horizon
    {α l d b c B : ℝ}
    (hα : 1/2 < α) (hα' : α < 1) (hd : 0 < d) (hl : 0 ≤ l) (hlB : l < B)
    (hB : d+b*B+c*B^2 ≤ 0) (T : ℝ) :
    ∃ w : ℝ → ℝ, Continuous w ∧ w 0 = l ∧
      (∀ s ∈ Icc 0 T, w s = l +
        volterraConvolution (fractionalK α) (fun u => d+b*w u+c*w u^2) s) ∧
      ∀ s ∈ Icc 0 T, 0 ≤ w s ∧ w s ≤ B := by
  have hα₀ : 0 < α := by linarith
  let S : Set ℝ := {A | 0 < A ∧ ∃ w : ℝ → ℝ, Continuous w ∧ w 0 = l ∧
    ∀ s ∈ Icc 0 A, w s = l + volterraConvolution (fractionalK α) (fun u => d+b*w u+c*w u^2) s}
  obtain ⟨A₀, hA₀, w₀, hw₀, hl₀, hV₀⟩ := exists_local_density_riccati
    (l := l) (d := d) (b := b) (c := c) hα₀ zero_lt_one
  have hS₀ : A₀ ∈ S := ⟨hA₀.1, w₀, hw₀, hl₀, hV₀⟩
  have hS : S.Nonempty := ⟨A₀,hS₀⟩
  have hSunbounded : ¬ BddAbove S := by
    intro hSbd
    let H := sSup S
    have hH : 0 < H := hA₀.1.trans_le (le_csSup hSbd hS₀)
    let M := ‖l‖ + (‖d‖+‖b‖*B+‖c‖*B^2) * ((H+1)^α/Real.Gamma (α+1)) +
      ‖d‖*(1/Real.Gamma (α+1))
    have hB₀ : 0 ≤ B := hl.trans hlB.le
    have hM : 0 ≤ M := by dsimp [M]; positivity
    let L := ‖b‖+2*‖c‖*(2*M+1)
    let Q (r : ℝ) := L*(r^α/Real.Gamma (α+1))
    have hQ : Continuous Q := continuous_const.mul ((Real.continuous_rpow_const hα₀.le).div_const _)
    have hQ₀ : Q 0 < 1/2 := by simp [Q, Real.zero_rpow hα₀.ne']
    obtain ⟨r, hr, hnear⟩ := Metric.eventually_nhds_iff.mp
      (hQ.continuousAt.eventually_lt continuousAt_const hQ₀)
    let ε := min 1 (r/2)
    have hε : 0 < ε := lt_min zero_lt_one (by positivity)
    have hε₁ : ε ≤ 1 := min_le_left _ _
    have hεr : dist ε 0 < r := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hε.le]
      exact (min_le_right _ _).trans_lt (by linarith)
    have hsmall : L*(ε^α/Real.Gamma (α+1)) ≤ 1/2 := (hnear hεr).le
    obtain ⟨A,hAS,hAnear⟩ := exists_lt_of_lt_csSup hS (show H-ε < H by linarith)
    have hAH := le_csSup hSbd hAS
    obtain ⟨hA,w,hw,hw₀,hV⟩ := hAS
    have hwb (s : ℝ) (hs : s ∈ Icc 0 A) : ‖w s‖ ≤ B := by
      obtain ⟨h₁,h₂⟩ := density_closed_interval_bounds hα hα' hA hd hw hw₀ hl hlB hB hV s hs
      exact (Real.norm_of_nonneg h₁).trans_le h₂
    obtain ⟨W,hW,hWV⟩ := extend_density_riccati_one_step hα₀ hα' hA hAH hε hε₁ hB₀ hM hw
      hwb le_rfl hsmall hV
    have hW₀ : W 0 = l := by
      simpa [volterraConvolution] using hWV 0 ⟨le_rfl, (add_pos hA hε).le⟩
    have hnew : A+ε ∈ S := ⟨add_pos hA hε, W, hW, hW₀, hWV⟩
    have hcontr := le_csSup hSbd hnew
    change A+ε ≤ H at hcontr
    linarith
  obtain ⟨A,hAS,hAT⟩ := not_bddAbove_iff.mp hSunbounded T
  obtain ⟨hA,w,hw,hw₀,hV⟩ := hAS
  have hSub : Icc (0 : ℝ) T ⊆ Icc 0 A := Icc_subset_Icc_right hAT.le
  exact ⟨w,hw,hw₀,fun s hs => hV s (hSub hs),
    fun s hs => density_closed_interval_bounds hα hα' hA hd hw hw₀ hl hlB hB hV s (hSub hs)⟩

/-- The cluster density forcing gives a solution family uniformly bounded
on any finite horizon for initial values in the unit interval. -/
theorem exists_cluster_density_riccati_family
    {α q κ a : ℝ}
    (hα : 1/2 < α) (hα' : α < 1) (hq : 0 < q) (hκ : 0 ≤ κ) (ha : 0 < a) (T : ℝ) :
    ∃ (B : ℝ) (w : ℝ → ℝ → ℝ), 0 ≤ B ∧
      (∀ l ∈ Icc (0 : ℝ) 1, Continuous (w l)) ∧
      (∀ l ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 T, ‖w l t‖ ≤ B) ∧
      ∀ l ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 T,
        w l t = l+volterraConvolution (fractionalK α)
          (fun s => q+κ*l-κ*w l s-a*(w l s)^2) t := by
  let B := 2+(q+κ)/a
  have hm : 0 ≤ (q+κ)/a := div_nonneg (add_nonneg hq.le hκ) ha.le
  have hB₁ : 1 < B := by dsimp [B]; linarith
  have hB : 0 ≤ B := zero_le_one.trans hB₁.le
  have hqκ : q+κ ≤ a*B^2 := by
    have hBa : (q+κ)/a ≤ B := by dsimp [B]; linarith
    have hBquad : B ≤ B^2 := by nlinarith [mul_nonneg hB (sub_nonneg.mpr hB₁.le)]
    exact (div_le_iff₀ ha).mp (hBa.trans hBquad) |>.trans_eq (mul_comm _ _)
  have hex (l : ℝ) (hl : l ∈ Icc 0 1) : ∃ w : ℝ → ℝ, Continuous w ∧
      (∀ t ∈ Icc 0 T, ‖w t‖ ≤ B) ∧
      ∀ t ∈ Icc 0 T, w t = l+volterraConvolution (fractionalK α)
        (fun s => q+κ*l-κ*w s-a*(w s)^2) t := by
    have hd : 0 < q+κ*l := hq.trans_le (le_add_of_nonneg_right (mul_nonneg hκ hl.1))
    have hs : q+κ*l + (-κ)*B + (-a)*B^2 ≤ 0 := by
      have hκl := mul_le_mul_of_nonneg_left hl.2 hκ
      have hn : 0 ≤ κ*B := mul_nonneg hκ hB
      linarith
    obtain ⟨w, hw, _, hv, hb⟩ :=
      exists_density_riccati_on_horizon hα hα' hd hl.1 (hl.2.trans_lt hB₁) hs T
    exact ⟨w,hw,fun t ht => (Real.norm_of_nonneg (hb t ht).1).trans_le (hb t ht).2,
      by simpa only [neg_mul, sub_eq_add_neg] using hv⟩
  classical
  choose w hw hwb hwV using hex
  let W (l : ℝ) := if hl : l ∈ Icc (0 : ℝ) 1 then w l hl else fun _ => 0
  have hW (l : ℝ) (hl : l ∈ Icc (0 : ℝ) 1) : W l = w l hl := dite_eq_left hl
  exact ⟨B,W,hB,fun l hl => hW l hl ▸ hw l hl,fun l hl => hW l hl ▸ hwb l hl,
    fun l hl => hW l hl ▸ hwV l hl⟩

#print axioms exists_density_riccati_on_horizon
#print axioms exists_cluster_density_riccati_family

end RoughHeston
