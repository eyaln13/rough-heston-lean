import StochasticFoundation

open MeasureTheory Filter
open scoped MeasureTheory ProbabilityTheory ENNReal NNReal

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

private theorem weighted_two_increments_integrable (hM₂ : ∀ t, MemLp (M t) 2 μ)
    {w : Ω → ℝ} (hw : MemLp w ⊤ μ) (a b c d : ℝ≥0) :
    Integrable (fun ω => w ω * ((M b ω - M a ω) * (M d ω - M c ω))) μ := by
  have hprod : MemLp ((M b - M a) * (M d - M c)) 1 μ :=
    ((hM₂ b).sub (hM₂ a)).mul ((hM₂ d).sub (hM₂ c))
  exact (hw.mul hprod : MemLp (w * ((M b - M a) * (M d - M c))) 1 μ).integrable le_rfl

private theorem weighted_increment_zero (hM : Martingale M F μ) (hM₂ : ∀ t, MemLp (M t) 2 μ)
    {a b : ℝ≥0} (hab : a ≤ b) {w : Ω → ℝ} (hwa : StronglyMeasurable[F a] w)
    (hw : MemLp w 2 μ) : (∫ ω, w ω * (M b ω - M a ω) ∂μ) = 0 := by
  let d := M b - M a
  have hd := (hM₂ b).sub (hM₂ a)
  have hwd : Integrable (w * d) μ := (hw.mul hd : MemLp (w * d) 1 μ).integrable le_rfl
  have hcond : μ[w * d | F a] =ᵐ[μ] (0 : Ω → ℝ) := by
    have h := (condExp_mul_of_stronglyMeasurable_left hwa hwd (hd.integrable (by norm_num))).trans
      (EventuallyEq.rfl.mul (conditional_mean_martingale_increment hM hab))
    simpa only [mul_zero] using h
  calc
    _ = ∫ ω, (μ[w * d | F a]) ω ∂μ := (integral_condExp (F.le a)).symm
    _ = 0 := by simp only [integral_congr_ae hcond, Pi.zero_apply, integral_zero]

private theorem weighted_increment_clock (hM : Martingale M F μ) (hM₂ : ∀ t, MemLp (M t) 2 μ)
    (hclock : Martingale (fun t ω => M t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) F μ)
    {a b : ℝ≥0} (hab : a ≤ b) (hbT : b ≤ T) {w : Ω → ℝ}
    (hwa : StronglyMeasurable[F a] w) (hw : MemLp w ⊤ μ) :
    (∫ ω, w ω * ((M b ω - M a ω) * (M b ω - M a ω)) ∂μ) =
      (∫ ω, w ω ∂μ) * ((b : ℝ) - a) := by
  let d := M b - M a
  let C (t : ℝ≥0) : Ω → ℝ := fun _ => ((min t T : ℝ≥0) : ℝ)
  have hsq : Martingale (fun t => M t * M t - C t) F μ := by
    convert hclock using 1
    funext t ω
    simp [C, pow_two]
  have hv := conditional_covariance_of_compensated_product hM hM hsq hM₂ hM₂ hab
  have hC : C b - C a = fun _ => (b : ℝ) - a := by
    funext ω
    simp only [C, Pi.sub_apply, min_eq_left hbT, min_eq_left (hab.trans hbT)]
  rw [hC, condExp_const (F.le a)] at hv
  have hd := (hM₂ b).sub (hM₂ a)
  have hdd : MemLp (d * d) 1 μ := hd.mul hd
  have hwdd : Integrable (w * (d * d)) μ :=
    (hw.mul hdd : MemLp (w * (d * d)) 1 μ).integrable le_rfl
  have hcond := (condExp_mul_of_stronglyMeasurable_left hwa hwdd
    (hdd.integrable le_rfl)).trans (EventuallyEq.rfl.mul hv)
  calc
    _ = ∫ ω, (μ[w * (d * d) | F a]) ω ∂μ := (integral_condExp (F.le a)).symm
    _ = ∫ ω, w ω * ((b : ℝ) - a) ∂μ := integral_congr_ae hcond
    _ = _ := integral_mul_const _ _

private theorem weighted_nested_increments (hM : Martingale M F μ)
    (hM₂ : ∀ t, MemLp (M t) 2 μ)
    (hclock : Martingale (fun t ω => M t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) F μ)
    {a b c : ℝ≥0} (hab : a ≤ b) (hbc : b ≤ c) (hbT : b ≤ T)
    {w : Ω → ℝ} (hwa : StronglyMeasurable[F a] w) (hw : MemLp w ⊤ μ) :
    (∫ ω, w ω * ((M b ω - M a ω) * (M c ω - M a ω)) ∂μ) =
      (∫ ω, w ω ∂μ) * ((b : ℝ) - a) := by
  have hwa' : StronglyMeasurable[F b] (w * (M b - M a)) :=
    (hwa.mono (F.mono hab)).mul ((hM.stronglyMeasurable b).sub
      ((hM.stronglyMeasurable a).mono (F.mono hab)))
  have hw₂ : MemLp (w * (M b - M a)) 2 μ :=
    hw.mul ((hM₂ b).sub (hM₂ a))
  have hzero : (∫ ω, w ω * ((M b ω - M a ω) * (M c ω - M b ω)) ∂μ) = 0 := by
    simpa only [Pi.mul_apply, Pi.sub_apply, mul_assoc] using
      weighted_increment_zero hM hM₂ hbc hwa' hw₂
  have ha := weighted_two_increments_integrable hM₂ hw a b b c
  have hb := weighted_two_increments_integrable hM₂ hw a b a b
  calc
    _ = (∫ ω, w ω * ((M b ω - M a ω) * (M c ω - M b ω)) ∂μ)
        + ∫ ω, w ω * ((M b ω - M a ω) * (M b ω - M a ω)) ∂μ := by
      rw [← integral_add ha hb]
      exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
    _ = _ := by rw [hzero, zero_add, weighted_increment_clock hM hM₂ hclock hab hbT hwa hw]

private theorem weighted_rect_increment_pairing_ordered (hM : Martingale M F μ)
    (hM₂ : ∀ r, MemLp (M r) 2 μ)
    (hclock : Martingale (fun r ω => M r ω ^ 2 - ((min r T : ℝ≥0) : ℝ)) F μ)
    {s t u v : ℝ≥0} (hsu : s ≤ u) (huv : u ≤ v) (htT : t ≤ T) (hvT : v ≤ T)
    {f g : Ω → ℝ} (hf : StronglyMeasurable[F s] f) (hg : StronglyMeasurable[F u] g)
    (hfTop : MemLp f ⊤ μ) (hgTop : MemLp g ⊤ μ) :
    (∫ ω, (f ω * (M t ω - M s ω)) * (g ω * (M v ω - M u ω)) ∂μ) =
      (∫ ω, f ω * g ω ∂μ) * max 0 (min (t : ℝ) v - max (s : ℝ) u) := by
  have hfg : StronglyMeasurable[F u] (f * g) := (hf.mono (F.mono hsu)).mul hg
  have hfgTop : MemLp (f * g) ⊤ μ := hfTop.mul hgTop
  rw [max_eq_right (show (s : ℝ) ≤ (u : ℝ) by exact_mod_cast hsu)]
  have hdisjoint (d : ℝ≥0) (hd : d ≤ u) :
      (∫ ω, (f ω * g ω) * ((M d ω - M s ω) * (M v ω - M u ω)) ∂μ) = 0 := by
    have hwa : StronglyMeasurable[F u] ((f * g) * (M d - M s)) :=
      hfg.mul (((hM.stronglyMeasurable d).mono (F.mono hd)).sub
        ((hM.stronglyMeasurable s).mono (F.mono hsu)))
    have hw : MemLp ((f * g) * (M d - M s)) 2 μ :=
      hfgTop.mul ((hM₂ d).sub (hM₂ s))
    simpa only [Pi.mul_apply, Pi.sub_apply, mul_assoc] using
      weighted_increment_zero hM hM₂ huv hwa hw
  by_cases htu : t ≤ u
  · have hz : min (t : ℝ) v - (u : ℝ) ≤ 0 :=
      sub_nonpos.mpr ((min_le_left _ _).trans (by exact_mod_cast htu))
    rw [max_eq_left hz, mul_zero, ← hdisjoint t htu]
    exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
  · have hut : u ≤ t := (lt_of_not_ge htu).le
    have hov : (∫ ω, (f ω * g ω) * ((M t ω - M u ω) * (M v ω - M u ω)) ∂μ) =
        (∫ ω, f ω * g ω ∂μ) * (min (t : ℝ) v - u) := by
      rcases le_total t v with htv | hvt
      · rw [min_eq_left (show (t : ℝ) ≤ (v : ℝ) by exact_mod_cast htv)]
        exact weighted_nested_increments hM hM₂ hclock hut htv htT hfg hfgTop
      · rw [min_eq_right (show (v : ℝ) ≤ (t : ℝ) by exact_mod_cast hvt)]
        calc
          _ = ∫ ω, (f ω * g ω) * ((M v ω - M u ω) * (M t ω - M u ω)) ∂μ :=
            integral_congr_ae (Eventually.of_forall fun ω => by ring)
          _ = _ := weighted_nested_increments hM hM₂ hclock huv hvt hvT hfg hfgTop
    have hn : 0 ≤ min (t : ℝ) v - (u : ℝ) :=
      sub_nonneg.mpr (le_min (by exact_mod_cast hut) (by exact_mod_cast huv))
    have hi₁ := weighted_two_increments_integrable hM₂ hfgTop s u u v
    have hi₂ := weighted_two_increments_integrable hM₂ hfgTop u t u v
    simp only [Pi.mul_apply] at hi₁ hi₂
    calc
      _ = (∫ ω, (f ω * g ω) * ((M u ω - M s ω) * (M v ω - M u ω)) ∂μ)
          + ∫ ω, (f ω * g ω) * ((M t ω - M u ω) * (M v ω - M u ω)) ∂μ := by
        rw [← integral_add hi₁ hi₂]
        exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
      _ = _ := by rw [hdisjoint u le_rfl, hov, zero_add, max_eq_right hn]

/-- The pairing of two bounded, past-measurable weighted increments is
their weight pairing times the length of the overlap of the intervals. -/
theorem joint_rect_increment_pairing (hM : Martingale M F μ)
    (hM₂ : ∀ r, MemLp (M r) 2 μ)
    (hclock : Martingale (fun r ω => M r ω ^ 2 - ((min r T : ℝ≥0) : ℝ)) F μ)
    {s t u v : ℝ≥0} (hst : s ≤ t) (huv : u ≤ v) (htT : t ≤ T) (hvT : v ≤ T)
    {f g : Ω → ℝ} (hf : StronglyMeasurable[F s] f) (hg : StronglyMeasurable[F u] g)
    (hfTop : MemLp f ⊤ μ) (hgTop : MemLp g ⊤ μ) :
    (∫ ω, (f ω * (M t ω - M s ω)) * (g ω * (M v ω - M u ω)) ∂μ) =
      (∫ ω, f ω * g ω ∂μ) * max 0 (min (t : ℝ) v - max (s : ℝ) u) := by
  rcases le_total s u with hsu | hus
  · exact weighted_rect_increment_pairing_ordered hM hM₂ hclock hsu huv htT hvT hf hg hfTop hgTop
  · calc
      _ = ∫ ω, (g ω * (M v ω - M u ω)) * (f ω * (M t ω - M s ω)) ∂μ :=
        integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
      _ = (∫ ω, g ω * f ω ∂μ) * max 0 (min (v : ℝ) t - max (u : ℝ) s) :=
        weighted_rect_increment_pairing_ordered hM hM₂ hclock hus hst hvT htT hg hf hgTop hfTop
      _ = _ := by rw [min_comm (v : ℝ), max_comm (u : ℝ), integral_congr_ae
        (Eventually.of_forall fun ω => mul_comm (g ω) (f ω))]

end RoughHeston

#print axioms RoughHeston.joint_rect_increment_pairing
