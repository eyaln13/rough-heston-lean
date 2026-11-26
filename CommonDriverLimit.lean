import StochasticCovariation

/-!
Removal of the regularization in the common-driver construction.
The input is a family of continuous martingales whose pairwise
compensated products have the specified integral densities.
-/

open MeasureTheory Filter Set
open scoped MeasureTheory ProbabilityTheory Topology NNReal ENNReal

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

/-- Freeze a martingale at a deterministic time while retaining the original
filtration. -/
theorem martingale_freeze_at [IsFiniteMeasure μ] {ι : Type*} [LinearOrder ι]
    {𝒢 : Filtration ι m} {M : ι → Ω → ℝ} (hM : Martingale M 𝒢 μ) (T : ι) :
    Martingale (fun t => M (min t T)) 𝒢 μ := by
  refine ⟨fun t => (hM.stronglyAdapted _).mono (𝒢.mono (min_le_left t T)), ?_⟩
  intro s t hst
  change μ[M (min t T) | 𝒢 s] =ᵐ[μ] M (min s T)
  by_cases hs : s ≤ T
  · rw [min_eq_left hs]
    exact hM.condExp_ae_eq (le_min hst hs)
  · have hTs : T ≤ s := le_of_not_ge hs
    rw [min_eq_right hTs, min_eq_right (hTs.trans hst)]
    exact EventuallyEq.of_eq (condExp_of_stronglyMeasurable (𝒢.le s)
      ((hM.stronglyAdapted T).mono (𝒢.mono hTs)) (hM.integrable T))

private theorem compensated_product_expectation [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} {X Y C : ℝ≥0 → Ω → ℝ}
    (h : Martingale (fun t => X t * Y t - C t) 𝒢 μ)
    (hx : ∀ t, MemLp (X t) 2 μ) (hy : ∀ t, MemLp (Y t) 2 μ)
    (hc : ∀ t, Integrable (C t) μ)
    (hx₀ : X 0 =ᵐ[μ] 0) (hy₀ : Y 0 =ᵐ[μ] 0) (hc₀ : C 0 =ᵐ[μ] 0) (t : ℝ≥0) :
    (∫ ω, X t ω * Y t ω ∂μ) = ∫ ω, C t ω ∂μ := by
  have hprod : Integrable (X t * Y t) μ := by
    exact ((hx t).mul (hy t) : MemLp (X t * Y t) 1 μ).integrable le_rfl
  have hzero : (X 0 * Y 0 - C 0) =ᵐ[μ] (0 : Ω → ℝ) := by
    filter_upwards [hx₀, hy₀, hc₀] with ω hxω hyω hcω
    simp only [Pi.mul_apply, Pi.sub_apply, hxω, hyω, hcω, Pi.zero_apply, mul_zero, sub_zero]
  have he := h.setIntegral_eq (show (0 : ℝ≥0) ≤ t from zero_le)
    (MeasurableSet.univ : MeasurableSet[𝒢 0] Set.univ)
  simp only [Measure.restrict_univ] at he
  have hz : (∫ ω, ((X 0 * Y 0 - C 0) : Ω → ℝ) ω ∂μ) = 0 := by
    simpa using integral_congr_ae hzero
  have htemp : (∫ ω, (X t * Y t - C t) ω ∂μ) = 0 := he.symm.trans hz
  change (∫ ω, (X t * Y t) ω - C t ω ∂μ) = 0 at htemp
  rw [integral_sub hprod (hc t)] at htemp
  exact sub_eq_zero.mp htemp

/-- Integrate a time density up to the observation time, with a finite
terminal horizon. -/
noncomputable def driverDensityIntegral (T : ℝ≥0) (f : ℝ → Ω → ℝ) (t : ℝ≥0) : Ω → ℝ :=
  fun ω => ∫ s in (0 : ℝ)..((min t T : ℝ≥0) : ℝ), f s ω

private theorem driverDensityIntegral_bound {T t : ℝ≥0} {f : ℝ → ℝ} {c : ℝ}
    (hi : IntervalIntegrable f volume 0 (T : ℝ))
    (h : ∀ s ∈ Icc (0 : ℝ) (T : ℝ), |f s| ≤ c) :
    |∫ s in (0 : ℝ)..((min t T : ℝ≥0) : ℝ), f s| ≤ c * (min t T : ℝ≥0) := by
  let r : ℝ := (min t T : ℝ≥0).toReal
  have hr : 0 ≤ r := NNReal.coe_nonneg _
  have hrT : r ≤ (T : ℝ) := by exact_mod_cast min_le_right t T
  have hs : uIcc (0 : ℝ) r ⊆ uIcc (0 : ℝ) (T : ℝ) := by
    rw [uIcc_of_le hr, uIcc_of_le (NNReal.coe_nonneg T)]
    exact Icc_subset_Icc le_rfl hrT
  have hf := hi.abs.mono_set hs
  refine (intervalIntegral.abs_integral_le_integral_abs hr).trans ?_
  have hm := intervalIntegral.integral_mono_on
    (f := fun s => |f s|) (g := fun _ => c) hr hf intervalIntegrable_const
    (fun s hs => h s (Icc_subset_Icc le_rfl hrT hs))
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] using hm

private theorem driver_l1_limit_from_bound [IsFiniteMeasure μ]
    {f : ℕ → Ω → ℝ} {g c : Ω → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hg : Integrable g μ)
    (hc : Integrable c μ) (hb : ∀ n, ∀ᵐ ω ∂μ, ‖(f n - g) ω‖ ≤ c ω)
    (hl : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) :
    Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0) := by
  have hl' : ∀ᵐ ω ∂μ, Tendsto (fun n => ‖(f n - g) ω‖) atTop (𝓝 ((0 : Ω → ℝ) ω)) := by
    filter_upwards [hl] with ω hω
    simpa only [Pi.sub_apply, Pi.zero_apply, sub_self, norm_zero] using
      (hω.sub (tendsto_const_nhds (x := g ω))).norm
  have hi := tendsto_integral_of_dominated_convergence c
    (fun n => ((hf n).sub hg).norm.aestronglyMeasurable) hc
    (fun n => by simpa only [norm_norm] using hb n) hl'
  have he (n : ℕ) : eLpNorm (f n - g) 1 μ =
      ENNReal.ofReal (∫ ω, ‖(f n - g) ω‖ ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm ((hf n).sub hg).aestronglyMeasurable, ofReal_integral_norm_eq_lintegral_enorm ((hf n).sub hg)]
  simpa only [Function.comp_def, ← he, Pi.zero_apply, integral_zero, ENNReal.ofReal_zero]
    using (ENNReal.continuous_ofReal.tendsto _).comp hi

/-- A pair of weights represents the covariance of a regularized driver.
The term for the auxiliary driver is kept at times when the amplitude
of the variance martingales vanishes. -/
def driverPairDensity (p q : ℕ → ℝ → Ω → ℝ) (n k : ℕ) (s : ℝ) (ω : Ω) : ℝ :=
  p n s ω * p k s ω + q n s ω * q k s ω

private theorem driver_pair_distance_bound {p q p' q' : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1)
    (hp' : p' ∈ Icc (0 : ℝ) 1) (hq' : q' ∈ Icc (0 : ℝ) 1) :
    |(p - p') ^ 2 + (q - q') ^ 2| ≤ 2 := by
  have ha : |p - p'| ≤ 1 := abs_le.mpr ⟨by linarith [hp.1, hp'.2], by linarith [hp.2, hp'.1]⟩
  have hb : |q - q'| ≤ 1 := abs_le.mpr ⟨by linarith [hq.1, hq'.2], by linarith [hq.2, hq'.1]⟩
  rw [abs_of_nonneg (by positivity), ← sq_abs (p - p'), ← sq_abs (q - q')]
  nlinarith [pow_le_pow_left₀ (abs_nonneg _) ha 2, pow_le_pow_left₀ (abs_nonneg _) hb 2]

private theorem tendsto_time_integrals_of_dominated
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {f : ι → ℝ → ℝ} {g c : ℝ → ℝ} {r : ℝ}
    (hr : 0 ≤ r) (hf : ∀ i, IntervalIntegrable (f i) volume 0 r)
    (hc : IntervalIntegrable c volume 0 r)
    (hb : ∀ i s, s ∈ Ioc (0 : ℝ) r → ‖f i s‖ ≤ c s)
    (hl : ∀ s ∈ Ioc (0 : ℝ) r, Tendsto (fun i => f i s) l (𝓝 (g s))) :
    Tendsto (fun i => ∫ s in (0 : ℝ)..r, f i s) l (𝓝 (∫ s in (0 : ℝ)..r, g s)) := by
  simpa only [intervalIntegral.integral_of_le hr] using
    (tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioc 0 r))
      c (Eventually.of_forall fun i => (hf i).1.aestronglyMeasurable)
      (Eventually.of_forall fun i => (ae_restrict_mem measurableSet_Ioc).mono (hb i))
      hc.1 ((ae_restrict_mem measurableSet_Ioc).mono hl) :
      Tendsto (fun i => ∫ s in Ioc (0 : ℝ) r, f i s) l (𝓝 (∫ s in Ioc (0 : ℝ) r, g s)))

private theorem tendsto_time_integrals_of_bounded
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {f : ι → ℝ → ℝ} {g : ℝ → ℝ} {r c : ℝ}
    (hr : 0 ≤ r) (hf : ∀ i, IntervalIntegrable (f i) volume 0 r)
    (hb : ∀ i s, s ∈ Ioc (0 : ℝ) r → ‖f i s‖ ≤ c)
    (hl : ∀ s ∈ Ioc (0 : ℝ) r, Tendsto (fun i => f i s) l (𝓝 (g s))) :
    Tendsto (fun i => ∫ s in (0 : ℝ)..r, f i s) l (𝓝 (∫ s in (0 : ℝ)..r, g s)) :=
  tendsto_time_integrals_of_dominated hr hf intervalIntegrable_const hb hl


/-- Removing the regularization gives a continuous martingale with
compensated square (B_t^2-(t∧T)). The pairwise covariance information
identifies the actual (L^2) limit and controls the case of zero amplitude. -/
theorem continuous_driver_of_pairwise_compensators [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} (T : ℝ≥0)
    {Bn : ℕ → ℝ≥0 → Ω → ℝ} {C : ℕ → ℕ → ℝ≥0 → Ω → ℝ}
    {p q : ℕ → ℝ → Ω → ℝ}
    (hB : ∀ n, Martingale (Bn n) 𝒢 μ) (hB₂ : ∀ n t, MemLp (Bn n t) 2 μ)
    (hB₀ : ∀ n, Bn n 0 =ᵐ[μ] 0)
    (hBfreeze : ∀ n t, Bn n t = Bn n (min t T))
    (hBcts : ∀ᵐ ω ∂μ, ∀ n, ContinuousOn (fun t => Bn n t ω) (Iic T))
    (hC : ∀ n k, Martingale (fun t => Bn n t * Bn k t - C n k t) 𝒢 μ)
    (hCeq : ∀ n k t, C n k t =ᵐ[μ] driverDensityIntegral T (driverPairDensity p q n k) t)
    (hweights : ∀ᵐ ω ∂μ,
      (∀ n, ContinuousOn (fun s => p n s ω) (Icc 0 (T : ℝ)) ∧
        ContinuousOn (fun s => q n s ω) (Icc 0 (T : ℝ))) ∧
      ∀ s ∈ Icc (0 : ℝ) (T : ℝ),
        (∀ n, p n s ω ∈ Icc (0 : ℝ) 1 ∧ q n s ω ∈ Icc (0 : ℝ) 1) ∧
        ∃ a b : ℝ, a ^ 2 + b ^ 2 = 1 ∧
          Tendsto (fun n => p n s ω) atTop (𝓝 a) ∧
          Tendsto (fun n => q n s ω) atTop (𝓝 b)) :
    ∃ B : ℝ≥0 → Ω → ℝ,
      Martingale B 𝒢 μ ∧ (∀ t, MemLp (B t) 2 μ) ∧ (B 0 =ᵐ[μ] 0) ∧
      (∀ᵐ ω ∂μ, Continuous (fun t => B t ω)) ∧
      (∀ t, Tendsto (fun n => eLpNorm (Bn n t - B t) 2 μ) atTop (𝓝 0)) ∧
      Martingale (fun t ω => B t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) 𝒢 μ := by
  let K (t : ℝ≥0) : Ω → ℝ := fun _ => ((min t T : ℝ≥0) : ℝ)
  have hprod (n k : ℕ) (t : ℝ≥0) : Integrable (Bn n t * Bn k t) μ :=
    ((hB₂ n t).mul (hB₂ k t) : MemLp (Bn n t * Bn k t) 1 μ).integrable le_rfl
  have hCi (n k : ℕ) (t : ℝ≥0) : Integrable (C n k t) μ := by
    simpa only [sub_sub_cancel] using (hprod n k t).sub ((hC n k).integrable t)
  have hC₀ (n k : ℕ) : C n k 0 =ᵐ[μ] 0 := by
    filter_upwards [hCeq n k 0] with ω he
    rw [he]
    simp [driverDensityIntegral]
  have hmom (n k : ℕ) :
      (∫ ω, Bn n T ω * Bn k T ω ∂μ) = ∫ ω, C n k T ω ∂μ :=
    compensated_product_expectation (hC n k) (hB₂ n) (hB₂ k) (hCi n k)
      (hB₀ n) (hB₀ k) (hC₀ n k) T
  let E (j : ℕ × ℕ) : Ω → ℝ :=
    (C j.1 j.1 T + C j.2 j.2 T) - (C j.1 j.2 T + C j.2 j.1 T)
  let e (j : ℕ × ℕ) (s : ℝ) (ω : Ω) : ℝ :=
    (p j.1 s ω - p j.2 s ω) ^ 2 + (q j.1 s ω - q j.2 s ω) ^ 2
  have hiE (j : ℕ × ℕ) : Integrable (E j) μ :=
    ((hCi j.1 j.1 T).add (hCi j.2 j.2 T)).sub ((hCi j.1 j.2 T).add (hCi j.2 j.1 T))
  have hden (ω : Ω) (hc : ∀ n,
      ContinuousOn (fun s => p n s ω) (Icc 0 (T : ℝ)) ∧
        ContinuousOn (fun s => q n s ω) (Icc 0 (T : ℝ))) (n k : ℕ) :
      ContinuousOn (fun s => driverPairDensity p q n k s ω) (Icc (0 : ℝ) T) :=
    ((hc n).1.mul (hc k).1).add ((hc n).2.mul (hc k).2)
  have hEeq : ∀ᵐ ω ∂μ, ∀ j, E j ω = driverDensityIntegral T (e j) T ω := by
    have hCeq' : ∀ᵐ ω ∂μ, ∀ n k, C n k T ω =
        driverDensityIntegral T (driverPairDensity p q n k) T ω :=
      ae_all_iff.mpr (fun n => ae_all_iff.mpr (fun k => hCeq n k T))
    filter_upwards [hCeq', hweights] with ω hω hw j
    let f (n k : ℕ) := fun s => driverPairDensity p q n k s ω
    have hf (n k : ℕ) : IntervalIntegrable (f n k) volume 0 (T : ℝ) := by
      apply ContinuousOn.intervalIntegrable
      simpa only [uIcc_of_le (NNReal.coe_nonneg T)] using hden ω hw.1 n k
    change (C j.1 j.1 T ω + C j.2 j.2 T ω) - (C j.1 j.2 T ω + C j.2 j.1 T ω) = _
    simp only [hω, driverDensityIntegral, min_self]
    rw [← intervalIntegral.integral_add (hf j.1 j.1) (hf j.2 j.2),
      ← intervalIntegral.integral_add (hf j.1 j.2) (hf j.2 j.1),
      ← intervalIntegral.integral_sub ((hf j.1 j.1).add (hf j.2 j.2))
        ((hf j.1 j.2).add (hf j.2 j.1))]
    congr 1
    funext s
    simp only [f, driverPairDensity, e]
    ring
  have ie (ω : Ω) (hw : ∀ n, ContinuousOn (fun s => p n s ω) (Icc 0 (T : ℝ)) ∧
      ContinuousOn (fun s => q n s ω) (Icc 0 (T : ℝ))) (j : ℕ × ℕ) :
      IntervalIntegrable (fun s => e j s ω) volume 0 (T : ℝ) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (NNReal.coe_nonneg T)]
    exact (((hw j.1).1.sub (hw j.2).1).pow 2).add (((hw j.1).2.sub (hw j.2).2).pow 2)
  have hEb (j : ℕ × ℕ) : ∀ᵐ ω ∂μ, ‖E j ω‖ ≤ 2 * (T : ℝ) := by
    filter_upwards [hweights, hEeq] with ω hw he
    rw [Real.norm_eq_abs, he, driverDensityIntegral, min_self]
    have hb := driverDensityIntegral_bound (T := T) (t := T) (ie ω hw.1 j)
      (fun s hs => driver_pair_distance_bound
        ((hw.2 s hs).1 j.1).1 ((hw.2 s hs).1 j.1).2
        ((hw.2 s hs).1 j.2).1 ((hw.2 s hs).1 j.2).2)
    simpa only [min_self] using hb
  have hEl : ∀ᵐ ω ∂μ, Tendsto (fun j => E j ω) atTop (𝓝 ((0 : Ω → ℝ) ω)) := by
    filter_upwards [hweights, hEeq] with ω hw hEω
    have hf : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
      rw [← Filter.prod_atTop_atTop_eq]; exact Filter.tendsto_fst
    have hg : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
      rw [← Filter.prod_atTop_atTop_eq]; exact Filter.tendsto_snd
    have hpoint (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) (T : ℝ)) :
        Tendsto (fun j => e j s ω) atTop (𝓝 0) := by
      obtain ⟨a, b, _, hp, hq⟩ := (hw.2 s (Ioc_subset_Icc_self hs)).2
      simpa only [Function.comp_def, e, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0),
        add_zero] using
        ((((hp.comp hf).sub (hp.comp hg)).pow 2).add (((hq.comp hf).sub (hq.comp hg)).pow 2))
    have htime := tendsto_time_integrals_of_bounded (NNReal.coe_nonneg T) (ie ω hw.1)
      (c := 2) (g := fun _ => 0)
      (fun j s hs => by
        have h := (hw.2 s (Ioc_subset_Icc_self hs)).1
        exact (Real.norm_eq_abs _).symm ▸
          driver_pair_distance_bound (h j.1).1 (h j.1).2 (h j.2).1 (h j.2).2) hpoint
    simpa only [hEω, driverDensityIntegral, min_self, intervalIntegral.integral_zero, Pi.zero_apply]
      using htime
  have hnorm : Tendsto (fun j => ∫ ω, E j ω ∂μ) atTop (𝓝 0) := by
    simpa only [Pi.zero_apply, integral_zero] using
      (tendsto_integral_filter_of_dominated_convergence (fun _ => 2 * (T : ℝ))
        (Eventually.of_forall fun j => (hiE j).aestronglyMeasurable)
        (Eventually.of_forall hEb) (integrable_const _) hEl)
  let u (n : ℕ) := (hB₂ n T).toLp (Bn n T)
  have hdist (j : ℕ × ℕ) : dist (u j.1) (u j.2) ^ 2 = ∫ ω, E j ω ∂μ := by
    rw [dist_toLp_two_sq]
    have heq : (fun ω => (Bn j.1 T ω - Bn j.2 T ω) ^ 2) =
        (Bn j.1 T * Bn j.1 T + Bn j.2 T * Bn j.2 T) -
          (Bn j.1 T * Bn j.2 T + Bn j.2 T * Bn j.1 T) := by
      ext ω
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
      ring
    rw [heq]
    change (∫ ω, (Bn j.1 T * Bn j.1 T + Bn j.2 T * Bn j.2 T) ω -
        (Bn j.1 T * Bn j.2 T + Bn j.2 T * Bn j.1 T) ω ∂μ) = _
    rw [integral_sub ((hprod j.1 j.1 T).add (hprod j.2 j.2 T))
      ((hprod j.1 j.2 T).add (hprod j.2 j.1 T))]
    simp only [Pi.add_apply]
    rw [integral_add (hprod j.1 j.1 T) (hprod j.2 j.2 T),
      integral_add (hprod j.1 j.2 T) (hprod j.2 j.1 T)]
    simp only [Pi.mul_apply, hmom]
    rw [← integral_add (hCi j.1 j.1 T) (hCi j.2 j.2 T),
      ← integral_add (hCi j.1 j.2 T) (hCi j.2 j.1 T)]
    change (∫ ω, (C j.1 j.1 T + C j.2 j.2 T) ω ∂μ) -
      (∫ ω, (C j.1 j.2 T + C j.2 j.1 T) ω ∂μ) = _
    rw [← integral_sub ((hCi j.1 j.1 T).add (hCi j.2 j.2 T))
        ((hCi j.1 j.2 T).add (hCi j.2 j.1 T))]
    rfl
  have hc : CauchySeq u := by
    rw [cauchySeq_iff_tendsto_dist_atTop_0]
    have hs : Tendsto (fun j : ℕ × ℕ => dist (u j.1) (u j.2) ^ 2) atTop (𝓝 0) :=
      hnorm.congr (fun j => (hdist j).symm)
    have hroot := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hs
    change Tendsto (fun j : ℕ × ℕ => Real.sqrt (dist (u j.1) (u j.2) ^ 2))
      atTop (𝓝 (Real.sqrt 0)) at hroot
    simpa only [Real.sqrt_sq dist_nonneg, Real.sqrt_zero] using hroot
  obtain ⟨I, hI⟩ := cauchySeq_tendsto_of_complete hc
  obtain ⟨hJ, hJ₂, hconv⟩ := martingale_limit_of_terminal_L2 hB (fun n => hB₂ n T) hI
  let : Nonempty (Iic T) := ⟨⟨0, Set.mem_Iic.mpr (zero_le)⟩⟩
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Iic T)
  obtain ⟨times, hD⟩ := hDc.exists_eq_range hDd.nonempty
  let times' := fun k => (times k : ℝ≥0)
  have ht' (k : ℕ) : times' k ≤ T := (times k).property
  have hd' : Iic T ⊆ closure (range times') := by
    intro t ht
    have hmem := hDd (⟨t, ht⟩ : Iic T)
    rwa [hD, closure_subtype, ← Set.range_comp] at hmem
  obtain ⟨J, hJm, hJver, hJcts, _⟩ :=
    continuous_martingale_version_of_L2_limits hB hJ hBcts times' ht' hd' hconv
  let B (t : ℝ≥0) := J (min t T)
  have hBm : Martingale B 𝒢 μ := martingale_freeze_at hJm T
  have hBmem (t : ℝ≥0) : MemLp (B t) 2 μ :=
    (memLp_congr_ae (hJver (min t T))).2 (hJ₂ (min t T))
  have hBlim (t : ℝ≥0) :
      Tendsto (fun n => eLpNorm (Bn n t - B t) 2 μ) atTop (𝓝 0) := by
    refine (hconv (min t T) (min_le_right t T)).congr (fun n => ?_)
    rw [hBfreeze n t]
    exact eLpNorm_congr_ae (EventuallyEq.rfl.sub (hJver (min t T)).symm)
  have hBzero : B 0 =ᵐ[μ] 0 := by
    have he (n : ℕ) : eLpNorm (Bn n 0 - B 0) 2 μ = eLpNorm (B 0) 2 μ := by
      have heq : Bn n 0 - B 0 =ᵐ[μ] 0 - B 0 := (hB₀ n).sub EventuallyEq.rfl
      rw [eLpNorm_congr_ae heq, zero_sub, eLpNorm_neg]
    have ht : Tendsto (fun _ : ℕ => eLpNorm (B 0) 2 μ) atTop (𝓝 0) :=
      (hBlim 0).congr he
    exact (eLpNorm_eq_zero_iff (by norm_num : (2 : ENNReal) ≠ 0)).mp
      (tendsto_nhds_unique tendsto_const_nhds ht)
  have hBc : ∀ᵐ ω ∂μ, Continuous (fun t => B t ω) := by
    filter_upwards [hJcts] with ω hω
    exact hω.comp_continuous (continuous_id.min continuous_const)
      (fun t => Set.mem_Iic.mpr (min_le_right t T))
  have hKlim (t : ℝ≥0) :
      Tendsto (fun n => eLpNorm (C n n t - K t) 1 μ) atTop (𝓝 0) := by
    let r : ℝ := ((min t T : ℝ≥0) : ℝ)
    have hr : 0 ≤ r := NNReal.coe_nonneg _
    have hrT : r ≤ (T : ℝ) := by exact_mod_cast min_le_right t T
    have hs : uIcc (0 : ℝ) r ⊆ uIcc (0 : ℝ) T := by
      rw [uIcc_of_le hr, uIcc_of_le (NNReal.coe_nonneg T)]
      exact Icc_subset_Icc le_rfl hrT
    apply driver_l1_limit_from_bound (fun n => hCi n n t) (integrable_const r)
      (integrable_const (2 * (T : ℝ) + (T : ℝ)))
    · intro n
      filter_upwards [hweights, hCeq n n t] with ω hw he
      have hi : IntervalIntegrable (fun s => driverPairDensity p q n n s ω) volume 0 (T : ℝ) := by
        apply ContinuousOn.intervalIntegrable
        simpa only [uIcc_of_le (NNReal.coe_nonneg T)] using hden ω hw.1 n n
      have hab (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) : |driverPairDensity p q n n s ω| ≤ 2 := by
        have ⟨hp, hq⟩ := (hw.2 s hs).1 n
        rw [driverPairDensity, abs_of_nonneg (add_nonneg (mul_nonneg hp.1 hp.1) (mul_nonneg hq.1 hq.1))]
        nlinarith [mul_le_mul hp.2 hp.2 hp.1 zero_le_one, mul_le_mul hq.2 hq.2 hq.1 zero_le_one]
      have hm := driverDensityIntegral_bound (T := T) (t := t) hi hab
      have hm' : |C n n t ω| ≤ 2 * r := by rw [he]; exact hm
      rw [Pi.sub_apply, Real.norm_eq_abs]
      change |C n n t ω - r| ≤ _
      have htri := abs_sub_le (C n n t ω) 0 r
      rw [sub_zero, zero_sub, abs_neg, abs_of_nonneg hr] at htri
      linarith
    · have hEq : ∀ᵐ ω ∂μ, ∀ n, C n n t ω = driverDensityIntegral T (driverPairDensity p q n n) t ω :=
        ae_all_iff.mpr fun n => hCeq n n t
      filter_upwards [hEq, hweights] with ω hEqω hw
      have hI (n : ℕ) : IntervalIntegrable (fun s => driverPairDensity p q n n s ω) volume 0 r := by
        apply IntervalIntegrable.mono_set _ hs
        apply ContinuousOn.intervalIntegrable
        simpa only [uIcc_of_le (NNReal.coe_nonneg T)] using hden ω hw.1 n n
      have hh (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) r) := hw.2 s (Icc_subset_Icc le_rfl hrT (Ioc_subset_Icc_self hs))
      have hpoint (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) r) :
          Tendsto (fun n => driverPairDensity p q n n s ω) atTop (𝓝 1) := by
        obtain ⟨a, b, hab, hp, hq⟩ := (hh s hs).2
        simpa only [driverPairDensity, ← pow_two, hab] using (hp.pow 2).add (hq.pow 2)
      have hb (n : ℕ) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) r) :
          ‖driverPairDensity p q n n s ω‖ ≤ 2 := by
        have ⟨hp, hq⟩ := (hh s hs).1 n
        rw [driverPairDensity, Real.norm_of_nonneg
          (add_nonneg (mul_nonneg hp.1 hp.1) (mul_nonneg hq.1 hq.1))]
        nlinarith [mul_le_mul hp.2 hp.2 hp.1 zero_le_one, mul_le_mul hq.2 hq.2 hq.1 zero_le_one]
      have hh' := tendsto_time_integrals_of_bounded hr hI hb hpoint
      simpa only [hEqω, driverDensityIntegral, K, intervalIntegral.integral_const, sub_zero,
        smul_eq_mul, mul_one] using hh'
  refine ⟨B, hBm, hBmem, hBzero, hBc, hBlim, ?_⟩
  have hBs := compensated_product_martingale_of_limits hBm.stronglyAdapted hBm.stronglyAdapted
    (fun _ => stronglyMeasurable_const) hBmem hBmem hB₂ hB₂
    (fun _ => integrable_const _) (fun n t => hCi n n t) (fun n => hC n n)
    hBlim hBlim hKlim
  simp only [pow_two]
  change Martingale (fun t => B t * B t - K t) 𝒢 μ
  exact hBs



/-- A sequence of cross-compensators with convergent time densities
has an adapted, timewise L¹ limit when the total dominating variation
is integrable. -/
theorem driver_compensator_of_dominated_density_limit [IsFiniteMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} (T : ℝ≥0) {C : ℕ → ℝ≥0 → Ω → ℝ}
    {D : ℝ → Ω → ℝ} {d : ℕ → ℝ → Ω → ℝ}
    (hCa : ∀ n, StronglyAdapted 𝒢 (C n)) (hCi : ∀ n t, Integrable (C n t) μ)
    (hCeq : ∀ n t, C n t =ᵐ[μ] driverDensityIntegral T (d n) t)
    (hDint : Integrable (fun ω => ∫ s in (0 : ℝ)..(T : ℝ), |D s ω|) μ)
    (hpath : ∀ᵐ ω ∂μ, ContinuousOn (fun s => D s ω) (Icc (0 : ℝ) T) ∧
      (∀ n, ContinuousOn (fun s => d n s ω) (Icc (0 : ℝ) T)) ∧
      ∀ s ∈ Icc (0 : ℝ) (T : ℝ), (∀ n, |d n s ω| ≤ |D s ω|) ∧
        Tendsto (fun n => d n s ω) atTop (𝓝 (D s ω))) :
    ∃ C' : ℝ≥0 → Ω → ℝ, StronglyAdapted 𝒢 C' ∧ (∀ t, Integrable (C' t) μ) ∧
      (∀ t, C' t =ᵐ[μ] driverDensityIntegral T D t) ∧
      ∀ t, Tendsto (fun n => eLpNorm (C n t - C' t) 1 μ) atTop (𝓝 0) := by
  let C' (t : ℝ≥0) (ω : Ω) := limUnder atTop fun n => C n t ω
  let mass (ω : Ω) := ∫ s in (0 : ℝ)..(T : ℝ), |D s ω|
  have hC'a : StronglyAdapted 𝒢 C' := by
    intro t
    let : MeasurableSpace Ω := 𝒢 t
    exact StronglyMeasurable.limUnder (l := atTop) (fun n => hCa n t)
  have hci (t : ℝ≥0) {f : ℝ → ℝ} (h : ContinuousOn f (Icc (0 : ℝ) T)) :
      IntervalIntegrable f volume 0 ((min t T : ℝ≥0) : ℝ) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (NNReal.coe_nonneg _)]
    exact h.mono (Icc_subset_Icc le_rfl (by exact_mod_cast min_le_right t T))
  have hcl (t : ℝ≥0) : ∀ᵐ ω ∂μ,
      Tendsto (fun n => C n t ω) atTop (𝓝 (driverDensityIntegral T D t ω)) := by
    have heq : ∀ᵐ ω ∂μ, ∀ n, C n t ω = driverDensityIntegral T (d n) t ω :=
      ae_all_iff.mpr fun n => hCeq n t
    filter_upwards [heq, hpath] with ω hEq hw
    have ht : ((min t T : ℝ≥0) : ℝ) ≤ (T : ℝ) := by exact_mod_cast min_le_right t T
    have hs (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) ((min t T : ℝ≥0) : ℝ)) :
        s ∈ Icc (0 : ℝ) (T : ℝ) := Icc_subset_Icc le_rfl ht (Ioc_subset_Icc_self hs)
    have hi := tendsto_time_integrals_of_dominated (NNReal.coe_nonneg (min t T))
      (fun n => hci t (hw.2.1 n)) (hci t hw.1).abs
      (fun n s hs' => by simpa only [Real.norm_eq_abs] using (hw.2.2 s (hs s hs')).1 n)
      (fun s hs' => (hw.2.2 s (hs s hs')).2)
    simpa only [hEq, driverDensityIntegral] using hi
  have hC'e (t : ℝ≥0) : C' t =ᵐ[μ] driverDensityIntegral T D t :=
    (hcl t).mono (fun _ hω => hω.limUnder_eq)
  have hbd (t : ℝ≥0) (ω : Ω) {f : ℝ → ℝ}
      (hD : ContinuousOn (fun s => D s ω) (Icc (0 : ℝ) T))
      (hf : ContinuousOn f (Icc (0 : ℝ) T))
      (hb : ∀ s ∈ Icc (0 : ℝ) (T : ℝ), |f s| ≤ |D s ω|) :
      |∫ s in (0 : ℝ)..((min t T : ℝ≥0) : ℝ), f s| ≤ mass ω := by
    have hr : 0 ≤ ((min t T : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
    have hrT : ((min t T : ℝ≥0) : ℝ) ≤ (T : ℝ) := by exact_mod_cast min_le_right t T
    refine (intervalIntegral.abs_integral_le_integral_abs hr).trans ?_
    refine le_trans (intervalIntegral.integral_mono_on hr (hci t hf).abs (hci t hD).abs
      (fun s hs => hb s (Icc_subset_Icc le_rfl hrT hs))) ?_
    have hfull : IntervalIntegrable (fun s => D s ω) volume 0 (T : ℝ) := by
      apply ContinuousOn.intervalIntegrable
      simpa only [uIcc_of_le (NNReal.coe_nonneg T)] using hD
    exact intervalIntegral.integral_mono_interval le_rfl hr hrT
      (Eventually.of_forall fun _ => abs_nonneg _) hfull.abs
  have hC'b (t : ℝ≥0) : ∀ᵐ ω ∂μ, |C' t ω| ≤ mass ω := by
    filter_upwards [hC'e t, hpath] with ω he hw
    rw [he, driverDensityIntegral]
    exact hbd t ω hw.1 hw.1 (fun _ _ => le_rfl)
  have hC'i (t : ℝ≥0) : Integrable (C' t) μ :=
    hDint.mono' ((hC'a t).mono (𝒢.le t)).aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs] using hC'b t)
  refine ⟨C', hC'a, hC'i, hC'e, fun t => ?_⟩
  apply driver_l1_limit_from_bound (fun n => hCi n t) (hC'i t) (hDint.const_mul 2)
  · intro n
    filter_upwards [hCeq n t, hC'b t, hpath] with ω he hx hw
    have hy : |C n t ω| ≤ mass ω := by
      rw [he, driverDensityIntegral]
      exact hbd t ω hw.1 (hw.2.1 n) (fun s hs => (hw.2.2 s hs).1 n)
    rw [Pi.sub_apply, Real.norm_eq_abs]
    have hh := abs_sub_le (C n t ω) 0 (C' t ω)
    simp only [sub_zero, zero_sub, abs_neg] at hh
    change |C n t ω - C' t ω| ≤ 2 * mass ω
    linarith
  · filter_upwards [hcl t, hC'e t] with ω hω he
    rwa [he]


end RoughHeston

#print axioms RoughHeston.martingale_freeze_at
#print axioms RoughHeston.continuous_driver_of_pairwise_compensators
#print axioms RoughHeston.driver_compensator_of_dominated_density_limit
