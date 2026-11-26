import SmoothVarianceLift
import Mathlib.Analysis.Calculus.Deriv.Slope
import MathFin.Probability.Brownian.Ito.ItoFormulaAdaptedProcess
import Mathlib.Probability.Process.HittingTime
import BrownianMotion.Choquet.Debut

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace RoughHeston

/-- A nonnegative `C²` test function detecting the negative half-line. -/
noncomputable def negativePartCube (x : ℝ) : ℝ := (max (-x) 0) ^ 3

noncomputable def negativePartCubePrime (x : ℝ) : ℝ := -3 * (max (-x) 0) ^ 2

noncomputable def negativePartCubeSecond (x : ℝ) : ℝ := 6 * max (-x) 0

private theorem hasDerivAt_glue_at_zero {f g h : ℝ → ℝ} {d : ℝ}
    (hg : HasDerivAt g d 0) (hh : HasDerivAt h d 0)
    (hneg : EqOn f g (Iic 0)) (hpos : EqOn f h (Ici 0)) : HasDerivAt f d 0 := by
  rw [← hasDerivWithinAt_univ, ← Iic_union_Ici (a := (0 : ℝ))]
  exact (hg.hasDerivWithinAt.congr hneg (hneg (mem_Iic.mpr (show (0 : ℝ) ≤ 0 from le_rfl)))).union
    (hh.hasDerivWithinAt.congr hpos (hpos (mem_Ici.mpr (show (0 : ℝ) ≤ 0 from le_rfl))))

private theorem negativePartCube_poly_derivative (x : ℝ) :
    HasDerivAt (fun y : ℝ => (-y) ^ 3) (-3 * (-x) ^ 2) x := by
  have h := ((hasDerivAt_id x).const_mul (-1 : ℝ)).pow 3
  convert h using 1
  · funext y
    change (-y) ^ 3 = (-1 * y) ^ 3
    ring
  · norm_num

private theorem negativePartCubePrime_poly_derivative (x : ℝ) :
    HasDerivAt (fun y : ℝ => -3 * (-y) ^ 2) (6 * (-x)) x := by
  have h := (((hasDerivAt_id x).const_mul (-1 : ℝ)).pow 2).const_mul (-3 : ℝ)
  convert h using 1
  · funext y
    change -3 * (-y) ^ 2 = -3 * (-1 * y) ^ 2
    ring
  · norm_num
    ring

/-- First derivative of the cubic negative part, including at zero. -/
theorem negativePartCube_hasDerivAt (x : ℝ) :
    HasDerivAt negativePartCube (negativePartCubePrime x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [negativePartCubePrime, max_eq_left (neg_nonneg.mpr hx.le)]
    refine (negativePartCube_poly_derivative x).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hx] with y hy
    rw [negativePartCube, max_eq_left (neg_nonneg.mpr (le_of_lt hy))]
  · have h0 : negativePartCubePrime 0 = 0 := by simp [negativePartCubePrime]
    rw [h0]
    have hn : HasDerivAt (fun y : ℝ => (-y) ^ 3) 0 0 := by
      simpa only [neg_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] using negativePartCube_poly_derivative 0
    refine hasDerivAt_glue_at_zero hn (hasDerivAt_const 0 0) ?_ ?_
    · intro y hy
      rw [negativePartCube, max_eq_left (neg_nonneg.mpr hy)]
    · intro y hy
      simp [negativePartCube, max_eq_right (neg_nonpos.mpr (mem_Ici.mp hy))]
  · rw [negativePartCubePrime, max_eq_right (neg_nonpos.mpr hx.le),
      zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]
    refine (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp [negativePartCube, max_eq_right (neg_nonpos.mpr (le_of_lt (mem_Ioi.mp hy)))]

/-- Second derivative of the cubic negative part, including at zero. -/
theorem negativePartCubePrime_hasDerivAt (x : ℝ) :
    HasDerivAt negativePartCubePrime (negativePartCubeSecond x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [negativePartCubeSecond, max_eq_left (neg_nonneg.mpr hx.le)]
    refine (negativePartCubePrime_poly_derivative x).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hx] with y hy
    rw [negativePartCubePrime, max_eq_left (neg_nonneg.mpr (le_of_lt hy))]
  · have h0 : negativePartCubeSecond 0 = 0 := by simp [negativePartCubeSecond]
    rw [h0]
    have hn : HasDerivAt (fun y : ℝ => -3 * (-y) ^ 2) 0 0 := by
      simpa only [neg_zero, mul_zero] using negativePartCubePrime_poly_derivative 0
    refine hasDerivAt_glue_at_zero hn (hasDerivAt_const 0 0) ?_ ?_
    · intro y hy
      rw [negativePartCubePrime, max_eq_left (neg_nonneg.mpr hy)]
    · intro y hy
      simp [negativePartCubePrime, max_eq_right (neg_nonpos.mpr (mem_Ici.mp hy))]
  · rw [negativePartCubeSecond, max_eq_right (neg_nonpos.mpr hx.le), mul_zero]
    refine (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp [negativePartCubePrime, max_eq_right (neg_nonpos.mpr (le_of_lt (mem_Ioi.mp hy)))]

theorem negativePartCubeSecond_continuous : Continuous negativePartCubeSecond := by
  unfold negativePartCubeSecond
  exact continuous_const.mul (continuous_neg.max continuous_const)

theorem negativePartCube_nonneg (x : ℝ) : 0 ≤ negativePartCube x :=
  pow_nonneg (le_max_right (-x) 0) _

theorem negativePartCube_eq_zero_iff (x : ℝ) : negativePartCube x = 0 ↔ 0 ≤ x := by
  constructor
  · intro hx
    by_contra! hn
    exact (pow_pos ((neg_pos.mpr hn).trans_le (le_max_left (-x) 0)) 3).ne' hx
  · intro hx
    simp [negativePartCube, max_eq_right (neg_nonpos.mpr hx)]

/-- For inward drift and vanishing diffusion on the nonpositive half-line,
the Itô drift of the negative-part test function is nonpositive. -/
theorem negativePartCube_itoDrift_nonpos {x b σ : ℝ}
    (hb : x ≤ 0 → 0 ≤ b) (hσ : x ≤ 0 → σ = 0) :
    negativePartCubePrime x * b + (1 / 2) * (negativePartCubeSecond x * σ ^ 2) ≤ 0 := by
  by_cases hx : x ≤ 0
  · rw [hσ hx, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, mul_zero, add_zero]
    apply mul_nonpos_of_nonpos_of_nonneg _ (hb hx)
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-3 : ℝ) ≤ 0) (sq_nonneg _)
  · have hx' : 0 ≤ x := le_of_not_ge hx
    simp [negativePartCubePrime, negativePartCubeSecond, max_eq_right (neg_nonpos.mpr hx')]

/-- The transformed stochastic integrand is pointwise zero. -/
theorem negativePartCube_itoNoise_zero {x σ : ℝ} (hσ : x ≤ 0 → σ = 0) :
    negativePartCubePrime x * σ = 0 := by
  by_cases hx : x ≤ 0
  · rw [hσ hx, mul_zero]
  · have hx' : 0 ≤ x := le_of_not_ge hx
    simp [negativePartCubePrime, max_eq_right (neg_nonpos.mpr hx')]

/-- Nonnegativity follows simultaneously in time from a cubic negative-part
Itô identity whose stochastic term is the integral of the zero integrand. -/
theorem ae_nonnegative_of_negativePartCube_ito_identity {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ν : Measure ℝ≥0} {T : ℝ≥0} {X b σ N : ℝ≥0 → Ω → ℝ} {x₀ : ℝ}
    (hinit : 0 ≤ x₀)
    (hcoeff : ∀ᵐ ω ∂μ, ∀ s ∈ Icc (0 : ℝ≥0) T, X s ω ≤ 0 → 0 ≤ b s ω ∧ σ s ω = 0)
    (hNoise : ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ≥0) T, N t ω = 0)
    (hIto : ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ≥0) T,
      negativePartCube (X t ω) = negativePartCube x₀ +
        (∫ s in Ioc 0 t, (negativePartCubePrime (X s ω) * b s ω +
          (1 / 2) * (negativePartCubeSecond (X s ω) * σ s ω ^ 2)) ∂ν) + N t ω) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ≥0) T, 0 ≤ X t ω := by
  filter_upwards [hcoeff, hNoise, hIto] with ω hc hn hi
  intro t ht
  have hInt : (∫ s in Ioc (0 : ℝ≥0) t, (negativePartCubePrime (X s ω) * b s ω +
      (1 / 2) * (negativePartCubeSecond (X s ω) * σ s ω ^ 2)) ∂ν) ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have h : X s ω ≤ 0 → 0 ≤ b s ω ∧ σ s ω = 0 := hc s ⟨hs.1.le, hs.2.trans ht.2⟩
    exact negativePartCube_itoDrift_nonpos (fun hx => (h hx).1) (fun hx => (h hx).2)
  have hX : negativePartCube (X t ω) ≤ 0 := by
    rw [hi t ht, (negativePartCube_eq_zero_iff x₀).2 hinit, hn t ht, zero_add, add_zero]
    exact hInt
  exact (negativePartCube_eq_zero_iff _).1 (le_antisymm hX (negativePartCube_nonneg _))

/-- A continuous path started in the nonnegative half-line stays there if it
is nondecreasing along every strictly negative excursion observed from a
start in a dense set. -/
theorem continuous_path_nonnegative_of_dense_excursion_monotonicity {T : ℝ≥0} {D : Set ℝ≥0}
    {f : ℝ≥0 → ℝ} (hD : Dense D) (hf : ContinuousOn f (Icc 0 T)) (h0 : 0 ≤ f 0)
    (hstep : ∀ s ∈ D, ∀ t ∈ Icc s T, (∀ u ∈ Icc s t, f u < 0) → f s ≤ f t) :
    ∀ t ∈ Icc (0 : ℝ≥0) T, 0 ≤ f t := by
  intro t ht
  by_contra! hneg
  let S : Set ℝ≥0 := {s ∈ Icc 0 t | 0 ≤ f s}
  have hSClosed : IsClosed S := isClosed_Icc.isClosed_le continuousOn_const
    (hf.mono (Icc_subset_Icc_right ht.2))
  have hcompact : IsCompact S := isCompact_Icc.of_isClosed_subset hSClosed (fun _ hu => hu.1)
  have hnonempty : S.Nonempty := ⟨0, ⟨⟨le_rfl, ht.1⟩, h0⟩⟩
  obtain ⟨a, ha⟩ := hcompact.exists_isGreatest hnonempty
  have hat : a < t := lt_of_le_of_ne ha.1.1.2 (fun h => (not_le_of_gt hneg) (h ▸ ha.1.2))
  have hafter (u : ℝ≥0) (hu : u ∈ Ioc a t) : f u < 0 := by
    by_contra! h
    exact (not_le_of_gt hu.1) (ha.2 ⟨⟨zero_le, hu.2⟩, h⟩)
  let E := Ioo a t ∩ D
  have hEa : a ∈ closure E := by
    have hsub := hD.open_subset_closure_inter (t := Ioo a t) isOpen_Ioo
    have hh := closure_mono hsub
    rw [closure_closure, closure_Ioo hat.ne] at hh
    exact hh ⟨le_rfl, hat.le⟩
  have hET : closure E ⊆ Icc 0 T := closure_minimal
    (fun s hs => ⟨zero_le, hs.1.2.le.trans ht.2⟩) isClosed_Icc
  have ha' : f a ≤ f t := by
    apply le_on_closure ?_ (hf.mono hET) continuousOn_const hEa
    intro s hs
    exact hstep s hs.2 t ⟨hs.1.2.le, ht.2⟩ (fun u hu =>
      hafter u ⟨hs.1.1.trans_le hu.1, hu.2⟩)
  exact (not_le_of_gt hneg) (ha.1.2.trans ha')

/-- On a stopped interval where the compensator stays at its initial
value, the stopped square-integrable martingale has zero increment. -/
theorem stoppedProcess_ae_eq_of_flat_square_compensator {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝒢 : Filtration ℝ≥0 m} [Approximable 𝒢 μ]
    {M A : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0} {s t : ℝ≥0}
    (hM : Martingale M 𝒢 μ) (hM2A : Martingale (fun u ω => M u ω ^ 2 - A u ω) 𝒢 μ)
    (hMrc : ∀ ω, IsRightContinuous (fun u => M u ω))
    (hM2Arc : ∀ ω, IsRightContinuous (fun u => M u ω ^ 2 - A u ω))
    (hτ : IsStoppingTime 𝒢 τ) (hsτ : ∀ ω, (s : WithTop ℝ≥0) ≤ τ ω) (hst : s ≤ t)
    (hAs : Integrable (A s) μ) (hflat : stoppedProcess A τ t =ᵐ[μ] A s) :
    stoppedProcess M τ t =ᵐ[μ] M s := by
  let U := stoppedProcess M τ
  let Q := stoppedProcess (fun u ω => M u ω ^ 2 - A u ω) τ
  have hU : Martingale U 𝒢 μ := hM.stoppedProcess hMrc hτ
  have hQ : Martingale Q 𝒢 μ := hM2A.stoppedProcess hM2Arc hτ
  have hs (ω : Ω) : U s ω = M s ω := by
    change M (min (s : WithTop ℝ≥0) (τ ω)).untopA ω = M s ω
    simp only [min_eq_left (hsτ ω)]
    rfl
  have hQsq (u : ℝ≥0) (h : stoppedProcess A τ u =ᵐ[μ] A s) :
      (fun ω => U u ω ^ 2) =ᵐ[μ] (fun ω => Q u ω + A s ω) := by
    filter_upwards [h] with ω hw
    change (stoppedProcess A τ u) ω = A s ω at hw
    change U u ω ^ 2 = U u ω ^ 2 - (stoppedProcess A τ u) ω + A s ω
    rw [hw, sub_add_cancel]
  have hQssq := hQsq s (Eventually.of_forall fun ω => by
    change A (min (s : WithTop ℝ≥0) (τ ω)).untopA ω = A s ω
    simp only [min_eq_left (hsτ ω)]
    rfl)
  have hQtsq := hQsq t hflat
  have hUssq : Integrable (fun ω => U s ω ^ 2) μ := ((hQ.integrable s).add hAs).congr hQssq.symm
  have hUtsq : Integrable (fun ω => U t ω ^ 2) μ := ((hQ.integrable t).add hAs).congr hQtsq.symm
  have hUs₂ : MemLp (U s) 2 μ :=
    (memLp_two_iff_integrable_sq ((hU.stronglyMeasurable s).mono (𝒢.le s)).aestronglyMeasurable).2 hUssq
  have hUt₂ : MemLp (U t) 2 μ :=
    (memLp_two_iff_integrable_sq ((hU.stronglyMeasurable t).mono (𝒢.le t)).aestronglyMeasurable).2 hUtsq
  let d := U t - U s
  have hd₂ : MemLp d 2 μ := hUt₂.sub hUs₂
  have hcross : Integrable (fun ω => U s ω * d ω) μ := hUs₂.integrable_mul hd₂
  have hcd : μ[d | 𝒢 s] =ᵐ[μ] (0 : Ω → ℝ) := by
    have h := (condExp_sub (hU.integrable t) (hU.integrable s) (𝒢 s)).trans
      ((hU.condExp_ae_eq hst).sub (hU.condExp_ae_eq (le_refl s)))
    simpa only [sub_self, d] using h
  have hmul : (∫ ω, U s ω * d ω ∂μ) = 0 := by
    have hce := (condExp_mul_of_stronglyMeasurable_left (hU.stronglyMeasurable s) hcross
      (hd₂.integrable (by norm_num))).trans (EventuallyEq.rfl.mul hcd)
    calc
      _ = ∫ ω, μ[U s * d | 𝒢 s] ω ∂μ := (integral_condExp (𝒢.le s)).symm
      _ = 0 := by rw [integral_congr_ae hce]; simp
  have hQi : (∫ ω, Q t ω ∂μ) = ∫ ω, Q s ω ∂μ :=
    (integral_condExp (𝒢.le s)).symm.trans (integral_congr_ae (hQ.condExp_ae_eq hst))
  have hsqs : (∫ ω, U t ω ^ 2 ∂μ) = ∫ ω, U s ω ^ 2 ∂μ := by
    rw [integral_congr_ae hQssq, integral_congr_ae hQtsq, integral_add (hQ.integrable t) hAs,
      integral_add (hQ.integrable s) hAs, hQi]
  have hzero : (∫ ω, d ω ^ 2 ∂μ) = 0 := by
    calc
      _ = ∫ ω, (U t ω ^ 2 - U s ω ^ 2) - 2 * (U s ω * d ω) ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun _ => by simp only [d, Pi.sub_apply]; ring
      _ = _ := by
        have hi : Integrable (fun ω => U t ω ^ 2 - U s ω ^ 2) μ := hUtsq.sub hUssq
        rw [integral_sub hi (hcross.const_mul 2), integral_sub hUtsq hUssq,
          integral_const_mul, hsqs, hmul, sub_self, mul_zero, sub_zero]
  have hae := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (d ω)) hd₂.integrable_sq).1 hzero
  filter_upwards [hae] with ω hw
  have he : d ω = 0 := sq_eq_zero_iff.mp hw
  exact (sub_eq_zero.mp he).trans (hs ω)

private theorem coe_untopA_finite {u : WithTop ℝ≥0} (hu : u ≠ ⊤) :
    (u.untopA : WithTop ℝ≥0) = u := by
  lift u to ℝ≥0 using hu
  rfl

/-- The compensator is unchanged when stopped at the first subsequent
nonnegative value, provided its density vanishes on negative values. -/
theorem stoppedCompensator_ae_eq_of_first_nonnegative {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ν : Measure ℝ≥0} [NullSingletonClass ν] {X A q : ℝ≥0 → Ω → ℝ} {s t T : ℝ≥0}
    (hst : s ≤ t) (ht : t ≤ T)
    (hA : ∀ᵐ ω ∂μ, ∀ u ∈ Icc (0 : ℝ≥0) T, A u ω = ∫ v in Ioc 0 u, q v ω ∂ν)
    (hq : ∀ᵐ ω ∂μ, ∀ u ∈ Icc (0 : ℝ≥0) T, X u ω < 0 → q u ω = 0) :
    stoppedProcess A (hittingAfter X (Ici (0 : ℝ)) s) t =ᵐ[μ] A s := by
  filter_upwards [hA, hq] with ω hwA hwq
  let τ := hittingAfter X (Ici (0 : ℝ)) s ω
  let u := (min (t : WithTop ℝ≥0) τ).untopA
  have htop : min (t : WithTop ℝ≥0) τ ≠ ⊤ :=
    (lt_of_le_of_lt (min_le_left _ _) (WithTop.coe_lt_top t)).ne
  have hu : (u : WithTop ℝ≥0) = min (t : WithTop ℝ≥0) τ := coe_untopA_finite htop
  have hsu : s ≤ u := by
    apply WithTop.coe_le_coe.mp
    rw [hu]
    exact le_min (WithTop.coe_le_coe.mpr hst) (le_hittingAfter ω)
  have hut : u ≤ t := by
    apply WithTop.coe_le_coe.mp
    rw [hu]
    exact min_le_left _ _
  have huτ : (u : WithTop ℝ≥0) ≤ τ := by rw [hu]; exact min_le_right _ _
  change A u ω = A s ω
  rw [hwA u ⟨zero_le, hut.trans ht⟩, hwA s ⟨zero_le, hst.trans ht⟩]
  rcases eq_or_lt_of_le hsu with h | h
  · rw [h]
  · rw [← setIntegral_congr_set (Ioo_ae_eq_Ioc : Ioo (0 : ℝ≥0) u =ᵐ[ν] Ioc 0 u)]
    have hsub : Ioc (0 : ℝ≥0) s ⊆ Ioo 0 u := fun v hv => ⟨hv.1, hv.2.trans_lt h⟩
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo hsub (fun v hv => ?_)
    have hsv : s ≤ v := by
      by_contra! hh
      exact hv.2 ⟨hv.1.1, hh.le⟩
    have hvτ : (v : WithTop ℝ≥0) < τ := (WithTop.coe_lt_coe.mpr hv.1.2).trans_le huτ
    have hx : X v ω < 0 := lt_of_not_ge (notMem_of_lt_hittingAfter hvτ hsv)
    exact hwq v ⟨zero_le, hv.1.2.le.trans (hut.trans ht)⟩ hx

private theorem stoppedProcess_continuousOn_of_continuous {Ω : Type*}
    {M : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0} (ω : Ω) (h : Continuous fun t => M t ω) :
    Continuous (fun t => stoppedProcess M τ t ω) := by
  by_cases ht : τ ω = ⊤
  · have he : (fun t => stoppedProcess M τ t ω) = fun t => M t ω := by
      funext t
      change M (min (t : WithTop ℝ≥0) (τ ω)).untopA ω = M t ω
      rw [ht, min_eq_left le_top]
      rfl
    rw [he]
    exact h
  · let u := (τ ω).untopA
    have hu : (u : WithTop ℝ≥0) = τ ω := coe_untopA_finite ht
    have he : (fun t => stoppedProcess M τ t ω) = fun t => M (min t u) ω := by
      funext t
      change M (min (t : WithTop ℝ≥0) (τ ω)).untopA ω = M (min t u) ω
      rw [← hu, ← WithTop.coe_min]
      rfl
    rw [he]
    exact h.comp (continuous_id.min continuous_const)

/-- Nonnegativity on an arbitrary filtration, from the coordinate equation
and its compensated square martingale, using first-return stopping times. -/
theorem ae_nonnegative_of_inward_drift_and_compensated_square {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝒢 : Filtration ℝ≥0 m} [Approximable 𝒢 μ]
    {ν : Measure ℝ≥0} [NullSingletonClass ν] {T : ℝ≥0} {X M A b q : ℝ≥0 → Ω → ℝ} {x₀ : ℝ}
    (hXc : ∀ᵐ ω ∂μ, ContinuousOn (fun u => X u ω) (Icc (0 : ℝ≥0) T))
    (hMc : ∀ ω, Continuous fun u => M u ω) (hAc : ∀ ω, Continuous fun u => A u ω)
    (hM : Martingale M 𝒢 μ) (hM2A : Martingale (fun u ω => M u ω ^ 2 - A u ω) 𝒢 μ)
    (hτ : ∀ s : ℝ≥0, IsStoppingTime 𝒢 (hittingAfter X (Ici (0 : ℝ)) s))
    (hAi : ∀ s, Integrable (A s) μ)
    (hinit : ∀ᵐ ω ∂μ, 0 ≤ X 0 ω)
    (hX : ∀ᵐ ω ∂μ, ∀ u ∈ Icc (0 : ℝ≥0) T,
      X u ω = x₀ + (∫ v in Ioc 0 u, b v ω ∂ν) + M u ω)
    (hA : ∀ᵐ ω ∂μ, ∀ u ∈ Icc (0 : ℝ≥0) T, A u ω = ∫ v in Ioc 0 u, q v ω ∂ν)
    (hbi : ∀ᵐ ω ∂μ, IntegrableOn (fun v => b v ω) (Ioc (0 : ℝ≥0) T) ν)
    (hinward : ∀ᵐ ω ∂μ, ∀ u ∈ Icc (0 : ℝ≥0) T, X u ω < 0 → 0 ≤ b u ω ∧ q u ω = 0) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ≥0) T, 0 ≤ X t ω := by
  classical
  have hMr : ∀ ω, IsRightContinuous (fun u => M u ω) := fun ω => (hMc ω).isRightContinuous
  have hM2Ar : ∀ ω, IsRightContinuous (fun u => M u ω ^ 2 - A u ω) := fun ω =>
    (((hMc ω).pow 2).sub (hAc ω)).isRightContinuous
  have hq : ∀ᵐ ω ∂μ, ∀ u ∈ Icc (0 : ℝ≥0) T, X u ω < 0 → q u ω = 0 :=
    hinward.mono fun _ hw u hu hx => (hw u hu hx).2
  have hstop (s : ℝ≥0) (hs : s ≤ T) : ∀ᵐ ω ∂μ, ∀ t ∈ Icc s T,
      stoppedProcess M (hittingAfter X (Ici (0 : ℝ)) s) t ω = M s ω := by
    let Y (u : ℝ≥0) (ω : Ω) := stoppedProcess M (hittingAfter X (Ici (0 : ℝ)) s) (max u s) ω
    have hc : ∀ᵐ ω ∂μ, ContinuousOn (fun u => Y u ω) (Icc (0 : ℝ≥0) T) :=
      Eventually.of_forall fun ω => ((stoppedProcess_continuousOn_of_continuous ω (hMc ω)).comp
        (continuous_id.max continuous_const)).continuousOn
    have he : ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ≥0) T, Y t ω = M s ω := by
      apply MathFin.LocalisationInMeasure.ae_forall_eq_of_continuousOn hc
        (Y' := fun _ => M s) (Eventually.of_forall fun _ => continuousOn_const)
      intro t ht
      exact stoppedProcess_ae_eq_of_flat_square_compensator hM hM2A hMr hM2Ar (hτ s)
        (fun ω => le_hittingAfter ω) (le_max_right _ _) (hAi s)
        (stoppedCompensator_ae_eq_of_first_nonnegative (le_max_right _ _) (max_le ht.2 hs) hA hq)
    exact he.mono fun ω hw t ht => by
      simpa only [Y, max_eq_left ht.1] using hw t ⟨zero_le, ht.2⟩
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  let D₀ := D ∩ Icc (0 : ℝ≥0) T
  have hD₀ : D₀.Countable := hDc.mono inter_subset_left
  have hstarts : ∀ᵐ ω ∂μ, ∀ s ∈ D₀, ∀ t ∈ Icc s T,
      stoppedProcess M (hittingAfter X (Ici (0 : ℝ)) s) t ω = M s ω :=
    (ae_ball_iff hD₀).2 (fun s hs => hstop s hs.2.2)
  filter_upwards [hXc, hinit, hX, hbi, hinward, hstarts] with ω hwc hw0 hwX hwbi hw hsω
  apply continuous_path_nonnegative_of_dense_excursion_monotonicity hDd hwc hw0
  intro s hs t ht hneg
  have hst : s ≤ t := ht.1
  have hsT : s ≤ T := hst.trans ht.2
  have htτ : (t : WithTop ℝ≥0) ≤ hittingAfter X (Ici (0 : ℝ)) s ω := by
    by_contra! hh
    obtain ⟨u, hu, hu'⟩ := hittingAfter_lt_iff.mp hh
    exact (not_le_of_gt (hneg u ⟨hu.1, hu.2.le⟩)) hu'
  have hMs : M t ω = M s ω := by
    have he := hsω s ⟨hs, ⟨zero_le, hsT⟩⟩ t ht
    change M (min (t : WithTop ℝ≥0) (hittingAfter X (Ici (0 : ℝ)) s ω)).untopA ω = M s ω at he
    rw [min_eq_left htτ] at he
    exact he
  have hb0 : 0 ≤ ∫ u in Ioc s t, b u ω ∂ν := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact (hw u ⟨zero_le, hu.2.trans ht.2⟩ (hneg u ⟨hu.1.le, hu.2⟩)).1
  have hbSplit : (∫ u in Ioc (0 : ℝ≥0) t, b u ω ∂ν) =
      (∫ u in Ioc (0 : ℝ≥0) s, b u ω ∂ν) + (∫ u in Ioc s t, b u ω ∂ν) := by
    rw [← Ioc_union_Ioc_eq_Ioc zero_le hst]
    refine setIntegral_union (Set.disjoint_left.mpr fun u hu hu' => hu.2.not_gt hu'.1)
      measurableSet_Ioc (hwbi.mono_set (Ioc_subset_Ioc_right hsT))
      (hwbi.mono_set (Ioc_subset_Ioc zero_le ht.2))
  rw [hwX s ⟨zero_le, hsT⟩, hwX t ⟨zero_le, ht.2⟩, hbSplit, hMs]
  linarith

/-- A progressively measurable variance process on a usual filtration has
the admissible first-return stopping times needed for the bracket argument. -/
theorem ae_nonnegative_of_inward_drift_and_compensated_square_usual {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝒢 : Filtration ℝ≥0 m}
    [𝒢.IsComplete μ] [𝒢.IsRightContinuous] {ν : Measure ℝ≥0} [NullSingletonClass ν]
    {T : ℝ≥0} {X M A b q : ℝ≥0 → Ω → ℝ} {x₀ : ℝ}
    (hXp : IsStronglyProgressive 𝒢 X)
    (hXc : ∀ᵐ ω ∂μ, ContinuousOn (fun u => X u ω) (Icc (0 : ℝ≥0) T))
    (hMc : ∀ ω, Continuous fun u => M u ω) (hAc : ∀ ω, Continuous fun u => A u ω)
    (hM : Martingale M 𝒢 μ) (hM2A : Martingale (fun u ω => M u ω ^ 2 - A u ω) 𝒢 μ)
    (hAi : ∀ s, Integrable (A s) μ)
    (hinit : ∀ᵐ ω ∂μ, 0 ≤ X 0 ω)
    (hX : ∀ᵐ ω ∂μ, ∀ u ∈ Icc (0 : ℝ≥0) T,
      X u ω = x₀ + (∫ v in Ioc 0 u, b v ω ∂ν) + M u ω)
    (hA : ∀ᵐ ω ∂μ, ∀ u ∈ Icc (0 : ℝ≥0) T, A u ω = ∫ v in Ioc 0 u, q v ω ∂ν)
    (hbi : ∀ᵐ ω ∂μ, IntegrableOn (fun v => b v ω) (Ioc (0 : ℝ≥0) T) ν)
    (hinward : ∀ᵐ ω ∂μ, ∀ u ∈ Icc (0 : ℝ≥0) T, X u ω < 0 → 0 ≤ b u ω ∧ q u ω = 0) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ≥0) T, 0 ≤ X t ω :=
  ae_nonnegative_of_inward_drift_and_compensated_square hXc hMc hAc hM hM2A
    (fun s => hXp.isStoppingTime_hittingAfter μ measurableSet_Ici s) hAi hinit hX hA hbi hinward

section BrownianNaturalFiltration

open ProbabilityTheory MathFin MathFin.ItoFormulaAdapted MathFin.ItoIntegralL2
  MathFin.ItoIntegralLocalised MathFin.ItoIntegralRiemannBridge MathFin.LocalisationInMeasure

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- The localized predictable Itô integral vanishes simultaneously on the
horizon when its integrand vanishes there almost surely. -/
theorem ae_predItoIntegral_zero_of_path_zero (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun s => B s ω)
    {θ : ℝ≥0 → Ω → ℝ} (hθ : IsStronglyPredictable (natFiltration hBmeas) θ)
    (hz : ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ≥0) T, θ t ω = 0) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ≥0) T, predItoIntegral (μ := μ) T hBmeas hθ t ω = 0 := by
  have hθc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => θ t ω) (Icc (0 : ℝ≥0) T) :=
    hz.mono fun _ hw => continuousOn_const.congr hw
  apply ae_forall_eq_of_continuousOn
    (ae_continuousOn_predItoIntegral hB T hBmeas hBcont hθ hθc)
    (Y' := fun _ _ => 0) (Eventually.of_forall fun _ => continuousOn_const)
  intro t ht
  have hleft := tendstoInMeasure_riemannσ_predItoIntegral hB T hBmeas hBcont hθ hθc ht.2
  have hr (n : ℕ) : riemannσ (B := B) θ t n =ᵐ[μ] (fun _ => 0) := by
    filter_upwards [hz] with ω hw
    have heq := riemannσ_congr (B := B) (θ' := fun _ _ => 0)
      (fun s hs => hw s ⟨hs.1, hs.2.trans ht.2⟩) n
    rw [heq]
    simp [riemannσ]
  have hconst : TendstoInMeasure μ (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (Eventually.of_forall fun _ => tendsto_const_nhds)
  exact tendstoInMeasure_ae_unique hleft (hconst.congr_left fun n => (hr n).symm)

/-- Brownian natural-filtration case of the nonnegativity argument, using
MathFin's process-level `C²` Itô theorem for its constructed Itô process. -/
theorem localItoProcess_ae_nonnegative_of_inward_coefficients (hB : IsPreBrownianReal B μ)
    (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t => B t ω)
    {σ b : ℝ≥0 → Ω → ℝ}
    (hσ_adap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (σ t))
    (hσ_cont : ∀ ω, Continuous fun t => σ t ω)
    (hb_adap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (b t))
    (hb_cont : ∀ ω, Continuous fun t => b t ω) {x₀ : ℝ} (hx₀ : 0 ≤ x₀)
    (hcoeff : ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ≥0) T,
      localItoProcess (μ := μ) T hBmeas hσ_adap hσ_cont x₀ b t ω ≤ 0 →
        0 ≤ b t ω ∧ σ t ω = 0) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ≥0) T,
      0 ≤ localItoProcess (μ := μ) T hBmeas hσ_adap hσ_cont x₀ b t ω := by
  let X := localItoProcess (μ := μ) T hBmeas hσ_adap hσ_cont x₀ b
  let θ (s : ℝ≥0) (ω : Ω) := negativePartCubePrime (X s ω) * σ s ω
  have hp : Continuous negativePartCubePrime :=
    Differentiable.continuous fun x => (negativePartCubePrime_hasDerivAt x).differentiableAt
  have hθ : IsStronglyPredictable (natFiltration hBmeas) θ :=
    itoIntegrand_isStronglyPredictable hB T hBmeas hBcont hσ_adap hσ_cont hb_adap hb_cont
      x₀ (f_x := fun _ x => negativePartCubePrime x) (hp.comp continuous_snd)
  have hz : ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ≥0) T, θ t ω = 0 := by
    filter_upwards [hcoeff] with ω hw t ht
    exact negativePartCube_itoNoise_zero (fun hx => (hw t ht hx).2)
  have hnoise := ae_predItoIntegral_zero_of_path_zero hB T hBmeas hBcont hθ hz
  have hIto := ito_formula_adapted_unbounded_C2_process hB T hBmeas hBcont hσ_adap hσ_cont
    hb_adap hb_cont x₀ negativePartCube_hasDerivAt negativePartCubePrime_hasDerivAt
    negativePartCubeSecond_continuous
  exact ae_nonnegative_of_negativePartCube_ito_identity hx₀ hcoeff hnoise hIto

end BrownianNaturalFiltration

end RoughHeston

#print axioms RoughHeston.negativePartCube_hasDerivAt
#print axioms RoughHeston.negativePartCubePrime_hasDerivAt
#print axioms RoughHeston.negativePartCubeSecond_continuous
#print axioms RoughHeston.negativePartCube_itoDrift_nonpos
#print axioms RoughHeston.negativePartCube_itoNoise_zero
#print axioms RoughHeston.ae_nonnegative_of_negativePartCube_ito_identity

#print axioms RoughHeston.ae_predItoIntegral_zero_of_path_zero
#print axioms RoughHeston.localItoProcess_ae_nonnegative_of_inward_coefficients

#print axioms RoughHeston.continuous_path_nonnegative_of_dense_excursion_monotonicity

#print axioms RoughHeston.stoppedProcess_ae_eq_of_flat_square_compensator

#print axioms RoughHeston.stoppedCompensator_ae_eq_of_first_nonnegative
#print axioms RoughHeston.ae_nonnegative_of_inward_drift_and_compensated_square

#print axioms RoughHeston.ae_nonnegative_of_inward_drift_and_compensated_square_usual
