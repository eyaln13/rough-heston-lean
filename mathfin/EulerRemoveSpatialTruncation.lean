import EulerCutoffTightness
import EulerGrowthCanonicalTestMoments
import MovingMartingaleTestLimits
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! Removal of radial spatial truncations from the finite-dimensional martingale problem. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BoundedContinuousFunction

namespace RoughHeston

private theorem tendsto_continuousMap_of_eventually_eq_on_compacts
    {X : Type*} [TopologicalSpace X] {F : ℕ → C(X, ℝ)} {f : C(X, ℝ)}
    (h : ∀ K : Set X, IsCompact K → ∀ᶠ n in atTop, ∀ x ∈ K, F n x = f x) :
    Tendsto F atTop (𝓝 f) := by
  rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [h K hK] with n hn x hx
  rw [hn x hx, dist_self]
  exact hε

private theorem canonicalMartingale_boundedContinuous_past_test
    {ι : Type*} [Fintype ι] {T : ℝ≥0} {μ : Measure (CanonicalPath T (ι → ℝ))}
    [IsProbabilityMeasure μ] {M : ℝ≥0 → CanonicalPath T (ι → ℝ) → ℝ}
    (hM : Martingale M (canonicalPathNaturalFiltration T) μ)
    {s t : ℝ≥0} (hst : s ≤ t) (f : CanonicalPath T (ι → ℝ) →ᵇ ℝ) :
    (∫ p, (M t p - M s p) * f (canonicalStoppedPath T s p) ∂μ) = 0 := by
  let Y (p : CanonicalPath T (ι → ℝ)) := f (canonicalStoppedPath T s p)
  have hY : StronglyMeasurable[canonicalPathNaturalFiltration (E := ι → ℝ) T s] Y := by
    rw [canonicalPathNaturalFiltration_eq_comap_stopped]
    exact (f.continuous.measurable.comp (comap_measurable _)).stronglyMeasurable
  have hYm : AEStronglyMeasurable Y μ :=
    (hY.mono ((canonicalPathNaturalFiltration T).le s)).aestronglyMeasurable
  have hI (r : ℝ≥0) : Integrable (fun p => M r p * Y p) μ :=
    (hM.integrable r).mul_bdd hYm (Eventually.of_forall fun p => f.norm_coe_le_norm (canonicalStoppedPath T s p))
  change (∫ p, (M t p - M s p) * Y p ∂μ) = 0
  simp_rw [sub_mul]
  rw [integral_sub (hI t) (hI s),
    integral_martingale_mul_past hM hst hY.aestronglyMeasurable (hI t), sub_self]

/-- A weak limit of actual radial-cutoff laws solves the original
finite-dimensional continuous linear-growth martingale problem. -/
theorem radialEulerLaw_weak_limit_martingale_problem
    {ι κ : Type*} [Fintype ι] [Fintype κ] {T : ℝ≥0}
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    (x : ι → ℝ)
    (hb : ∀ i, Continuous (fun z : ℝ≥0 × (ι → ℝ) => b z.1 z.2 i))
    (hσ : ∀ i j, Continuous (fun z : ℝ≥0 × (ι → ℝ) => σ z.1 z.2 i j))
    {L : ℝ} (hL : 0 ≤ L)
    (hB : ∀ r y i, ‖b r y i‖ ≤ L*(1+‖y‖))
    (hC : ∀ r y i j, ‖σ r y i j‖ ≤ L*(1+‖y‖))
    (Pn : ℕ → ProbabilityMeasure (CanonicalPath T (ι → ℝ)))
    (hInit : ∀ n, (Pn n : Measure (CanonicalPath T (ι → ℝ))) {p | canonicalPathEval T 0 p = x} = 1)
    (hM : ∀ (n : ℕ) i, Martingale (canonicalEulerMartingaleCoordinate T (radialEulerDrift ((n : ℝ)+1) b) x i)
      (canonicalPathNaturalFiltration T) (Pn n : Measure _))
    (hQ : ∀ (n : ℕ) i l, Martingale (canonicalEulerCompensatedProduct T (radialEulerDrift ((n : ℝ)+1) b)
      (radialEulerDiffusion ((n : ℝ)+1) σ) x i l) (canonicalPathNaturalFiltration T) (Pn n : Measure _))
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {P : ProbabilityMeasure (CanonicalPath T (ι → ℝ))}
    (hweak : Tendsto (Pn ∘ φ) atTop (𝓝 P)) :
    (P : Measure (CanonicalPath T (ι → ℝ))) {p | canonicalPathEval T 0 p = x} = 1 ∧
      (∀ i, Martingale (canonicalEulerMartingaleCoordinate T b x i)
        (canonicalPathNaturalFiltration T) (P : Measure _)) ∧
      (∀ i l, Martingale (canonicalEulerCompensatedProduct T b σ x i l)
        (canonicalPathNaturalFiltration T) (P : Measure _)) := by
  let Path := CanonicalPath T (ι → ℝ)
  let R (n : ℕ) := (n : ℝ)+1
  let bR (n : ℕ) := radialEulerDrift (R n) b
  let σR (n : ℕ) := radialEulerDiffusion (R n) σ
  let B (n : ℕ) := L*(1+R n)
  have hR (n : ℕ) : 0 < R n := by dsimp [R]; positivity
  have hB₀ (n : ℕ) : 0 ≤ B n := by dsimp [B, R]; positivity
  have hbR (n : ℕ) (i : ι) : Continuous (fun z : ℝ≥0 × (ι → ℝ) => bR n z.1 z.2 i) :=
    continuous_comp_radialTruncation (hR n) (c := fun r y => b r y i) (hb i)
  have hσR (n : ℕ) (i : ι) (j : κ) : Continuous (fun z : ℝ≥0 × (ι → ℝ) => σR n z.1 z.2 i j) :=
    continuous_comp_radialTruncation (hR n) (c := fun r y => σ r y i j) (hσ i j)
  have hBR (n : ℕ) (r : ℝ≥0) (y : ι → ℝ) (i : ι) : ‖bR n r y i‖ ≤ B n :=
    (radialEulerCoefficient_bounds (hR n) hL (fun r y => hB r y i)).1 r y
  have hCR (n : ℕ) (r : ℝ≥0) (y : ι → ℝ) (i : ι) (j : κ) : ‖σR n r y i j‖ ≤ B n :=
    (radialEulerCoefficient_bounds (hR n) hL (fun r y => hC r y i j)).1 r y
  have hBgr (n : ℕ) (r : ℝ≥0) (y : ι → ℝ) (i : ι) : ‖bR n r y i‖ ≤ L*(1+‖y‖) :=
    (radialEulerCoefficient_bounds (hR n) hL (fun r y => hB r y i)).2 r y
  have hCgr (n : ℕ) (r : ℝ≥0) (y : ι → ℝ) (i : ι) (j : κ) : ‖σR n r y i j‖ ≤ L*(1+‖y‖) :=
    (radialEulerCoefficient_bounds (hR n) hL (fun r y => hC r y i j)).2 r y
  let D := 8*L^4*(1+(Fintype.card ι : ℝ))
  let A := (boundedMartingaleEvenPowerConstant 2).toReal
  let K := 64*(Fintype.card ι : ℝ)*D*((T : ℝ)^3 + A*(T : ℝ)*(Fintype.card κ : ℝ)^2)
  let H := 2*(8*(∑ i, (x i)^4)+K*(T : ℝ))*Real.exp ((2*K+1)*(T : ℝ))
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hH : 0 ≤ H := by
    dsimp only [H]
    have hx : 0 ≤ ∑ i, (x i)^4 := Finset.sum_nonneg fun _ _ => by positivity
    positivity
  have h4 (n : ℕ) (t : ℝ≥0) (i : ι) : Integrable (fun p : Path => (canonicalPathEval T t p i)^4) (Pn n : Measure Path) :=
    (bounded_canonicalEulerStateFourthMoment (hInit n) (hbR n) (hσR n) (hBR n)
      (hB₀ n) (hCR n) (hM n) (fun i => hQ n i i)).1 t i
  have hHbound (n : ℕ) (t : ℝ≥0) : canonicalEulerStateFourthMoment T (Pn n : Measure Path) t ≤ H :=
    canonicalEulerStateFourthMoment_le_linear_growth (hInit n) (hbR n) (hσR n) (hBR n)
      (hB₀ n) (hCR n) (hBgr n) (hCgr n) (hM n) (fun i => hQ n i i) t
  let M (i : ι) (t : ℝ≥0) : C(Path, ℝ) :=
    ⟨canonicalEulerMartingaleCoordinate T b x i t,
      continuous_canonicalEulerMartingaleCoordinate_of_growth T t x i (hb i) hL (fun r y => hB r y i)⟩
  let Mn (n : ℕ) (i : ι) (t : ℝ≥0) : C(Path, ℝ) :=
    ⟨canonicalEulerMartingaleCoordinate T (bR n) x i t,
      continuous_canonicalEulerMartingaleCoordinate T t x i (hbR n i) (fun r y => hBR n r y i)⟩
  let Q (i l : ι) (t : ℝ≥0) : C(Path, ℝ) :=
    ⟨canonicalEulerCompensatedProduct T b σ x i l t,
      continuous_canonicalEulerCompensatedProduct_of_growth T t x i l hb hσ hL hB hC⟩
  let Qn (n : ℕ) (i l : ι) (t : ℝ≥0) : C(Path, ℝ) :=
    ⟨canonicalEulerCompensatedProduct T (bR n) (σR n) x i l t,
      continuous_canonicalEulerCompensatedProduct T t x i l (hbR n) (hσR n)
        (hBR n) (hB₀ n) (hCR n)⟩
  have hRbig (r : ℝ) : ∀ᶠ n : ℕ in atTop, r ≤ R (φ n) := by
    obtain ⟨N, hN⟩ := exists_nat_gt r
    filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop N)] with n hn
    have hnn : (N : ℝ) ≤ (φ n : ℝ) := by exact_mod_cast hn
    exact hN.le.trans (hnn.trans (by dsimp [R]; linarith))
  have hME (i : ι) (t : ℝ≥0) (C : Set Path) (hC : IsCompact C) :
      ∀ᶠ n : ℕ in atTop, ∀ p ∈ C, Mn (φ n) i t p = M i t p := by
    obtain ⟨r, hr⟩ := canonicalCoefficientIntegral_eventually_eq_radialTruncation_on_compact T
      (fun u y => b u y i) hC
    filter_upwards [hRbig r] with n hn p hp
    unfold Mn M
    dsimp [canonicalEulerMartingaleCoordinate, bR, radialEulerDrift]
    rw [hr _ hn p hp t]
  have hQE (i l : ι) (t : ℝ≥0) (C : Set Path) (hC : IsCompact C) :
      ∀ᶠ n : ℕ in atTop, ∀ p ∈ C, Qn (φ n) i l t p = Q i l t p := by
    obtain ⟨r, hr⟩ := canonicalCoefficientIntegral_eventually_eq_radialTruncation_on_compact T
      (eulerCovarianceCoefficient σ i l) hC
    filter_upwards [hRbig r, hME i t C hC, hME l t C hC] with n hn hi hl p hp
    have hm : canonicalCoefficientIntegral T (eulerCovarianceCoefficient (σR (φ n)) i l) t p =
        canonicalCoefficientIntegral T (eulerCovarianceCoefficient σ i l) t p := hr _ hn p hp t
    change Mn (φ n) i t p * Mn (φ n) l t p -
      canonicalCoefficientIntegral T (eulerCovarianceCoefficient (σR (φ n)) i l) t p =
      M i t p * M l t p - canonicalCoefficientIntegral T (eulerCovarianceCoefficient σ i l) t p
    rw [hi p hp, hl p hp, hm]
  let V (i : ι) := 8*(8*(H+(x i)^4)+D*(T : ℝ)^4*(1+H))
  let U (i l : ι) := 2*((V i+V l)/2 + (Fintype.card κ : ℝ)^2*D*(T : ℝ)^2*(1+H))
  have hV (i : ι) : 0 ≤ V i := by dsimp only [V]; positivity
  have hU (i l : ι) : 0 ≤ U i l := by dsimp only [U]; positivity
  have hLimInit : (P : Measure Path) {p | canonicalPathEval T 0 p = x} = 1 := by
    let S : Set Path := {p | canonicalPathEval T 0 p = x}
    have hc : IsClosed S := isClosed_eq (continuous_canonicalPathEval T 0) continuous_const
    have h := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hweak hc
    change Filter.limsup (fun n => (Pn (φ n) : Measure Path) S) atTop ≤ (P : Measure Path) S at h
    simp only [show ∀ n, (Pn n : Measure Path) S = 1 from hInit, Filter.limsup_const] at h
    exact le_antisymm prob_le_one h
  refine ⟨hLimInit, ?_, ?_⟩
  · intro i
    refine martingale_of_exact_moving_continuous_tests hweak (M := M i) (Mn := fun n => Mn (φ n) i)
      (stronglyAdapted_canonicalEulerMartingaleCoordinate_of_growth T x i (hb i) hL (fun r y => hB r y i))
      (continuous_canonicalStoppedPath T) (canonicalPathNaturalFiltration_eq_comap_stopped T)
      (fun t => tendsto_continuousMap_of_eventually_eq_on_compacts (hME i t))
      (fun s t hst f n => canonicalMartingale_boundedContinuous_past_test (hM (φ n) i) hst f)
      ?_ ?_
    · intro t
      refine ⟨1+V i, by positivity, fun n => ?_⟩
      have h := canonicalEulerMartingaleCoordinate_fourth_bound_of_state x i t (hb i) hL hH
        (fun r y => hB r y i) (Pn (φ n) : Measure Path) (h4 (φ n)) (hHbound (φ n))
      have h₂ := integral_sq_le_one_add_integral_pow_four h.1
      exact ⟨h₂.1, h₂.2.trans (add_le_add le_rfl h.2)⟩
    · intro t
      refine ⟨1+V i, by positivity, fun n => ?_⟩
      have h := canonicalEulerMartingaleCoordinate_fourth_bound_of_state x i t (hbR (φ n) i) hL hH
        (fun r y => hBgr (φ n) r y i) (Pn (φ n) : Measure Path) (h4 (φ n)) (hHbound (φ n))
      have h₂ := integral_sq_le_one_add_integral_pow_four h.1
      exact ⟨h₂.1, h₂.2.trans (add_le_add le_rfl h.2)⟩
  · intro i l
    refine martingale_of_exact_moving_continuous_tests hweak (M := Q i l) (Mn := fun n => Qn (φ n) i l)
      (stronglyAdapted_canonicalEulerCompensatedProduct_of_growth T x i l hb hσ hL hB hC)
      (continuous_canonicalStoppedPath T) (canonicalPathNaturalFiltration_eq_comap_stopped T)
      (fun t => tendsto_continuousMap_of_eventually_eq_on_compacts (hQE i l t))
      (fun s t hst f n => canonicalMartingale_boundedContinuous_past_test (hQ (φ n) i l) hst f)
      ?_ ?_
    · intro t
      exact ⟨U i l, hU i l, fun n => canonicalEulerCompensatedProduct_sq_bound_of_state
        x i l t hb hσ hL hH hB hC (Pn (φ n) : Measure Path) (h4 (φ n)) (hHbound (φ n))⟩
    · intro t
      exact ⟨U i l, hU i l, fun n => canonicalEulerCompensatedProduct_sq_bound_of_state
        x i l t (hbR (φ n)) (hσR (φ n)) hL hH (hBgr (φ n)) (hCgr (φ n))
        (Pn (φ n) : Measure Path) (h4 (φ n)) (hHbound (φ n))⟩

#print axioms RoughHeston.radialEulerLaw_weak_limit_martingale_problem

end RoughHeston
