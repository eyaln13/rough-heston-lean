import EulerUniformFourthEnergy
import CanonicalProperPathTightness

/-! Weak compactness of the radial-cutoff martingale-problem laws. -/

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston

open MathFin.ItoIntegralCLM

/-- Constant for the uniform fourth increment bound of cutoff laws. -/
noncomputable def cutoffEulerIncrementFourthConstant (ι κ : Type*) [Fintype ι] [Fintype κ]
    (T L : ℝ) (x : ι → ℝ) : ℝ :=
  let Q := 8*L^4*(1+(Fintype.card ι : ℝ))
  let C₄ := (boundedMartingaleEvenPowerConstant 2).toReal
  let J := (Fintype.card κ : ℝ)
  let K := 64*(Fintype.card ι : ℝ)*Q*(T^3+C₄*T*J^2)
  let A := 8*(∑ i, (x i)^4) + K*T
  let H := 2*A*Real.exp ((2*K+1)*T)
  8*Q*(T^2+C₄*J^2)*(1+H)

/-- The uniform fourth-moment criterion for a bounded canonical law with
a common linear-growth bound. Neither coefficient supremum enters the result. -/
theorem integral_fourth_canonicalEulerState_sub_le_uniform
    {ι κ : Type*} [Fintype ι] [Fintype κ] {T : ℝ≥0}
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    {x : ι → ℝ} {μ : Measure (CanonicalPath T (ι → ℝ))} [IsProbabilityMeasure μ]
    (hInit : μ {p | canonicalPathEval T 0 p = x} = 1)
    (hb : ∀ i, Continuous (fun z : ℝ≥0 × (ι → ℝ) => b z.1 z.2 i))
    (hσ : ∀ i j, Continuous (fun z : ℝ≥0 × (ι → ℝ) => σ z.1 z.2 i j))
    {B C L : ℝ} (hB : ∀ r y i, ‖b r y i‖ ≤ B) (hC₀ : 0 ≤ C)
    (hC : ∀ r y i j, ‖σ r y i j‖ ≤ C)
    (hBG : ∀ r y i, ‖b r y i‖ ≤ L * (1+‖y‖))
    (hCG : ∀ r y i j, ‖σ r y i j‖ ≤ L * (1+‖y‖))
    (hM : ∀ i, Martingale (canonicalEulerMartingaleCoordinate T b x i)
      (canonicalPathNaturalFiltration T) μ)
    (hQ : ∀ i, Martingale (canonicalEulerCompensatedProduct T b σ x i i)
      (canonicalPathNaturalFiltration T) μ)
    (i : ι) {s t : ℝ≥0} (hst : s ≤ t) (ht : t ≤ T) :
    let f (p : CanonicalPath T (ι → ℝ)) := canonicalPathEval T t p i - canonicalPathEval T s p i
    MemLp f 4 μ ∧
      (∫ p, (f p)^4 ∂μ) ≤ cutoffEulerIncrementFourthConstant ι κ T L x * ((t : ℝ)-(s : ℝ))^2 := by
  dsimp only
  let P := CanonicalPath T (ι → ℝ)
  let G := canonicalEulerStateFourthMoment T μ
  let Q := 8*L^4*(1+(Fintype.card ι : ℝ))
  let C₄ := (boundedMartingaleEvenPowerConstant 2).toReal
  let J := (Fintype.card κ : ℝ)
  let K := 64*(Fintype.card ι : ℝ)*Q*((T : ℝ)^3+C₄*(T : ℝ)*J^2)
  let A := 8*(∑ i, (x i)^4) + K*(T : ℝ)
  let H := 2*A*Real.exp ((2*K+1)*(T : ℝ))
  let Δ := (t : ℝ)-(s : ℝ)
  let ν := eulerTimeSlice s t
  have hΔ : 0 ≤ Δ := sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst)
  have hΔT : Δ ≤ (T : ℝ) := (sub_le_self _ s.coe_nonneg).trans (NNReal.coe_le_coe.mpr ht)
  have hNQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hNC₄ : 0 ≤ C₄ := ENNReal.toReal_nonneg
  have hNH : 0 ≤ H := by
    have hK : 0 ≤ K := by dsimp only [K]; positivity
    have hA : 0 ≤ A := by
      dsimp only [A]
      exact add_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => by positivity))
        (mul_nonneg hK T.coe_nonneg)
    dsimp only [H]
    positivity
  have h4 := (bounded_canonicalEulerStateFourthMoment hInit hb hσ hB hC₀ hC hM hQ).1
  have hU (r : ℝ≥0) : G r ≤ H :=
    canonicalEulerStateFourthMoment_le_linear_growth hInit hb hσ hB hC₀ hC hBG hCG hM hQ r
  have hMass : ν.real univ = Δ := eulerTimeSlice_mass s t hst
  have hGI : Integrable G ν := (integrable_const H).mono'
    (measurable_canonicalEulerStateFourthMoment T μ).stronglyMeasurable.aestronglyMeasurable
    (Eventually.of_forall fun r => by
      have hGr : 0 ≤ G r := Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => by positivity
      rw [Real.norm_of_nonneg hGr]
      exact hU r)
  have hG : (∫ r, G r ∂ν) ≤ H*Δ := by
    refine (integral_mono hGI (integrable_const H) hU).trans_eq ?_
    rw [integral_const, smul_eq_mul, hMass, mul_comm]
  have hb4 (r : ℝ≥0) (y : ι → ℝ) : ‖(b r y i)^4‖ ≤ B^4 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hB _ _ _) 4
  have hCov2 (r : ℝ≥0) (y : ι → ℝ) :
      ‖(eulerCovarianceCoefficient σ i i r y)^2‖ ≤ (J*C^2)^2 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_eulerCovarianceCoefficient_le hC₀ hC i i r y) 2
  have hD := integral_slice_mean_le_of_state_fourth T ((hb i).pow 4) hb4
    (fun r y => growth_fourth_le (hBG r y i)) μ h4 hU ν
  have hA := integral_slice_mean_le_of_state_fourth T
    ((continuous_eulerCovarianceCoefficient hσ i i).pow 2) hCov2
    (covariance_sq_le_of_growth hCG i) μ h4 hU ν
  rw [hMass] at hD hA
  have hD' := hD.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hG) hNQ)
  have hA' := hA.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hG)
    (mul_nonneg (sq_nonneg (Fintype.card κ : ℝ)) hNQ))
  have hInc := integral_fourth_canonicalEulerState_sub_le_energy hInit hb hσ hB hC₀ hC i (hM i) (hQ i) hst
  refine ⟨hInc.1, hInc.2.trans ?_⟩
  rw [min_eq_left ht, min_eq_left (hst.trans ht)]
  change 8 * (Δ^3 * (∫ r, ∫ p : P, (b r (canonicalPathEval T r p) i)^4 ∂μ ∂ν) +
    C₄ * Δ * (∫ r, ∫ p : P, (eulerCovarianceCoefficient σ i i r (canonicalPathEval T r p))^2 ∂μ ∂ν))
    ≤ cutoffEulerIncrementFourthConstant ι κ T L x * Δ^2
  have hDmul := mul_le_mul_of_nonneg_left hD' (pow_nonneg hΔ 3)
  have hAmul := mul_le_mul_of_nonneg_left hA' (mul_nonneg hNC₄ hΔ)
  have hsum := mul_le_mul_of_nonneg_left (add_le_add hDmul hAmul) (show (0 : ℝ) ≤ 8 by norm_num)
  have hPow := pow_le_pow_left₀ hΔ hΔT 2
  have hMul := mul_le_mul_of_nonneg_left hPow (show 0 ≤ 8*Q*(1+H)*Δ^2 by positivity)
  apply hsum.trans
  change _ ≤ 8*Q*((T : ℝ)^2+C₄*J^2)*(1+H)*Δ^2
  nlinarith [hMul]

/-- Radially truncate both spatial coefficients using the same radius. -/
noncomputable def radialEulerDrift {ι : Type*} [Fintype ι] (R : ℝ)
    (b : ℝ≥0 → (ι → ℝ) → ι → ℝ) (t : ℝ≥0) (y : ι → ℝ) := b t (radialTruncation R y)

noncomputable def radialEulerDiffusion {ι κ : Type*} [Fintype ι] (R : ℝ)
    (σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ) (t : ℝ≥0) (y : ι → ℝ) := σ t (radialTruncation R y)

theorem radialEulerCoefficient_bounds {ι : Type*} [Fintype ι]
    {c : ℝ≥0 → (ι → ℝ) → ℝ} {R L : ℝ} (hR : 0 < R) (hL : 0 ≤ L)
    (hc : ∀ t y, ‖c t y‖ ≤ L*(1+‖y‖)) :
    (∀ t y, ‖c t (radialTruncation R y)‖ ≤ L*(1+R)) ∧
    (∀ t y, ‖c t (radialTruncation R y)‖ ≤ L*(1+‖y‖)) := by
  constructor
  · intro t y
    exact (norm_comp_radialTruncation_le hR hL hc t y).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl (min_le_left _ _)) hL)
  · intro t y
    exact (norm_comp_radialTruncation_le hR hL hc t y).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl (min_le_right _ _)) hL)

private theorem edist_coord_fourth_le_sum {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    (edist x y)^(4 : ℕ) ≤ ∑ i, ENNReal.ofReal ((x i-y i)^4) := by
  let B := ∑ i, (x i-y i)^4
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => by positivity
  let R := Real.sqrt (Real.sqrt B)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR4 : R^4 = B := by
    calc
      _ = (R^2)^2 := by ring
      _ = _ := by dsimp only [R]; rw [Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hB]
  have hd : dist x y ≤ R := (dist_pi_le_iff hR).2 fun i => by
    apply le_of_pow_le_pow_left₀ (by decide : (4 : ℕ) ≠ 0) hR
    rw [hR4, Real.dist_eq, ← abs_pow, abs_of_nonneg (by positivity : 0 ≤ (x i-y i)^4)]
    exact Finset.single_le_sum (f := fun j => (x j-y j)^4) (fun _ _ => by positivity) (Finset.mem_univ i)
  have h := pow_le_pow_left₀ dist_nonneg hd 4
  rw [hR4] at h
  rw [edist_dist, ← ENNReal.ofReal_pow dist_nonneg, ← ENNReal.ofReal_sum_of_nonneg
    (fun _ _ => by positivity)]
  exact ENNReal.ofReal_le_ofReal h

/-- The actual sequence of radial-cutoff solutions has a weakly
convergent subsequence on the full finite-dimensional path space. -/
theorem radialEulerMartingaleProblem_subsequence
    {ι κ : Type*} [Fintype ι] [Fintype κ] {T : ℝ≥0} (hT : 0 < T)
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
      (radialEulerDiffusion ((n : ℝ)+1) σ) x i l) (canonicalPathNaturalFiltration T) (Pn n : Measure _)) :
    ∃ P : ProbabilityMeasure (CanonicalPath T (ι → ℝ)), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (Pn ∘ φ) atTop (𝓝 P) := by
  let Q := cutoffEulerIncrementFourthConstant ι κ T L x
  let D := (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal Q
  have hFin : D ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
  have hInit' (n : ℕ) : (Pn n : Measure (CanonicalPath T (ι → ℝ)))
      {p | ‖x‖ < ‖p (canonicalEvalTime T 0)‖} = 0 := by
    let S : Set (CanonicalPath T (ι → ℝ)) := {p | canonicalPathEval T 0 p = x}
    have hS : MeasurableSet S :=
      (isClosed_eq (continuous_canonicalPathEval T 0) continuous_const).measurableSet
    have hs : (Pn n : Measure _) Sᶜ = 0 := by
      rw [measure_compl hS (measure_ne_top _ _), show (Pn n : Measure _) S = 1 from hInit n,
        measure_univ, tsub_self]
    refine le_antisymm ((measure_mono ?_).trans_eq hs) bot_le
    intro p hp
    change ¬ canonicalPathEval T 0 p = x
    intro he
    change ‖x‖ < ‖canonicalPathEval T 0 p‖ at hp
    rw [he] at hp
    exact (lt_irrefl _ hp)
  have hMoment (n : ℕ) (s t : CanonicalPathTime T) (hst : s ≤ t) :
      (∫⁻ p : CanonicalPath T (ι → ℝ), edist (p t) (p s) ^ (4 : ℝ) ∂(Pn n : Measure _)) ≤ D * edist s t^(2 : ℝ) := by
    let R : ℝ := n+1
    let B := L*(1+R)
    let V (i : ι) (p : CanonicalPath T (ι → ℝ)) := p t i - p s i
    let Δ := ((t.val : ℝ≥0) : ℝ) - ((s.val : ℝ≥0) : ℝ)
    have hR : 0 < R := by dsimp [R]; positivity
    have hB₀ : 0 ≤ B := by dsimp [B]; positivity
    have hb' (i : ι) := continuous_comp_radialTruncation hR
      (c := fun r y => b r y i) (hb i)
    have hσ' (i : ι) (j : κ) := continuous_comp_radialTruncation hR
      (c := fun r y => σ r y i j) (hσ i j)
    have hb'B (r : ℝ≥0) (y : ι → ℝ) (i : ι) := (radialEulerCoefficient_bounds hR hL (fun r y => hB r y i)).1 r y
    have hσ'B (r : ℝ≥0) (y : ι → ℝ) (i : ι) (j : κ) := (radialEulerCoefficient_bounds hR hL (fun r y => hC r y i j)).1 r y
    have hb'G (r : ℝ≥0) (y : ι → ℝ) (i : ι) := (radialEulerCoefficient_bounds hR hL (fun r y => hB r y i)).2 r y
    have hσ'G (r : ℝ≥0) (y : ι → ℝ) (i : ι) (j : κ) := (radialEulerCoefficient_bounds hR hL (fun r y => hC r y i j)).2 r y
    have hV (i : ι) : MemLp (V i) 4 (Pn n : Measure _) ∧
        (∫ p, (V i p)^4 ∂(Pn n : Measure _)) ≤ Q*Δ^2 := by
      have h := integral_fourth_canonicalEulerState_sub_le_uniform
        (b := radialEulerDrift R b) (σ := radialEulerDiffusion R σ)
        (hInit n) hb' hσ' hb'B hB₀ hσ'B hb'G hσ'G (hM n) (fun i => hQ n i i) i
        (show s.val ≤ t.val from hst) t.property.2
      have hs' : canonicalEvalTime T s.val = s := Subtype.ext (min_eq_left s.property.2)
      have ht' : canonicalEvalTime T t.val = t := Subtype.ext (min_eq_left t.property.2)
      simpa only [canonicalPathEval, hs', ht', V, Δ, Q] using h
    have hV4 (i : ι) := integrable_pow_four_of_memLp (hV i).1
    have hd : 0 ≤ Δ := sub_nonneg.mpr (NNReal.coe_le_coe.mpr (show s.val ≤ t.val from hst))
    have hTime : ENNReal.ofReal (Δ^2) = edist s t^(2 : ℝ) := by
      have hdist : dist s t = Δ := by
        change |((s.val : ℝ≥0) : ℝ) - ((t.val : ℝ≥0) : ℝ)| = Δ
        rw [abs_of_nonpos (sub_nonpos.mpr (NNReal.coe_le_coe.mpr (show s.val ≤ t.val from hst)))]
        dsimp [Δ]
        ring
      rw [edist_dist, hdist, ENNReal.ofReal_pow hd]
      simp
    have hQ₀ : 0 ≤ Q := by
      have : 0 ≤ (boundedMartingaleEvenPowerConstant 2).toReal := ENNReal.toReal_nonneg
      dsimp [Q, cutoffEulerIncrementFourthConstant]
      positivity
    simp_rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
    calc
      _ ≤ ∫⁻ p, ∑ i, ENNReal.ofReal ((V i p)^4) ∂(Pn n : Measure _) :=
        lintegral_mono fun p => edist_coord_fourth_le_sum (p t) (p s)
      _ = ∑ i, ∫⁻ p, ENNReal.ofReal ((V i p)^4) ∂(Pn n : Measure _) :=
        lintegral_finsetSum' Finset.univ fun i _ => (hV4 i).aestronglyMeasurable.aemeasurable.ennreal_ofReal
      _ ≤ ∑ _i : ι, ENNReal.ofReal (Q*Δ^2) := by
        apply Finset.sum_le_sum
        intro i _
        rw [← ofReal_integral_eq_lintegral_ofReal (hV4 i) (Eventually.of_forall fun _ => by positivity)]
        exact ENNReal.ofReal_le_ofReal (hV i).2
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul hQ₀, hTime]
        ring
  refine canonicalProperPath_subsequence_of_increment_moments hT 4 2 ‖x‖ (by norm_num)
    (by norm_num) Pn D hFin hInit' fun n s t => ?_
  rcases le_total s t with h | h
  · have he (p : CanonicalPath T (ι → ℝ)) : edist (p t) (p s) = edist (p s) (p t) := edist_comm _ _
    simpa only [he] using hMoment n s t h
  · simpa only [edist_comm t s] using hMoment n t s h

#print axioms RoughHeston.integral_fourth_canonicalEulerState_sub_le_uniform
#print axioms RoughHeston.radialEulerMartingaleProblem_subsequence

end RoughHeston
