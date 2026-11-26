import CanonicalPhysicalVectorMoments
import FractionalSmoothResidualIncrementRate

/-! Uniform Kolmogorov input for the fixed-dimensional coupled law. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston

set_option maxHeartbeats 1400000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {T : ℝ≥0} {α κ σ : ℝ} {v : Option ι → ℝ} {β : Option ι → ℝ≥0 → ℝ}

theorem edist_canonicalPathTime_eq_ofReal {s t : CanonicalPathTime T} (hst : s.val ≤ t.val) :
    edist s t = ENNReal.ofReal ((t.val:ℝ)-(s.val:ℝ)) := by
  rw [edist_nndist, ← ENNReal.ofReal_coe_nnreal, coe_nndist]
  change ENNReal.ofReal |(s.val:ℝ)-(t.val:ℝ)| = _
  rw [abs_of_nonpos (sub_nonpos.mpr (NNReal.coe_le_coe.mpr hst)), neg_sub]

/-- Uniform increment moments of the joint variance/residual path
at every dyadic order (2^{j+1}) with (j≥1). -/
theorem uniform_fixedPhysicalLaw_increment_moment
    (hα : 1/2 < α) (hα' : α < 1) (hκ : 0 ≤ κ) (hv : ∀ i, 0 ≤ v i)
    (L : ∀ n, FractionalCoupledSmoothLaw T α n κ σ v β)
    {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B)
    (j : ℕ) (hj : 1 ≤ j) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ n (s t : CanonicalPathTime T),
      (∫⁻ p : CanonicalPath T (CoupledPhysicalState ι), edist (p s) (p t)^((2*(2^j:ℕ):ℕ):ℝ)
        ∂((L n).fixedPhysicalLaw hB hβ hβB : Measure _)) ≤
      C*edist s t^((2*α-1)*((2^j:ℕ):ℝ)) := by
  let m : ℕ := 2^j
  let q : ℕ := 2*m
  let e : ℝ := (2*α-1)*(m:ℝ)
  have hm : 2 ≤ m := by
    dsimp [m]
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hj
  have he : 0 ≤ e := mul_nonneg (by linarith) (Nat.cast_nonneg _)
  obtain ⟨Cₘ, hCₘ, hVm⟩ := uniform_fractionalSmooth_variance_dyadic_powers hα hα' hκ hv L hB hβ hβB j
  obtain ⟨C₂ₘ, hC₂ₘ, hV₂ₘ⟩ := uniform_fractionalSmooth_variance_dyadic_powers hα hα' hκ hv L hB hβ hβB (j+1)
  have hV₂ (n : ℕ) (i : Option ι) :
      ∀ u ≤ T, (∫⁻ p, ENNReal.ofReal (max ((L n).variance i u p) 0)^q ∂((L n).law : Measure _)) ≤ C₂ₘ := by
    simpa only [q, m, pow_succ, mul_comm (2^j : ℕ)] using hV₂ₘ n i
  let dn := (2/(Real.Gamma α*α))
  let fn := σ^2*(2/(Real.Gamma α^2*(2*α-1)))
  let D := (2:ℝ≥0∞)^q*(ENNReal.ofReal B^q+‖κ‖ₑ^q*C₂ₘ)
  let CV := (2:ℝ≥0∞)^q*((2:ℝ≥0∞)^q*
    (ENNReal.ofReal dn^q*ENNReal.ofReal ((T:ℝ)^(m:ℝ))*D*2) +
    (2:ℝ≥0∞)^q*(boundedMartingaleEvenPowerConstant m * ENNReal.ofReal fn^m*Cₘ*2))
  let CM := boundedMartingaleEvenPowerConstant m * ENNReal.ofReal (σ^2)^m *
    ENNReal.ofReal ((T:ℝ)^((2-2*α)*(m:ℝ))) * Cₘ
  let C := (Fintype.card (Option ι) : ℝ≥0∞)*(CV+CM)
  have hBd := boundedMartingaleEvenPowerConstant_ne_top m hm
  have hC : C ≠ ⊤ := by
    dsimp [C, CV, CM, D]
    finiteness
  refine ⟨C, hC, ?_⟩
  have hOrder (n : ℕ) (s t : CanonicalPathTime T) (hst : s.val ≤ t.val) :
      (∫⁻ p : CanonicalPath T (CoupledPhysicalState ι), edist (p s) (p t)^(q:ℝ)
        ∂((L n).fixedPhysicalLaw hB hβ hβB : Measure _)) ≤ C*edist s t^e := by
    let μ := ((L n).fixedPhysicalLaw hB hβ hβB : Measure (CanonicalPath T (CoupledPhysicalState ι)))
    let ψ := (L n).fixedPhysicalPath hB hβ hβB
    have hψ := (L n).measurable_fixedPhysicalPath hB hβ hβB
    have hPair (i : Option ι) (u : ℝ≥0) (p : CanonicalPath T (FractionalCoupledSmoothState ι n)) :
        canonicalPhysicalVariance T i u (ψ p) = (L n).variance i u p ∧
        canonicalPhysicalResidual T i u (ψ p) = (L n).residual i u p := by
      unfold canonicalPhysicalVariance canonicalPhysicalResidual ψ
      rw [(L n).canonicalPathEval_fixedPhysicalPath hB hβ hβB]
      exact ⟨rfl, rfl⟩
    have hE : edist s t^e = ENNReal.ofReal (((t.val:ℝ)-(s.val:ℝ))^e) := by
      rw [edist_canonicalPathTime_eq_ofReal hst, ENNReal.ofReal_rpow_of_nonneg
        (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst)) he]
    have hV (i : Option ι) :
        (∫⁻ p, ‖canonicalPhysicalVariance T i t p-canonicalPhysicalVariance T i s p‖ₑ^q ∂μ) ≤
          CV*edist s t^e := by
      let F (p : CanonicalPath T (CoupledPhysicalState ι)) :=
        ‖canonicalPhysicalVariance T i t p-canonicalPhysicalVariance T i s p‖ₑ^q
      have hc (u : ℝ≥0) : Continuous (canonicalPhysicalVariance T i u) :=
        ((continuous_apply i).comp continuous_fst).comp (continuous_canonicalPathEval T u)
      have hFm : Measurable F := (((hc t).sub (hc s)).measurable.enorm).pow_const _
      change (∫⁻ p, F p ∂Measure.map ψ ((L n).law : Measure _)) ≤ _
      rw [lintegral_map hFm hψ]
      have hEq (p : CanonicalPath T (FractionalCoupledSmoothState ι n)) :
          F (ψ p) = ‖(L n).variance i t p-(L n).variance i s p‖ₑ^q := by
        dsimp only [F]
        rw [(hPair i t p).1, (hPair i s p).1]
      rw [lintegral_congr hEq]
      rw [hE]
      exact (L n).variance_increment_even_moment_le hα hα' i hB hβ hβB hst t.property.2 m hm
        (hVm n i) (hV₂ n i)
    have hM (i : Option ι) :
        (∫⁻ p, ‖canonicalPhysicalResidual T i t p-canonicalPhysicalResidual T i s p‖ₑ^q ∂μ) ≤
          CM*edist s t^e := by
      let F (p : CanonicalPath T (CoupledPhysicalState ι)) :=
        ‖canonicalPhysicalResidual T i t p-canonicalPhysicalResidual T i s p‖ₑ^q
      have hc (u : ℝ≥0) : Continuous (canonicalPhysicalResidual T i u) :=
        ((continuous_apply i).comp continuous_snd).comp (continuous_canonicalPathEval T u)
      have hFm : Measurable F := (((hc t).sub (hc s)).measurable.enorm).pow_const _
      change (∫⁻ p, F p ∂Measure.map ψ ((L n).law : Measure _)) ≤ _
      rw [lintegral_map hFm hψ]
      have hEq (p : CanonicalPath T (FractionalCoupledSmoothState ι n)) :
          F (ψ p) = ‖(L n).residual i t p-(L n).residual i s p‖ₑ^q := by
        dsimp only [F]
        rw [(hPair i t p).2, (hPair i s p).2]
      rw [lintegral_congr hEq]
      rw [hE]
      exact (L n).residual_increment_even_moment_le hα hα' i hB hβ hβB hst t.property.2 m hm (hVm n i)
    have hEq : (∫⁻ p : CanonicalPath T (CoupledPhysicalState ι), edist (p s) (p t)^(q:ℝ) ∂μ) =
        ∫⁻ p : CanonicalPath T (CoupledPhysicalState ι), edist (p s) (p t)^q ∂μ :=
      lintegral_congr fun p => ENNReal.rpow_natCast _ q
    change (∫⁻ p : CanonicalPath T (CoupledPhysicalState ι), edist (p s) (p t)^(q:ℝ) ∂μ) ≤ _
    rw [hEq]
    exact (canonicalPhysical_lintegral_edist_pow_le_of_rows s t q hV hM).trans_eq (by
      dsimp [C]
      rw [← add_mul, ← mul_assoc])
  intro n s t
  rcases le_total s.val t.val with hst | hts
  · exact hOrder n s t hst
  · simpa only [edist_comm] using hOrder n t s hts

#print axioms RoughHeston.uniform_fixedPhysicalLaw_increment_moment

end RoughHeston
