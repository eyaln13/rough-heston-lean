import ExplicitLebesgueAggregateForward
import AggregateCenteredIncrementRate
import CenteredCanonicalTightness

/-! Uniform moments are transferred from the actual Brownian extension
back to the original two-dimensional variance path laws. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston

open GirsanovPort
set_option maxHeartbeats 2200000

variable {T : ℝ≥0} {α κ σ b ε v₀ : ℝ}
local notation "I" => FixedMeshClusterIndex (T:ℝ) b ε
local notation "Ω" => CanonicalPath T (CoupledPhysicalState I)
local notation "Ω'" => Ω × (ℝ≥0 → ℝ)
local notation "Ω₂" => CanonicalPath T (ℝ × ℝ)
local notation "V" => lebesgueMeshInitial (T:ℝ) b ε v₀
local notation "βN" => lebesgueMeshInput (T:ℝ) α b ε
local notation "d" => lebesguePulseDuration α ε
local notation "βR" => explicitPulsedRate (T:ℝ) b ε d

theorem lebesguePulseDuration_pow_eq_mass (hα : 0 < α) (hε : 0 < ε) : d^α = ε := by
  unfold lebesguePulseDuration
  rw [← Real.rpow_mul hε.le, one_div, inv_mul_cancel₀ hα.ne', Real.rpow_one]

noncomputable def lebesgueAggregateDeterministicCap (α T b v₀ : ℝ) :=
  v₀+b*(T^α/(Real.Gamma α*α))+2/(Real.Gamma α*α)

private theorem lebesgueAggregateDeterministicCap_bounds
    (hα : 1/2 < α) (hα' : α < 1) (hb : 0 < b) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hdΔ : d ≤ ε/b) (hv₀ : 0 ≤ v₀) :
    let C := lebesgueAggregateDeterministicCap α T b v₀
    0 ≤ C ∧ ∀ t ∈ Icc (0:ℝ) T,
      v₀+volterraConvolution (hestonKernel α) βR t ≤ C ∧
      v₀+constantImmigrationConvolution α b t ≤ C := by
  intro C
  have h0 : 0 < α := by linarith
  have hΓ : 0 < Real.Gamma α*α := mul_pos (Real.Gamma_pos_of_pos h0) h0
  have hd : 0 < d := Real.rpow_pos_of_pos hε _
  have hd₁ : d ≤ 1 := by
    unfold lebesguePulseDuration
    simpa only [Real.one_rpow] using Real.rpow_le_rpow hε.le hε₁ (show 0 ≤ 1/α by positivity)
  have hB : 0 ≤ b*((T:ℝ)^α/(Real.Gamma α*α)) := by positivity
  have hE : 0 ≤ 2/(Real.Gamma α*α) := by positivity
  refine ⟨add_nonneg (add_nonneg hv₀ hB) hE,?_⟩
  intro t ht
  have hConst : b*(∫ r in (0:ℝ)..t, hestonKernel α r) ≤ b*((T:ℝ)^α/(Real.Gamma α*α)) := by
    rw [hestonKernel_integral h0 ht.1]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (Real.rpow_le_rpow ht.1 ht.2 h0.le) hΓ.le) hb.le
  have h := (explicitPulsed_convolution_difference_bounds h0 hα'.le hε hb hd hdΔ ht).2
  have hRate : (ε/d)*(d^α/(Real.Gamma α*α)) = d^(2*α-1)/(Real.Gamma α*α) := by
    calc
      _ = (d^α/d)*(d^α/(Real.Gamma α*α)) :=
        congrArg (fun x : ℝ => (x/d)*(d^α/(Real.Gamma α*α))) (lebesguePulseDuration_pow_eq_mass h0 hε).symm
      _ = _ := heston_scaled_pulse_bound hd
  change volterraConvolution (hestonKernel α) βR t ≤
    b*(∫ r in (0:ℝ)..t,hestonKernel α r)+2*((ε/d)*(d^α/(Real.Gamma α*α))) at h
  rw [hRate] at h
  have hR : d^(2*α-1) ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow hd.le hd₁ (show 0 ≤ 2*α-1 by linarith)
  have hc : 2*(d^(2*α-1)/(Real.Gamma α*α)) ≤ 2/(Real.Gamma α*α) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right ((mul_le_mul_of_nonneg_left hR (show (0:ℝ) ≤ 2 by norm_num)).trans_eq (mul_one _)) hΓ.le
  rw [constantImmigrationConvolution_eq h0 ht.1]
  change _ ≤ v₀+b*((T:ℝ)^α/(Real.Gamma α*α))+2/(Real.Gamma α*α) ∧
    _ ≤ v₀+b*((T:ℝ)^α/(Real.Gamma α*α))+2/(Real.Gamma α*α)
  exact ⟨by linarith only [h,hConst,hc],by linarith only [hConst,hE]⟩

private theorem edist_prod_pow_le_scalar_increments (z w : ℝ × ℝ) (q : ℕ) :
    edist z w^q ≤ ‖w.1-z.1‖ₑ^q+‖w.2-z.2‖ₑ^q := by
  rw [edist_comm, edist_eq_enorm_sub]
  have he : ‖w-z‖ₑ = max ‖w.1-z.1‖ₑ ‖w.2-z.2‖ₑ := by
    rw [← ofReal_norm, Prod.norm_def]
    simp only [Prod.fst_sub, Prod.snd_sub, ENNReal.ofReal_max, ofReal_norm]
  rw [he]
  rcases le_total ‖w.1-z.1‖ₑ ‖w.2-z.2‖ₑ with h | h
  · rw [max_eq_right h]; exact le_add_self
  · rw [max_eq_left h]; exact le_self_add

/-- Uniform fourth moments and the centered Kolmogorov estimate on the
actual projected pair law, with constants independent of its pulse mesh. -/
theorem lebesguePulse_pairLaw_fourth_and_centered_increment
    (L : FractionalFixedMeshLaw T α κ σ V βN) (hT : 0 < T) (hα : 1/2 < α) (hα' : α < 1)
    (hκ : 0 ≤ κ) (hσ : 0 ≤ σ) (hb : 0 < b) (hε : 0 < ε) (hε₁ : ε ≤ 1) (hdΔ : d ≤ ε/b)
    (hv₀ : 0 ≤ v₀) (n : ℕ) :
    let C := lebesgueAggregateDeterministicCap α T b v₀
    let center := explicitPulsedCanonicalCenter T (show 0 < α by linarith) hε hb (Real.rpow_pos_of_pos hε (1/α))
    let P₂ := L.pairLaw
    let Q := P₂.map (fun p => p-center)
    (∀ t ≤ T,
      (∫⁻ p, ‖canonicalFirstVariance (canonicalPathEval T t p)‖ₑ^4 ∂(P₂ : Measure Ω₂)) ≤
        ENNReal.ofReal (fractionalAggregateMomentCap σ α T C 2) ∧
      (∫⁻ p, ‖canonicalSecondVariance (canonicalPathEval T t p)‖ₑ^4 ∂(P₂ : Measure Ω₂)) ≤
        ENNReal.ofReal (fractionalAggregateMomentCap σ α T C 2)) ∧
    (∀ s t : CanonicalPathTime T,
      (∫⁻ p : Ω₂, edist (p s) (p t)^((2*2^n:ℕ):ℝ) ∂(Q : Measure Ω₂)) ≤
        (2*fractionalCenteredIncrementCap σ α κ T C n)*edist s t^((2*α-1)*(2^n:ℕ))) := by
  intro C center P₂ Q
  let P := (L.law : Measure Ω).prod gaussianLimit
  let ψ (z : Ω') := canonicalAggregatePair z.1
  have hψ : Measurable ψ := continuous_canonicalAggregatePair.measurable.comp measurable_fst
  have hMap : Measure.map ψ P = (P₂ : Measure Ω₂) := by
    change Measure.map (canonicalAggregatePair ∘ (Prod.fst : Ω' → Ω)) P =
      Measure.map canonicalAggregatePair (L.law : Measure Ω)
    rw [← Measure.map_map continuous_canonicalAggregatePair.measurable measurable_fst,
      (measurePreserving_fst (μ := (L.law : Measure Ω)) (ν := gaussianLimit)).map_eq]
  obtain ⟨B, hB₂, hbB, hNull, hBm, hClock, ⟨X⟩, ⟨Y⟩⟩ :=
    explicitLebesguePulseLaw_aggregate_forward L hT hα hα' hσ hb hε
  obtain ⟨hC,hD⟩ := lebesgueAggregateDeterministicCap_bounds hα hα' hb hε hε₁ hdΔ hv₀ (T := T)
  have hMomX (j : ℕ) := aggregateVariance_dyadic_moment_le hα hα'.le hκ hbB hNull hB₂ hBm hClock
    X.predictable X.nonnegative X.integrable X.meanLe X.continuous_pathLp.stronglyMeasurable
    X.continuous_pathLp.continuousOn X.rep hC (fun t ht => (hD t ht).1) X.forward j
  have hMomY (j : ℕ) := aggregateVariance_dyadic_moment_le hα hα'.le hκ hbB hNull hB₂ hBm hClock
    Y.predictable Y.nonnegative Y.integrable Y.meanLe Y.continuous_pathLp.stronglyMeasurable
    Y.continuous_pathLp.continuousOn Y.rep hC (fun t ht => (hD t ht).2) Y.forward j
  have hFourth (f : C(ℝ × ℝ, ℝ)) (h₀ : ∀ x, 0 ≤ f x) (t : ℝ≥0)
      (hm : Integrable (fun z : Ω' => (f (canonicalPathEval T t (ψ z)))^4) P)
      (h : (∫ z : Ω', (f (canonicalPathEval T t (ψ z)))^4 ∂P) ≤ fractionalAggregateMomentCap σ α T C 2) :
      (∫⁻ p, ‖f (canonicalPathEval T t p)‖ₑ^4 ∂(P₂ : Measure Ω₂)) ≤
        ENNReal.ofReal (fractionalAggregateMomentCap σ α T C 2) := by
    let f₄ (p : Ω₂) := ‖f (canonicalPathEval T t p)‖ₑ^4
    have hfm : Measurable f₄ := ((f.continuous.comp (continuous_canonicalPathEval T t)).measurable.enorm).pow_const _
    change ∫⁻ p, f₄ p ∂(P₂ : Measure Ω₂) ≤ _
    rw [← hMap,lintegral_map hfm hψ]
    have he : (∫⁻ z, f₄ (ψ z) ∂P) = ∫⁻ z : Ω', ENNReal.ofReal ((f (canonicalPathEval T t (ψ z)))^4) ∂P := by
      apply lintegral_congr
      intro z
      simp only [f₄, ← ofReal_norm, Real.norm_of_nonneg (h₀ _), ENNReal.ofReal_pow (h₀ _)]
    rw [he, ← ofReal_integral_eq_lintegral_ofReal hm (ae_of_all _ fun _ => pow_nonneg (h₀ _) _)]
    exact ENNReal.ofReal_le_ofReal h
  constructor
  · intro t ht
    obtain ⟨hXi,hX⟩ := hMomX 2 t ht
    obtain ⟨hYi,hY⟩ := hMomY 2 t ht
    exact ⟨hFourth canonicalFirstVariance (fun _ => le_max_left _ _) t hXi hX,
      hFourth canonicalSecondVariance (fun _ => le_max_left _ _) t hYi hY⟩
  · have hN : ∀ᵐ z : Ω' ∂P, z.1 ∈ canonicalPhysicalNonnegative (ι := I) T :=
      (measurePreserving_fst (μ := (L.law : Measure Ω)) (ν := gaussianLimit)).quasiMeasurePreserving.ae L.nonnegative
    let ψc (z : Ω') := ψ z-center
    have hψc : Measurable ψc := hψ.sub measurable_const
    have hQ : Measure.map ψc P = (Q : Measure Ω₂) := by
      have hsub : Measurable (fun p : Ω₂ => p-center) := (continuous_id.sub continuous_const).measurable
      change Measure.map ((fun p : Ω₂ => p-center) ∘ ψ) P = Measure.map (fun p => p-center) (P₂ : Measure Ω₂)
      rw [← Measure.map_map hsub hψ, hMap]
    let q : ℕ := 2*2^n
    let e := (2*α-1)*((2^n:ℕ):ℝ)
    have he : 0 ≤ e := mul_nonneg (by linarith) (Nat.cast_nonneg _)
    let H := fractionalCenteredIncrementCap σ α κ T C n
    have hOrder (s t : CanonicalPathTime T) (hst : s.val ≤ t.val) :
        (∫⁻ p : Ω₂, edist (p s) (p t)^(q:ℝ) ∂(Q : Measure Ω₂)) ≤ 2*H*edist s t^e := by
      let fQ (p : Ω₂) := edist (p s) (p t)^(q:ℝ)
      have hfQ : Measurable fQ := (((continuous_eval_const s).edist (continuous_eval_const t)).measurable).pow_const _
      change (∫⁻ p, fQ p ∂(Q : Measure Ω₂)) ≤ _
      rw [← hQ, lintegral_map hfQ hψc]
      have hx := aggregate_centered_increment_lintegral_le hα hα'.le hκ hbB hNull hB₂ hBm hClock X
        hC (fun u hu => (hD u hu).1) n s.val.coe_nonneg (NNReal.coe_le_coe.mpr hst) (NNReal.coe_le_coe.mpr t.property.2)
      have hy := aggregate_centered_increment_lintegral_le hα hα'.le hκ hbB hNull hB₂ hBm hClock Y
        hC (fun u hu => (hD u hu).2) n s.val.coe_nonneg (NNReal.coe_le_coe.mpr hst) (NNReal.coe_le_coe.mpr t.property.2)
      let W₁ (z : Ω') := ((ψc z t).1-(ψc z s).1)
      let W₂ (z : Ω') := ((ψc z t).2-(ψc z s).2)
      have hEval (u : CanonicalPathTime T) : canonicalEvalTime T u = u := Subtype.ext (min_eq_left u.property.2)
      have hc₁ (u : CanonicalPathTime T) :
          (center u).1 = volterraConvolution (hestonKernel α) βR (u.val:ℝ) := rfl
      have hc₂ (u : CanonicalPathTime T) : (center u).2 = constantImmigrationConvolution α b (u.val:ℝ) := rfl
      have h1 : W₁ =ᵐ[P] fun z =>
          (FractionalFixedMeshLaw.liftedAggregateVariance (ι := I) (T := T) canonicalFirstVariance t z -
            (v₀+volterraConvolution (hestonKernel α) βR (t.val:ℝ))) -
          (FractionalFixedMeshLaw.liftedAggregateVariance (ι := I) (T := T) canonicalFirstVariance s z -
            (v₀+volterraConvolution (hestonKernel α) βR (s.val:ℝ))) := by
        filter_upwards [hN] with z hz
        have hNt := canonicalAggregatePair_nonnegative z.1 hz t.val t.property.2
        have hNs := canonicalAggregatePair_nonnegative z.1 hz s.val s.property.2
        simp only [canonicalPathEval,hEval] at hNt hNs
        change ((ψ z t).1-(center t).1)-((ψ z s).1-(center s).1) = _
        rw [hc₁ t,hc₁ s]
        simp only [FractionalFixedMeshLaw.liftedAggregateVariance,canonicalFirstVariance,ContinuousMap.coe_mk,
          canonicalPathEval, hEval, ψ, max_eq_right hNt.1,max_eq_right hNs.1]
        ring
      have h2 : W₂ =ᵐ[P] fun z =>
          (FractionalFixedMeshLaw.liftedAggregateVariance (ι := I) (T := T) canonicalSecondVariance t z -
            (v₀+constantImmigrationConvolution α b (t.val:ℝ))) -
          (FractionalFixedMeshLaw.liftedAggregateVariance (ι := I) (T := T) canonicalSecondVariance s z -
            (v₀+constantImmigrationConvolution α b (s.val:ℝ))) := by
        filter_upwards [hN] with z hz
        have hNt := canonicalAggregatePair_nonnegative z.1 hz t.val t.property.2
        have hNs := canonicalAggregatePair_nonnegative z.1 hz s.val s.property.2
        simp only [canonicalPathEval,hEval] at hNt hNs
        change ((ψ z t).2-(center t).2)-((ψ z s).2-(center s).2) = _
        rw [hc₂ t,hc₂ s]
        simp only [FractionalFixedMeshLaw.liftedAggregateVariance,canonicalSecondVariance,ContinuousMap.coe_mk,
          canonicalPathEval, hEval, ψ, max_eq_right hNt.2,max_eq_right hNs.2]
        ring
      have h₁ : (∫⁻ z, ‖W₁ z‖ₑ^q ∂P) ≤ H*edist s t^e := by
        have heq := lintegral_congr_ae (h1.mono fun _ h => congrArg (fun x : ℝ => ‖x‖ₑ^q) h)
        rw [heq,edist_canonicalPathTime_eq_ofReal hst, ENNReal.ofReal_rpow_of_nonneg
          (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst)) he]
        simpa only [Real.toNNReal_coe] using hx
      have h₂ : (∫⁻ z, ‖W₂ z‖ₑ^q ∂P) ≤ H*edist s t^e := by
        have heq := lintegral_congr_ae (h2.mono fun _ h => congrArg (fun x : ℝ => ‖x‖ₑ^q) h)
        rw [heq,edist_canonicalPathTime_eq_ofReal hst, ENNReal.ofReal_rpow_of_nonneg
          (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst)) he]
        simpa only [Real.toNNReal_coe] using hy
      have hP := lintegral_mono (μ := P) (fun z => edist_prod_pow_le_scalar_increments (ψc z s) (ψc z t) q)
      change _ ≤ ∫⁻ z, ‖W₁ z‖ₑ^q+‖W₂ z‖ₑ^q ∂P at hP
      have hW : Measurable (fun z => ‖W₁ z‖ₑ^q) := (((continuous_eval_const t).measurable.comp hψc).fst.sub
        ((continuous_eval_const s).measurable.comp hψc).fst).enorm.pow_const _
      rw [lintegral_add_left hW] at hP
      have hEq : (∫⁻ z, fQ (ψc z) ∂P) = ∫⁻ z, edist (ψc z s) (ψc z t)^q ∂P :=
        lintegral_congr fun _ => ENNReal.rpow_natCast _ q
      rw [hEq,two_mul, add_mul]
      exact hP.trans (add_le_add h₁ h₂)
    intro s t
    rcases le_total s.val t.val with h | h
    · exact hOrder s t h
    · simpa only [edist_comm] using hOrder t s h

#print axioms RoughHeston.lebesguePulse_pairLaw_fourth_and_centered_increment

end RoughHeston
