import FractionalPulseBias
import UniformPulseTailConstants

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace RoughHeston

/-- Both denominator lower tails hold for the genuine fractional pulse
under terminal size bias. The common coefficient is chosen before all
pulse masses, observation ages, filtrations, and probability laws. -/
theorem uniform_actual_fractional_pulse_mass_tails
    {Ω : Type*} {m : MeasurableSpace Ω} {α κ a C₀ : ℝ} {H : ℝ≥0}
    (hα : 1/2<α) (hα' : α<1) (hκ : 0≤κ) (ha : 0<a) (hH : 0<H) (hC₀ : 0<C₀) :
    ∃ D : ℝ, 0<D ∧ ∀ (μ : Measure Ω) [IsProbabilityMeasure μ]
      (𝒢 : Filtration ℝ≥0 m) (r : ℝ≥0) (ε : ℝ) (M U C : ℝ≥0 → Ω → ℝ),
      let d := ε^(1/α)
      let s₀ := d/4
      let J := clusterAccumulatedVariance (fun s => U s.toNNReal)
      let Z := fractionalPulseMass ε M
      let Q := @sizeBiasedLaw Ω m μ (Z r) ε
      0<ε → r≤H → s₀≤(r:ℝ) →
      FractionalPulseProcess μ 𝒢 H α κ a ε d M U C →
      (∫ ω,(Z s₀.toNNReal ω)^2 ∂μ)≤C₀*ε^2 →
      (∀ x, 0<x → x≤1 → Q.real {ω | J s₀ ω≤x*s₀^(2*α)}≤D*Real.sqrt x) ∧
      (∀ s : ℝ≥0, 2*d≤(s:ℝ) → s≤r → ∀ x,0<x → x≤1 →
        Q.real {ω | J s ω≤x*(s:ℝ)^(2*α)}≤D*Real.sqrt x) := by
  let _ : MeasurableSpace Ω := m
  have hα₀ : 0<α := by linarith
  have hHr : 0<(H:ℝ) := NNReal.coe_pos.mpr hH
  obtain ⟨De,hDe,hEarly⟩ := uniform_cluster_earlypulse_mass_tail (Ω := Ω) (Ξ := ℝ)
    hα hα' hκ ha hHr hC₀ (by norm_num : (0:ℝ)<1/8)
  obtain ⟨Dp,hDp,hPost⟩ := uniform_cluster_postpulse_mass_tail (Ω := Ω) (Ξ := ℝ)
    hα hα' hκ ha hHr
  let D := max De Dp
  refine ⟨D,hDe.trans_le (le_max_left _ _),?_⟩
  intro μ _ 𝒢 r ε M U C
  dsimp only
  intro hε hr hs₀ hP hZ₂
  let d := ε^(1/α)
  let s₀ : ℝ := d/4
  let J := clusterAccumulatedVariance (fun s => U s.toNNReal)
  let Z := fractionalPulseMass ε M
  let Q := sizeBiasedLaw μ (Z r) ε
  have hd : 0<d := Real.rpow_pos_of_pos hε _
  have hs₀p : 0<s₀ := div_pos hd (by norm_num)
  have hs₀r : s₀.toNNReal≤r := Real.toNNReal_le_iff_le_coe.mpr hs₀
  have hs₀c : (s₀.toNNReal:ℝ)=s₀ := Real.coe_toNNReal s₀ hs₀p.le
  have hJad (s : ℝ≥0) : StronglyMeasurable[𝒢 s] (J s) :=
    fractional_pulse_accumulated_adapted hP.variance_adapted hP.variance_continuous s
  have hJm (s : ℝ≥0) : Measurable (J s) := ((hJad s).mono (𝒢.le s)).measurable
  have hJn (s : ℝ) (ω : Ω) : 0≤J s ω := integral_nonneg fun _ => hP.variance_nonnegative _ _
  have hAt (s : ℝ≥0) (hs : s≤r) (x : ℝ) :
      Q.real {ω | J s ω≤x*(s:ℝ)^(2*α)} =
        (sizeBiasedLaw μ (Z s) ε).real {ω | J s ω≤x*(s:ℝ)^(2*α)} :=
    fractional_pulse_bias_agrees_on_past hα₀ hα' hκ hε hd hs hr hP
      (measurableSet_le (hJad s).measurable measurable_const)
  refine ⟨?_,?_⟩
  · intro x hx hx₁
    let t := s₀.toNNReal
    let ν := rectangularPulseMeasure ε d s₀
    let : IsFiniteMeasure ν := rectangularPulseMeasure_isFiniteMeasure ε d s₀
    obtain ⟨hZm,hZn,hZi,hZmean,hZLp⟩ := fractional_pulse_mass_data hα₀ hα' hκ hε hd
      (hs₀r.trans hr) hP
    have hJmeas : Measurable (J s₀) := by
      have hJt : Measurable (J (t:ℝ)) := hJm t
      rw [show (t:ℝ)=s₀ from hs₀c] at hJt
      exact hJt
    have hMass : (1/8:ℝ)*s₀^α≤ν.real {v | s₀/2≤s₀-v} := by
      have h := rectangularPulseMeasure_earlypulse_scaled hε hα₀
      change s₀^α/8≤_ at h
      linarith
    have hTransform (q : ℝ) (hq : 0<q) (w : ℝ→ℝ) (hw : Continuous w)
        (he : ∀ s∈Icc 0 s₀, w s=volterraConvolution (fractionalK α)
          (fun u => q+(-κ)*w u+(-a)*(w u)^2) s) :
        (∫ ω,Real.exp (-q*J s₀ ω) ∂μ)=Real.exp (-(∫ v,w (s₀-v) ∂ν)) := by
      have he' (s : ℝ) (hs : s∈Ioc 0 (t:ℝ)) :
          w s=volterraConvolution (fractionalK α)
            (fun u => q+(0:ℝ)*(fractionalL α u+κ)-κ*w u-a*(w u)^2) s := by
        rw [hs₀c] at hs
        simpa only [zero_mul,add_zero,neg_mul,sub_eq_add_neg] using he s (Ioc_subset_Icc_self hs)
      have hA := fractional_pulse_density_affine_transform hα hα' hκ ha hε hd
        (Real.toNNReal_pos.mpr hs₀p) (hs₀r.trans hr) hq (show 0≤(0:ℝ) from le_rfl) hP hw he'
      rw [rectangularPulseMeasure_integral_eq_convolution hε.le hd]
      calc
        _ = ∫ ω,Real.exp (-(volterraConvolution (fun _ => q) (fun u => U u.toNNReal ω) s₀)) ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          change Real.exp (-q*J s₀ ω)=Real.exp (-(volterraConvolution (fun _ => q) (fun u => U u.toNNReal ω) s₀))
          unfold J clusterAccumulatedVariance volterraConvolution
          rw [integral_const_mul,neg_mul]
        _ = _ := by simpa only [zero_mul,add_zero,hs₀c] using hA
    have hTail := hEarly μ ν (age := fun v => s₀-v) hs₀p
      (hs₀.trans (NNReal.coe_le_coe.mpr hr)) hε hJmeas hZm (ae_of_all _ (hJn s₀)) hZn hZi
      hZmean hZLp hZ₂ (measurable_const.sub measurable_id)
      (rectangularPulseMeasure_ae_age hs₀p.le) hMass hTransform x hx hx₁
    have he := hAt t hs₀r x
    rw [show ((t:ℝ))=s₀ from hs₀c] at he
    change Q.real {ω | J s₀ ω≤x*s₀^(2*α)}≤D*Real.sqrt x
    rw [he]
    exact hTail.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
  · intro s hds hsr x hx hx₁
    have hsr₀ : 0<(s:ℝ) := (show 0<2*d by positivity).trans_le hds
    have hs : s≤H := hsr.trans hr
    let ν := rectangularPulseMeasure ε d (s:ℝ)
    let : IsFiniteMeasure ν := rectangularPulseMeasure_isFiniteMeasure ε d (s:ℝ)
    obtain ⟨hZm,hZn,hZi,hZmean,_⟩ := fractional_pulse_mass_data hα₀ hα' hκ hε hd hs hP
    obtain ⟨hνmass,hνage⟩ := rectangularPulseMeasure_postpulse hε.le hd hds
    have hTransform (q : ℝ) (hq : 0<q) (l : ℝ) (hl : l∈Icc (0:ℝ) 1) (w : ℝ→ℝ)
        (hw : Continuous w)
        (he : ∀ t∈Icc 0 (s:ℝ), w t=l+volterraConvolution (fractionalK α)
          (fun u => q+κ*l-κ*w u-a*(w u)^2) t) :
        (∫ ω,Real.exp (-q*J s ω-l*Z s ω) ∂μ)=Real.exp (-(∫ v,w ((s:ℝ)-v) ∂ν)) := by
      have he' (t : ℝ) (ht : t∈Ioc 0 (s:ℝ)) := density_riccati_affine_convolution hα₀ hα' ht hw he
      have hA := fractional_pulse_density_affine_transform hα hα' hκ ha hε hd
        (NNReal.coe_pos.mp hsr₀) hs hq hl.1 hP hw he'
      change (∫ ω,Real.exp (-q*J s ω-l*Z s ω) ∂μ)=
        Real.exp (-(∫ v,w ((s:ℝ)-v) ∂rectangularPulseMeasure ε d (s:ℝ)))
      rw [rectangularPulseMeasure_integral_eq_convolution hε.le hd]
      refine (integral_congr_ae ?_).trans hA
      filter_upwards [fractional_pulse_postpulse_affine_payoff (q := q) (l := l)
        hα₀ hα' hε.le hd (show d≤(s:ℝ) by linarith) hs hP] with ω hω
      rw [hω]
      congr 1
      ring
    have hTail := hPost μ ν (age := fun v => (s:ℝ)-v) hsr₀ (NNReal.coe_le_coe.mpr hs) hε
      (hJm s) hZm (ae_of_all _ (hJn s)) hZn hZi hZmean
      (measurable_const.sub measurable_id) hνage hνmass hTransform x hx hx₁
    change Q.real {ω | J s ω≤x*(s:ℝ)^(2*α)}≤D*Real.sqrt x
    rw [hAt s hsr x]
    exact hTail.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _))

#print axioms uniform_actual_fractional_pulse_mass_tails

end RoughHeston
