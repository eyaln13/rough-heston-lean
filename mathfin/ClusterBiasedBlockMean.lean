import ClusterBurstScaling

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston.GirsanovPort

/-- Passing from the old-law block supremum to its terminal mass tilt.
The mass scale cancels before the first moment is taken. -/
theorem sizeBiased_block_mean {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z W : Ω → ℝ} {ε s a Kz Kw : ℝ} {m : ℕ}
    (hm : 0<m) (hε : 0<ε) (hs : 0<s) (ha : 0<a)
    (hZ : Measurable Z) (hZ₀ : ∀ᵐ ω ∂P, 0≤Z ω) (hZ₂ : MemLp Z 2 P)
    (hW : Measurable W) (hW₀ : ∀ ω, 0≤W ω)
    (hZi : (∫ ω, Z ω^2 ∂P) ≤ Kz*ε*s)
    (hWi : Integrable (fun ω => W ω^(2*m)) P)
    (hWE : (∫ ω, W ω^(2*m) ∂P) ≤ Kw*(ε/s)*a^(2*m))
    (hQ : IsProbabilityMeasure (sizeBiasedLaw P Z ε)) :
    Integrable W (sizeBiasedLaw P Z ε) ∧ (∫ ω, W ω ∂sizeBiasedLaw P Z ε) ≤
      a*(1+(Kz+Kw)/2) := by
  let Q := sizeBiasedLaw P Z ε
  let g (ω : Ω) := (W ω/a)^m
  have hg : Measurable g := (hW.div_const a).pow_const m
  have hg₀ (ω : Ω) : 0≤g ω := pow_nonneg (div_nonneg (hW₀ ω) ha.le) _
  have he (ω : Ω) : g ω^2=W ω^(2*m)/a^(2*m) := by dsimp [g]; rw [← pow_mul, Nat.mul_comm m 2, div_pow]
  have hgi : Integrable (fun ω => g ω^2) P := by simpa only [he] using hWi.div_const (a^(2*m))
  have hg₂ : MemLp g 2 P := (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mpr hgi
  have hgi' : (∫ ω,g ω^2 ∂P)≤Kw*(ε/s) := by
    simp_rw [he]; rw [integral_div]; exact (div_le_iff₀ (pow_pos ha _)).mpr hWE
  have hprod := hZ₂.integrable_mul hg₂
  have hgQ : Integrable g Q := by
    apply (integrable_withDensity_iff_integrable_smul' (hZ.div_const ε).ennreal_ofReal
      (ae_of_all P fun _ => ENNReal.ofReal_lt_top)).2
    apply (hprod.div_const ε).congr
    filter_upwards [hZ₀] with ω h
    rw [ENNReal.toReal_ofReal (div_nonneg h hε.le),smul_eq_mul, Pi.mul_apply]; ring
  have hzs := hZ₂.integrable_sq
  have hu : (∫ ω, Z ω*g ω ∂P) ≤ ((∫ ω,Z ω^2 ∂P)/s+s*(∫ ω,g ω^2 ∂P))/2 := by
    have h := integral_mono_ae hprod (((hzs.div_const s).add (hgi.const_mul s)).div_const 2)
      (ae_of_all P (fun ω => (show Z ω*g ω ≤ (Z ω^2/s+s*g ω^2)/2 by
        field_simp [hs.ne']; nlinarith only [sq_nonneg (Z ω-s*g ω)])))
    change (∫ ω, Z ω*g ω ∂P) ≤ (∫ ω, (Z ω^2/s+s*g ω^2)/2 ∂P) at h
    rwa [integral_div,integral_add (hzs.div_const s) (hgi.const_mul s),integral_div,integral_const_mul] at h
  have hEg : (∫ ω,g ω ∂Q)≤(Kz+Kw)/2 := by
    rw [integral_sizeBiasedLaw_eq hε hZ hZ₀]
    apply (div_le_iff₀ hε).mpr
    apply hu.trans
    have h1 := (div_le_iff₀ hs).mpr hZi
    have h2 := mul_le_mul_of_nonneg_left hgi' hs.le
    have h3 : s*(Kw*(ε/s))=Kw*ε := by field_simp
    rw [h3] at h2
    linarith
  have hdom (ω : Ω) : W ω≤a*(1+g ω) := by
    have h : W ω/a≤1+g ω := by
      rcases le_total (W ω/a) 1 with h|h
      · linarith [hg₀ ω]
      · exact (le_self_pow₀ h hm.ne').trans (by dsimp [g]; linarith)
    exact (div_le_iff₀ ha).mp h |>.trans_eq (mul_comm _ _)
  have hG : Integrable (fun ω => a*(1+g ω)) Q := ((integrable_const (1:ℝ)).add hgQ).const_mul a
  have hi : Integrable W Q := hG.mono' hW.aestronglyMeasurable (ae_of_all Q
    (fun ω => (Real.norm_of_nonneg (hW₀ ω)).le.trans (hdom ω)))
  refine ⟨hi,(integral_mono_ae hi hG (ae_of_all Q hdom)).trans ?_⟩
  rw [integral_const_mul,integral_add (integrable_const _) hgQ,integral_const]
  have : IsProbabilityMeasure Q := hQ
  rw [probReal_univ,one_smul]
  gcongr

#print axioms sizeBiased_block_mean

end RoughHeston.GirsanovPort
