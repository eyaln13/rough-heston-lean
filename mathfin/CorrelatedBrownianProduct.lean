import UsualPhysicalPulsedFocalDriver
import FiniteBrownianFrozenMartingales

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MathFinBridge

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 m} {T : ℝ≥0} {B W : ℝ≥0 → Ω → ℝ}

/-- An adapted version of a finite-horizon Brownian motion has the same
increment laws and independence relative to the stated filtration. -/
theorem BrownianOn.congr_adapted (hB : BrownianOn P F T B)
    (hW : StronglyAdapted F W)
    (hWc : ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) (Icc 0 T))
    (he : ∀ t, B t =ᵐ[P] W t) : BrownianOn P F T W := by
  refine ⟨hW, (he 0).symm.trans hB.zero_at_start, hWc, ?_, ?_⟩
  · intro s t hst ht
    exact (Measure.map_congr ((he t).sub (he s)).symm).trans (hB.normal_increment s t hst ht)
  · intro s t hst ht
    have hi : @IndepFun Ω ℝ Ω m (borel ℝ) (F s) (fun ω => B t ω - B s ω) id P := by
      simpa only [IndepFun_iff_Indep, MeasurableSpace.comap_id] using hB.independent_of_past s t hst ht
    have hd : (fun ω => B t ω - B s ω) =ᵐ[P] (fun ω => W t ω - W s ω) := (he t).sub (he s)
    simpa only [IndepFun_iff_Indep, MeasurableSpace.comap_id] using
      hi.congr hd (EventuallyEq.rfl : (id : Ω → Ω) =ᵐ[P] id)

end MathFinBridge

namespace RoughHeston

open MathFin.ItoLocalMartingale (nullAugmentation)
open MathFinBridge (BrownianOn)

section UnitClock

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 m} {T : ℝ≥0} {B C : ℝ≥0 → Ω → ℝ}

/-- The two orthogonal unit clocks identify the clock of every normalized
linear combination. In particular, each one is Brownian in the common past. -/
theorem orthogonal_unit_clock_brownian_projections [IsProbabilityMeasure P] [F.IsComplete P]
    (hB : Martingale B F P) (hC : Martingale C F P)
    (hBc : ∀ᵐ ω ∂P, Continuous (fun t => B t ω))
    (hCc : ∀ᵐ ω ∂P, Continuous (fun t => C t ω))
    (hB₀ : B 0 =ᵐ[P] 0) (hC₀ : C 0 =ᵐ[P] 0)
    (hBsq : Martingale (fun t ω => B t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) F P)
    (hCsq : Martingale (fun t ω => C t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) F P)
    (hBC : Martingale (fun t => B t * C t) F P)
    (x y : ℝ) (hxy : x ^ 2 + y ^ 2 = 1) :
    BrownianOn P F T (fun t ω => x * B t ω + y * C t ω) ∧
    Martingale (fun t ω => (x * B t ω + y * C t ω) ^ 2 - ((min t T : ℝ≥0) : ℝ)) F P := by
  let W (t : ℝ≥0) (ω : Ω) := x * B t ω + y * C t ω
  have hWm : Martingale W F P := (hB.smul x).add (hC.smul y)
  have hWc : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) :=
    (hBc.and hCc).mono fun ω h => (continuous_const.mul h.1).add (continuous_const.mul h.2)
  have hW₀ : W 0 =ᵐ[P] 0 := by
    filter_upwards [hB₀, hC₀] with ω hb hc
    simp [W, show B 0 ω = 0 from hb, show C 0 ω = 0 from hc]
  have hWs : Martingale (fun t ω => W t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) F P := by
    convert ((hBsq.smul (x ^ 2)).add (hCsq.smul (y ^ 2))).add (hBC.smul (2*x*y)) using 1
    funext t ω
    change (x*B t ω+y*C t ω)^2-((min t T:ℝ≥0):ℝ)=
      x^2*(B t ω^2-((min t T:ℝ≥0):ℝ))+y^2*(C t ω^2-((min t T:ℝ≥0):ℝ))+2*x*y*(B t ω*C t ω)
    nlinarith [congrArg (fun z : ℝ => z * ((min t T : ℝ≥0) : ℝ)) hxy]
  obtain ⟨W', hW', he⟩ := MathFinBridge.brownianOn_modification_of_frozen_compensated_martingales
    (fun E hE => Filtration.IsComplete.measurableSet_of_null (𝓕 := F) hE 0) hWm hWs hWc hW₀
  exact ⟨hW'.congr_adapted hWm.stronglyAdapted (hWc.mono fun _ h => h.continuousOn) he, hWs⟩

end UnitClock

section Product

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℝ≥0 m} {T : ℝ≥0} {B : ℝ≥0 → Ω → ℝ}

local notation "Paths" => (ℝ≥0 → ℝ)
local notation "P" => (μ.prod gaussianLimit)
local notation "Q" => (physicalCompletedMeasure P)
local notation "F" =>
  (physicalUsualFiltration P (nullAugmentation (prodFiltration 𝒢 canonicalAuxiliaryFiltration) P))

/-- The first coordinate of the usual completed independent extension has
exactly the original law. -/
theorem correlated_product_fst_measurePreserving [IsProbabilityMeasure μ] :
    @MeasurePreserving (Ω × Paths) Ω (physicalCompletedSpace P) m Prod.fst Q μ := by
  let : MeasurableSpace (Ω × Paths) := physicalCompletedSpace P
  have hm : @Measurable (Ω × Paths) Ω (physicalCompletedSpace P) m Prod.fst :=
    measurable_fst.mono (physical_ambient_le_completion P) le_rfl
  refine ⟨hm, ?_⟩
  ext A hA
  rw [Measure.map_apply hm hA]
  change P (Prod.fst ⁻¹' A) = μ A
  rw [show Prod.fst ⁻¹' A = A ×ˢ (univ : Set Paths) by ext z; simp, Measure.prod_prod, measure_univ, mul_one]

/-- The independent extension preserves the original Brownian clock, supplies
an orthogonal unit-clock coordinate, and realizes every allowed correlation
with the actual linear combination of the two coordinates. -/
theorem brownianOn_correlated_product [IsProbabilityMeasure μ]
    (hB : BrownianOn μ 𝒢 T B) (ρ : ℝ) (hρ : |ρ| ≤ 1) :
    let X (t : ℝ≥0) (z : Ω × Paths) := B (min t T) z.1
    let C (t : ℝ≥0) (z : Ω × Paths) := brownian (min t T) z.2
    let W (t : ℝ≥0) (z : Ω × Paths) := ρ * X t z + Real.sqrt (1 - ρ ^ 2) * C t z
    BrownianOn Q F T X ∧ BrownianOn Q F T C ∧ BrownianOn Q F T W ∧
    Martingale (fun t z => X t z * W t z - ρ * ((min t T : ℝ≥0) : ℝ)) F Q ∧
    (∀ x y : ℝ, x ^ 2 + y ^ 2 = 1 → BrownianOn Q F T (fun t z => x * X t z + y * C t z)) := by
  intro X C W
  let : MeasurableSpace (Ω × Paths) := physicalCompletedSpace P
  let Bf (t : ℝ≥0) := B (min t T)
  obtain ⟨_, hBm, hBs⟩ := GirsanovPort.finiteBrownianOn_frozen_martingales hB
  have hBc : ∀ᵐ ω ∂μ, Continuous (fun t => Bf t ω) :=
    hB.continuous_paths.mono fun ω h => h.comp_continuous (continuous_id.min continuous_const)
      (fun t => ⟨zero_le, min_le_right t T⟩)
  have hX : Martingale X F Q := martingale_usual_physical_product_fst hBm hBc
  have hPres := correlated_product_fst_measurePreserving (μ := μ)
  have hXc : ∀ᵐ z ∂Q, Continuous (fun t => X t z) :=
    hPres.quasiMeasurePreserving.ae hBc
  have hX₀ : X 0 =ᵐ[Q] 0 := by
    filter_upwards [hPres.quasiMeasurePreserving.ae hB.zero_at_start] with z hz
    change B (min 0 T) z.1 = 0
    rw [min_eq_left (zero_le : 0 ≤ T)]
    exact hz
  have hXs : Martingale (fun t z => X t z ^ 2 - ((min t T : ℝ≥0) : ℝ)) F Q :=
    martingale_usual_physical_product_fst hBs (hBc.mono fun ω h =>
      (h.pow 2).sub (NNReal.continuous_coe.comp (continuous_id.min continuous_const)))
  obtain ⟨hC, _, hC₀, hCc, hCs⟩ := usual_physical_product_auxiliary_driver (μ := μ) 𝒢 T
  have hCs' : Martingale (fun t z => C t z ^ 2 - ((min t T : ℝ≥0) : ℝ)) F Q := by
    simpa only [pow_two] using hCs
  have hCX : Martingale (fun t => X t * C t) F Q := by
    convert usual_physical_product_auxiliary_orthogonal T hBm hBc using 1
    funext t z
    exact mul_comm _ _
  have hPr x y hxy := orthogonal_unit_clock_brownian_projections hX hC hXc (ae_of_all _ hCc)
    hX₀ hC₀ hXs hCs' hCX x y hxy
  have hρsq : 0 ≤ 1 - ρ ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg ρ) hρ 2
    rw [sq_abs, one_pow] at h
    exact sub_nonneg.mpr h
  have hPyth : ρ ^ 2 + Real.sqrt (1 - ρ ^ 2) ^ 2 = 1 := by
    rw [Real.sq_sqrt hρsq]
    ring
  refine ⟨?_, ?_, (hPr ρ _ hPyth).1, ?_, fun x y hxy => (hPr x y hxy).1⟩
  · simpa only [one_mul, zero_mul, add_zero] using (hPr 1 0 (by norm_num)).1
  · simpa only [zero_mul, one_mul, zero_add] using (hPr 0 1 (by norm_num)).1
  · convert (hXs.smul ρ).add (hCX.smul (Real.sqrt (1 - ρ ^ 2))) using 1
    funext t z
    change X t z * (ρ * X t z + Real.sqrt (1 - ρ ^ 2) * C t z) -
        ρ * ((min t T : ℝ≥0) : ℝ) =
      ρ * (X t z ^ 2 - ((min t T : ℝ≥0) : ℝ)) + Real.sqrt (1 - ρ ^ 2) * (X t z * C t z)
    ring

end Product

#print axioms MathFinBridge.BrownianOn.congr_adapted
#print axioms orthogonal_unit_clock_brownian_projections
#print axioms correlated_product_fst_measurePreserving
#print axioms brownianOn_correlated_product

end RoughHeston
