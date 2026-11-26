import StochasticFoundation
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Filter Set
open scoped MeasureTheory ProbabilityTheory

namespace RoughHeston

variable {Ω Γ ι : Type*} {mΩ : MeasurableSpace Ω} {mΓ : MeasurableSpace Γ} [Preorder ι]

/-- The filtration with the product of the two past σ-algebras at each time. -/
def prodFiltration (F : Filtration ι mΩ) (G : Filtration ι mΓ) :
    Filtration ι (mΩ.prod mΓ) where
  seq t := (F t).prod (G t)
  mono' := fun _ _ hst => sup_le_sup (MeasurableSpace.comap_mono (F.mono hst))
    (MeasurableSpace.comap_mono (G.mono hst))
  le' := fun t => sup_le_sup (MeasurableSpace.comap_mono (F.le t))
    (MeasurableSpace.comap_mono (G.le t))

variable {μ : Measure Ω} {ν : Measure Γ}

/-- Fubini's theorem on the sections of a measurable subset of the product. -/
private theorem setIntegral_prod_vertical_sections [SFinite μ] [SFinite ν] {A : Set (Ω × Γ)}
    (hA : MeasurableSet A) {f : Ω × Γ → ℝ} (hf : Integrable f (μ.prod ν)) :
    (∫ z in A, f z ∂μ.prod ν) =
      ∫ y, ∫ x in (fun x => (x, y)) ⁻¹' A, f (x, y) ∂μ ∂ν := by
  rw [← integral_indicator hA, integral_prod_symm _ (hf.indicator hA)]
  apply integral_congr_ae
  refine Eventually.of_forall fun y => ?_
  change (∫ x, A.indicator f (x, y) ∂μ) =
    ∫ x in (fun x => (x, y)) ⁻¹' A, f (x, y) ∂μ
  rw [← integral_indicator (measurable_prodMk_right hA)]
  exact integral_congr_ae (Eventually.of_forall fun x =>
    (Set.indicator_comp_right (fun x : Ω => (x, y))).symm)

private theorem setIntegral_prod_horizontal_sections [SFinite μ] [SFinite ν] {A : Set (Ω × Γ)}
    (hA : MeasurableSet A) {f : Ω × Γ → ℝ} (hf : Integrable f (μ.prod ν)) :
    (∫ z in A, f z ∂μ.prod ν) =
      ∫ x, ∫ y in (fun y => (x, y)) ⁻¹' A, f (x, y) ∂ν ∂μ := by
  rw [← integral_indicator hA, integral_prod _ (hf.indicator hA)]
  apply integral_congr_ae
  refine Eventually.of_forall fun x => ?_
  change (∫ y, A.indicator f (x, y) ∂ν) =
    ∫ y in (fun y => (x, y)) ⁻¹' A, f (x, y) ∂ν
  rw [← integral_indicator (measurable_prodMk_left hA)]
  exact integral_congr_ae (Eventually.of_forall fun y =>
    (Set.indicator_comp_right (fun y : Γ => (x, y))).symm)

/-- Pullback along the first projection preserves the martingale property
on a finite product measure, with the product of the supplied filtrations. -/
theorem martingale_prod_fst [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {F : Filtration ι mΩ} {G : Filtration ι mΓ} {X : ι → Ω → ℝ}
    (hX : Martingale X F μ) :
    Martingale (fun (t : ι) (z : Ω × Γ) => X t z.1) (prodFiltration F G) (μ.prod ν) := by
  have hint (t : ι) : Integrable (fun z : Ω × Γ => X t z.1) (μ.prod ν) :=
    (hX.integrable t).comp_fst ν
  refine martingale_of_past_set_integrals (fun t => ?_) hint ?_
  · exact (hX.stronglyAdapted t).comp_measurable (@measurable_fst Ω Γ (F t) (G t))
  · intro s t hst A hA
    have hA' : MeasurableSet A := (prodFiltration F G).le s A hA
    rw [setIntegral_prod_vertical_sections hA' (hint s),
      setIntegral_prod_vertical_sections hA' (hint t)]
    apply integral_congr_ae
    refine Eventually.of_forall fun y => hX.setIntegral_eq hst ?_
    exact (@measurable_prodMk_right Ω Γ (F s) (G s) y) hA

/-- Pullback along the second projection preserves the martingale property. -/
theorem martingale_prod_snd [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {F : Filtration ι mΩ} {G : Filtration ι mΓ} {Y : ι → Γ → ℝ}
    (hY : Martingale Y G ν) :
    Martingale (fun (t : ι) (z : Ω × Γ) => Y t z.2) (prodFiltration F G) (μ.prod ν) := by
  have hint (t : ι) : Integrable (fun z : Ω × Γ => Y t z.2) (μ.prod ν) :=
    (hY.integrable t).comp_snd μ
  refine martingale_of_past_set_integrals (fun t => ?_) hint ?_
  · exact (hY.stronglyAdapted t).comp_measurable (@measurable_snd Ω Γ (F t) (G t))
  · intro s t hst A hA
    have hA' : MeasurableSet A := (prodFiltration F G).le s A hA
    rw [setIntegral_prod_horizontal_sections hA' (hint s),
      setIntegral_prod_horizontal_sections hA' (hint t)]
    apply integral_congr_ae
    refine Eventually.of_forall fun x => hY.setIntegral_eq hst ?_
    exact (@measurable_prodMk_left Ω Γ (F s) (G s) x) hA

/-- The product of martingales on separate coordinates is a martingale
on the product filtration, giving a zero cross-compensator. -/
theorem martingale_prod_mul [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {F : Filtration ι mΩ} {G : Filtration ι mΓ} {X : ι → Ω → ℝ} {Y : ι → Γ → ℝ}
    (hX : Martingale X F μ) (hY : Martingale Y G ν) :
    Martingale (fun (t : ι) (z : Ω × Γ) => X t z.1 * Y t z.2)
      (prodFiltration F G) (μ.prod ν) := by
  have hint (i j : ι) : Integrable (fun z : Ω × Γ => X i z.1 * Y j z.2) (μ.prod ν) :=
    (hX.integrable i).mul_prod (hY.integrable j)
  refine martingale_of_past_set_integrals ?_ (fun t => hint t t) ?_
  · exact (martingale_prod_fst (G := G) (ν := ν) hX).stronglyAdapted.mul
      (martingale_prod_snd (F := F) (μ := μ) hY).stronglyAdapted
  · intro s t hst A hA
    have hA' : MeasurableSet A := (prodFiltration F G).le s A hA
    calc
      (∫ z in A, X s z.1 * Y s z.2 ∂μ.prod ν) =
          ∫ z in A, X t z.1 * Y s z.2 ∂μ.prod ν := by
        rw [setIntegral_prod_vertical_sections hA' (hint s s),
          setIntegral_prod_vertical_sections hA' (hint t s)]
        apply integral_congr_ae
        refine Eventually.of_forall fun y => ?_
        change (∫ x in (fun x => (x, y)) ⁻¹' A, X s x * Y s y ∂μ) =
          ∫ x in (fun x => (x, y)) ⁻¹' A, X t x * Y s y ∂μ
        have hsection := (@measurable_prodMk_right Ω Γ (F s) (G s) y) hA
        rw [integral_mul_const, integral_mul_const, hX.setIntegral_eq hst hsection]
      _ = ∫ z in A, X t z.1 * Y t z.2 ∂μ.prod ν := by
        rw [setIntegral_prod_horizontal_sections hA' (hint t s),
          setIntegral_prod_horizontal_sections hA' (hint t t)]
        apply integral_congr_ae
        refine Eventually.of_forall fun x => ?_
        change (∫ y in (fun y => (x, y)) ⁻¹' A, X t x * Y s y ∂ν) =
          ∫ y in (fun y => (x, y)) ⁻¹' A, X t x * Y t y ∂ν
        have hsection := (@measurable_prodMk_left Ω Γ (F s) (G s) x) hA
        rw [integral_const_mul, integral_const_mul, hY.setIntegral_eq hst hsection]

/-- The probability of separation of two paths is preserved when both
paths are pulled back along the first coordinate of a probability product. -/
theorem measure_separation_prod_fst [IsProbabilityMeasure ν]
    (T : ι) (X Y : ι → Ω → ℝ) :
    (μ.prod ν) {z | ∃ t ≤ T, X t z.1 ≠ Y t z.1} =
      μ {ω | ∃ t ≤ T, X t ω ≠ Y t ω} := by
  let A : Set Ω := {ω | ∃ t ≤ T, X t ω ≠ Y t ω}
  have he : {z : Ω × Γ | ∃ t ≤ T, X t z.1 ≠ Y t z.1} = A ×ˢ (Set.univ : Set Γ) := by
    ext z
    simp [A]
  rw [he, Measure.prod_prod, measure_univ, mul_one]

end RoughHeston

#print axioms RoughHeston.martingale_prod_fst
#print axioms RoughHeston.martingale_prod_snd
#print axioms RoughHeston.martingale_prod_mul
#print axioms RoughHeston.measure_separation_prod_fst
