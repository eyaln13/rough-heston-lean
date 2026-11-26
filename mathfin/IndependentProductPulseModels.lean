import CanonicalUsualModels
import IndependentCommonDriver

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Interval

namespace RoughHeston

open MathFin.ItoLocalMartingale (nullAugmentation)

variable {Ω Γ : Type*} [mΩ : MeasurableSpace Ω] [mΓ : MeasurableSpace Γ]
  {P : Measure Ω} [IsProbabilityMeasure P] (ν : Measure Γ) [IsProbabilityMeasure ν]
  {F : Filtration ℝ≥0 mΩ} (G : Filtration ℝ≥0 mΓ)
  {H : ℝ≥0} {α κ a b v₀ ε d : ℝ} {M V C : ℝ≥0 → Ω → ℝ}

/-- The law on the physical product is the one on which the aggregate
Brownian and its focal bracket were selected. -/
theorem HestonBoundaryProcess.on_independent_product
    (h : HestonBoundaryProcess P F H α κ a b v₀ M V C) :
    let lift (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (z : Ω×Γ) := X t z.1
    HestonBoundaryProcess (P.prod ν) (nullAugmentation (prodFiltration F G) (P.prod ν)) H
      α κ a b v₀ (lift M) (lift V) (lift C) := by
  let fstP := measurePreserving_fst (μ:=P) (ν:=ν)
  have aeLift {p : Ω→Prop} (h : ∀ᵐ ω ∂P,p ω) : ∀ᵐ z : Ω×Γ ∂P.prod ν,p z.1 :=
    fstP.quasiMeasurePreserving.ae h
  have liftM {X : ℝ≥0→Ω→ℝ} (hX : Martingale X F P) := martingale_physical_nullAugmentation
    (martingale_prod_fst (G:=G) (ν:=ν) hX)
  have had (t : ℝ≥0) := ((h.variance_adapted t).comp_measurable
    (@measurable_fst Ω Γ (F t) (G t))).mono (show (prodFiltration F G) t ≤
      (nullAugmentation (prodFiltration F G) (P.prod ν)) t from le_sup_left)
  obtain ⟨A,hA,hmean⟩ := h.variance_mean_bound
  obtain ⟨D,hD,hsec⟩ := h.variance_second_bound
  refine ⟨liftM h.martingale,fun t => (h.martingale_memLp t).comp_fst ν,
    fun z => h.martingale_continuous z.1,aeLift h.martingale_zero,had,fun z => h.variance_continuous z.1,
    fun t z => h.variance_nonnegative t z.1,fun z => h.variance_initial_bound z.1,
    aeLift h.variance_initial,fun t ht => fstP.integrable_comp_of_integrable (h.variance_integrable t ht),
    fun t ht => fstP.integrable_comp_of_integrable (h.variance_second_integrable t ht),
    ⟨A,hA,?_⟩,⟨D,hD,?_⟩,liftM h.compensated_square,
    fun t => fstP.integrable_comp_of_integrable (h.compensator_integrable t),
    fun s t ht => aeLift (h.compensator_monotone s t ht),fun t ht => aeLift (h.compensator t ht),
    aeLift h.inverse⟩
  · intro t ht
    rw [integral_fun_fst,probReal_univ,one_smul]
    exact hmean t ht
  · intro t ht
    change (∫ z : Ω×Γ,(fun ω => V t ω^2) z.1 ∂P.prod ν)≤D
    rw [integral_fun_fst (μ:=P) (ν:=ν) (fun ω => V t ω^2),probReal_univ,one_smul]
    exact hsec t ht

/-- The first coordinate retains its finite-age fractional pulse law
when an independent noise coordinate is added on the physical clock. -/
theorem FractionalPulseProcess.on_independent_product {b₀ : ℝ≥0}
    (h : FractionalPulseProcess P (pulseAgeFiltration F b₀) H α κ a ε d M V C) :
    let lift (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (z : Ω×Γ) := X t z.1
    FractionalPulseProcess (P.prod ν)
      (pulseAgeFiltration (nullAugmentation (prodFiltration F G) (P.prod ν)) b₀) H
      α κ a ε d (lift M) (lift V) (lift C) := by
  let fstP := measurePreserving_fst (μ:=P) (ν:=ν)
  have aeLift {p : Ω→Prop} (h : ∀ᵐ ω ∂P,p ω) : ∀ᵐ z : Ω×Γ ∂P.prod ν,p z.1 :=
    fstP.quasiMeasurePreserving.ae h
  have liftM {X : ℝ≥0→Ω→ℝ} (hX : Martingale X (pulseAgeFiltration F b₀) P) :=
    martingale_physical_nullAugmentation (martingale_prod_fst (G:=pulseAgeFiltration G b₀) (ν:=ν) hX)
  have he : pulseAgeFiltration (nullAugmentation (prodFiltration F G) (P.prod ν)) b₀ =
      nullAugmentation (prodFiltration (pulseAgeFiltration F b₀) (pulseAgeFiltration G b₀)) (P.prod ν) := by
    ext t : 1
    rfl
  dsimp only
  rw [he]
  have had (t : ℝ≥0) := ((h.variance_adapted t).comp_measurable
    (@measurable_fst Ω Γ ((pulseAgeFiltration F b₀) t) ((pulseAgeFiltration G b₀) t))).mono
      (show (prodFiltration (pulseAgeFiltration F b₀) (pulseAgeFiltration G b₀)) t ≤
        (nullAugmentation (prodFiltration (pulseAgeFiltration F b₀) (pulseAgeFiltration G b₀)) (P.prod ν)) t from le_sup_left)
  exact ⟨liftM h.martingale,fun t => (h.martingale_memLp t).comp_fst ν,fun z => h.martingale_continuous z.1,
    aeLift h.martingale_zero,had,fun z => h.variance_continuous z.1,fun t z => h.variance_nonnegative t z.1,
    fun z => h.variance_zero z.1,liftM h.compensated_square,fun t => fstP.integrable_comp_of_integrable (h.compensator_integrable t),
    fun s t ht => aeLift (h.compensator_monotone s t ht),fun t ht => aeLift (h.compensator t ht),aeLift h.inverse⟩

#print axioms HestonBoundaryProcess.on_independent_product
#print axioms FractionalPulseProcess.on_independent_product

end RoughHeston
