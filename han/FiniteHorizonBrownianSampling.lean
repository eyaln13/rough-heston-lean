import BrownianSampling
import FiniteHorizonLevy

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace RoughHeston
namespace GirsanovPort

open MathFinBridge (BrownianOn)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 mΩ} {H : ℝ≥0} {X : ℝ≥0 → Ω → ℝ}

private noncomputable def lastTime (I : Finset ℝ≥0) : ℝ≥0 :=
  if h : I.Nonempty then I.max' h else 0

private theorem le_lastTime (I : Finset ℝ≥0) (j : I) : (j : ℝ≥0) ≤ lastTime I := by
  have hI : I.Nonempty := ⟨j, j.property⟩
  simpa only [lastTime, dite_eq_left hI] using I.le_max' j j.property

private noncomputable def insertObservation (I : Finset ℝ≥0) (t : ℝ≥0)
    (y : (I → ℝ) × ℝ) (j : (insert t I : Finset ℝ≥0)) : ℝ :=
  if hj : j.val ∈ I then y.1 ⟨j.val, hj⟩
  else (if h : I.Nonempty then y.1 ⟨I.max' h, I.max'_mem h⟩ else 0) + y.2

private theorem measurable_insertObservation (I : Finset ℝ≥0) (t : ℝ≥0) :
    Measurable (insertObservation I t) := by
  apply Measurable.of_eval
  intro j
  by_cases hj : j.val ∈ I
  · simp only [insertObservation, dite_eq_left hj]
    fun_prop
  · by_cases hI : I.Nonempty
    · simp only [insertObservation, dite_eq_right hj, dite_eq_left hI]
      fun_prop
    · simp only [insertObservation, dite_eq_right hj, dite_eq_right hI, zero_add]
      exact measurable_snd

/-- A finite Brownian sampling law can be extended by its last time
using independence of the increment from the full supplied past. -/
private theorem sample_insert_map (hX : BrownianOn μ F H X) (I : Finset ℝ≥0) (t : ℝ≥0)
    (ht : t ≤ H) (hmax : ∀ j ∈ I, j < t) :
    μ.map (fun ω (j : (insert t I : Finset ℝ≥0)) => X j ω) =
      (((μ.map (fun ω (j : I) => X j ω)).prod (gaussianReal 0 (t - lastTime I))).map
        (insertObservation I t)) := by
  let s := lastTime I
  have hst : s ≤ t := by
    by_cases hI : I.Nonempty
    · simpa only [s, lastTime, dite_eq_left hI] using (hmax (I.max' hI) (I.max'_mem hI)).le
    · simp [s, lastTime, hI]
  let past (ω : Ω) (j : I) := X j ω
  let inc (ω : Ω) := X t ω - X s ω
  have hFpast : Measurable[F s] past := by
    exact @Measurable.of_eval Ω I (fun _ => ℝ) (F s) _ past fun j =>
      ((hX.adapted j).mono (F.mono (le_lastTime I j))).measurable
  have hpast : Measurable past := hFpast.mono (F.le s) le_rfl
  have hinc : Measurable inc :=
    ((hX.adapted t).mono (F.le t)).measurable.sub ((hX.adapted s).mono (F.le s)).measurable
  have hind : IndepFun past inc μ :=
    (IndepFun_iff_Indep _ _ _).2
      (indep_of_indep_of_le_right (hX.independent_of_past s t hst ht) hFpast.comap_le).symm
  have hrec : (fun ω (j : (insert t I : Finset ℝ≥0)) => X j ω) =ᵐ[μ]
      (insertObservation I t) ∘ (fun ω => (past ω, inc ω)) := by
    filter_upwards [hX.zero_at_start] with ω hω
    funext j
    by_cases hj : j.val ∈ I
    · simp [Function.comp_apply, insertObservation, hj, past]
    have he : j.val = t := (Finset.mem_insert.mp j.property).resolve_right hj
    have htI : t ∉ I := fun h => (lt_irrefl t) (hmax t h)
    by_cases hI : I.Nonempty
    · simp [Function.comp_apply, insertObservation, hI, past, inc, s, lastTime, he, htI]
    · simp [Function.comp_apply, insertObservation, hI, inc, s, lastTime, he, htI, hω]
  rw [Measure.map_congr hrec, ← Measure.map_map (measurable_insertObservation I t) (hpast.prodMk hinc),
    hind.map_prod_eq_prod_map_map hpast.aemeasurable hinc.aemeasurable,
    hX.normal_increment s t hst ht]

variable {Ω' : Type*} [mΩ' : MeasurableSpace Ω'] {ν : Measure Ω'} [IsProbabilityMeasure ν]
  {G : Filtration ℝ≥0 mΩ'} {Y : ℝ≥0 → Ω' → ℝ}

/-- Every finite observation inside the common horizon has the same law
for Brownian motions on two arbitrary supplied filtered spaces. -/
theorem sample_map_eq_of_brownianOn (hX : BrownianOn μ F H X) (hY : BrownianOn ν G H Y)
    (I : Finset ℝ≥0) (hI : ∀ t ∈ I, t ≤ H) :
    μ.map (fun ω (i : I) => X i ω) = ν.map (fun ω (i : I) => Y i ω) := by
  induction I using Finset.induction_on_max with
  | empty =>
    rw [show (fun ω (i : (∅ : Finset ℝ≥0)) => X i ω) = fun _ => (0 : (∅ : Finset ℝ≥0) → ℝ)
      from funext fun ω => funext fun i => False.elim (Finset.notMem_empty i.val i.property)]
    rw [show (fun ω (i : (∅ : Finset ℝ≥0)) => Y i ω) = fun _ => (0 : (∅ : Finset ℝ≥0) → ℝ)
      from funext fun ω => funext fun i => False.elim (Finset.notMem_empty i.val i.property)]
    simp
  | insert t I hmax ih =>
    have ht : t ≤ H := hI t (Finset.mem_insert_self _ _)
    rw [sample_insert_map hX I t ht hmax, sample_insert_map hY I t ht hmax]
    rw [ih fun s hs => hI s (Finset.mem_insert_of_mem hs)]

private theorem referenceBrownianOn (T : ℝ≥0) :
    BrownianOn gaussianLimit
      (Filtration.natural brownian (fun t => (measurable_brownian t).stronglyMeasurable)) T brownian := by
  have hB := isBrownianReal_brownian.toIsPreBrownianReal
  have hF := hB.isFilteredPreBrownian measurable_brownian
  refine ⟨hF.stronglyAdapted, hB.eval_zero_ae_eq_zero,
    ae_of_all _ (fun ω => (continuous_brownian ω).continuousOn), ?_, ?_⟩
  · intro s t hst _
    have hdiff : nndist t s = t - s := by
      apply Subtype.ext
      change dist (t : ℝ) (s : ℝ) = ((t - s : ℝ≥0) : ℝ)
      rw [Real.dist_eq, NNReal.coe_sub hst, abs_of_nonneg]
      exact sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst)
    change Measure.map (brownian t - brownian s) gaussianLimit = _
    simpa only [hdiff] using (hasLaw_brownian_sub (s := t) (t := s)).map_eq
  · intro s t hst _
    exact hF.indep s t hst

/-- Finite-horizon Brownian motions have the required Gaussian law even
when the observation array repeats a physical time. -/
theorem hasLaw_sampled_brownianOn (hX : BrownianOn μ F H X) {n : ℕ} (t : Fin n → ℝ≥0)
    (ht : ∀ i, t i ≤ H) :
    HasLaw (fun ω => WithLp.toLp 2 (fun i => X (t i) ω))
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
        (fun i j => ((min (t i) (t j) : ℝ≥0) : ℝ))) μ := by
  classical
  let I : Finset ℝ≥0 := Finset.univ.image t
  let f (i : Fin n) : I := ⟨t i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  let R (z : I → ℝ) : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => z (f i))
  have hR : Measurable R := (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable.comp
    (Measurable.of_eval fun i => measurable_pi_apply (f i))
  have hIm : ∀ s ∈ I, s ≤ H := by
    intro s hs
    rcases Finset.mem_image.mp hs with ⟨i, _, rfl⟩
    exact ht i
  have hXmeas : Measurable (fun ω (j : I) => X j ω) :=
    Measurable.of_eval fun j => ((hX.adapted j).mono (F.le j)).measurable
  have hBm : Measurable (fun ω (j : I) => brownian j ω) :=
    Measurable.of_eval fun j => measurable_brownian j
  refine ⟨(hR.comp hXmeas).aemeasurable, ?_⟩
  change Measure.map (R ∘ (fun ω (j : I) => X j ω)) μ = _
  rw [← Measure.map_map hR hXmeas, sample_map_eq_of_brownianOn hX (referenceBrownianOn H) I hIm,
    Measure.map_map hR hBm]
  exact (hasLaw_sampled_preBrownian isBrownianReal_brownian.toIsPreBrownianReal t).map_eq

omit [IsProbabilityMeasure μ] in
/-- The repeated scalar increment retains its independence from the
supplied past without any Brownian assumptions beyond the horizon. -/
theorem indep_repeated_increment_of_brownianOn (hX : BrownianOn μ F H X) (n : ℕ)
    {s t : ℝ≥0} (hst : s ≤ t) (ht : t ≤ H) :
    Indep (MeasurableSpace.comap
      (fun ω => WithLp.toLp 2 (fun _ : Fin n => X t ω - X s ω))
      (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n)))) (F s) μ := by
  apply indep_of_indep_of_le_left (hX.independent_of_past s t hst ht)
  let V (a : ℝ) : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun _ => a
  change MeasurableSpace.comap (V ∘ (X t - X s)) _ ≤ _
  rw [← MeasurableSpace.comap_comp]
  apply MeasurableSpace.comap_mono (Measurable.comap_le _)
  fun_prop

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.sample_map_eq_of_brownianOn
#print axioms RoughHeston.GirsanovPort.hasLaw_sampled_brownianOn
#print axioms RoughHeston.GirsanovPort.indep_repeated_increment_of_brownianOn
