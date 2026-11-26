import CanonicalMartingaleLimits
import SeparatedInverseMartingales

open MeasureTheory ProbabilityTheory Filter Set
open scoped MeasureTheory Topology NNReal ENNReal

namespace RoughHeston

variable {T : ℝ≥0} {α v₀ κ θ : ℝ}

/-- An observable of the joint variance path, frozen at the horizon. -/
def canonicalVarianceCoordinate (T : ℝ≥0) (f : C(ℝ × ℝ, ℝ))
    (t : ℝ≥0) (p : CanonicalPath T (ℝ × ℝ)) : ℝ := f (canonicalPathEval T t p)

theorem stronglyAdapted_canonicalVarianceCoordinate (T : ℝ≥0) (f : C(ℝ × ℝ, ℝ)) :
    StronglyAdapted (canonicalPathNaturalFiltration T) (canonicalVarianceCoordinate T f) := by
  have ha : StronglyAdapted (canonicalPathNaturalFiltration (E := ℝ × ℝ) T) (canonicalPathEval T) :=
    Filtration.stronglyAdapted_natural (fun t =>
      (ContinuousMap.measurable_eval (canonicalEvalTime T t)).stronglyMeasurable)
  exact fun t => f.continuous.comp_stronglyMeasurable (ha t)

theorem continuous_canonicalVarianceCoordinate_time (T : ℝ≥0) (f : C(ℝ × ℝ, ℝ))
    (p : CanonicalPath T (ℝ × ℝ)) :
    Continuous (fun t => canonicalVarianceCoordinate T f t p) :=
  f.continuous.comp (p.continuous.comp ((continuous_id.min continuous_const).subtype_mk _))

theorem continuous_canonicalVarianceCoordinate_path (T : ℝ≥0) (f : C(ℝ × ℝ, ℝ))
    (t : ℝ≥0) : Continuous (canonicalVarianceCoordinate T f t) :=
  f.continuous.comp (continuous_canonicalPathEval T t)

variable {μ : Measure (CanonicalPath T (ℝ × ℝ))} [IsFiniteMeasure μ]

private theorem canonicalVarianceCoordinate_norm_le
    {f : C(ℝ × ℝ, ℝ)} (hbound : ∀ x : ℝ × ℝ, ‖f x‖ ≤ ‖x‖)
    (t : ℝ≥0) (p : CanonicalPath T (ℝ × ℝ)) :
    ‖canonicalVarianceCoordinate T f t p‖ ≤ ‖p‖ :=
  (hbound (canonicalPathEval T t p)).trans (p.norm_coe_le_norm (canonicalEvalTime T t))

omit [IsFiniteMeasure μ] in
/-- A square-integrable uniform path bound controls every variance
evaluation in the same L² space. -/
theorem canonicalVarianceCoordinate_memLp {f : C(ℝ × ℝ, ℝ)}
    (hbound : ∀ x : ℝ × ℝ, ‖f x‖ ≤ ‖x‖)
    (hpath : MemLp (fun p : CanonicalPath T (ℝ × ℝ) => ‖p‖) 2 μ) (t : ℝ≥0) :
    MemLp (canonicalVarianceCoordinate T f t) 2 μ := by
  apply hpath.mono (continuous_canonicalVarianceCoordinate_path T f t).measurable.aestronglyMeasurable
  exact ae_of_all μ fun p => (canonicalVarianceCoordinate_norm_le hbound t p).trans
    (le_of_eq (norm_norm p).symm)

omit [IsFiniteMeasure μ] in
/-- Dominated convergence gives L² continuity of the variance evaluation
from the square-integrable uniform path bound. -/
theorem continuous_canonicalVarianceCoordinate_Lp {f : C(ℝ × ℝ, ℝ)}
    (hbound : ∀ x : ℝ × ℝ, ‖f x‖ ≤ ‖x‖)
    (hpath : MemLp (fun p : CanonicalPath T (ℝ × ℝ) => ‖p‖) 2 μ) :
    Continuous (fun t => (canonicalVarianceCoordinate_memLp hbound hpath t).toLp
      (canonicalVarianceCoordinate T f t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  apply tendsto_nhds_iff_seq_tendsto.2
  intro u hu
  apply tendsto_iff_edist_tendsto_0.mpr
  simp only [Function.comp_apply, Lp.edist_toLp_toLp]
  apply tendsto_eLpNorm_two_dominated (hpath.const_mul 2)
  · intro n
    exact ((continuous_canonicalVarianceCoordinate_path T f (u n)).sub
      (continuous_canonicalVarianceCoordinate_path T f t)).measurable.aestronglyMeasurable
  · intro n
    exact ae_of_all μ fun p => by
      change ‖canonicalVarianceCoordinate T f (u n) p - canonicalVarianceCoordinate T f t p‖ ≤
        ‖(2 : ℝ) * ‖p‖‖
      rw [Real.norm_of_nonneg (by positivity : 0 ≤ (2 : ℝ) * ‖p‖)]
      exact (norm_sub_le _ _).trans (by
        linarith [canonicalVarianceCoordinate_norm_le hbound (u n) p,
          canonicalVarianceCoordinate_norm_le hbound t p])
  · exact ae_of_all μ fun p => by
      have hp := ((continuous_canonicalVarianceCoordinate_time T f p).tendsto t).comp hu
      simpa only [Function.comp_apply, Pi.sub_apply, sub_self] using hp.sub (tendsto_const_nhds (x := canonicalVarianceCoordinate T f t p))

/-- The reconstructed inverse martingale has continuous time paths. -/
theorem continuous_canonicalVarianceMartingale_time (T : ℝ≥0)
    {α : ℝ} (hα : α < 1) (v₀ κ θ : ℝ) (f : C(ℝ × ℝ, ℝ))
    (p : CanonicalPath T (ℝ × ℝ)) :
    Continuous (fun t => canonicalVarianceMartingale T α v₀ κ θ f t p) := by
  let v (s : ℝ) := f (p (realTimeOnHorizon T s))
  have hvc : Continuous v := f.continuous.comp (p.continuous.comp (realTimeOnHorizon T).continuous)
  have hL := continuousOn_volterra_forcing (k := fractionalL α) (g := fun s => v s - v₀)
    (NNReal.coe_nonneg T) (fractionalL_measurable α) (fractionalL_integrableOn_Ioc hα T)
    (hvc.sub continuous_const).continuousOn
  have hC := continuousOn_volterra_forcing (k := fun _ => (1 : ℝ)) (g := v)
    (NNReal.coe_nonneg T) measurable_const (integrable_const _) hvc.continuousOn
  let s (t : ℝ≥0) : ℝ := ((min t T : ℝ≥0) : ℝ)
  have hsc : Continuous s := NNReal.continuous_coe.comp (continuous_id.min continuous_const)
  have hsh (t : ℝ≥0) : s t ∈ Icc (0 : ℝ) (T : ℝ) :=
    ⟨NNReal.coe_nonneg (min t T), NNReal.coe_le_coe.mpr (min_le_right t T)⟩
  have hL' := hL.comp_continuous hsc hsh
  have hC' := hC.comp_continuous hsc hsh
  have hD := (continuous_const (y := κ * θ)).mul hsc
  have hE := hL'.sub hD |>.add ((continuous_const (y := κ)).mul hC')
  convert hE using 1
  funext t
  simp only [canonicalVarianceMartingale, recoveredVarianceMartingale, Function.comp_apply,
    Pi.add_apply, Pi.sub_apply, Pi.mul_apply, volterraSmulConvolution, smul_eq_mul, one_mul,
    ContinuousMap.comp_apply, v, s]

/-- The inverse process recovered from the canonical path supplies
the one-coordinate data for the common-Brownian construction. -/
theorem canonicalVarianceInverseMartingaleData
    (hα : α < 1) {f : C(ℝ × ℝ, ℝ)}
    (hnonneg : ∀ x, 0 ≤ f x) (hbound : ∀ x : ℝ × ℝ, ‖f x‖ ≤ ‖x‖)
    (hpath : MemLp (fun p : CanonicalPath T (ℝ × ℝ) => ‖p‖) 2 μ)
    (hM : Martingale (canonicalVarianceMartingale T α v₀ κ θ f)
      (canonicalPathNaturalFiltration T) μ)
    (hM₂ : ∀ t, MemLp (canonicalVarianceMartingale T α v₀ κ θ f t) 2 μ) :
    VarianceInverseMartingaleData μ (canonicalPathNaturalFiltration T) T α v₀ κ θ
      (canonicalVarianceCoordinate T f) (canonicalVarianceMartingale T α v₀ κ θ f) := by
  let V := canonicalVarianceCoordinate T f
  have hVl₂ (t : ℝ≥0) : MemLp (V t) 2 μ := canonicalVarianceCoordinate_memLp hbound hpath t
  have hVi (t : ℝ≥0) : Integrable (V t) μ := (hVl₂ t).integrable one_le_two
  have hfC : ∃ C, ∀ t, (∫ p, V t p ∂μ) ≤ C := by
    refine ⟨∫ p, ‖p‖ ∂μ, fun t => ?_⟩
    apply integral_mono (hVi t) (hpath.integrable one_le_two)
    intro p
    exact (le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs] using canonicalVarianceCoordinate_norm_le hbound t p)
  have hct : Continuous (fun t => (hVl₂ t).toLp (V t)) :=
    continuous_canonicalVarianceCoordinate_Lp hbound hpath
  let v0L := (memLp_const v₀ : MemLp (fun _ : CanonicalPath T (ℝ × ℝ) => v₀) 2 μ).toLp _
  let θL := (memLp_const θ : MemLp (fun _ : CanonicalPath T (ℝ × ℝ) => θ) 2 μ).toLp _
  let vL (s : ℝ) := (hVl₂ s.toNNReal).toLp (V s.toNNReal)
  have hvLc : Continuous vL := hct.comp continuous_real_toNNReal
  let fL (s : ℝ) := vL s - v0L
  let gL (s : ℝ) := κ • (θL - vL s)
  have hfLt : Continuous fL := hvLc.sub continuous_const
  have hgLt : Continuous gL := (continuous_const.sub hvLc).const_smul κ
  have hVrep (s : ℝ) : ⇑(vL s) =ᵐ[μ] V s.toNNReal :=
    (hVl₂ s.toNNReal).coeFn_toLp
  have hfLrep (s : ℝ) : ⇑(fL s) =ᵐ[μ] fun p => V s.toNNReal p - v₀ :=
    (Lp.coeFn_sub (vL s) v0L).trans ((hVrep s).sub (memLp_const v₀).coeFn_toLp)
  have hgLrep (s : ℝ) : ⇑(gL s) =ᵐ[μ] fun p => κ * (θ - V s.toNNReal p) := by
    filter_upwards [Lp.coeFn_smul κ (θL - vL s), Lp.coeFn_sub θL (vL s),
      (memLp_const θ : MemLp (fun _ : CanonicalPath T (ℝ × ℝ) => θ) 2 μ).coeFn_toLp,
      hVrep s] with p h1 h2 h3 h4
    change (κ • (θL - vL s) : Lp ℝ 2 μ) p = κ * (θ - V s.toNNReal p)
    rw [h1, Pi.smul_apply, smul_eq_mul, h2, Pi.sub_apply, h3, h4]
  refine ⟨stronglyAdapted_canonicalVarianceCoordinate T f,
    continuous_canonicalVarianceCoordinate_time T f, fun t p => hnonneg _,
    hVi, hfC, ⟨fL, gL, hfLt, hgLt, hfLrep, hgLrep⟩, hM, hM₂, ?_, ?_⟩
  · exact ae_of_all μ fun p => (continuous_canonicalVarianceMartingale_time T hα v₀ κ θ f p).continuousOn
  · intro t ht
    refine ae_of_all μ fun p => ?_
    have hv : Continuous (fun s : ℝ => V s.toNNReal p) :=
      (continuous_canonicalVarianceCoordinate_time T f p).comp continuous_real_toNNReal
    have hVi' : IntegrableOn (fun s : ℝ => V s.toNNReal p) (Ioc 0 (t : ℝ)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le t.prop).1
        (hv.intervalIntegrable 0 t)
    change (∫ s in Ioc (0 : ℝ) (t : ℝ), fractionalL α ((t : ℝ) - s) * (V s.toNNReal p - v₀)) =
      (∫ s in Ioc (0 : ℝ) (t : ℝ), κ * (θ - V s.toNNReal p)) +
        canonicalVarianceMartingale T α v₀ κ θ f t p
    rw [integral_const_mul, integral_sub (integrable_const θ) hVi']
    have hθ : (∫ _ in Ioc (0 : ℝ) (t : ℝ), θ) = (t : ℝ) * θ := by
      simp [smul_eq_mul]
    rw [hθ, canonicalVarianceMartingale, min_eq_left ht, recoveredVarianceMartingale]
    simp only [ContinuousMap.comp_apply]
    change _ = _ + ((∫ s in Ioc (0 : ℝ) (t : ℝ), fractionalL α ((t : ℝ) - s) *
      (V s.toNNReal p - v₀)) - κ * θ * (t : ℝ) + κ * (∫ s in Ioc (0 : ℝ) (t : ℝ), V s.toNNReal p))
    ring

end RoughHeston

#print axioms RoughHeston.canonicalVarianceCoordinate_memLp
#print axioms RoughHeston.continuous_canonicalVarianceCoordinate_Lp
#print axioms RoughHeston.continuous_canonicalVarianceMartingale_time
#print axioms RoughHeston.canonicalVarianceInverseMartingaleData
