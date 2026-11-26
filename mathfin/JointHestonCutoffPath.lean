import JointHestonWeights

open MeasureTheory Filter Set
open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℝ≥0 m} {V : ℝ≥0 → Ω → ℝ}

/-- Each cutoff weight is adapted to the filtration of the variance process. -/
theorem heston_cutoffWeight_stronglyAdapted
    (hV : StronglyAdapted 𝒢 V) (α : ℝ) (t : ℝ≥0) (n : ℕ) :
    StronglyAdapted 𝒢 (hestonCutoffWeight α t V n) := by
  intro s
  let : MeasurableSpace Ω := 𝒢 s
  have hVmeas : Measurable (V s) := (hV s).measurable
  exact stronglyMeasurable_const.mul (hVmeas.sqrt.min measurable_const).stronglyMeasurable

private theorem continuous_heston_cutoff_kernel (α : ℝ) (t : ℝ≥0) (n : ℕ) :
    Continuous (fun s : ℝ≥0 =>
      hestonKernel α (max ((n : ℝ) + 1)⁻¹ ((t : ℝ) - (s : ℝ)))) := by
  let k (s : ℝ≥0) : ℝ := max ((n : ℝ) + 1)⁻¹ ((t : ℝ) - (s : ℝ))
  have hp (s : ℝ≥0) : 0 < k s :=
    (inv_pos.mpr (by positivity : 0 < (n : ℝ) + 1)).trans_le (le_max_left _ _)
  have hk : Continuous k :=
    continuous_const.max (continuous_const.sub continuous_subtype_val)
  have he : (fun s : ℝ≥0 => hestonKernel α (k s)) =
      (fun s : ℝ≥0 => k s ^ (α - 1) / Real.Gamma α) := by
    funext s
    exact ite_eq_left (hp s)
  change Continuous (fun s : ℝ≥0 => hestonKernel α (k s))
  rw [he]
  exact (hk.rpow_const (fun s => Or.inl (hp s).ne')).div_const _

/-- A cutoff preserves almost sure continuity of the variance path
on the interval of integration. -/
theorem heston_cutoffWeight_ae_continuousOn
    (α : ℝ) (t : ℝ≥0) (n : ℕ)
    (hV : ∀ᵐ ω ∂μ, ContinuousOn (fun s => V s ω) (Icc 0 t)) :
    ∀ᵐ ω ∂μ, ContinuousOn (fun s => hestonCutoffWeight α t V n s ω) (Icc 0 t) := by
  filter_upwards [hV] with ω hω
  exact (continuous_heston_cutoff_kernel α t n).continuousOn.mul
    (continuous_min.comp_continuousOn (hω.sqrt.prodMk continuousOn_const))

/-- Every section of a cutoff weight is essentially bounded. -/
theorem heston_cutoffWeight_memLp_top
    (hV : StronglyAdapted 𝒢 V) {α : ℝ} (hα : 0 < α) (hα' : α ≤ 1)
    (t : ℝ≥0) (n : ℕ) (s : ℝ≥0) :
    MemLp (hestonCutoffWeight α t V n s) ⊤ μ :=
  memLp_top_of_bound
    (((heston_cutoffWeight_stronglyAdapted hV α t n s).mono (𝒢.le s)).aestronglyMeasurable) _
    (Eventually.of_forall (heston_cutoffWeight_bound hα hα' t V n s))

end RoughHeston

#print axioms RoughHeston.heston_cutoffWeight_stronglyAdapted
#print axioms RoughHeston.heston_cutoffWeight_ae_continuousOn
#print axioms RoughHeston.heston_cutoffWeight_memLp_top
