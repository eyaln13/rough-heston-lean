import KernelMomentTransfer
import FractionalBoundaryHistory
import FractionalKernelIncrements

/-! The integrated time profile in the cluster moment induction. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace RoughHeston

theorem weighted_kernel_moment_time_profile {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    {ν : Measure S} {μ : Measure Ω} [SFinite ν] [SFinite μ]
    {w c : S → ℝ≥0∞} {V : S → Ω → ℝ≥0∞} {m : ℝ} (hm : 1 < m)
    (hw : Measurable w) (hV : Measurable (Function.uncurry V))
    (hc : ∀ᵐ s ∂ν, (∫⁻ ω, V s ω ^ m ∂μ) ≤ c s) :
    (∫⁻ ω, (∫⁻ s,w s * V s ω ∂ν)^m ∂μ) ≤
      (∫⁻ s,w s ∂ν)^(m-1) * (∫⁻ s,w s*c s ∂ν) := by
  let h (s : S) (ω : Ω) := w s*V s ω^m
  have hh : Measurable (Function.uncurry h) :=
    (hw.comp measurable_fst).mul (ENNReal.continuous_rpow_const.measurable.comp hV)
  have hmean : (∫⁻ s, ∫⁻ ω,h s ω ∂μ ∂ν) ≤ ∫⁻ s,w s*c s ∂ν := by
    apply lintegral_mono_ae
    filter_upwards [hc] with s hs
    have hv : Measurable (fun ω => V s ω ^ m) := ENNReal.continuous_rpow_const.measurable.comp
      (hV.comp (measurable_const.prodMk measurable_id))
    rw [show (∫⁻ ω,h s ω ∂μ) = w s*(∫⁻ ω,V s ω^m ∂μ) from lintegral_const_mul _ hv]
    gcongr
  let A := ∫⁻ s,w s ∂ν
  calc
    _ ≤ ∫⁻ ω, A^(m-1)*(∫⁻ s,h s ω ∂ν) ∂μ := by
      apply lintegral_mono
      intro ω
      exact lintegral_weighted_rpow_le (μ := ν) hw (hV.comp (measurable_id.prodMk measurable_const)) hm
    _ = A^(m-1)*(∫⁻ ω, ∫⁻ s,h s ω ∂ν ∂μ) := lintegral_const_mul _ hh.lintegral_prod_left'
    _ = A^(m-1)*(∫⁻ s, ∫⁻ ω,h s ω ∂μ ∂ν) :=
      congrArg (fun x => A^(m-1)*x) (lintegral_lintegral_swap hh.aemeasurable).symm
    _ ≤ _ := by gcongr

/-- The exact beta integral retains the immigration factor e and gains
m copies of the positive exponent β=2α−1 in one moment-doubling step. -/
theorem cluster_beta_moment_step {α v : ℝ} (hα : 1/2 < α) (hv : 0 < v) (m e : ℝ) :
    let β := 2*α-1
    v^(β*(m-1)) * (∫ u in Ioc (0:ℝ) v, (v-u)^(β-1)*(e*u^(α-1))) =
      (Real.Gamma α*Real.Gamma β/Real.Gamma (α+β))*e*v^(α-1+m*β) := by
  dsimp only
  let β := 2*α-1
  have hb : 0 < β := by dsimp [β]; linarith
  have ha : 0 < α := by linarith
  have hi := (real_beta_weight_scaled ha hb hv).2
  change v^(β*(m-1)) * (∫ u in Ioc (0:ℝ) v, (v-u)^(β-1)*(e*u^(α-1))) = _
  have he : (fun u : ℝ => (v-u)^(β-1)*(e*u^(α-1))) =
      fun u => e*(u^(α-1)*(v-u)^(β-1)) := by funext u; ring
  rw [he, integral_const_mul, hi]
  have hpow : v^(β*(m-1))*v^(α+β-1)=v^(α-1+m*β) := by
    rw [← Real.rpow_add hv]; congr 1; ring
  dsimp only [β] at *
  linear_combination e*(Real.Gamma α * Real.Gamma (2*α-1) / Real.Gamma (α+(2*α-1)))*hpow

#print axioms weighted_kernel_moment_time_profile
#print axioms cluster_beta_moment_step

end RoughHeston
