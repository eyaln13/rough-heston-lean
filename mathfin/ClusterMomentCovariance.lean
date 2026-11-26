import SizeBiasedBurst
import StochasticCovariation
import Mathlib.Probability.Martingale.Basic

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Interval Topology

namespace RoughHeston
namespace GirsanovPort

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {P : Measure Ω}
  [Preorder ι] {F : Filtration ι m} {M C : ι → Ω → ℝ}

private theorem cluster_gridIntegral_unit (grid : ℕ →o ι) (n : ℕ) :
    gridIntegral grid (fun _ _ => (1 : ℝ)) M n = M (grid n) - M (grid 0) := by
  induction n with
  | zero => simp [gridIntegral, runningSum]
  | succ n ih =>
    rw [gridIntegral_succ, ih]
    ext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, one_mul]
    ring

/-- Pairing the same martingale's deterministic stochastic sum with
its terminal value gives the expected bracket increments with the
same deterministic weights. -/
theorem deterministic_stochastic_grid_covariance [IsFiniteMeasure P]
    (hM : Martingale M F P) (hM₂ : ∀ t, MemLp (M t) 2 P)
    (hC : Martingale (fun t => M t * M t - C t) F P)
    (grid : ℕ →o ι) (n : ℕ) (w : ℕ → ℝ)
    (hStart : M (grid 0) =ᵐ[P] 0) :
    (∫ ω, gridIntegral grid (fun k _ => w k) M n ω * M (grid n) ω ∂P) =
      ∑ k ∈ Finset.range n, w k * (∫ ω, C (grid (k + 1)) ω - C (grid k) ω ∂P) := by
  have he := grid_integral_cross_isometry grid hM hM hC hM₂ hM₂
    (a := fun k _ => w k) (b := fun _ _ => 1) (fun _ => stronglyMeasurable_const)
    (fun _ => stronglyMeasurable_const) (fun _ => memLp_const _) (fun _ => memLp_const _) n
  rw [cluster_gridIntegral_unit] at he
  calc
    _ = ∫ ω, gridIntegral grid (fun k _ => w k) M n ω * (M (grid n) - M (grid 0)) ω ∂P := by
      apply integral_congr_ae
      filter_upwards [hStart] with ω hw
      simp only [Pi.sub_apply, hw, Pi.zero_apply, sub_zero]
    _ = _ := by
      rw [he]
      simp only [mul_one, integral_const_mul]

private theorem deterministic_stochastic_grid_mean_zero [IsFiniteMeasure P]
    (hM : Martingale M F P) (hM₂ : ∀ t, MemLp (M t) 2 P)
    (grid : ℕ →o ι) (n : ℕ) (w : ℕ → ℝ) :
    (∫ ω, gridIntegral grid (fun k _ => w k) M n ω ∂P) = 0 := by
  have hM' := grid_integral_martingale grid hM hM₂ (a := fun k _ => w k)
    (fun _ => stronglyMeasurable_const) (fun _ => memLp_const _)
  have h := hM'.setIntegral_eq (Nat.zero_le n) (s := univ) MeasurableSet.univ
  simpa only [Measure.restrict_univ, gridIntegral, runningSum_zero, Pi.zero_apply, integral_zero] using h.symm

/-- The mean and covariance identities survive the actual mean-square
limit. The second limit is a deterministic quadrature for the bracket. -/
theorem deterministic_stochastic_limit_covariance [IsFiniteMeasure P]
    (hM : Martingale M F P) (hM₂ : ∀ t, MemLp (M t) 2 P)
    (hC : Martingale (fun t => M t * M t - C t) F P)
    (grid : ℕ → ℕ →o ι) (n : ℕ → ℕ) (w : ℕ → ℕ → ℝ) (H : ι)
    (hStart : ∀ j, M (grid j 0) =ᵐ[P] 0) (hEnd : ∀ j, grid j (n j) = H)
    {S : Ω → ℝ} (hS : MemLp S 2 P)
    (hConv : Tendsto (fun j => eLpNorm (gridIntegral (grid j) (fun k _ => w j k) M (n j) - S) 2 P) atTop (𝓝 0))
    {q : ℝ} (hQuad : Tendsto (fun j => ∑ k ∈ Finset.range (n j),
      w j k * (∫ ω, C (grid j (k + 1)) ω - C (grid j k) ω ∂P)) atTop (𝓝 q)) :
    (∫ ω, S ω ∂P) = 0 ∧ (∫ ω, S ω * M H ω ∂P) = q := by
  let Sn (j : ℕ) := gridIntegral (grid j) (fun k _ => w j k) M (n j)
  have hSn (j : ℕ) : MemLp (Sn j) 2 P :=
    grid_integral_memLp_two (grid j) hM₂ (a := fun k _ => w j k) (fun _ => memLp_const _) (n j)
  have hPair {f : Ω → ℝ} (hf : MemLp f 2 P) :
      Tendsto (fun j => ∫ ω, Sn j ω * f ω ∂P) atTop (𝓝 (∫ ω, S ω * f ω ∂P)) := by
    have hconst : Tendsto (fun _ : ℕ => eLpNorm (f - f) 2 P) atTop (𝓝 0) := by
      simpa only [sub_self, eLpNorm_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
    exact tendsto_integral_of_L1' (S * f)
      (Eventually.of_forall fun j => (hSn j).integrable_mul hf)
      (product_L1_limit_of_L2_limits hS hf hSn (fun _ => hf) hConv hconst)
  constructor
  · have h := hPair (memLp_const (1 : ℝ))
    simp only [mul_one] at h
    have he (j : ℕ) : (∫ ω, Sn j ω ∂P) = 0 :=
      deterministic_stochastic_grid_mean_zero hM hM₂ (grid j) (n j) (w j)
    simp only [he] at h
    exact (tendsto_nhds_unique h tendsto_const_nhds)
  · have h := hPair (hM₂ H)
    apply tendsto_nhds_unique h
    refine hQuad.congr fun j => ?_
    have he := deterministic_stochastic_grid_covariance hM hM₂ hC (grid j) (n j) (w j) (hStart j)
    rw [hEnd j] at he
    exact he.symm

/-- The cluster mass square and the terminal size-biased mean follow
from the old square compensator and the bilinear covariance. -/
theorem sizeBiased_cluster_terminal_means [IsProbabilityMeasure P]
    {o r : ι} (hor : o ≤ r) (hM : Martingale M F P) (hM₂ : MemLp (M r) 2 P)
    (hM₀ : M o =ᵐ[P] 0) (hC₀ : C o =ᵐ[P] 0)
    (hC : Martingale (fun t => M t * M t - C t) F P)
    {ε m q : ℝ} (hε : 0 < ε) {S U : Ω → ℝ}
    (hS₂ : MemLp S 2 P) (hS₀ : (∫ ω, S ω ∂P) = 0)
    (hCross : (∫ ω, S ω * M r ω ∂P) = q)
    (hU : U =ᵐ[P] fun ω => m + S ω)
    (hZpos : ∀ᵐ ω ∂P, 0 ≤ ε + M r ω) :
    let Z (ω : Ω) := ε + M r ω
    let Q := sizeBiasedLaw P Z ε
    IsProbabilityMeasure Q ∧
      (∫ ω, Z ω ^ 2 ∂P) = ε ^ 2 + (∫ ω, C r ω ∂P) ∧
      (∫ ω, U ω ∂Q) = m + q / ε ∧
      (∫ ω, Z ω ∂Q) = ε + (∫ ω, C r ω ∂P) / ε := by
  let Z (ω : Ω) := ε + M r ω
  let Q := sizeBiasedLaw P Z ε
  have hZmeas : Measurable Z := measurable_const.add ((hM.stronglyMeasurable r).mono (F.le r)).measurable
  have hZ₂ : MemLp Z 2 P := (memLp_const ε).add hM₂
  have hMN : (∫ ω, M r ω ∂P) = 0 := by
    have he := hM.setIntegral_eq hor (s := univ) MeasurableSet.univ
    rw [Measure.restrict_univ, integral_congr_ae hM₀] at he
    simpa only [Pi.zero_apply, integral_zero] using he.symm
  have hZmean : (∫ ω, Z ω ∂P) = ε := by
    change (∫ ω, ε + M r ω ∂P) = ε
    rw [integral_add (integrable_const ε) (hM₂.integrable one_le_two), hMN]
    simp
  have hMrSq : Integrable (M r * M r) P := hM₂.integrable_mul hM₂
  have hCi : Integrable (C r) P := by
    simpa only [sub_sub_cancel] using hMrSq.sub (hC.integrable r)
  have hMclock : (∫ ω, M r ω ^ 2 ∂P) = ∫ ω, C r ω ∂P := by
    have he := hC.setIntegral_eq hor (s := univ) MeasurableSet.univ
    rw [Measure.restrict_univ] at he
    have hh : (fun ω => (M o * M o - C o) ω) =ᵐ[P] 0 := by
      filter_upwards [hM₀, hC₀] with ω hm hc
      simp only [Pi.mul_apply, Pi.sub_apply, hm, hc, Pi.zero_apply, zero_mul, sub_self]
    rw [integral_congr_ae hh] at he
    simp only [Pi.zero_apply, integral_zero] at he
    change (0 : ℝ) = ∫ ω, (M r * M r) ω - C r ω ∂P at he
    rw [integral_sub hMrSq hCi] at he
    simpa only [Pi.mul_apply, pow_two] using sub_eq_zero.mp he.symm
  have hZsq : (∫ ω, Z ω ^ 2 ∂P) = ε ^ 2 + (∫ ω, C r ω ∂P) := by
    have hi : Integrable (fun ω => 2 * ε * M r ω) P := (hM₂.integrable one_le_two).const_mul _
    have h0 : Integrable (fun _ : Ω => ε ^ 2) P := integrable_const _
    have h3 : Integrable (fun ω => M r ω ^ 2) P := hM₂.integrable_sq
    have hA : Integrable (fun ω => ε ^ 2 + 2 * ε * M r ω) P := h0.add hi
    simp_rw [show ∀ ω, Z ω ^ 2 = ε ^ 2 + 2 * ε * M r ω + M r ω ^ 2 from fun ω => by dsimp [Z]; ring]
    rw [integral_add hA h3, integral_add h0 hi, integral_const_mul, hMN, hMclock]
    simp
  have hQ := sizeBiasedLaw_isProbabilityMeasure hε (hZ₂.integrable one_le_two) hZpos hZmean
  refine ⟨hQ, hZsq, ?_, ?_⟩
  · rw [integral_sizeBiasedLaw_eq hε hZmeas hZpos]
    have he : (∫ ω, Z ω * U ω ∂P) = (∫ ω, (m * Z ω + ε * S ω) + S ω * M r ω ∂P) := by
      apply integral_congr_ae
      filter_upwards [hU] with ω hw
      change U ω = m + S ω at hw
      rw [hw]
      dsimp [Z]
      ring
    have hsm : Integrable (fun ω => S ω * M r ω) P := hS₂.integrable_mul hM₂
    have h1 : Integrable (fun ω => m * Z ω) P := (hZ₂.integrable one_le_two).const_mul m
    have h2 : Integrable (fun ω => ε * S ω) P := (hS₂.integrable one_le_two).const_mul ε
    have hA : Integrable (fun ω => m * Z ω + ε * S ω) P := h1.add h2
    rw [he, integral_add hA hsm, integral_add h1 h2, integral_const_mul, integral_const_mul, hZmean,
      hS₀, hCross]
    field_simp
    ring
  · rw [integral_sizeBiasedLaw_eq hε hZmeas hZpos]
    change (∫ ω, Z ω * Z ω ∂P) / ε = _
    rw [show (fun ω => Z ω * Z ω) = (fun ω => Z ω ^ 2) from funext fun ω => (pow_two (Z ω)).symm, hZsq]
    field_simp

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.deterministic_stochastic_limit_covariance
#print axioms RoughHeston.GirsanovPort.sizeBiased_cluster_terminal_means
