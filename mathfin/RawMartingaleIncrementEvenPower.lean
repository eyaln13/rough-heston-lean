import ContinuousRawBDG

/-! Fourth moments of increments in an arbitrary continuous-time filtration. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston

/-- Shift the martingale and its square compensator at deterministic
time s, and apply the continuous raw-filtration fourth-moment estimate. -/
theorem continuous_raw_martingale_increment_even_power_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {M A : ℝ≥0 → Ω → ℝ} (hM : Martingale M F μ)
    (hM₂ : ∀ t, MemLp (M t) 2 μ)
    (hMCont : ∀ ω, Continuous (fun t => M t ω))
    (hQ : Martingale (fun t => M t * M t - A t) F μ)
    (hACont : ∀ ω, Continuous (fun t => A t ω))
    (hAMono : ∀ᵐ ω ∂μ, Monotone (fun t => A t ω))
    {s t : ℝ≥0} (hst : s ≤ t) (m : ℕ) (hm : 2 ≤ m) :
    (∫⁻ ω, ‖M t ω - M s ω‖ₑ ^ (2*m : ℕ) ∂μ) ≤
      boundedMartingaleEvenPowerConstant m *
        (∫⁻ ω, ENNReal.ofReal (A t ω - A s ω) ^ m ∂μ) := by
  let v (r : ℝ≥0) := s+r
  let G : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω) :=
    ⟨fun r => F (v r), fun _ _ h => F.mono (add_le_add (le_rfl : s ≤ s) h), fun r => F.le (v r)⟩
  let X (r : ℝ≥0) := M (v r) - M s
  let B (r : ℝ≥0) := A (v r) - A s
  let Q (r : ℝ≥0) := M r * M r - A r
  have hv : Monotone v := fun _ _ h => add_le_add (le_rfl : s ≤ s) h
  have hMv : Martingale (fun r => M (v r)) G μ :=
    ⟨fun r => hM.stronglyMeasurable (v r), fun _ _ h => hM.condExp_ae_eq (hv h)⟩
  have hQv : Martingale (fun r => Q (v r)) G μ :=
    ⟨fun r => hQ.stronglyMeasurable (v r), fun _ _ h => hQ.condExp_ae_eq (hv h)⟩
  have hMs : StronglyMeasurable[G 0] (M s) := by
    change StronglyMeasurable[F (s+0)] (M s)
    rw [add_zero]
    exact hM.stronglyMeasurable s
  have hMc : Martingale (fun _ : ℝ≥0 => M s) G μ :=
    martingale_const_fun G μ hMs (hM.integrable s)
  have hX : Martingale X G μ := hMv.sub hMc
  have hCross : Martingale (fun r => M s * M (v r)) G μ := by
    refine ⟨fun r => (hMs.mono (G.mono (show (0 : ℝ≥0) ≤ r from zero_le))).mul
      (hMv.stronglyMeasurable r), ?_⟩
    intro a b hab
    exact (condExp_mul_of_stronglyMeasurable_left
      (hMs.mono (G.mono (show (0 : ℝ≥0) ≤ a from zero_le)))
      ((hM₂ s).integrable_mul (hM₂ (v b))) (hM.integrable (v b))).trans
        (EventuallyEq.rfl.mul (hMv.condExp_ae_eq hab))
  have hSquare : Integrable (M s * M s) μ := (hM₂ s).integrable_mul (hM₂ s)
  have hA := (hSquare.sub (hQ.integrable s))
  have hAsi : Integrable (A s) μ := by
    apply hA.congr
    exact Eventually.of_forall fun ω => by
      change M s ω * M s ω - (M s ω * M s ω - A s ω) = A s ω
      ring
  have hAsm : StronglyMeasurable[G 0] (A s) := by
    have h := (hMs.mul hMs).sub
      (show StronglyMeasurable[G 0] (Q s) by
        change StronglyMeasurable[F (s+0)] (Q s)
        rw [add_zero]
        exact hQ.stronglyMeasurable s)
    convert h using 1
    funext ω
    simp only [Q, Pi.sub_apply, Pi.mul_apply]
    ring
  have hInit : Martingale (fun _ : ℝ≥0 => M s * M s + A s) G μ :=
    martingale_const_fun G μ ((hMs.mul hMs).add hAsm) (hSquare.add hAsi)
  have hP : Martingale (fun r => X r * X r - B r) G μ := by
    convert (hQv.sub (hCross.smul (2 : ℝ))).add hInit using 1
    funext r ω
    simp only [X, B, Q, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hX0 : X 0 =ᵐ[μ] 0 := Eventually.of_forall fun ω => by simp [X, v]
  have hXC (ω : Ω) : Continuous (fun r => X r ω) :=
    ((hMCont ω).comp (continuous_const.add continuous_id)).sub continuous_const
  have hBC (ω : Ω) : Continuous (fun r => B r ω) :=
    ((hACont ω).comp (continuous_const.add continuous_id)).sub continuous_const
  have hBM : ∀ᵐ ω ∂μ, Monotone (fun r => B r ω) :=
    hAMono.mono fun _ hω _ _ h => sub_le_sub_right (hω (hv h)) _
  have hStep := continuous_raw_martingale_even_power_le hX hX0 hXC hP hBC hBM
    (t-s) m hm
  have he (ω : Ω) : B (t-s) ω - B 0 ω = A t ω - A s ω := by
    simp [B, v, add_tsub_cancel_of_le hst]
  simpa only [X, v, add_tsub_cancel_of_le hst, Pi.sub_apply, he] using hStep

#print axioms RoughHeston.continuous_raw_martingale_increment_even_power_le

end RoughHeston
