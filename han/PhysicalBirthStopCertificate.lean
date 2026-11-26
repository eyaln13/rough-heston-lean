import ActualCappedLawOnBirthTrace

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Interval

namespace RoughHeston.GirsanovPort

/-- The original physical companion and its actual common Brownian
motion across the fixed mesh. The inverse uses the nonnegative
physical input, so choosing a birth does not discard its history. -/
structure PhysicalBirthStopCertificate {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) (F : Filtration ℝ≥0 m) (T : ℝ≥0) (α κ σ : ℝ)
    (B M Y C : ℝ≥0 → Ω → ℝ) (j : ℝ → ℝ) : Prop where
  driver : MathFinBridge.BrownianOn P F T B
  driver_memLp : ∀ t, MemLp (B t) 2 P
  driver_martingale : Martingale B F P
  driver_clock : Martingale (fun t ω => B t ω^2-((min t T:ℝ≥0):ℝ)) F P
  affine_input : ∀ t : ℝ≥0, 0<t → t≤T → AffineInputOn (t:ℝ) j
  residual_martingale : Martingale M F P
  residual_memLp : ∀ t, MemLp (M t) 2 P
  residual_continuous : ∀ ω, Continuous (fun t => M t ω)
  residual_zero : M 0 =ᵐ[P] 0
  variance_predictable : IsStronglyPredictable F Y
  variance_continuous : ∀ ω, Continuous (fun t => Y t ω)
  variance_nonnegative : ∀ t ω, 0≤Y t ω
  variance_initial_bound : ∃ y₀ : ℝ, ∀ ω, Y 0 ω≤y₀
  variance_fourth_bound : ∃ K : ℝ, ∀ t,
    Integrable (fun ω => Y t ω^4) P ∧ (∫ ω,Y t ω^4 ∂P)≤K
  compensated_square : Martingale (fun t => M t*M t-C t) F P
  compensator_integrable : ∀ t, Integrable (C t) P
  compensator_monotone : ∀ u t, u≤t → C u≤ᵐ[P] C t
  compensator : ∀ t≤T, C t =ᵐ[P] fun ω => ∫ u in (0:ℝ)..(t:ℝ), σ^2*Y u.toNNReal ω
  inverse : ∀ᵐ ω ∂P, ∀ t∈Ioc (0:ℝ) (T:ℝ), M t.toNNReal ω =
    volterraConvolution (fractionalL α) (fun u => Y u.toNNReal ω) t +
      ∫ u in Ioc (0:ℝ) t, κ*Y u.toNNReal ω-j u
  amplitude : HasAmplitudeCutoffIntegral F P T B M (fun t ω => σ*Real.sqrt (Y t ω))

/-- Restrict a Brownian law to a shorter deterministic horizon
while keeping the process and filtration. -/
theorem finiteBrownianOn_shorten {Ω : Type*} {m : MeasurableSpace Ω}
    {P : Measure Ω} {F : Filtration ℝ≥0 m} {T t : ℝ≥0} {B : ℝ≥0 → Ω → ℝ}
    (hB : MathFinBridge.BrownianOn P F T B) (ht : t≤T) :
    MathFinBridge.BrownianOn P F t B := by
  refine ⟨hB.adapted,hB.zero_at_start,?_,?_,?_⟩
  · exact hB.continuous_paths.mono fun _ hw => hw.mono (Icc_subset_Icc le_rfl ht)
  · exact fun _ _ hst h => hB.normal_increment _ _ hst (h.trans ht)
  · exact fun _ _ hst h => hB.independent_of_past _ _ hst (h.trans ht)

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.finiteBrownianOn_shorten
