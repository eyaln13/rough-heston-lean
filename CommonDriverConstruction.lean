import CommonDriverLimit

/-!
For a continuous square-integrable martingale with variance density
(a^2), construct its normalized driver using an orthogonal auxiliary
martingale of variance density one.
-/

open MeasureTheory Filter Set
open scoped BigOperators MeasureTheory ProbabilityTheory Topology NNReal ENNReal

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

private structure BoundedDriverWeight (𝒢 : Filtration ℝ≥0 m)
    (T : ℝ≥0) (H : ℝ≥0 → Ω → ℝ) : Prop where
  stronglyAdapted : StronglyAdapted 𝒢 H
  continuous_paths : ∀ᵐ ω ∂μ, ContinuousOn (fun t => H t ω) (Icc 0 T)
  bounded : ∃ c : ℝ, 0 ≤ c ∧ ∀ t ω, |H t ω| ≤ c

private theorem BoundedDriverWeight.memLp_top {𝒢 : Filtration ℝ≥0 m} {T : ℝ≥0}
    {H : ℝ≥0 → Ω → ℝ} (hH : BoundedDriverWeight (μ := μ) 𝒢 T H) (t : ℝ≥0) :
    MemLp (H t) ⊤ μ := by
  obtain ⟨c, _, hc⟩ := hH.bounded
  exact memLp_top_of_bound ((hH.stronglyAdapted t).mono (𝒢.le t)).aestronglyMeasurable c
    (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hc t ω)

private noncomputable def regularizedInverseWeight (a : ℝ≥0 → Ω → ℝ) (d : ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ := (a t ω + d)⁻¹

private theorem regularized_inverse_weight {𝒢 : Filtration ℝ≥0 m} {T : ℝ≥0}
    {a : ℝ≥0 → Ω → ℝ} {d : ℝ}
    (haa : StronglyAdapted 𝒢 a) (hac : ∀ᵐ ω ∂μ, ContinuousOn (fun t => a t ω) (Icc 0 T))
    (ha : ∀ t ω, 0 ≤ a t ω) (hd : 0 < d) :
    BoundedDriverWeight (μ := μ) 𝒢 T (regularizedInverseWeight a d) := by
  constructor
  · intro t
    let : MeasurableSpace Ω := 𝒢 t
    exact (((haa t).add stronglyMeasurable_const).measurable.inv).stronglyMeasurable
  · filter_upwards [hac] with ω hω
    exact (hω.add continuousOn_const).inv₀
      (fun t _ => (add_pos_of_nonneg_of_pos (ha t ω) hd).ne')
  · refine ⟨d⁻¹, inv_nonneg.mpr hd.le, fun t ω => ?_⟩
    have hu : 0 < a t ω + d := add_pos_of_nonneg_of_pos (ha t ω) hd
    rw [regularizedInverseWeight, abs_of_nonneg (inv_nonneg.mpr hu.le)]
    simpa only [one_div] using one_div_le_one_div_of_le hd (le_add_of_nonneg_left (ha t ω))

private theorem regularized_auxiliary_weight {𝒢 : Filtration ℝ≥0 m} {T : ℝ≥0}
    {a : ℝ≥0 → Ω → ℝ} {d : ℝ}
    (haa : StronglyAdapted 𝒢 a) (hac : ∀ᵐ ω ∂μ, ContinuousOn (fun t => a t ω) (Icc 0 T))
    (ha : ∀ t ω, 0 ≤ a t ω) (hd : 0 < d) :
    BoundedDriverWeight (μ := μ) 𝒢 T (fun t ω => d * regularizedInverseWeight a d t ω) := by
  have hH := regularized_inverse_weight haa hac ha hd
  constructor
  · intro t
    exact stronglyMeasurable_const.mul (hH.stronglyAdapted t)
  · filter_upwards [hH.continuous_paths] with ω hω
    exact continuousOn_const.mul hω
  · refine ⟨1, zero_le_one, fun t ω => ?_⟩
    have hu : 0 < a t ω + d := add_pos_of_nonneg_of_pos (ha t ω) hd
    rw [regularizedInverseWeight, abs_of_nonneg (mul_nonneg hd.le (inv_nonneg.mpr hu.le)),
      ← div_eq_mul_inv]
    exact (div_le_one hu).mpr (le_add_of_nonneg_left (ha t ω))

private structure FrozenDriverIntegral (𝒢 : Filtration ℝ≥0 m) (T : ℝ≥0)
    (X H : ℝ≥0 → Ω → ℝ) where
  process : ℝ≥0 → Ω → ℝ
  martingale : Martingale process 𝒢 μ
  square_integrable : ∀ t, MemLp (process t) 2 μ
  starts_at_zero : process 0 =ᵐ[μ] 0
  frozen : ∀ t, process t = process (min t T)
  continuous_paths : ∀ᵐ ω ∂μ, ContinuousOn (fun t => process t ω) (Iic T)
  grid_limit : ∀ t ≤ T, Tendsto (fun j => eLpNorm
    (gridIntegralProcess ((uniformDyadicGrids T).grid j)
      (fun k => H ((uniformDyadicGrids T).grid j k)) X (2 ^ j) t - process t) 2 μ) atTop (𝓝 0)

private noncomputable def frozen_driver_integral [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} (T : ℝ≥0) {X H C : ℝ≥0 → Ω → ℝ}
    (hX : Martingale X 𝒢 μ) (hX₂ : ∀ t, MemLp (X t) 2 μ)
    (hXc : ∀ᵐ ω ∂μ, Continuous (fun t => X t ω))
    (hC : Martingale (fun t => X t * X t - C t) 𝒢 μ)
    (hCi : ∀ t, Integrable (C t) μ) (hCm : ∀ s t, s ≤ t → C s ≤ᵐ[μ] C t)
    (hH : BoundedDriverWeight (μ := μ) 𝒢 T H) :
    FrozenDriverIntegral (μ := μ) 𝒢 T X H := by
  classical
  have hJ : ∃ J : ℝ≥0 → Ω → ℝ, Martingale J 𝒢 μ ∧ (∀ t, MemLp (J t) 2 μ) ∧
      (∀ᵐ ω ∂μ, ContinuousOn (fun t => J t ω) (Iic T)) ∧
      ∀ t ≤ T, Tendsto (fun j => eLpNorm (gridIntegralProcess ((uniformDyadicGrids T).grid j)
        (fun k => H ((uniformDyadicGrids T).grid j k)) X (2 ^ j) t - J t) 2 μ) atTop (𝓝 0) := by
    obtain ⟨b, hb, hbnd⟩ := hH.bounded
    obtain ⟨J, hJ, hJ₂, hJc, hJl, _⟩ := exists_continuous_integral_of_bounded_continuous_paths
      T hb hX hX₂ hXc hC hCi hCm hH.stronglyAdapted hH.memLp_top hH.continuous_paths
      (Eventually.of_forall fun ω t _ => hbnd t ω)
    exact ⟨J, hJ, hJ₂, hJc, hJl⟩
  let J := hJ.choose
  obtain ⟨hJm, hJ₂, hJc, hJl⟩ := hJ.choose_spec
  let Fz (t : ℝ≥0) := J (min t T)
  have hgrid0 (j : ℕ) :
      gridIntegralProcess ((uniformDyadicGrids T).grid j)
        (fun k => H ((uniformDyadicGrids T).grid j k)) X (2 ^ j) 0 = 0 := by
    unfold gridIntegralProcess
    rw [Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro k _
    exact stochasticStep_before (zero_le) (((uniformDyadicGrids T).grid j).monotone k.le_succ) _ _
  have hJ0 : J 0 =ᵐ[μ] 0 := by
    have hh : Tendsto (fun _ : ℕ => eLpNorm (J 0) 2 μ) atTop (𝓝 0) := by
      simpa only [hgrid0, zero_sub, eLpNorm_neg] using hJl 0 (zero_le)
    exact (eLpNorm_eq_zero_iff (by norm_num : (2 : ENNReal) ≠ 0)).mp
      (tendsto_nhds_unique tendsto_const_nhds hh)
  refine ⟨Fz, martingale_freeze_at hJm T, fun t => hJ₂ (min t T), ?_, ?_, ?_, ?_⟩
  · simpa only [Fz, min_eq_left (zero_le)] using hJ0
  · intro t
    simp only [Fz, min_assoc, min_self]
  · filter_upwards [hJc] with ω hω
    exact (hω.comp_continuous (continuous_id.min continuous_const)
      (fun t => Set.mem_Iic.mpr (min_le_right t T))).continuousOn
  · intro t ht
    simpa only [Fz, min_eq_left ht] using hJl t ht

private theorem real_time_continuous {T : ℝ≥0} {f : ℝ≥0 → ℝ}
    (h : ContinuousOn f (Icc (0 : ℝ≥0) T)) :
    ContinuousOn (fun s : ℝ => f s.toNNReal) (Icc (0 : ℝ) (T : ℝ)) := by
  apply h.comp continuous_real_toNNReal.continuousOn
  intro s hs
  refine ⟨zero_le, ?_⟩
  have hT : (s.toNNReal : ℝ) ≤ (T : ℝ) := by
    rw [Real.coe_toNNReal s hs.1]
    exact hs.2
  exact_mod_cast hT

private theorem frozen_driver_integral_pair [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} {T : ℝ≥0}
    {X Y H G C : ℝ≥0 → Ω → ℝ} {D : ℝ → Ω → ℝ}
    (hX : Martingale X 𝒢 μ) (hY : Martingale Y 𝒢 μ)
    (hX₂ : ∀ t, MemLp (X t) 2 μ) (hY₂ : ∀ t, MemLp (Y t) 2 μ)
    (hXY : Martingale (fun t => X t * Y t - C t) 𝒢 μ)
    (hH : BoundedDriverWeight (μ := μ) 𝒢 T H)
    (hG : BoundedDriverWeight (μ := μ) 𝒢 T G)
    (I : FrozenDriverIntegral (μ := μ) 𝒢 T X H)
    (J : FrozenDriverIntegral (μ := μ) 𝒢 T Y G)
    (hCeq : ∀ t ≤ T, C t =ᵐ[μ] fun ω => ∫ s in (0 : ℝ)..(t : ℝ), D s ω)
    (hDc : ∀ᵐ ω ∂μ, ContinuousOn (fun s => D s ω) (Icc (0 : ℝ) (T : ℝ)))
    (hDi : Integrable (fun ω => ∫ s in (0 : ℝ)..(T : ℝ), |D s ω|) μ) :
    ∃ Cw : ℝ≥0 → Ω → ℝ,
      (∀ t, Cw t =ᵐ[μ] driverDensityIntegral T
        (fun s ω => H s.toNNReal ω * G s.toNNReal ω * D s ω) t) ∧
      Martingale (fun t => I.process t * J.process t - Cw t) 𝒢 μ := by
  obtain ⟨c, hc, hcb⟩ := hH.bounded
  obtain ⟨d, hd, hdb⟩ := hG.bounded
  have hHG : ∀ᵐ ω ∂μ, ContinuousOn (fun s => H s ω * G s ω) (Icc 0 T) := by
    filter_upwards [hH.continuous_paths, hG.continuous_paths] with ω h₁ h₂ using h₁.mul h₂
  have hDG : ∀ᵐ ω ∂μ, IntervalIntegrable (fun s => H s.toNNReal ω * G s.toNNReal ω * D s ω)
      volume 0 (T : ℝ) := by
    filter_upwards [hHG, hDc] with ω hc hdc
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (NNReal.coe_nonneg T)]
    exact (real_time_continuous hc).mul hdc
  have hD : ∀ᵐ ω ∂μ, IntervalIntegrable (fun s => D s ω) volume 0 (T : ℝ) := by
    filter_upwards [hDc] with ω hω
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le (NNReal.coe_nonneg T)] using hω
  have hbound : ∀ᵐ ω ∂μ, ∀ t ≤ T, |H t ω * G t ω| ≤ c * d :=
    Eventually.of_forall fun ω t _ => by
      rw [abs_mul]
      exact mul_le_mul (hcb t ω) (hdb t ω) (abs_nonneg _) hc
  obtain ⟨Cw, hW, hM⟩ := continuous_integrals_compensated_product T
    (mul_nonneg hc hd) hX hY hXY hX₂ hY₂ hH.stronglyAdapted hG.stronglyAdapted hH.memLp_top hG.memLp_top
    I.martingale.stronglyAdapted J.martingale.stronglyAdapted I.square_integrable J.square_integrable
    hCeq hHG hbound hD hDG hDi I.grid_limit J.grid_limit
  refine ⟨Cw, hW, ?_⟩
  have heq : (fun t => I.process (min t T) * J.process (min t T) - Cw t) =
      (fun t => I.process t * J.process t - Cw t) := by
    funext t
    rw [← I.frozen t, ← J.frozen t]
  rwa [heq] at hM


private theorem martingale_from_ae_version [IsFiniteMeasure μ] {ι : Type*} [Preorder ι]
    {𝒢 : Filtration ι m} {X Y : ι → Ω → ℝ}
    (hX : Martingale X 𝒢 μ) (hY : StronglyAdapted 𝒢 Y)
    (he : ∀ t, X t =ᵐ[μ] Y t) : Martingale Y 𝒢 μ := by
  refine ⟨hY, fun s t hst => ?_⟩
  exact (condExp_congr_ae (he t).symm).trans ((hX.condExp_ae_eq hst).trans (he s))

private theorem regularized_pair_limits {a : ℝ} {d : ℕ → ℝ}
    (ha : 0 ≤ a) (hd : ∀ n, 0 < d n) (hl : Tendsto d atTop (𝓝 0)) :
    let p := fun n => a * (a + d n)⁻¹
    let q := fun n => d n * (a + d n)⁻¹
    (∀ n, p n ∈ Icc (0 : ℝ) 1 ∧ q n ∈ Icc (0 : ℝ) 1) ∧
      ∃ u v : ℝ, u ^ 2 + v ^ 2 = 1 ∧
        Tendsto p atTop (𝓝 u) ∧ Tendsto q atTop (𝓝 v) := by
  dsimp only
  refine ⟨?_, ?_⟩
  · intro n
    have hp := add_pos_of_nonneg_of_pos ha (hd n)
    simp only [← div_eq_mul_inv, Set.mem_Icc]
    exact ⟨⟨div_nonneg ha hp.le, (div_le_one hp).mpr (le_add_of_nonneg_right (hd n).le)⟩,
      ⟨div_nonneg (hd n).le hp.le, (div_le_one hp).mpr (le_add_of_nonneg_left ha)⟩⟩
  · by_cases ha0 : a = 0
    · subst a
      refine ⟨0, 1, by norm_num, ?_, ?_⟩
      · simpa only [zero_mul] using (tendsto_const_nhds (x := (0 : ℝ)) :
          Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
      · have he (n : ℕ) : d n * (0 + d n)⁻¹ = 1 := by simp [(hd n).ne']
        simpa only [he] using (tendsto_const_nhds (x := (1 : ℝ)) :
          Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
    · have hden : Tendsto (fun n => a + d n) atTop (𝓝 a) := by
        simpa only [add_zero] using (tendsto_const_nhds (x := a)).add hl
      refine ⟨1, 0, by norm_num, ?_, ?_⟩
      · have h := (tendsto_const_nhds (x := a)).div hden ha0
        change Tendsto (fun n => a / (a + d n)) atTop (𝓝 (a / a)) at h
        simpa only [div_eq_mul_inv, mul_inv_cancel₀ ha0] using h
      · have h := hl.div hden ha0
        change Tendsto (fun n => d n / (a + d n)) atTop (𝓝 (0 / a)) at h
        simpa only [zero_div, div_eq_mul_inv, zero_mul] using h


private theorem gridIntegralProcess_unit (grid : ℕ →o ℝ≥0)
    (X : ℝ≥0 → Ω → ℝ) (n : ℕ) (t : ℝ≥0) :
    gridIntegralProcess grid (fun _ _ => (1 : ℝ)) X n t =
      X (min t (grid n)) - X (min t (grid 0)) := by
  induction n with
  | zero => simp [gridIntegralProcess_zero]
  | succ n ih =>
    rw [gridIntegralProcess_succ, Pi.add_apply, ih, stochasticStep]
    ext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, one_mul]
    ring

private theorem unit_driver_weight (𝒢 : Filtration ℝ≥0 m) (T : ℝ≥0) :
    BoundedDriverWeight (μ := μ) 𝒢 T (fun _ _ => (1 : ℝ)) :=
  ⟨fun _ => stronglyMeasurable_const, Eventually.of_forall fun _ => continuousOn_const,
    ⟨1, zero_le_one, fun _ _ => by norm_num⟩⟩

private def unit_frozen_driver_integral [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} (T : ℝ≥0) {N : ℝ≥0 → Ω → ℝ}
    (hN : Martingale N 𝒢 μ) (hN₂ : ∀ t, MemLp (N t) 2 μ)
    (hNc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => N t ω) (Iic T))
    (hN₀ : N 0 =ᵐ[μ] 0) :
    FrozenDriverIntegral (μ := μ) 𝒢 T N (fun _ _ => (1 : ℝ)) := by
  refine ⟨fun t => N (min t T), martingale_freeze_at hN T, fun t => hN₂ (min t T),
    ?_, ?_, ?_, ?_⟩
  · simpa only [min_eq_left (zero_le)] using hN₀
  · intro t
    rw [min_assoc, min_self]
  · filter_upwards [hNc] with ω hω
    exact (hω.comp_continuous (continuous_id.min continuous_const)
      (fun t => Set.mem_Iic.mpr (min_le_right t T))).continuousOn
  · intro t ht
    have he (j : ℕ) :
        eLpNorm (gridIntegralProcess ((uniformDyadicGrids T).grid j)
          (fun _ _ => (1 : ℝ)) N (2 ^ j) t - N (min t T)) 2 μ = 0 := by
      rw [gridIntegralProcess_unit, uniform_dyadic_terminal_vertex, uniform_dyadic_first_vertex,
        min_eq_right (zero_le)]
      have h : N (min t T) - N 0 - N (min t T) =ᵐ[μ] (0 : Ω → ℝ) := by
        filter_upwards [hN₀] with ω hω
        simp only [Pi.sub_apply, hω, Pi.zero_apply, sub_zero, sub_self]
      rw [eLpNorm_congr_ae h, eLpNorm_zero]
    simpa only [he] using (tendsto_const_nhds (x := (0 : ENNReal)) :
      Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))


/-- Construct the normalized common-driver candidate on a supplied
filtered space with an orthogonal auxiliary martingale. The construction
uses the actual dyadic integrals against the two drivers at every positive
regularization level and preserves the unit bracket in the limit. -/
theorem exists_normalized_driver [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} (T : ℝ≥0) {S W C a : ℝ≥0 → Ω → ℝ}
    (hS : Martingale S 𝒢 μ) (hW : Martingale W 𝒢 μ)
    (hS₂ : ∀ t, MemLp (S t) 2 μ) (hW₂ : ∀ t, MemLp (W t) 2 μ)
    (hSc : ∀ᵐ ω ∂μ, Continuous (fun t => S t ω))
    (hWc : ∀ᵐ ω ∂μ, Continuous (fun t => W t ω))
    (hSsq : Martingale (fun t => S t * S t - C t) 𝒢 μ)
    (hWsq : Martingale (fun t ω => W t ω * W t ω - ((min t T : ℝ≥0) : ℝ)) 𝒢 μ)
    (hSW : Martingale (fun t => S t * W t) 𝒢 μ)
    (hCi : ∀ t, Integrable (C t) μ) (hCm : ∀ s t, s ≤ t → C s ≤ᵐ[μ] C t)
    (hCeq : ∀ᵐ ω ∂μ, ∀ t ≤ T, C t ω = ∫ s in (0 : ℝ)..(t : ℝ), (a s.toNNReal ω) ^ 2)
    (hDi : Integrable (fun ω => ∫ s in (0 : ℝ)..(T : ℝ), (a s.toNNReal ω) ^ 2) μ)
    (haa : StronglyAdapted 𝒢 a) (hac : ∀ᵐ ω ∂μ, ContinuousOn (fun t => a t ω) (Icc 0 T))
    (ha : ∀ t ω, 0 ≤ a t ω) :
    ∃ B : ℝ≥0 → Ω → ℝ, Martingale B 𝒢 μ ∧ (∀ t, MemLp (B t) 2 μ) ∧
      (B 0 =ᵐ[μ] 0) ∧ (∀ᵐ ω ∂μ, Continuous (fun t => B t ω)) ∧
      Martingale (fun t ω => B t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) 𝒢 μ ∧
      ∀ (N Csn b : ℝ≥0 → Ω → ℝ),
        Martingale N 𝒢 μ → (∀ t, MemLp (N t) 2 μ) →
        (∀ᵐ ω ∂μ, ContinuousOn (fun t => N t ω) (Iic T)) → (N 0 =ᵐ[μ] 0) →
        Martingale (fun t => S t * N t - Csn t) 𝒢 μ →
        Martingale (fun t => W t * N t) 𝒢 μ →
        (∀ᵐ ω ∂μ, ∀ t ≤ T, Csn t ω =
          ∫ s in (0 : ℝ)..(t : ℝ), a s.toNNReal ω * b s.toNNReal ω) →
        (∀ᵐ ω ∂μ, ContinuousOn (fun t => b t ω) (Icc 0 T)) →
        (∀ᵐ ω ∂μ, ∀ t ≤ T, a t ω = 0 → b t ω = 0) →
        Integrable (fun ω => ∫ s in (0 : ℝ)..(T : ℝ), |a s.toNNReal ω * b s.toNNReal ω|) μ →
        Integrable (fun ω => ∫ s in (0 : ℝ)..(T : ℝ), |b s.toNNReal ω|) μ →
        ∃ Cb : ℝ≥0 → Ω → ℝ,
          (∀ t, Cb t =ᵐ[μ] driverDensityIntegral T (fun s ω => b s.toNNReal ω) t) ∧
          Martingale (fun t => B t * N (min t T) - Cb t) 𝒢 μ := by
  classical
  let d (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹
  have hd (n : ℕ) : 0 < d n := by dsimp [d]; positivity
  have hdzero : Tendsto d atTop (𝓝 0) := by
    have h := tendsto_atTop_mono (g := fun n : ℕ => (n : ℝ) + 1)
      (fun _ => le_add_of_nonneg_right zero_le_one) tendsto_natCast_atTop_atTop
    exact tendsto_inv_atTop_zero.comp h
  let H (n : ℕ) := regularizedInverseWeight a (d n)
  let G (n : ℕ) := fun t ω => d n * H n t ω
  let K (t : ℝ≥0) : Ω → ℝ := fun _ => ((min t T : ℝ≥0) : ℝ)
  let D (s : ℝ) (ω : Ω) : ℝ := (a s.toNNReal ω) ^ 2
  have hH (n : ℕ) : BoundedDriverWeight (μ := μ) 𝒢 T (H n) :=
    regularized_inverse_weight haa hac ha (hd n)
  have hG (n : ℕ) : BoundedDriverWeight (μ := μ) 𝒢 T (G n) :=
    regularized_auxiliary_weight haa hac ha (hd n)
  have hWsq' : Martingale (fun t => W t * W t - K t) 𝒢 μ := hWsq
  have hSW' : Martingale (fun t => S t * W t - (0 : Ω → ℝ)) 𝒢 μ := by
    simpa only [sub_zero] using hSW
  let L (n : ℕ) := frozen_driver_integral T hS hS₂ hSc hSsq hCi hCm (hH n)
  let R (n : ℕ) := frozen_driver_integral T hW hW₂ hWc hWsq'
    (fun _ => integrable_const _) (fun s t hst => Eventually.of_forall fun _ => by
      change ((min s T : ℝ≥0) : ℝ) ≤ ((min t T : ℝ≥0) : ℝ)
      exact_mod_cast min_le_min_right T hst) (hG n)
  let Bn (n : ℕ) := (L n).process + (R n).process
  let p (n : ℕ) (s : ℝ) (ω : Ω) := a s.toNNReal ω * H n s.toNNReal ω
  let q (n : ℕ) (s : ℝ) (ω : Ω) := G n s.toNNReal ω
  have hDc : ∀ᵐ ω ∂μ, ContinuousOn (fun s => D s ω) (Icc (0 : ℝ) (T : ℝ)) := by
    filter_upwards [hac] with ω hω using (real_time_continuous hω).pow 2
  have hmW : ∀ t ≤ T, K t =ᵐ[μ] fun _ => ∫ _ in (0 : ℝ)..(t : ℝ), (1 : ℝ) :=
    fun t ht => Eventually.of_forall fun _ => by
      change ((min t T : ℝ≥0) : ℝ) = ∫ _ in (0 : ℝ)..(t : ℝ), (1 : ℝ)
      rw [min_eq_left ht]
      simp
  have h0W : ∀ t ≤ T, (0 : Ω → ℝ) =ᵐ[μ] fun _ => ∫ _ in (0 : ℝ)..(t : ℝ), (0 : ℝ) :=
    fun _ _ => Eventually.of_forall fun _ => by simp
  have hmix (n k : ℕ) : Martingale (fun t => (L n).process t * (R k).process t) 𝒢 μ := by
    obtain ⟨Csw, hCe, hm⟩ := frozen_driver_integral_pair hS hW hS₂ hW₂ hSW'
      (hH n) (hG k) (L n) (R k) h0W
      (Eventually.of_forall fun _ => continuousOn_const)
      (integrable_const _)
    refine martingale_from_ae_version hm
      ((L n).martingale.stronglyAdapted.mul (R k).martingale.stronglyAdapted) (fun t => ?_)
    filter_upwards [hCe t] with ω hω
    simp only [Pi.sub_apply, hω, driverDensityIntegral, mul_zero, intervalIntegral.integral_zero, sub_zero]
  have hpairs (n k : ℕ) : ∃ Q : ℝ≥0 → Ω → ℝ,
      Martingale (fun t => Bn n t * Bn k t - Q t) 𝒢 μ ∧
      ∀ t, Q t =ᵐ[μ] driverDensityIntegral T (driverPairDensity p q n k) t := by
    obtain ⟨Cs, hCs, hMs⟩ := frozen_driver_integral_pair hS hS hS₂ hS₂ hSsq
      (hH n) (hH k) (L n) (L k) (fun t ht => hCeq.mono fun _ h => h t ht) hDc (by
        simpa only [D, abs_of_nonneg (sq_nonneg (_ : ℝ))] using hDi)
    obtain ⟨Cw, hCw, hMw⟩ := frozen_driver_integral_pair hW hW hW₂ hW₂ hWsq'
      (hG n) (hG k) (R n) (R k) hmW (Eventually.of_forall fun _ => continuousOn_const)
      (integrable_const _)
    refine ⟨Cs + Cw, ?_, fun t => ?_⟩
    · convert (((hMs.add hMw).add (hmix n k)).add (hmix k n)) using 1
      ext t ω
      simp only [Bn, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
      ring
    · filter_upwards [hCs t, hCw t, (hH n).continuous_paths, (hH k).continuous_paths,
        (hG n).continuous_paths, (hG k).continuous_paths, hDc] with ω hs hw h₁ h₂ h₃ h₄ hd'
      let r : ℝ := ((min t T : ℝ≥0) : ℝ)
      have hr : 0 ≤ r := NNReal.coe_nonneg _
      have hrT : r ≤ (T : ℝ) := by exact_mod_cast min_le_right t T
      have hi (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (0 : ℝ) (T : ℝ))) :
          IntervalIntegrable f volume (0 : ℝ) r := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hr]
        exact hf.mono (Icc_subset_Icc le_rfl hrT)
      have hIs : IntervalIntegrable
          (fun s => H n s.toNNReal ω * H k s.toNNReal ω * a s.toNNReal ω ^ 2) volume 0 r :=
        hi _ (((real_time_continuous h₁).mul (real_time_continuous h₂)).mul hd')
      have hIw : IntervalIntegrable
          (fun s => G n s.toNNReal ω * G k s.toNNReal ω * 1) volume 0 r :=
        hi _ (((real_time_continuous h₃).mul (real_time_continuous h₄)).mul
          (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) _))
      change Cs t ω + Cw t ω = _
      rw [hs, hw]
      simp only [driverDensityIntegral]
      rw [← intervalIntegral.integral_add hIs hIw]
      congr 1
      funext s
      simp only [driverPairDensity, p, q, mul_one]
      ring
  choose Q hQ hQeq using hpairs
  have hWgt : ∀ᵐ ω ∂μ,
      (∀ n, ContinuousOn (fun s => p n s ω) (Icc 0 (T : ℝ)) ∧
        ContinuousOn (fun s => q n s ω) (Icc 0 (T : ℝ))) ∧
      ∀ s ∈ Icc (0 : ℝ) (T : ℝ),
        (∀ n, p n s ω ∈ Icc (0 : ℝ) 1 ∧ q n s ω ∈ Icc (0 : ℝ) 1) ∧
        ∃ u v : ℝ, u ^ 2 + v ^ 2 = 1 ∧
          Tendsto (fun n => p n s ω) atTop (𝓝 u) ∧
          Tendsto (fun n => q n s ω) atTop (𝓝 v) := by
    filter_upwards [hac, ae_all_iff.mpr (fun n => (hH n).continuous_paths),
      ae_all_iff.mpr (fun n => (hG n).continuous_paths)] with ω hω hs hw
    refine ⟨fun n => ⟨(real_time_continuous hω).mul (real_time_continuous (hs n)),
      real_time_continuous (hw n)⟩, fun s _ => ?_⟩
    exact regularized_pair_limits (ha s.toNNReal ω) hd hdzero
  have hBn (n : ℕ) : Martingale (Bn n) 𝒢 μ := (L n).martingale.add (R n).martingale
  have hBn₂ (n : ℕ) (t : ℝ≥0) : MemLp (Bn n t) 2 μ :=
    ((L n).square_integrable t).add ((R n).square_integrable t)
  have hBn0 (n : ℕ) : Bn n 0 =ᵐ[μ] 0 := by
    filter_upwards [(L n).starts_at_zero, (R n).starts_at_zero] with ω h₁ h₂
    simp only [Bn, Pi.add_apply, h₁, h₂, Pi.zero_apply, add_zero]
  have hBnf (n : ℕ) (t : ℝ≥0) : Bn n t = Bn n (min t T) := by
    change (L n).process t + (R n).process t = (L n).process (min t T) + (R n).process (min t T)
    rw [← (L n).frozen t, ← (R n).frozen t]
  have hBnc : ∀ᵐ ω ∂μ, ∀ n, ContinuousOn (fun t => Bn n t ω) (Iic T) := by
    filter_upwards [ae_all_iff.mpr (fun n => (L n).continuous_paths),
      ae_all_iff.mpr (fun n => (R n).continuous_paths)] with ω h₁ h₂ n
    exact (h₁ n).add (h₂ n)
  obtain ⟨B, hB, hB₂, hB0, hBc, hBlim, hBsq⟩ :=
    continuous_driver_of_pairwise_compensators T hBn hBn₂ hBn0 hBnf hBnc hQ hQeq hWgt
  refine ⟨B, hB, hB₂, hB0, hBc, hBsq, ?_⟩
  intro N Csn b hN hN₂ hNc hN₀ hSN hWN hCsn hbc hbz habi hbi
  let J := unit_frozen_driver_integral T hN hN₂ hNc hN₀
  let Db (s : ℝ) (ω : Ω) := b s.toNNReal ω
  let Dsn (s : ℝ) (ω : Ω) := a s.toNNReal ω * Db s ω
  let Dn (n : ℕ) (s : ℝ) (ω : Ω) := p n s ω * Db s ω
  have hDsnc : ∀ᵐ ω ∂μ, ContinuousOn (fun s => Dsn s ω) (Icc (0 : ℝ) T) := by
    filter_upwards [hac, hbc] with ω h₁ h₂
    exact (real_time_continuous h₁).mul (real_time_continuous h₂)
  have hWN' : Martingale (fun t => W t * N t - (0 : Ω → ℝ)) 𝒢 μ := by
    simpa only [sub_zero] using hWN
  have hCN (n : ℕ) : ∃ Cbn : ℝ≥0 → Ω → ℝ,
      (∀ t, Cbn t =ᵐ[μ] driverDensityIntegral T (Dn n) t) ∧
      Martingale (fun t => Bn n t * J.process t - Cbn t) 𝒢 μ := by
    obtain ⟨Cx, hCe, hmx⟩ := frozen_driver_integral_pair hS hN hS₂ hN₂ hSN
      (hH n) (unit_driver_weight 𝒢 T) (L n) J (fun t ht => hCsn.mono fun _ h => h t ht) hDsnc habi
    obtain ⟨Cy, hCye, hmy⟩ := frozen_driver_integral_pair hW hN hW₂ hN₂ hWN'
      (hG n) (unit_driver_weight 𝒢 T) (R n) J h0W
      (Eventually.of_forall fun _ => continuousOn_const) (integrable_const _)
    have hmy' : Martingale (fun t => (R n).process t * J.process t) 𝒢 μ := by
      refine martingale_from_ae_version hmy
        ((R n).martingale.stronglyAdapted.mul J.martingale.stronglyAdapted) (fun t => ?_)
      filter_upwards [hCye t] with ω hω
      simp only [Pi.sub_apply, hω, driverDensityIntegral, mul_zero, intervalIntegral.integral_zero, sub_zero]
    refine ⟨Cx, fun t => ?_, ?_⟩
    · have heq : (fun s ω => H n s.toNNReal ω * (1 : ℝ) * Dsn s ω) = Dn n := by
        funext s ω
        simp only [Dn, p, Dsn, mul_one]
        ring
      rw [heq] at hCe
      exact hCe t
    · convert hmx.add hmy' using 1
      ext t ω
      simp only [Bn, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
      ring
  choose Cbn hCbne hCbnm using hCN
  have hCbna (n : ℕ) : StronglyAdapted 𝒢 (Cbn n) :=
    adapted_compensator_of_compensated_product (hBn n).stronglyAdapted J.martingale.stronglyAdapted (hCbnm n)
  have hCbni (n : ℕ) (t : ℝ≥0) : Integrable (Cbn n t) μ := by
    have hh : Integrable (Bn n t * J.process t) μ :=
      ((hBn₂ n t).mul (J.square_integrable t) : MemLp (Bn n t * J.process t) 1 μ).integrable le_rfl
    simpa only [sub_sub_cancel] using hh.sub ((hCbnm n).integrable t)
  have hDn : ∀ᵐ ω ∂μ, ContinuousOn (fun s => Db s ω) (Icc (0 : ℝ) T) ∧
      (∀ n, ContinuousOn (fun s => Dn n s ω) (Icc (0 : ℝ) T)) ∧
      ∀ s ∈ Icc (0 : ℝ) (T : ℝ), (∀ n, |Dn n s ω| ≤ |Db s ω|) ∧
        Tendsto (fun n => Dn n s ω) atTop (𝓝 (Db s ω)) := by
    filter_upwards [hbc, hbz, hWgt] with ω hbω hz hw
    have hc : ContinuousOn (fun s => Db s ω) (Icc (0 : ℝ) T) := real_time_continuous hbω
    refine ⟨hc, fun n => (hw.1 n).1.mul hc, fun s hs => ⟨fun n => ?_, ?_⟩⟩
    · have hp := ((hw.2 s hs).1 n).1
      change |p n s ω * Db s ω| ≤ |Db s ω|
      rw [abs_mul, abs_of_nonneg hp.1]
      exact mul_le_of_le_one_left (abs_nonneg _) hp.2
    · by_cases hzero : a s.toNNReal ω = 0
      · have hT : s.toNNReal ≤ T := by
          have hh : (s.toNNReal : ℝ) ≤ (T : ℝ) := by
            rw [Real.coe_toNNReal s hs.1]; exact hs.2
          exact_mod_cast hh
        have he : Db s ω = 0 := hz _ hT hzero
        simp only [Dn, he, mul_zero]
        exact tendsto_const_nhds
      · let u : ℝ := a s.toNNReal ω
        have hu : u ≠ 0 := hzero
        have hden : Tendsto (fun n => u + d n) atTop (𝓝 u) := by
          simpa only [add_zero] using (tendsto_const_nhds (x := u)).add hdzero
        have hp : Tendsto (fun n => p n s ω) atTop (𝓝 1) := by
          have he : (fun n => p n s ω) = fun n => u / (u + d n) := by
            funext n
            exact (div_eq_mul_inv _ _).symm
          rw [he]
          have h := (tendsto_const_nhds (x := u)).div hden hu
          change Tendsto (fun n => u / (u + d n)) atTop (𝓝 (u / u)) at h
          simpa only [div_self hu] using h
        have h := hp.mul (tendsto_const_nhds (x := Db s ω))
        change Tendsto (fun n => p n s ω * Db s ω) atTop (𝓝 (1 * Db s ω)) at h
        simpa only [Dn, one_mul] using h
  obtain ⟨Cb, hCba, hCbi, hCbe, hCbl⟩ :=
    driver_compensator_of_dominated_density_limit T hCbna hCbni hCbne hbi hDn
  have hCbm := compensated_product_martingale_of_limits
    hB.stronglyAdapted J.martingale.stronglyAdapted hCba hB₂ J.square_integrable hBn₂
    (fun _ t => J.square_integrable t) hCbi hCbni hCbnm hBlim
    (fun t => by simpa only [sub_self, eLpNorm_zero] using
      (tendsto_const_nhds (x := (0 : ENNReal)) : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0)))
    hCbl
  exact ⟨Cb, hCbe, hCbm⟩

/-- Identify a martingale with the integral of its amplitude against a
unit-clock driver. The conclusion takes the dyadic limit at each bounded
cutoff and then removes that cutoff in L². -/
theorem recover_martingale_from_driver [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} (T : ℝ≥0) {B M A C b : ℝ≥0 → Ω → ℝ}
    (hB : Martingale B 𝒢 μ) (hM : Martingale M 𝒢 μ)
    (hB₂ : ∀ t, MemLp (B t) 2 μ) (hM₂ : ∀ t, MemLp (M t) 2 μ)
    (hBc : ∀ᵐ ω ∂μ, Continuous (fun t => B t ω))
    (hMc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => M t ω) (Iic T))
    (hM₀ : M 0 =ᵐ[μ] 0)
    (hBsq : Martingale (fun t ω => B t ω ^ 2 - ((min t T : ℝ≥0) : ℝ)) 𝒢 μ)
    (hMsq : Martingale (fun t => M t * M t - A t) 𝒢 μ)
    (hBM : Martingale (fun t => B t * M t - C t) 𝒢 μ)
    (hAe : ∀ᵐ ω ∂μ, ∀ t ≤ T,
      A t ω = ∫ s in (0 : ℝ)..(t : ℝ), (b s.toNNReal ω) ^ 2)
    (hCe : ∀ t ≤ T, C t =ᵐ[μ] fun ω => ∫ s in (0 : ℝ)..(t : ℝ), b s.toNNReal ω)
    (henergy : Integrable (fun ω => ∫ s in (0 : ℝ)..(T : ℝ), (b s.toNNReal ω) ^ 2) μ)
    (hmass : Integrable (fun ω => ∫ s in (0 : ℝ)..(T : ℝ), |b s.toNNReal ω|) μ)
    (hba : StronglyAdapted 𝒢 b) (hbc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => b t ω) (Icc 0 T))
    (hb : ∀ t ω, 0 ≤ b t ω) :
    ∃ J : ℕ → ℝ≥0 → Ω → ℝ, (∀ n, Martingale (J n) 𝒢 μ) ∧
      (∀ n t, MemLp (J n t) 2 μ) ∧
      (∀ (n : ℕ) t, t ≤ T → Tendsto (fun j => eLpNorm
        (gridIntegralProcess ((uniformDyadicGrids T).grid j)
          (fun k ω => min (b ((uniformDyadicGrids T).grid j k) ω) (n : ℝ))
          B (2 ^ j) t - J n t) 2 μ) atTop (𝓝 0)) ∧
      ∀ t, Tendsto (fun n => eLpNorm (J n t - M (min t T)) 2 μ) atTop (𝓝 0) := by
  classical
  let H (n : ℕ) (t : ℝ≥0) (ω : Ω) := min (b t ω) (n : ℝ)
  have hH (n : ℕ) : BoundedDriverWeight (μ := μ) 𝒢 T (H n) := by
    constructor
    · intro t
      let : MeasurableSpace Ω := 𝒢 t
      exact ((hba t).measurable.min measurable_const).stronglyMeasurable
    · exact hbc.mono (fun _ h =>
        continuous_min.comp_continuousOn (h.prodMk continuousOn_const))
    · refine ⟨n, Nat.cast_nonneg n, fun t ω => ?_⟩
      exact (abs_of_nonneg (le_min (hb t ω) (Nat.cast_nonneg n))).trans_le (min_le_right _ _)
  let K (t : ℝ≥0) : Ω → ℝ := fun _ => ((min t T : ℝ≥0) : ℝ)
  have hBs : Martingale (fun t => B t * B t - K t) 𝒢 μ := by
    simpa only [Pi.mul_def, Pi.sub_def, K, pow_two] using hBsq
  have hKi : ∀ t, Integrable (K t) μ := fun _ => integrable_const _
  have hKe : ∀ t ≤ T, K t =ᵐ[μ] fun _ => ∫ s in (0 : ℝ)..(t : ℝ), (1 : ℝ) :=
    fun t ht => Eventually.of_forall fun _ => by
      change ((min t T : ℝ≥0) : ℝ) = ∫ _ in (0 : ℝ)..(t : ℝ), (1 : ℝ)
      rw [min_eq_left ht]
      simp
  let I (n : ℕ) := frozen_driver_integral T hB hB₂ hBc hBs hKi
    (fun s t hst => Eventually.of_forall fun ω => by
      change ((min s T : ℝ≥0) : ℝ) ≤ ((min t T : ℝ≥0) : ℝ)
      exact_mod_cast min_le_min_right T hst) (hH n)
  let F := unit_frozen_driver_integral T hM hM₂ hMc hM₀
  let D (s : ℝ) (ω : Ω) := b s.toNNReal ω
  have hDc : ∀ᵐ ω ∂μ, ContinuousOn (fun s => D s ω) (Icc (0 : ℝ) (T : ℝ)) :=
    hbc.mono (fun _ => real_time_continuous)
  have hKmass : Integrable (fun ω : Ω => ∫ s in (0 : ℝ)..(T : ℝ), |(1 : ℝ)|) μ :=
    integrable_const _
  have hJ (n : ℕ) := frozen_driver_integral_pair hB hB hB₂ hB₂ hBs (hH n) (hH n)
    (I n) (I n) hKe (Eventually.of_forall fun _ => continuousOn_const) hKmass
  have hJF (n : ℕ) := frozen_driver_integral_pair hB hM hB₂ hM₂ hBM (hH n) (unit_driver_weight 𝒢 T)
    (I n) F hCe hDc hmass
  choose L hLe hLm using hJ
  choose R hRe hRm using hJF
  let E (n : ℕ) (t : ℝ≥0) : Ω → ℝ := L n t + A (min t T) - (R n t + R n t)
  have hEprod (n : ℕ) :
      Martingale (fun t => ((I n).process t - F.process t) *
        ((I n).process t - F.process t) - E n t) 𝒢 μ := by
    convert ((hLm n).add (martingale_freeze_at hMsq T)).sub ((hRm n).add (hRm n)) using 1
    ext t ω
    simp only [F, unit_frozen_driver_integral, E, Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
    ring
  have hEeq (n : ℕ) (t : ℝ≥0) : E n t =ᵐ[μ] driverDensityIntegral T
      (fun s ω => (H n s.toNNReal ω - D s ω) ^ 2) t := by
    filter_upwards [hLe n t, hRe n t, hAe, hDc] with ω hL hR hA hcont
    have hi : ∀ {f : ℝ → ℝ}, ContinuousOn f (Icc (0 : ℝ) T) →
        IntervalIntegrable f volume 0 ((min t T : ℝ≥0) : ℝ) := by
      intro f hf
      exact ContinuousOn.intervalIntegrable_of_Icc (NNReal.coe_nonneg (min t T))
        (hf.mono (Icc_subset_Icc le_rfl (by exact_mod_cast min_le_right t T)))
    have hc : ContinuousOn (fun s => H n s.toNNReal ω) (Icc (0 : ℝ) (T : ℝ)) :=
      continuous_min.comp_continuousOn (hcont.prodMk continuousOn_const)
    simp only [E, Pi.add_apply, Pi.sub_apply, hL, hR, hA _ (min_le_right t T),
      driverDensityIntegral, mul_one]
    change (_ + (∫ s in (0 : ℝ)..((min t T : ℝ≥0) : ℝ), D s ω ^ 2) - _) = _
    have hHH : IntervalIntegrable (fun s => H n s.toNNReal ω * H n s.toNNReal ω)
        volume 0 (min t T : ℝ≥0) := hi (hc.mul hc)
    have hDD : IntervalIntegrable (fun s => D s ω ^ 2)
        volume 0 (min t T : ℝ≥0) := hi (hcont.pow 2)
    have hHD : IntervalIntegrable (fun s => H n s.toNNReal ω * b s.toNNReal ω)
        volume 0 (min t T : ℝ≥0) := hi (hc.mul hcont)
    rw [← intervalIntegral.integral_add hHH hDD,
      ← intervalIntegral.integral_add hHD hHD,
      ← intervalIntegral.integral_sub (hHH.add hDD) (hHD.add hHD)]
    congr 1
    funext s
    simp only [D]
    ring
  have hEi (n : ℕ) (t : ℝ≥0) : Integrable (E n t) μ := by
    have hx := ((I n).square_integrable t).sub (F.square_integrable t)
    have hs := (hx.mul hx : MemLp (_ * _) 1 μ).integrable le_rfl
    simpa only [sub_sub_cancel] using hs.sub ((hEprod n).integrable t)
  have hlim (t : ℝ≥0) : Tendsto (fun n => ∫ ω, E n t ω ∂μ) atTop (𝓝 0) := by
    let mass (ω : Ω) := ∫ s in (0 : ℝ)..(T : ℝ), D s ω ^ 2
    have hbound (n : ℕ) : ∀ᵐ ω ∂μ, ‖E n t ω‖ ≤ mass ω := by
      filter_upwards [hEeq n t, hDc] with ω he hc
      have hr : (0 : ℝ) ≤ ((min t T : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
      have hrT : ((min t T : ℝ≥0) : ℝ) ≤ (T : ℝ) := by exact_mod_cast min_le_right t T
      have hsub := Icc_subset_Icc (show (0 : ℝ) ≤ 0 from le_rfl) hrT
      have hf : ContinuousOn (fun s => (H n s.toNNReal ω - D s ω) ^ 2) (Icc (0 : ℝ) T) :=
        ((continuous_min.comp_continuousOn (hc.prodMk continuousOn_const)).sub hc).pow 2
      have hfull : IntervalIntegrable (fun s => D s ω ^ 2) volume 0 (T : ℝ) :=
        (hc.pow 2).intervalIntegrable_of_Icc (NNReal.coe_nonneg T)
      rw [he, driverDensityIntegral, Real.norm_of_nonneg
        (intervalIntegral.integral_nonneg hr (fun _ _ => sq_nonneg _))]
      refine (intervalIntegral.integral_mono_on hr
        ((hf.mono hsub).intervalIntegrable_of_Icc hr)
        ((hc.pow 2).mono hsub |>.intervalIntegrable_of_Icc hr) (fun s _ => ?_)).trans ?_
      · have h₀ : 0 ≤ H n s.toNNReal ω := le_min (hb _ _) (Nat.cast_nonneg n)
        have h₁ : H n s.toNNReal ω ≤ D s ω := min_le_left _ _
        rw [← neg_sq]
        exact pow_le_pow_left₀ (by linarith) (by linarith) 2
      · exact intervalIntegral.integral_mono_interval le_rfl hr hrT
          (Eventually.of_forall fun _ => sq_nonneg _) hfull
    have hpoint : ∀ᵐ ω ∂μ, Tendsto (fun n => E n t ω) atTop (𝓝 ((0 : Ω → ℝ) ω)) := by
      filter_upwards [ae_all_iff.mpr (fun n => hEeq n t), hDc] with ω he hc
      obtain ⟨c, hcap⟩ := isCompact_Icc.bddAbove_image hc
      have hlarge : ∀ᶠ n : ℕ in atTop, c ≤ (n : ℝ) :=
        (tendsto_atTop.1 tendsto_natCast_atTop_atTop) c
      refine (tendsto_const_nhds (x := (0 : ℝ))).congr' (hlarge.mono fun n hn => ?_)
      change (0 : ℝ) = E n t ω
      rw [he n, driverDensityIntegral, intervalIntegral.integral_of_le (NNReal.coe_nonneg _)]
      symm
      calc
        _ = ∫ s in Ioc (0 : ℝ) ((min t T : ℝ≥0) : ℝ), (0 : ℝ) := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro s hs
          have hmem : s ∈ Icc (0 : ℝ) (T : ℝ) :=
            ⟨hs.1.le, hs.2.trans (by exact_mod_cast min_le_right t T)⟩
          have hle := (hcap (mem_image_of_mem _ hmem)).trans hn
          simp [H, D, min_eq_left hle]
        _ = 0 := integral_zero _ _
    simpa only [Pi.zero_apply, integral_zero] using
      tendsto_integral_of_dominated_convergence mass (fun n => (hEi n t).aestronglyMeasurable)
        henergy hbound hpoint
  refine ⟨fun n => (I n).process, fun n => (I n).martingale,
    fun n => (I n).square_integrable, fun n => (I n).grid_limit, fun t => ?_⟩
  let f (n : ℕ) : Ω → ℝ := (I n).process t - F.process t
  have hf (n : ℕ) : MemLp (f n) 2 μ := ((I n).square_integrable t).sub (F.square_integrable t)
  have he (n : ℕ) : (∫ ω, f n ω ^ 2 ∂μ) = ∫ ω, E n t ω ∂μ := by
    have h₀ : (I n).process 0 - F.process 0 =ᵐ[μ] 0 := by
      filter_upwards [(I n).starts_at_zero, F.starts_at_zero] with ω h₁ h₂
      simp only [Pi.sub_apply, Pi.zero_apply, h₁, h₂, sub_self]
    have hC₀ : E n 0 =ᵐ[μ] 0 := by
      filter_upwards [hEeq n 0] with ω hω
      simp [hω, driverDensityIntegral]
    have hz : (((I n).process 0 - F.process 0) * ((I n).process 0 - F.process 0) - E n 0)
        =ᵐ[μ] (0 : Ω → ℝ) := by
      filter_upwards [h₀, hC₀] with ω h₁ h₂
      rw [Pi.sub_apply, Pi.mul_apply, h₁, h₂]
      simp
    have hh := (hEprod n).setIntegral_eq (show (0 : ℝ≥0) ≤ t from zero_le)
      (MeasurableSet.univ : MeasurableSet[𝒢 0] Set.univ)
    simp only [Measure.restrict_univ] at hh
    rw [integral_congr_ae hz] at hh
    simp only [Pi.zero_apply, integral_zero] at hh
    have hsq : Integrable (f n * f n) μ :=
      ((hf n).mul (hf n) : MemLp (f n * f n) 1 μ).integrable le_rfl
    change (0 : ℝ) = ∫ ω, (f n * f n) ω - E n t ω ∂μ at hh
    rw [integral_sub hsq (hEi n t)] at hh
    simpa only [Pi.mul_apply, pow_two] using sub_eq_zero.mp hh.symm
  have hnorm (n : ℕ) : eLpNorm (f n) 2 μ = ENNReal.ofReal (Real.sqrt (∫ ω, E n t ω ∂μ)) := by
    have hs := norm_toLp_two_sq (hf n)
    rw [he n] at hs
    have hs' := congrArg Real.sqrt hs
    rw [Real.sqrt_sq (norm_nonneg _)] at hs'
    rw [← hs', Lp.norm_toLp,
      ENNReal.ofReal_toReal ((hf n).eLpNorm_ne_top)]
  have h := (ENNReal.continuous_ofReal.tendsto (Real.sqrt 0)).comp
    ((Real.continuous_sqrt.tendsto 0).comp (hlim t))
  change Tendsto (fun n => eLpNorm (f n) 2 μ) atTop (𝓝 0)
  simpa only [Function.comp_def, Real.sqrt_zero, ENNReal.ofReal_zero, ← hnorm] using h


end RoughHeston

#print axioms RoughHeston.exists_normalized_driver
#print axioms RoughHeston.recover_martingale_from_driver
