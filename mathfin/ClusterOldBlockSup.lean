import ClusterPhysicalSupBound

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston

/-- The immigration mass survives in the physical supremum bound. Both the
constant and moment order are fixed before choosing a probability space. -/
theorem cluster_old_block_sup {p : ℕ} (hp : 0<p) {γ β α A C : ℝ} (hγ : 1<γ)
    (hβ : 0≤β) (hA : 0≤A) (hC : 0≤C) (hpβ : α≤(p:ℝ)*β) :
    ∃ K : ℝ, 0≤K ∧ ∀ {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (F : Filtration ℝ≥0 m) (U : ℝ≥0 → Ω → ℝ)
      (I : ℝ≥0 → ℝ) {T : ℝ≥0} {S d ε : ℝ},
      0<T → 0<d → d≤S → ε=d^α → (T:ℝ)≤2*S →
      StronglyAdapted F U → (∀ ω, ContinuousOn (fun t => U t ω) (Icc 0 T)) →
      ContinuousOn I (Icc 0 T) → (∀ ω, U 0 ω=I 0) →
      (∀ t≤T, I t≤A*d^β) →
      (∀ a b : ℝ≥0, a<b → b≤T →
        let Y (ω : Ω) := (U b ω-I b)-(U a ω-I a)
        Integrable (fun ω => ‖Y ω‖^p) P ∧
          (∫ ω, ‖Y ω‖^p ∂P) ≤ C*(ε*S^((p:ℝ)*β-α-γ)*((b:ℝ)-(a:ℝ))^γ)) →
      ∃ W : Ω → ℝ, Measurable[F T] W ∧ (∀ ω,0≤W ω) ∧
        (∀ t≤T, ∀ ω,U t ω≤W ω) ∧ Integrable (fun ω => W ω^p) P ∧
        (∫ ω, W ω^p ∂P)≤K*ε*S^((p:ℝ)*β-α) := by
  obtain ⟨K,hK,hsup⟩ := physical_sup_power_of_increments hp hγ
  refine ⟨2^(p-1)*(K*C*2^γ+A^p),by positivity,?_⟩
  intro Ω m P inst F U I T S d ε hT hd hdS hε hTS hUa hUc hIc h0 hpeak hinc
  let N (t : ℝ≥0) (ω : Ω) := U t ω-I t
  have hN (t : ℝ≥0) : Measurable[F t] (N t) := (hUa t).measurable.sub measurable_const
  have hS := hd.trans_le hdS
  have hε₀ : 0≤ε := hε ▸ Real.rpow_nonneg hd.le _
  let c := C*ε*S^((p:ℝ)*β-α-γ)
  have hc : 0≤c := by dsimp [c]; positivity
  obtain ⟨W,hWm,hWM,hW,hdom,hi,hE⟩ := hsup hT P N (fun t => (hN t).mono (F.le t) le_rfl)
    (fun ω => (hUc ω).sub hIc) (ae_of_all _ fun ω => sub_eq_zero.mpr (h0 ω)) c hc
    (fun a b hab hbT => ⟨(hinc a b hab hbT).1,(hinc a b hab hbT).2.trans_eq (by dsimp [c]; ring)⟩)
  let J := A*d^β
  have hJ : 0≤J := by dsimp [J]; positivity
  have hscale : S^((p:ℝ)*β-α-γ)*S^γ=S^((p:ℝ)*β-α) := by
    rw [← Real.rpow_add hS]; congr 1; ring
  have hnoise : (∫ ω,W ω^p ∂P) ≤ (K*C*2^γ)*ε*S^((p:ℝ)*β-α) := by
    refine hE.trans ?_
    have ht := Real.rpow_le_rpow T.coe_nonneg hTS (by linarith : 0≤γ)
    rw [Real.mul_rpow (by norm_num : 0≤(2:ℝ)) hS.le] at ht
    calc
      K*c*(T:ℝ)^γ ≤ K*c*((2:ℝ)^γ*S^γ) := by gcongr
      _ = (K*C*2^γ)*ε*(S^((p:ℝ)*β-α-γ)*S^γ) := by dsimp [c];ring
      _ = _ := by rw [hscale]
  have hdet : J^p≤A^p*ε*S^((p:ℝ)*β-α) := by
    have he : (d^β)^p=d^α*d^((p:ℝ)*β-α) := by
      rw [← Real.rpow_mul_natCast hd.le,← Real.rpow_add hd]
      congr 1; ring
    dsimp [J]; rw [mul_pow,he,hε,← mul_assoc]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hd.le hdS (sub_nonneg.mpr hpβ))
      (mul_nonneg (pow_nonneg hA _) (Real.rpow_nonneg hd.le _))
  have hwM : Measurable[F T] W := hWM _ (fun t ht => (hN t).mono (F.mono ht) le_rfl)
  refine ⟨fun ω => W ω+J,hwM.add measurable_const,fun ω => add_nonneg (hW ω) hJ,?_,?_,?_⟩
  · intro t ht ω
    have h := (le_abs_self (N t ω)).trans (hdom t ht ω)
    dsimp [N] at h
    linarith [hpeak t ht]
  all_goals
    have hbd (ω : Ω) := add_pow_le (hW ω) hJ p
    have him : Integrable (fun ω => (2:ℝ)^(p-1)*(W ω^p+J^p)) P :=
      (hi.add (integrable_const _)).const_mul _
    have him' : Integrable (fun ω => (W ω+J)^p) P := him.mono'
      ((hWm.add measurable_const).pow_const p).aestronglyMeasurable
      (ae_of_all P (fun ω => (Real.norm_of_nonneg (pow_nonneg (add_nonneg (hW ω) hJ) _)).le.trans (hbd ω)))
  · exact him'
  · refine (integral_mono_ae him' him (ae_of_all _ hbd)).trans ?_
    rw [integral_const_mul,integral_add hi (integrable_const _),integral_const,probReal_univ,one_smul]
    exact (mul_le_mul_of_nonneg_left (add_le_add hnoise hdet) (by positivity)).trans_eq (by ring)

#print axioms cluster_old_block_sup

end RoughHeston
