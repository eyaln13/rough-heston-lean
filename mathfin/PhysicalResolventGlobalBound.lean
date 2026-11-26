import FractionalResolventProfile
import FractionalResolventIdentity

open MeasureTheory Set
open scoped NNReal ENNReal

namespace RoughHeston

/-- The globally defined second-kind resolvent admits a finite fractional
envelope on every compact horizon. Near-zero positivity is unnecessary. -/
theorem fractionalSecondKindResolvent_finite_kernel_bound {α κ T : ℝ}
    (hα : 0<α) (hT : 0≤T) :
    ∃ D : ℝ,0≤D ∧ ∀ r∈Ioc (0:ℝ) T,
      |fractionalSecondKindResolvent α κ r|≤D*fractionalK α r := by
  let A := max 1 (|κ| * T^α)
  have hA : 1≤A := le_max_left _ _
  have hAn : 0≤A := zero_le_one.trans hA
  obtain ⟨C,hC,hLip⟩ := fractionalResolventProfile_lipschitz_on hα hA
  let D := Real.Gamma α*(C*A+1/Real.Gamma α)
  have hΓ := Real.Gamma_pos_of_pos hα
  have hD : 0≤D :=
    mul_nonneg hΓ.le (add_nonneg (mul_nonneg hC hAn) (one_div_nonneg.mpr hΓ.le))
  refine ⟨D,hD,?_⟩
  intro r hr
  let x := -κ*r^α
  have hx : |x|≤A := by
    dsimp [x]
    rw [abs_mul,abs_neg,abs_of_nonneg (Real.rpow_nonneg hr.1.le _)]
    exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr.1.le hr.2 hα.le)
      (abs_nonneg _)).trans (le_max_right _ _)
  have hp := hLip x 0 hx (by simpa only [abs_zero] using hAn)
  rw [fractionalResolventProfile_zero,sub_zero] at hp
  have hp' : |fractionalResolventProfile α x|≤C*A+1/Real.Gamma α := by
    calc
      _ = |(fractionalResolventProfile α x-1/Real.Gamma α)+1/Real.Gamma α| := by
        rw [sub_add_cancel]
      _ ≤ |fractionalResolventProfile α x-1/Real.Gamma α|+|1/Real.Gamma α| := abs_add_le _ _
      _ ≤ C*A+1/Real.Gamma α := by
        rw [abs_of_nonneg (one_div_nonneg.mpr hΓ.le)]
        exact add_le_add (hp.trans (mul_le_mul_of_nonneg_left hx hC)) le_rfl
  rw [fractionalSecondKindResolvent_factor hr.1,abs_mul,abs_of_nonneg (Real.rpow_nonneg hr.1.le _)]
  change r^(α-1)*|fractionalResolventProfile α x|≤D*fractionalK α r
  rw [fractionalK,ite_eq_right (not_le.mpr hr.1)]
  exact (mul_le_mul_of_nonneg_left hp' (Real.rpow_nonneg hr.1.le _)).trans_eq (by
    dsimp [D]
    field_simp)

theorem measurable_physical_fractionalSecondKindResolvent (α κ : ℝ) :
    Measurable (fractionalSecondKindResolvent α κ) :=
  Measurable.tsum fun n => (fractionalK_measurable (((n:ℝ)+1)*α)).const_mul ((-κ)^n)

#print axioms fractionalSecondKindResolvent_finite_kernel_bound
#print axioms measurable_physical_fractionalSecondKindResolvent

end RoughHeston
