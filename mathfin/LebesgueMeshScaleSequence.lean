import ExplicitLebesguePulseLaw

/-! A sequence of admissible deterministic pulse masses tending to zero. -/

open Filter Set
open scoped Topology

namespace RoughHeston

/-- Choose any positive mass threshold for the separation estimates.
The literal rectangular pulse fits inside its mesh cell along the sequence. -/
theorem exists_lebesgueMesh_mass_sequence {α b εbar : ℝ}
    (hα : 0 < α) (hα' : α < 1) (hb : 0 < b) (hεbar : 0 < εbar) :
    ∃ ε : ℕ → ℝ, (∀ n, 0 < ε n) ∧ (∀ n, ε n ≤ 1) ∧ (∀ n, ε n ≤ εbar) ∧
      Tendsto ε atTop (𝓝 0) ∧ (∀ n, lebesguePulseDuration α (ε n) ≤ ε n/b) := by
  let g (n : ℕ) := 1/((n:ℝ)+1)
  have hg₀ : Tendsto g atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hgp (n : ℕ) : 0 < g n := by dsimp [g]; positivity
  have hg₁ (n : ℕ) : g n ≤ 1 := by
    dsimp [g]
    exact (div_le_one₀ (by positivity : 0 < (n:ℝ)+1)).2 (by linarith [show (0:ℝ) ≤ (n:ℝ) from Nat.cast_nonneg n])
  have hExp : 0 < 1/α-1 := by
    exact sub_pos.mpr ((lt_div_iff₀ hα).2 (by simpa only [one_mul] using hα'))
  have hK := (hg₀.rpow_const_nhds_zero hExp).const_mul b
  have hlim : Tendsto (fun n => b*(g n)^(1/α-1)) atTop (𝓝 0) := by simpa only [mul_zero] using hK
  have hEv : ∀ᶠ n in atTop, g n ≤ εbar ∧ b*(g n)^(1/α-1) ≤ 1 :=
    ((hg₀.eventually (Iio_mem_nhds hεbar)).mono fun _ h => h.le).and
      ((hlim.eventually (Iio_mem_nhds zero_lt_one)).mono fun _ h => h.le)
  obtain ⟨N,hN⟩ := eventually_atTop.1 hEv
  let ε (n : ℕ) := g (n+N)
  have hAtTop : Tendsto (fun n : ℕ => n+N) atTop atTop := by
    apply tendsto_atTop.2
    intro k
    exact eventually_atTop.2 ⟨k,fun n hn => hn.trans (Nat.le_add_right n N)⟩
  refine ⟨ε, fun n => hgp _, fun n => hg₁ _, fun n => (hN _ (Nat.le_add_left _ _)).1,
    hg₀.comp hAtTop, ?_⟩
  intro n
  have hn := (hN (n+N) (Nat.le_add_left _ _)).2
  have hε : 0 < ε n := hgp _
  have he : lebesguePulseDuration α (ε n) = ε n*(ε n)^(1/α-1) := by
    unfold lebesguePulseDuration
    calc
      _ = (ε n)^(1+(1/α-1)) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hε, Real.rpow_one]
  rw [he, le_div_iff₀ hb]
  have h := mul_le_mul_of_nonneg_right hn hε.le
  dsimp only [ε] at h ⊢
  nlinarith only [h,show g (n+N)*g (n+N)^(1/α-1)*b =
    b*g (n+N)^(1/α-1)*g (n+N) by ring]

#print axioms RoughHeston.exists_lebesgueMesh_mass_sequence

end RoughHeston
