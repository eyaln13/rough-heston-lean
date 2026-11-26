import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

open Set
open scoped NNReal

namespace RoughHeston

/-- Interior birth indices for Lebesgue immigration with spacing ε/b. -/
noncomputable def interiorPulseBirths (T b ε : ℝ) : Finset ℕ :=
  Finset.Icc ⌈(T/3)/(ε/b)⌉₊ ⌊(2*T/3)/(ε/b)⌋₊

theorem mem_interiorPulseBirths {T b ε : ℝ} (hT : 0≤T) (hb : 0<b) (hε : 0<ε)
    {i : ℕ} :
    i∈interiorPulseBirths T b ε ↔ (i:ℝ)*(ε/b)∈Icc (T/3) (2*T/3) := by
  have hd : 0<ε/b := div_pos hε hb
  rw [interiorPulseBirths,Finset.mem_Icc,Nat.ceil_le,Nat.le_floor_iff (by positivity : 0≤(2*T/3)/(ε/b))]
  exact and_congr (div_le_iff₀ hd) (le_div_iff₀ hd)

theorem interiorPulseBirths_subset_full {T b ε : ℝ} (hT : 0≤T) (hb : 0<b) (hε : 0<ε) :
    interiorPulseBirths T b ε ⊆ Finset.range (⌊T/(ε/b)⌋₊+1) := by
  intro i hi
  have hd : 0<ε/b := div_pos hε hb
  have hep := (mem_interiorPulseBirths hT hb hε).mp hi
  have hit : (i:ℝ)*(ε/b)≤T := hep.2.trans (by linarith)
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_floor_iff (by positivity)).mpr
    ((le_div_iff₀ hd).mpr hit)))

/-- A uniform cardinality estimate, in physical immigration mass units. -/
theorem interiorPulseBirths_card_mass {T b ε : ℝ} (hT : 0<T) (hb : 0<b) (hε : 0<ε)
    (hsmall : ε≤b*T/12) :
    b*T/4≤((interiorPulseBirths T b ε).card:ℝ)*ε ∧
      ((interiorPulseBirths T b ε).card:ℝ)*ε≤b*T := by
  let d := ε/b
  let l := T/3/d
  let u := (2*T/3)/d
  have hd : 0<d := div_pos hε hb
  have hl : 0≤l := by dsimp [l]; positivity
  have hu : 0≤u := by dsimp [u]; positivity
  have hdT : d≤T/12 := by
    exact (div_le_iff₀ hb).mpr (hsmall.trans_eq (by ring))
  have hlu : l+2≤u := by
    apply (le_div_iff₀ hd).mpr
    have hld : l*d=T/3 := div_mul_cancel₀ _ hd.ne'
    linarith only [hld,hdT,hT,show (l+2)*d=l*d+2*d by ring]
  let m := ⌈l⌉₊
  let n := ⌊u⌋₊
  have hm₁ : l≤(m:ℝ) := Nat.le_ceil _
  have hm₂ : (m:ℝ)<l+1 := Nat.ceil_lt_add_one hl
  have hn₁ : (n:ℝ)≤u := Nat.floor_le hu
  have hn₂ : u<(n:ℝ)+1 := Nat.lt_floor_add_one _
  have hmn : m≤n := by
    exact_mod_cast (show (m:ℝ)≤(n:ℝ) by linarith)
  have ha : ((interiorPulseBirths T b ε).card:ℝ)=(n:ℝ)+1-(m:ℝ) := by
    change ((Finset.Icc m n).card:ℝ)=_
    rw [Nat.card_Icc,Nat.cast_sub (hmn.trans (Nat.le_succ _)),Nat.cast_succ]
  have hlow : u-l-1≤(n:ℝ)+1-(m:ℝ) := by linarith
  have hup : (n:ℝ)+1-(m:ℝ)≤u-l+1 := by linarith
  have hluE : (u-l)*ε=b*T/3 := by
    dsimp [u,l,d]
    field_simp [hε.ne',hb.ne']
    ring
  have heps : ε≤b*T/12 := hsmall
  rw [ha]
  constructor
  · have h := mul_le_mul_of_nonneg_right hlow hε.le
    linarith only [h,hluE,heps,show (u-l-1)*ε=(u-l)*ε-ε by ring]
  · have h := mul_le_mul_of_nonneg_right hup hε.le
    linarith only [h,hluE,heps,show (u-l+1)*ε=(u-l)*ε+ε by ring,
      show 0≤b*T from mul_nonneg hb.le hT.le]

#print axioms interiorPulseBirths_card_mass

end RoughHeston
