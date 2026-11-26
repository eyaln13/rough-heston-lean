import BirthTraceMartingaleShift

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Interval Topology

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 m} {b H T : ℝ≥0} {A : Set Ω} {J C d : ℝ≥0 → Ω → ℝ}

/-- A fixed birth mass plus the focal increments is a martingale on the
conditioned age clock, with a constant value after that horizon. -/
theorem focalMass_birthTrace_martingale
    (hA : MeasurableSet[F b] A) (hp : 0 < P A) (hJ : Martingale J F P) (ε : ℝ) :
    Martingale (fun t (ω : A) => J (b+min t H) ω - J b ω + ε)
      (birthTraceFiltration F b A) (birthTraceLaw P A) := by
  let Q := birthTraceLaw P A
  let G := birthTraceFiltration F b A
  have : IsProbabilityMeasure Q := birthTraceLaw_isProbability (F.le b A hA) hp
  let J' (t : ℝ≥0) (ω : A) := J (b+t) ω
  have hJ' : Martingale J' G Q := martingale_birthTrace hA hp hJ
  have hJ₀ : StronglyMeasurable[G ⊥] (fun ω : A => J b ω) := by
    have h := hJ'.stronglyMeasurable 0
    change StronglyMeasurable[G 0] (fun ω : A => J (b+0) ω) at h
    rwa [add_zero] at h
  have hJI : Integrable (fun ω : A => J b ω) Q := by
    have h := hJ'.integrable 0
    change Integrable (fun ω : A => J (b+0) ω) Q at h
    rwa [add_zero] at h
  have h := ((martingale_freeze_at hJ' H).sub (martingale_const_fun G Q hJ₀ hJI)).add (martingale_const G Q ε)
  exact h

/-- Shifting the focal square compensator preserves the bracket after
centering at birth and adding the immigration mass. -/
theorem focalMass_birthTrace_sq_compensator
    (hA : MeasurableSet[F b] A) (hp : 0 < P A) (hBH : b+H ≤ T)
    (hJ : Martingale J F P) (hJ₂ : ∀ t, MemLp (J t) 2 P)
    (hJclock : Martingale (fun t => J t * J t - C t) F P)
    (hd : IsStronglyPredictable F d)
    (hInt : ∀ᵐ ω ∂P, IntervalIntegrable (fun r : ℝ => d r.toNNReal ω) volume 0 (T : ℝ))
    (hCeq : ∀ t ≤ T, C t =ᵐ[P] fun ω => ∫ r in 0..(t : ℝ), d r.toNNReal ω) (ε : ℝ) :
    let Z (t : ℝ≥0) (ω : A) := J (b+min t H) ω - J b ω + ε
    Martingale (fun t (ω : A) => Z t ω ^ 2 -
      ∫ r, d (b+r) ω ∂hestonTimeMeasure (min t H)) (birthTraceFiltration F b A) (birthTraceLaw P A) := by
  let Q := birthTraceLaw P A
  let G := birthTraceFiltration F b A
  have : IsProbabilityMeasure Q := birthTraceLaw_isProbability (F.le b A hA) hp
  have hBase := martingale_compensatedProduct_birthTrace_density hA hp hBH hJ hJ hJ₂ hJ₂ hJclock hd hInt hCeq 0
  have hCent := focalMass_birthTrace_martingale (H := H) hA hp hJ 0
  convert ((hBase.add (hCent.smul (2*ε))).add (martingale_const G Q (ε^2))) using 1
  ext t ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_zero]
  ring

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.focalMass_birthTrace_martingale
#print axioms RoughHeston.GirsanovPort.focalMass_birthTrace_sq_compensator
