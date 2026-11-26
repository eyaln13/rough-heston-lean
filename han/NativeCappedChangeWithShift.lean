import SHEStochastic.ScalarGirsanovCappedTransport

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace RoughHeston
namespace GirsanovPort

open SHEStochastic

variable {Ω C ι : Type*} [m : MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 m} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}

local notation "ν" => FiniteScalarIto.inputMeasure F μ H

/-- Compose the library's capped law and raw Itô transport while
retaining the almost-sure identity of the continuous family with the
actual shift. The measure and the joint filtration are the same in
both conclusions. -/
theorem native_cap_change_with_shift (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (hnull : SHE.NullCompleteFiltration.ContainsNullSets F μ)
    (u : Lp C 2 ν) (δ : ℝ) (hδ : 0 ≤ δ) (hcap : ∀ᵐ ω ∂μ, NativeEnergy.energy u ω ≤ δ) :
    let Q := NativeGirsanovTilt.measure P e u
    ∃ (_ : IsProbabilityMeasure Q) (R : FiniteScalarIto.Family F Q H ι),
      Q ≪ μ ∧ μ ≪ Q ∧
      (∀ i, ∀ᵐ ω ∂μ, ∀ t, R.W i t ω =
        ScalarGirsanovCoordinateShift.shift P e (NativeInputEquiv.inverse F μ H u) i t ω) ∧
      ∀ (v : Lp C 2 ν) (w : Lp C 2 (FiniteScalarIto.inputMeasure F Q H)),
        v =ᵐ[ν] w → FiniteCylindricalIto.rawIntegral R.toCoordinates e w =ᵐ[Q]
          (fun ω => FiniteCylindricalIto.rawIntegral P.toCoordinates e v ω + NativeCrossEnergy.cross v u ω) := by
  dsimp only
  let Q := NativeGirsanovTilt.measure P e u
  let hQ : IsProbabilityMeasure Q := NativeGirsanovTilt.probability P e u δ hδ hcap
  let U := NativeInputEquiv.inverse F μ H u
  have hU : FiniteCylindricalIto.processTransport U = u := NativeInputEquiv.transport_inverse F μ H u
  have hbracket : ∀ᵐ ω ∂μ, SHE.StochasticExponential.bracket F μ H U ω ≤ δ := by
    have he := NativeBoundedNovikov.energy_transport_ae U
    rw [hU] at he
    filter_upwards [he, hcap] with ω heω hcapω
    exact heω ▸ hcapω
  have hQeq : NativeChangedCoordinates.changedMeasure P e U = Q := by
    have he := NativeGirsanovRows.measure_transport P e U
    rw [hU] at he
    exact he.symm
  have hAC : Q ≪ μ := withDensity_absolutelyContinuous _ _
  have hrev : μ ≪ Q := by
    apply withDensity_absolutelyContinuous'
      (NativeExponential.stronglyMeasurable P e (-1) u).measurable.ennreal_ofReal.aemeasurable
    exact ae_of_all _ fun _ => ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have hlaw (n : ℕ) (a : Fin n → ι) :
      SHE.FiniteBrownianLawOn F Q H (fun i => ScalarGirsanovCoordinateShift.shift P e U (a i))
        (fun i j => if a i = a j then 1 else 0) :=
    hQeq ▸ ScalarGirsanovCoordinateShift.finite_cap P e U δ hδ hbracket n a
  obtain ⟨R, hshift⟩ := ScalarGirsanovContinuousFamily.exists_family P e U hAC hnull hlaw
  refine ⟨hQ, R, hAC, hrev, hshift, ?_⟩
  intro v w hsame
  have hagree : ScalarGirsanovIntegralTransport.Agrees P e U R.toCoordinates :=
    fun i t _ => (hshift i).mono fun _ hw => hw t
  have htransport := ScalarGirsanovIntegralTransport.integral P e U R.toCoordinates hAC hagree v w hsame
  rw [hU] at htransport
  exact htransport

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.native_cap_change_with_shift
