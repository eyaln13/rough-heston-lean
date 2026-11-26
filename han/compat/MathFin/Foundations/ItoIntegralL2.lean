module
public import MathFin.Probability.Brownian.Ito.ItoIntegralL2
public import MathFin.Probability.Analysis.LpMulIsometry

@[expose] public section
open MeasureTheory
open scoped ENNReal

namespace MathFin.ItoIntegralL2

theorem lp_two_norm_sq {α : Type*} {mα : MeasurableSpace α} {ν : Measure α}
    (g : Lp ℝ 2 ν) : ‖g‖ ^ 2 = ∫ a, (g a) ^ 2 ∂ν :=
  MathFin.lp_two_norm_sq g

end MathFin.ItoIntegralL2
