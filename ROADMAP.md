# Roadmap to Theorem 1.1

The proof constructs two variance paths on one filtered probability space, driven by the same Brownian motion. The event that the paths differ somewhere before or at the horizon has strictly positive probability. The variance theorem is `RoughHeston.theorem1_1`. The full result, `RoughHeston.theorem1_1_full`, also constructs both asset prices with the same price Brownian motion for every admissible correlation. [Variance statement](TheoremStatement.lean) · [Variance proof](han/RoughHestonVarianceTheorem.lean) · [Full statement and proof](han/RoughHestonFullTheorem.lean)

## How separation is obtained

Write $b=\kappa\theta$. In the approximation, $X^\varepsilon$ is the sum of an initial component and immigrant clusters. The companion variance $Y^\varepsilon$ receives constant immigration at rate $b$. The superscript indexes an approximation with pulse mass $\varepsilon$. The limits $X$ and $Y$ both solve the original constant-immigration equation.

1. **Construct the two approximating paths together.** An immigrant arrives every $\varepsilon/b$ time units. Each arrival contributes a pulse of duration $\varepsilon^{1/\alpha}$ and mass $\varepsilon$. The declaration `exists_explicitLebesguePulseLaw` constructs one law for the clusters and the companion, including the martingale and compensated-product identities that specify how their noises are coupled. [Pulse schedule and existence](mathfin/ExplicitLebesguePulseLaw.lean) · [Fixed-mesh law](mathfin/FractionalFixedMeshLaw.lean)

2. **Estimate the companion near zero.** At an interior birth time $\tau$, the event $Y^\varepsilon_\tau=0$ has probability bounded below uniformly in the mesh. Conditional on that event, the probability that $Y^\varepsilon_{\tau+s}>0$ is at most $D s^\eta$ for small $s$, with $\eta>0$. An affine transform and a fractional differential comparison bound the contribution of the companion’s history before $\tau$. The two probability estimates are combined in `uniform_explicitLebesgueCompanion_zero_boundary`. [Caputo comparison](mathfin/CaputoMeanComparison.lean) · [Uniform boundary estimate](han/UniformCompanionSecondMoments.lean)

3. **Separate a single immigrant from the companion.** Work on the event $Y^\varepsilon_\tau=0$, retaining the joint history up to birth. First size-bias by the focal cluster’s mass. Han’s stopped Girsanov theorem then removes the drift induced in the companion driver, up to the stopping times that bound the cluster and the accumulated drift energy. Returning to the original law gives a probability of at least $c\varepsilon$ that, at age $r$, the focal variance is at least $\ell$ and the companion variance is zero. The positive constants $r,c,\ell$ are chosen before the mesh. [First change of measure](han/RawFocalFirstTilt.lean) · [Stopped Girsanov on the birth event](han/RawBirthTracePulseStoppedLaw.lean) · [Single-birth estimate](han/PhysicalSingleBirthTraceSeparation.lean) · [Original-law bound](han/RoughHestonVarianceTheorem.lean)

4. **Count births and pass to the limit.** There are of order $1/\varepsilon$ interior births. First- and second-moment estimates for the number of successful births yield $p_*>0$, independent of the fine mesh, such that $\mathbb P(\|X^\varepsilon-Y^\varepsilon\|_\infty\geq\ell)\geq p_*$. Here the norm is the supremum over $[0,T]$. Moment estimates give tightness of the joint path laws. The gap event is closed in the uniform topology, so the same lower bound holds along a weak limit. [Counting estimate](mathfin/UniformExplicitMeshSeparation.lean) · [From single births to the uniform gap](han/ExplicitLebesgueBirthEndpoint.lean) · [Limit on continuous path space](han/ExplicitLebesgueMeshLimit.lean)

## How the limiting noises are identified

5. **Recover one Brownian motion for both variances.** Martingale and compensated-product identities pass to the limit. The variance martingales have quadratic variation densities $\sigma^2 X$ and $\sigma^2Y$ and joint covariation density $\sigma^2\sqrt{XY}$. Normalizing their sum when at least one variance is positive and using independent Brownian noise when both variances vanish gives one Brownian driver in the joint filtration. The fractional convolution identity recovers both variance equations. The equivalence theorem identifies their dyadic stochastic convolutions with the predictable Brownian Itô integrals. [Common-driver construction](CommonDriverConstruction.lean) · [Application to the limiting law](han/ExplicitLebesgueMeshLimit.lean) · [Itô equivalence](mathfin/HestonBrownianItoEquivalence.lean)

6. **Construct the prices.** On an independent enlargement, take $W=\rho B+\sqrt{1-\rho^2}\,B^\perp$. For each $V\in\{X,Y\}$ the stochastic exponential gives a positive price from the same $S_0$ satisfying $dS_t=S_t\sqrt{V_t}\,dW_t$. The construction includes $\rho=\pm1$. The variance separation from step 4 therefore distinguishes the two price–variance solutions. [Correlated Brownian pair](mathfin/CorrelatedRegularVariancePair.lean) · [Price equation](han/HestonPriceSDE.lean) · [Assembly of the full theorem](han/RoughHestonFullTheorem.lean)

## Checking the declarations

After building the project, the following imports the full proof and prints the axioms of both results. The verification record includes the kernel replay and the hashes of the two theorem files. [Build and verification guide](VERIFICATION.md) · [Recorded kernel replay](han/theorem-kernel-check.txt)

```lean
import RoughHestonFullTheorem

example : RoughHeston.Theorem1_1 := RoughHeston.theorem1_1
example : RoughHeston.FullRoughHestonTheorem := RoughHeston.theorem1_1_full

#print axioms RoughHeston.theorem1_1
#print axioms RoughHeston.theorem1_1_full
```
