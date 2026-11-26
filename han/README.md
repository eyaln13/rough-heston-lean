# Stopped change of measure

`StoppedCompetitorGirsanov.lean` gives the stopped Brownian drift shift in the coupling on a given usual filtered space. Its hypotheses include the focal and total variances, the strictly positive focal mass and the Brownian motion under the birth-conditioned, size-biased law. The theorem constructs an equivalent probability law, preserves the full history at birth, shifts the driver on a single full-measure event throughout the horizon, and transports each compatible pair of square-integrable stochastic integrands. The signed correction is the physical time integral of the product with the stopped drift.

The stopping times and the sharp entropy estimate are in the main project. `StoppedTransformOccupation.lean` proves equality of the expected stopped test under the new law and its expected birth value under the old law, from the stopped stochastic representation. The original physical companion supplies this representation in the proof of the variance theorem. [Original affine point tests](RawOriginalPointTests.lean)

The first, focal change of measure identifies the shifted Brownian motion under size bias from the original compensated products. The square-energy bound comes from the entropy of the focal mass martingale. The second change removes the competitor's active drift up to the two stopping times. Together with a stopped occupation estimate this gives a quantitative lower bound for a focal burst with zero competing variance. [First tilt](FocalSizeBiasBrownian.lean) · [Competitor estimate](StoppedCompetitorSeparation.lean)

## Reproduction

The build guide gives the pinned revisions, environment, and commands for compiling the stopped Girsanov proof and replaying the two final theorems. [Reproducing the Lean proof](../REPRODUCE.md)

## Moments of the stochastic convolution

Han's scalar Burkholder–Davis–Gundy inequality applies to arbitrary predictable square-integrable rows. The bridge identifies his terminal integral and physical time measure with those used in the variance equation. For a row of the form σk(t)√Uₜ the bound retains the lower moment of U at each time inside the kernel integral. The weight k may change sign when estimating increments. [Joint Itô integral](JointItoPowerMoments.lean) · [Time-dependent moment bound](HestonKernelNoiseMoment.lean) · [Ordinary expectation and integrability](HestonRealKernelNoiseMoment.lean)

For the competitor, the affine point-test density constructed from the inverse equation has a continuous adapted path and an exact terminal value. On a stopped interval the joint Itô integral equals the difference of its endpoint and birth values. Checking the occupation estimate for the coupled model also requires applying these facts to its conditioned law and its stopped drift. [Point-test density](AffinePointPathData.lean) · [Stopped integral after birth](JointAffineStopAfterBirth.lean) · [Change of drift for the test](StoppedAffineTestTransport.lean)

## Use in the variance theorem

`RoughHeston.theorem1_1` constructs two variance solutions with a common Brownian motion. At every focal birth the capped reverse law is constructed under the birth-conditioned measure. The affine point test uses the companion's original history up to birth. The resulting single-birth probability is uniform over meshes and gives the separated weak limit. [Capped law](RawBirthTracePulseStoppedLaw.lean) · [Single-birth estimate](PhysicalSingleBirthTraceSeparation.lean) · [Unconditional variance theorem](RoughHestonVarianceTheorem.lean)


## Price equation

The full theorem uses one Brownian pair with the specified correlation for both solutions. The square-root variance integral gives the log martingale of each price. The stochastic exponential satisfies the price SDE through increasing stopping times which eventually reach the horizon on every path. [Continuous log martingale](HestonContinuousLogMartingale.lean) · [Localized price integral](LocalizedPriceExponential.lean) · [Full theorem](RoughHestonFullTheorem.lean)
