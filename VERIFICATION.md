# Verification of the rough Heston draft

Section 5 of the manuscript proves Theorem 1.1. Lean 4.35.0 verifies
the variance assertion and its consequence for the price–variance system.
The build uses MathFin at commit `cbe842dda1e71fd7173f3325971796686dbf7feb`
and its pinned mathlib at `e91b128082cc221d6432a6a5aadcd3243af8e76c`.
[Theorem and proof](han/RoughHestonFullTheorem.lean) · [Kernel and source verification record](han/theorem-kernel-check.txt) ·
[Pinned MathFin source](https://github.com/formal-applied-math/formal-mathfin/tree/cbe842dda1e71fd7173f3325971796686dbf7feb)

`TheoremStatement.lean` defines the target proposition
`RoughHeston.Theorem1_1`. It specifies the two variance solutions using
the same Brownian motion relative to the same filtration, the direct
Volterra equation, and positive probability of path separation. Lean
also checks that the integral equation gives the common initial variance.
The fractional kernel belongs to L² on bounded time intervals, and the
regularized weights converge in the L² energy norm when the target
convolution weight is square integrable.
For the mathematical argument and the Lean declarations proving each step, see the [proof roadmap](ROADMAP.md).

| Manuscript step | Lean theorem |
| --- | --- |
| Strict gap between the critical Caputo coefficient and the Riccati coefficient, and existence of an exponent in the required interval | `comparison_exponent` |
| Fractional inverse kernel identity \(K*L=1\) | `fractional_beta_integral`, `fractional_kernel_inverse` |
| Weighted occupation integral in the stopped change of measure | `occupation_cost_integral` |
| Identity covariance of the cluster noise projection | `cluster_projection` |
| Variance and covariation when the two aggregate martingales are normalized | `normalized_sum_variance`, `normalized_sum_covariation` |
| Bound on the squared drift of the competing driver | `tilt_cost_bound` |
| Uniform lower bound from the two count moments and Cauchy–Schwarz | `count_lower_bound` |
| Transfer of a uniform lower bound for a closed separation event under weak convergence | `separation_of_weak_limit` |
| Strict sign of the fractional derivative at a first zero and the resulting comparison on a compact time interval | **fractional_memory_negative_at_contact**, **fractional_first_contact_comparison** |
| Caputo inequality for the terminal power barrier, including the improper beta integral | **caputo_terminal_power_bound** |
| Measure bound for reversing the size bias and discarding the three bad events | **undo_size_bias**, **remove_bad_events**, **separation_from_tilt_bounds** |
| Second moment bound on the positive support of a random variable on a finite measure space | **second_moment_support** |
| Strictly positive probability of distinct limiting paths from uniform count moments, support inclusion and weak convergence | **weak_limit_distinct_from_count_moments** |
| Transfer of Laplace-complement bounds to positive variance occupation | **positive_probability_of_laplace_bounds** |
| Associativity on the Volterra triangle and deterministic drift inversion for a measurable L¹ input | `volterra_convolution_assoc`, `fractional_causal_kernel_inverse`, `fractional_volterra_triangle_integrable`, `fractional_volterra_inverts_drift` |

## Stochastic foundations

`StochasticFoundation.lean` uses mathlib's actual filtrations,
conditional expectations, martingales, and `MemLp` predicates. It defines
the finite stochastic sum along any deterministic ordered grid and checks
the following results on a fixed filtered space.

| Step | Lean theorem |
| --- | --- |
| Centering increments and determining their conditional covariance from the compensated product | `conditional_mean_martingale_increment`, `conditional_covariance_of_compensated_product` |
| Pulling out predictable weights and preserving the martingale property | `centered_predictable_increment`, `predictable_increment_covariance`, `grid_integral_martingale` |
| Compensated products and the covariance and Itô isometries on a grid | `compensated_running_product_martingale`, `runningSum_cross_isometry`, `grid_integral_cross_isometry`, `grid_integral_ito_isometry` |
| Refinement consistency and the difference on a common grid | `grid_integral_invariant_under_doubling`, `grid_integral_sub_weights` |
| Earlier-event tests and passage of martingale properties through timewise L¹ limits on a fixed space | `martingale_of_past_set_integrals`, `martingale_of_timewise_L1_limits` |
| Passage of compensated products when the processes converge in L² and the compensators converge in L¹ | `product_L1_limit_of_L2_limits`, `compensated_product_martingale_of_limits` |
| Vanishing at a fixed time from a square martingale, upgrading equality at countably many times, and applying both after localization | `zero_of_square_martingale`, `indistinguishable_of_ae_eq_on_dense`, `zero_of_localized_square_martingales` |

## Terminal stochastic integration

`StochasticCompletion.lean` constructs the terminal stochastic integral
as a mean-square limit for martingales admitting an integrable,
nondecreasing compensator of their square. The compensator can be random.
In particular, the code verifies that sampling an adapted integrand with
almost surely continuous paths and a deterministic uniform bound on the
interval produces convergent stochastic sums. The modulus of continuity
can depend on the sample path. A measurable envelope for the refinement
errors and dominated convergence give the required Cauchy criterion.

| Step | Lean theorem |
| --- | --- |
| Consistency and predictability after any number of dyadic refinements | `NestedDyadicGrids.integral_at_refinement`, `NestedDyadicGrids.predictable_lift` |
| Exact mean-square error as the energy of a coefficient difference on the finer grid | `dyadic_terminalLp_refinement_energy` |
| Existence and uniqueness of the terminal limit from the energy Cauchy criterion | `exists_unique_dyadic_terminal_limit` |
| Equality of limits when the energy of the difference tends to zero | `dyadic_terminal_limit_independent` |
| Passage of the Itô isometry to the terminal limit | `dyadic_terminal_limit_isometry` |
| Energy bound from an essentially bounded random envelope | `dyadic_refinement_energy_le_of_bounded_envelope` |
| Convergence for continuous bounded adapted integrands | `exists_unique_integral_of_bounded_continuous_paths` |

## Continuous martingale construction

`StochasticProcess.lean` stops each grid increment at the observation
time, so the approximating processes are continuous martingales on the
original filtration. Conditional expectation propagates terminal L²
convergence to every earlier time. The proof applies mathlib's Doob
maximal inequality on finite ordered sets of times, extends the bound
to a countable dense set, and uses Borel–Cantelli to obtain almost sure
uniform convergence of a subsequence. The limit is adapted and is a
continuous modification of the conditional-expectation martingale.

| Step | Lean theorem |
| --- | --- |
| The stopped stochastic sum is a continuous martingale | `gridIntegralProcess_martingale`, `gridIntegralProcess_continuous` |
| Terminal L² convergence gives timewise L² convergence | `martingale_limit_of_terminal_L2`, `dyadic_integral_martingale_of_terminal_limit` |
| Doob's bound on a countable set of times | `countable_martingale_maximal_ineq` |
| Construction of an adapted continuous modification | `continuous_martingale_version_of_L2_limits` |
| Continuous Itô integral for bounded adapted integrands with continuous paths | `exists_continuous_integral_of_bounded_continuous_paths` |

## Compensated products of continuous stochastic integrals

`StochasticCovariation.lean` verifies the cross-compensator for two grid
integrals on the full filtration. When the driving cross-compensator has
an integrable time density, the product of the two bounded continuous
integrands weights that density. Equality with the time integral is
needed almost surely at each fixed time. At a fixed observation time,
the grid vertices used across refinements form a countable set.
A pathwise estimate for the cell integrals and dominated convergence
give L¹ convergence of the compensators. Together with timewise
L² convergence of the stochastic sums, this proves the
compensated-product martingale identity for the limit.

| Step | Lean theorem |
| --- | --- |
| Compensated product of two weighted grid sums at every observation time | `gridIntegralProcess_compensated_product` |
| Approximation of the density integral by the weighted cell integrals | `grid_density_error`, `dyadic_density_tendsto` |
| L¹ convergence to an adapted representative of the cross-compensator | `dyadic_compensator_density_L1` |
| Compensated product of the two limiting stochastic integrals | `continuous_integrals_compensated_product` |

## Common-driver construction

`CommonDriverConstruction.lean` starts with continuous square-integrable
martingales \(S,W\) on a supplied filtration. Their square compensators have
densities \(A^2\) and \(1\) on \([0,T]\), and \(SW\) is a martingale.
For \(\delta_n=1/(n+1)\), it integrates \((A+\delta_n)^{-1}\) against
\(S\) and \(\delta_n/(A+\delta_n)\) against \(W\) using stopped dyadic
sums. It proves the compensated products between every pair of
regularization levels, including the zero mixed compensators between
the integrals against \(S\) and \(W\).

`CommonDriverLimit.lean` uses the pairwise compensators to show that
the drivers are Cauchy in terminal L². It constructs a continuous
martingale \(B\) on that filtration with \(B_0=0\) almost surely and
\(B_t^2-(t\wedge T)\) a martingale. On \(\{A=0\}\), the auxiliary
term carries the unit bracket.

The construction also checks the mixed compensators. For a test
martingale \(N\) with cross-compensator density \(Ab\) against \(S\) and zero
cross-compensator against \(W\), the limiting cross-compensator
against \(B\) has density \(b\). This uses the continuity and
integrability hypotheses in the theorem and the condition
\(b=0\) where \(A=0\). In the manuscript, \(S=M^X+M^Y\),
\(A=\sigma(\sqrt X+\sqrt Y)\), and \(b=\sigma\sqrt X\) or
\(\sigma\sqrt Y\). `RankOneCompensators.lean` derives the square and
mixed compensators of \(S\) from the three compensated products of
\(M^X,M^Y\). It derives orthogonality of \(S\) and \(W\) from the
assumed orthogonality of \(W\) to each of \(M^X,M^Y\).

The recovery step takes the bounded weights \(\min(b,n)\) against
the candidate driver \(B\). At each time the expected squared
difference between the cutoff integral and the original martingale
equals the expected time integral of \((\min(b,n)-b)^2\). The latter
goes to zero when the expected integral of \(b^2\) is finite.
Thus the dyadic cutoff integrals recover the martingale in L² on the
same filtration.

`rank_one_pair_has_common_driver` combines these steps. Given the
three original martingale compensators, the orthogonal auxiliary
martingale and the stated amplitude hypotheses, it supplies one
continuous unit-clock martingale and both amplitude-integral
representations in a single checked result.

| Step | Lean theorem |
| --- | --- |
| Derivation of the aggregate square and mixed compensators from the rank-one covariance densities | `rank_one_aggregate_compensators` |
| Regularized normalization and limiting bracket densities | `common_driver_regularized_coefficients` |
| Freezing at the horizon on the same filtration | `martingale_freeze_at` |
| Continuous driver with unit bracket from pairwise compensators and an L² limit | `continuous_driver_of_pairwise_compensators` |
| Adapted L¹ limit for a dominated cross-compensator density | `driver_compensator_of_dominated_density_limit` |
| Construction from dyadic sums and passage to the mixed compensators with each test martingale | `exists_normalized_driver` |
| Recovery of the original martingale as the L² limit of cutoff integrals against the unit-clock driver | `recover_martingale_from_driver` |
| Joint recovery of both variance martingales against one driver from the rank-one input | `rank_one_pair_has_common_driver` |
| The three compensated products give a square martingale for the difference | `difference_square_martingale_of_common_compensator` |
| The difference vanishes simultaneously at all times for continuous paths | `indistinguishable_of_common_compensator` |

## Independent enlargement and Brownian identification

`ProductFiltrationLift.lean` forms the filtration whose past at each
time is the product of the two past σ-algebras. Fubini on sections of a
past event shows that each coordinate lift is a martingale and that
the product of the two lifts is a martingale. The product identity
gives zero cross-compensator with the auxiliary Brownian coordinate.

`mathfin/CanonicalAuxiliaryDriver.lean` supplies the canonical
Brownian martingale on MathFin's path space. It is frozen at \(T\) and
its compensated square has clock \(t\wedge T\).
`mathfin/FiniteHorizonLevy.lean` identifies the Brownian modification
on the supplied filtration using exit-time localization and the
exponential martingale identity. For the modification, it suffices
that ambient measurable null sets belong to the time-zero
σ-algebra. A measurable null superset covers the exceptional paths.

`mathfin/CommonBrownianDriver.lean` converts the Lévy conclusion to
the manuscript's `IsBrownianOn` and proves that both amplitude-cutoff
representations survive the modification. For each fixed grid, the
stopped increments of the two versions agree almost surely.
`mathfin/IndependentCommonDriver.lean` combines this with the
rank-one construction on the product with the canonical Brownian
path space. It augments the product filtration with ambient measurable
null sets and uses MathFin's `condExp_sup_nulls` to preserve the
martingale identities. Given the variance martingales and their
rank-one compensators on the original space, the theorem supplies one
Brownian motion on the enlarged joint filtration and both lifted
amplitude-cutoff integrals against it.

| Step | Lean theorem |
| --- | --- |
| Lift the variance martingales and compensated products through the first projection | `martingale_prod_fst` |
| Lift the auxiliary martingale and its compensated square through the second projection | `martingale_prod_snd` |
| Establish orthogonality of martingales from separate coordinates | `martingale_prod_mul` |
| Preserve the probability of path separation on the product space | `measure_separation_prod_fst` |
| Construct the auxiliary martingale with unit clock up to the horizon | `canonical_auxiliary_driver` |
| Obtain a Brownian modification using ambient measurable null sets | `brownianOn_modification_of_measurable_nulls`, `isBrownianOn_modification_of_unit_clock` |
| Transfer both cutoff-integral identities to the Brownian modification | `HasAmplitudeCutoffIntegral.congr_driver`, `pair_has_common_brownian_of_unit_clock` |
| Obtain one Brownian motion and both recovered integrals on the augmented product space | `rank_one_pair_has_common_brownian_on_product` |

## Joint-filtration Itô integration

The finite-horizon integration space is the product of the time measure
on \((0,T]\) and the probability measure, restricted to the predictable
sigma-algebra of the supplied filtration. `JointPredictableDensity.lean`
and `JointSimpleAssembly.lean` give density of the adapted simple
processes in its L² space. The overlap formula for the two weighted
increments uses the conditional mean and compensated square on that
filtration. It gives the same double-sum formula as the squared norm
of the simple integrand. `JointItoAssembly.lean` extends the resulting
isometry to a continuous linear stochastic integral and applies
MathFin's stochastic Fubini theorem to it. [MathFin density proof](https://github.com/formal-applied-math/formal-mathfin/blob/cbe842dda1e71fd7173f3325971796686dbf7feb/MathFin/Probability/Brownian/Ito/ItoIntegralHorizonDense.lean) · [MathFin stochastic Fubini](https://github.com/formal-applied-math/formal-mathfin/blob/cbe842dda1e71fd7173f3325971796686dbf7feb/MathFin/Probability/Brownian/Ito/StochasticFubini.lean)

`ProductKernelEnergy.lean` proves square integrability of the Heston
convolution weight, given joint measurability, nonnegativity and a
uniform first-moment bound for the variance. The time measure agrees
with the one used in the predictable L² space. The endpoint has zero
mass, and the bounded cutoff weights converge in L².

| Step | Lean theorem |
| --- | --- |
| Square integrability of the shifted fractional kernel and variance weight | `heston_shifted_kernel_memLp_two`, `heston_convolution_weight_memLp_two` |
| Convergence in energy from the variance moment bound | `heston_cutoff_weight_L2_of_uniform_mean` |
| Density of adapted simple processes on the joint filtration | `dense_span_jointPredictableMeasure`, `jointSimpleAssembly_denseRange` |
| Conditional increment pairing and the overlap formula | `joint_rect_increment_pairing`, `jointSimpleAssembly_norm_sq` |
| Itô isometry and agreement with finite increment sums | `jointItoAssembly_isometry`, `jointItoIntegralCLM_norm`, `jointItoIntegralCLM_agrees` |
| Stochastic Fubini under the Bochner and representative integrability hypotheses | `jointItoIntegralCLM_fubini` |

## The fractional stochastic convolution

The predictable Heston weight and each bounded cutoff belong to the
joint L² space. The shifted kernel has the same energy as the
unshifted kernel integrated up to the observation time. A uniform
first-moment bound controls this energy for every inner time on a
fixed horizon. The uniform dyadic simple processes converge for
continuous cutoff paths. Applying the checked Itô isometry to the
inner and outer limits gives the exact definition
`IsHestonConvolutionAt` in the theorem statement. The limit is unique
up to almost sure equality at each time and is preserved under
timewise almost sure equality of the driver.

For the fractional Fubini identity, the parameter family of forward
kernel weights is strongly measurable in the fixed predictable
L² space. The L¹ estimate for the reflected inverse kernel and the
uniform L² estimate give Bochner integrability. The integrated
representative is the square-root amplitude by \(L*K_\alpha=1\).
MathFin's interchange theorem therefore gives the inverse of the
forward stochastic convolution in terminal L². Restricting the
predictable measure to a shorter time interval gives an isometric
extension by zero into the original predictable L² space. The Itô
integral agrees with the integral against the stopped driver on the
shorter interval. Thus the fixed-horizon kernel integral gives the
exact dyadic-cutoff convolution at each observation time, and the
recovered amplitude martingale agrees almost surely with the integral
of the corresponding stopped amplitude on that same space.

The forward kernel family is continuous in the predictable L² norm.
The deterministic inversion and injectivity proofs also apply to
continuous paths with values in a real Banach space, including L².
On one fixed horizon, the inverse convolution of the stochastic
convolution equals the stopped square-root integral at each earlier
time. This gives the direct variance equation in L² from the inverse
identity in L².
Once the direct equation holds almost surely at every fixed time,
the residual of the variance path defines a single version of the
stochastic convolution that satisfies the equation throughout the
interval. The proof checks that replacing the Itô convolution by
this version preserves both dyadic-cutoff limits.

| Step | Lean theorem |
| --- | --- |
| L¹ estimates for the causal kernels and the reflected inverse kernel | `fractionalK_integrableOn_Ioc`, `fractionalL_integrableOn_Ioc`, `fractionalL_reflected_integrable_hestonTimeMeasure` |
| Heston cutoff convergence in the trimmed predictable measure | `heston_cutoff_weight_L2_joint_of_uniform_mean` |
| Agreement of uniform dyadic sums with the joint Itô integral | `jointItoIntegralCLM_dyadic` |
| Exact target convolution, uniqueness and invariance under driver modification | `isHestonConvolutionAt_jointIto`, `IsHestonConvolutionAt.ae_unique`, `IsHestonConvolutionAt.congr_driver` |
| Uniform squared-energy estimate for the forward kernel family | `heston_convolution_weight_energy_le` |
| Strong measurability and Bochner integrability of the inverse-weighted family | `hestonKernelFamilyLp_stronglyMeasurable`, `integrable_fractionalL_smul_heston_family` |
| Joint integrability and integrated amplitude representative | `heston_fubini_jointIntegrable`, `heston_fubini_integrated_weight_ae` |
| Fractional stochastic Fubini in terminal L² | `heston_fractionalVolterra_fubini` |
| Injectivity of the inverse convolution on continuous real paths | `fractionalL_zero_implies_path_zero` |
| Continuity of the forward kernel family in the predictable energy space | `hestonKernelFamilyLp_continuous` |
| Drift inversion and injectivity in a real Banach space | `fractional_volterra_smul_inverts_drift`, `fractionalL_smul_zero_implies_path_zero` |
| Restriction of the predictable measure and isometric extension by zero | `jointPredictableMeasure_eq_restrict`, `jointBandExtend` |
| Compatibility of the joint Itô integral across horizons | `jointItoIntegralCLM_cross_horizon` |
| The fixed-horizon Itô map satisfies the exact convolution and amplitude limits at shorter observation times | `isHestonConvolutionAt_jointIto_fixed_horizon`, `HasAmplitudeCutoffIntegral.ae_eq_jointIto_fixed_horizon` |
| The inverse identity in L² gives the forward equation in L² | `fixedHestonConvolutionLp_fractional_inverse`, `heston_L2_of_inverse` |
| Recover sample-path time integration from the Bochner L² path | `coeFn_integral_weighted_L2_path_ae` |
| Obtain the simultaneous direct equation from its fixed-time versions | `isHestonVarianceSolution_of_fixed_time_equations` |
| Direct rough Heston variance solution from the inverse identity in L² | `isHestonVarianceSolution_of_L2_inverse` |
| Convert the sample-path inverse identity and the recovered amplitude integral into the inverse identity in L² | `heston_L2_inverse_of_samplewise` |
| Two direct variance solutions with one Brownian motion from separated inverse martingale data | `separated_heston_of_inverse_martingales` |

## Martingale identities under weak convergence

Stopping a continuous canonical path is continuous for the uniform
topology. The natural filtration is the pullback of the Borel σ-algebra
by this stopped path. Testing against bounded continuous functions of
the stopped path determines the martingale identities on all measurable
past events. Uniform second moments give convergence of unbounded
continuous test integrals by truncation. Deterministic errors from the
immigration input disappear in the tests for the recovered martingales
and their compensated products. The inverse-kernel integral used to
recover each variance martingale and the time integrals of continuous
covariance densities are continuous functions of the canonical path
and measurable with respect to its natural past. This gives the
limiting martingale and compensated-product identities under the
assumed approximating identities, moment bounds, and weak convergence.
The closed event of a fixed uniform gap transfers a positive lower
probability bound to the limiting paths.

| Step | Lean theorem |
| --- | --- |
| Continuity of stopping a path and identification of its natural past | `continuous_canonicalStoppedPath`, `canonicalPathNaturalFiltration_eq_comap_stopped` |
| Convergence of continuous test integrals under uniform second moments | `tendsto_integral_of_weak_of_uniform_sq_moment'` |
| Bounded continuous tests imply the identity on all measurable past events | `setIntegral_preimage_eq_of_boundedContinuous_tests` |
| Approximate bounded continuous tests give martingales under the limiting law | `martingale_of_weak_limit_of_boundedContinuous_past_tests` |
| Vanishing test errors from deterministic shifts in martingales and compensated products | `tendsto_boundedContinuous_past_tests_of_deterministic_shift`, `tendsto_boundedContinuous_compensated_product_past_tests_of_deterministic_shift` |
| Passage of the canonical inverse martingales and compensated products to the limiting law | `canonicalVarianceMartingale_of_weak_limit`, `canonicalVarianceCompensatedProduct_of_weak_limit` |
| Positive path separation under the limiting law from a uniform separation bound for the approximations | `canonicalPairDifferent_of_weak_limit` |
| Compactness with a common Hölder modulus and subsequence extraction for tight canonical laws | `isCompact_canonicalPairPath_holder`, `canonicalPairPath_subsequence_of_uniform_tightness` |
| Tightness and weak subsequence extraction from uniform increment moments and bounded starting values | `canonicalPairPath_subsequence_of_increment_moments` |
| Supremum-norm second moments and L² continuity of the coordinate paths | `uniform_canonicalPath_sup_sq_moment`, `continuous_canonicalVarianceCoordinate_Lp` |
| Preservation of nonnegative paths under weak convergence | `canonicalPair_ae_nonnegative_of_weak_limit` |
| Combined passage from the increment moment, martingale and separation bounds to the exact variance witnesses | `separated_heston_of_canonical_increment_moments` |

## Coupled approximation estimates

The finite-dimensional diffusion coefficients use the positive parts
of the cluster coordinates. Each coefficient is continuous at zero
total mass, and the row covariances give the orthogonal cluster noises
and their prescribed covariations with the competing variance. For
every nonnegative decreasing kernel dominated by the fractional
kernel, the squared translation difference is bounded by the
difference of the two squared kernel values. Integration telescopes
and gives the uniform L² increment rate. The corresponding L¹ bound
controls the drift. The finite exponential mixture identity and the
bound and convergence for the inverse convolutions are also checked.
The Volterra moment argument obtains a uniform bound by subdividing
time once a common moment inequality and per-approximation boundedness
have been established.

| Step | Lean theorem |
| --- | --- |
| Continuity and covariance of the smooth system's diffusion coefficients | `continuous_clusterSharedCoefficient`, `continuous_clusterAuxiliaryCoefficient`, `clusterDiffusion_covariance`, `clusterDiffusion_competitor_covariance` |
| Kernel increment bounds uniform over dominated decreasing kernels | `heston_dominated_kernel_increment_L2`, `heston_dominated_kernel_increment_L1` |
| Gamma Laplace formula and convergence of the inverse equation for dominated kernel approximations | `hestonKernel_laplace_integral`, `fractionalL_convolution_approximation` |
| Positive finite exponential approximations dominated by K, with pointwise and L² convergence | `fractionalExponentialApproximation_le_hestonKernel`, `fractionalExponentialApproximation_tendsto`, `fractionalExponentialApproximation_tendsto_integral_sq` |
| Interlacing, positive simple residues, and endpoint constants for the smooth-kernel resolvent | `exponentialMixtureLaplace_interlaces`, `exponentialMixtureLaplace_residue_pos`, `exponentialMixtureLaplace_origin_residue`, `exponentialMixtureLaplace_resolvent_atTop` |
| Polynomial factorization and the global partial-fraction identity for the resolvent transform | `exponentialLaplaceNumerator_factorization`, `exponentialMixtureLaplace_partialFractions` |
| Positive first-kind resolvent in the time domain, with a decreasing density | `positive_exponential_resolvent_time_domain`, `positive_exponential_density_deriv_nonpos` |
| The lifted exponential memory equations and the inward drift bound | `exponentialVarianceMemory_hasDerivAt`, `smoothVarianceLiftDrift_fst_nonneg` |
| Nonnegative variance paths from the smooth equations on a usual filtration | `ae_nonnegative_of_inward_drift_and_compensated_square_usual` |
| Adapted Euler states and the martingale property of their noise coordinates for bounded diffusion coefficients | `eulerGridState_stronglyAdapted`, `eulerGridState_noise_martingale` |
| Conditional row covariance and compensated products for Euler noise in the sampled filtration | `eulerGridNoise_compensated_product_of_independent_increments` |
| Second-moment bounds for Euler noise and state increments over arbitrary grid blocks | `integral_eulerGridNoise_sub_sq_le`, `integral_eulerGridState_sub_sq_le` |
| Fourth-moment bounds for Euler noise over arbitrary grid blocks with Gaussian driver increments | `integral_runningSum_sub_fourth_le`, `integral_eulerGridNoise_sub_fourth_le` |
| Uniform timewise moment bound from the Volterra inequality | `uniform_fractional_volterra_moment_bound` |
| Continuous-time Doob bound, exact expected grid expansion, and even moments from the localized power identity | `exists_continuous_martingale_norm_envelope`, `integral_grid_ito_expansion`, `terminal_even_moment_le_of_localized_power_identities` |
| Vanishing dyadic Taylor remainder and the upper even-moment bound for bounded continuous martingales | `tendsto_expected_dyadic_ito_compensator_sum`, `bounded_martingale_even_power_le` |
| Stopping-time localization of the upper even-moment bound for almost surely continuous martingales and their square compensators | `continuous_martingale_even_power_le`, `ae_continuous_martingale_even_power_le` |
| Weighted kernel moment estimates and the transfer from a terminal BDG bound | `lintegral_weighted_kernel_moment_le`, `kernel_noise_moment_le_of_bdg` |
| Cumulative pulse clock and the telescoping estimate for completed mesh cells | `cumulativePulsedInput_error_le`, `pulse_early_cells_telescope` |
| Convolution bound for a full or partly elapsed pulse, uniform over dominated kernels | `heston_pulse_convolution_le`, `heston_scaled_pulse_bound` |
| Fractional kernel convolution powers and a lower bound for the Gamma function used to control the series | `fractionalK_convolution_add`, `fractionalKIterate_eq`, `gamma_ge_of_unit_interval` |
| Absolute convergence and the exact second-kind resolvent equation | `fractionalSecondKindResolvent_norm_summable`, `fractionalSecondKindResolvent_identity` |
| Zero covariance at different observation times and the joint cluster exceedance bound | `orthogonal_deterministic_grid_limits_mean_and_cross`, `joint_cluster_exceedance_le_of_orthogonal_noise` |
| Uniform separation from single-cluster and pair event bounds, and its transfer to the weak limit | `clusterEventUnion_uniform_probability_bound`, `canonicalPairDifferent_of_cluster_event_bounds` |
| Size-biased law and a positive burst probability from its moment bounds | `integral_sizeBiasedLaw_eq`, `burst_probability_of_moments` |
| Original separation probability from a capped event under the birth-conditioned size-biased law | `measureReal_lower_bound_of_conditioned_size_bias` |
| Positivity of the biased mass from the nonnegative cluster's past before the end of the pulse | `pulsed_cluster_mass_pos` |

For bounded coefficients, the continuous interpolated Euler states now give
a weakly convergent subsequence on the full finite-dimensional continuous
path space. The fourth moment of each coordinate increment is bounded
uniformly by a constant times the square of the time increment. The limit solves the canonical martingale problem for bounded continuous
coefficients. The proof constructs the finite Gaussian driver and obtains
its conditional increment covariances in the product filtration. The fourth-moment bounds for the spatially truncated laws are uniform in
the radius. A second weak limit removes the truncation and solves the
canonical martingale problem for arbitrary continuous coefficients of
linear growth. For the pulsed finite-exponential model, Lean instantiates the coefficients, translates by the immigration primitive and proves nonnegativity of the variance coordinates. It obtains all the coordinate square and mixed compensators on the same probability space. [Finite exponential coupling](mathfin/SmoothCoupledRealization.lean)
[Euler weak limit](mathfin/EulerWeakLawExtraction.lean) · [Existence for bounded coefficients](mathfin/FiniteEulerMartingaleExistence.lean) · [Existence for linear growth](mathfin/FiniteLinearGrowthExistence.lean)

## Zero boundary and conditioning

The affine Laplace exponent bound implies positive mass at zero by
dominated convergence. Normalized Laplace tilts converge to
conditioning at that atom under integrable tests. A bound on the
conditional affine exponents controls the probability of positive
variance under the conditional law. The affine identities and the
quantitative control of their exponents must be supplied by the model.

| Step | Lean theorem |
| --- | --- |
| Positive atom from a uniform bound on unconditional affine exponents | `laplaceBoundary_atom_of_affine_bound` |
| Passing a tilted conditional mean bound to the zero atom | `boundaryConditionalMean_le_of_laplaceTilt` |
| Conditional positivity from the conditional affine exponent estimate | `boundaryConditionalPositive_le_of_affine_bound` |
| History bound from a backward conditional mean of order u^p | `conditionalHistory_power_bound` |
| History splitting and the derivative of the fractional inverse kernel | `fractional_history_input_splitting`, `hasDerivAt_fractionalL` |
| The forward history convolution gives the power h^(p+1−2α) | `conditionalHistory_forward_convolution_bound` |
| Point-charge Riccati local existence, its inverse equation, scaling, and the singular comparison profile | `exists_local_fractional_riccati_point_charge`, `fractional_riccati_rl_primitive`, `fractional_riccati_rescale`, `singularRiccatiProfile_solves` |
| Local continuation of a point-charge solution through a positive time where it is continuous | `exists_point_charge_riccati_continuation` |
| Actual Marchaud derivative formula, singular comparison for C¹ solutions, and the first smoothing estimate | `fractional_rl_hasDerivAt_memory`, `point_charge_riccati_lt_singular_profile`, `fractional_volterra_local_input_increment` |
| Local C¹ regularity of a continuous point-charge solution with its weighted asymptotic and Volterra equation | `point_charge_riccati_contDiffAt_of_volterra` |
| Positivity, charge monotonicity, and comparison between damped and undamped point-charge solutions | `point_charge_riccati_pos`, `point_charge_riccati_strictMono_charge`, `point_charge_riccati_damped_le_undamped` |
| Identification of the undamped singular Riccati limit from the integrated equation, scaling, positivity, and monotonicity | `tendsto_undamped_riccati_charge` |
| Quantitative damping error and a strict finite-charge lower bound for the Caputo barrier comparison | `point_charge_riccati_damping_error`, `exists_finite_charge_strict_caputo_lower` |
| Rescaling the regular point-charge family and obtaining one coefficient for the small-time boundary comparison | `PointChargeRiccatiOn.rescale`, `exists_scaled_riccati_uniform_boundary_lower` |
| Exact Caputo lower bound for the backward power barrier | `backwardPower_caputo_lower_bound` |
| Deriving the Caputo equation from the preterminal Volterra mean equation, then obtaining a uniform backward power bound | `caputo_mean_equation_of_volterra`, `caputo_mean_le_backwardPower_of_volterra` |
| One-time and deterministic time-weighted expectations under a terminal density martingale | `integral_martingale_mul_past_of_memLp_two`, `integral_densityTilt_past` |
| Stochastic Fubini for the Riccati kernel in the joint filtration | `heston_weighted_stochastic_fubini`, `heston_riccati_stochastic_term` |
| Integrability and association of the affine Volterra triangle under the fractional bounds | `riccati_affine_triangle_smul_integrable`, `volterra_affine_smul_assoc_of_riccati_bounds` |
| The terminal affine convolution identity for a point charge and an integrable density test in L² | `heston_affineTransform_identity` |
| Bilinear Itô identity for the stochastic term of the tilted mean, given the density's Itô representation | `integral_density_mul_heston_stochastic_term` |
| Tilted mean integral equation from the variance equation and the bounded density martingale representation | `tiltedVarianceMean_integral_equation` |
| Martingale property of a bounded local martingale and the conditional affine formula from its local density and exponent identities | `martingale_of_bounded_localMartingale`, `conditional_laplace_of_affine_local_density` |
| Cluster small-mass probability from its large-charge Laplace estimate | `cluster_mass_lower_tail_of_laplace` |
| Stopped positive occupation and the integrable quadratic drift cost | `stopped_positive_le_of_laplace_test`, `stopped_occupation_cost_bound` |
| Event-probability change from a stopped exponential and its doubled-density moment bound | `event_probability_diff_le_stopped_density_cost` |
| Predictable capping of simple grid integrands, with a bound on the squared approximation error | `gridCappedCoefficient_stronglyMeasurable`, `gridEnergy_capping_error_le` |

The point-charge Riccati equation has a unique positive solution on all
positive times. The proof continues the local solution through a finite
endpoint and proves the lower bound used for the backward comparison
without assuming the existence of a family of solutions or its singular
limit. For constant density forcing the global bounded family is also
constructed. Lean constructs the solution of the linearized equation and identifies the
right derivative at zero charge. For the post-pulse and early-pulse
regimes the resulting lower-tail estimates apply under the specified
terminal affine formula. The rectangular pulse has mass ε after the pulse
and contributes exactly ε/8 from the specified ages at time d/4. [Global point-charge
solution](mathfin/RiccatiGlobal.lean) · [Uniform lower bound](mathfin/RiccatiGlobalBoundary.lean)
· [Density tests](mathfin/DensityChargeGlobal.lean) · [Right derivative](mathfin/ClusterDensitySensitivity.lean) · [Post-pulse bound](mathfin/ClusterSizeBiasedLowerTail.lean) · [Rectangular pulse and mass bounds](mathfin/RectangularPulseLowerTail.lean)

## The variance theorem

Lean proves `RoughHeston.theorem1_1 : RoughHeston.Theorem1_1`. For every parameter choice in the manuscript it constructs one filtered probability space, one Brownian motion in that filtration and two continuous, nonnegative variance solutions driven by that Brownian motion. The probability that the solutions differ before or at the horizon is strictly positive. The axiom report lists `propext`, `Classical.choice` and `Quot.sound`. [Unconditional proof and axiom report](han/RoughHestonVarianceTheorem.lean) · [Target and definition of the stochastic convolution](TheoremStatement.lean)

The proof first constructs the fractional coupled law at fixed immigration mesh. It conditions on the event that the companion is zero at a focal birth, retains the companion's earlier history in its affine transform, and uses Han's stopped change of measure to bound the probability that the companion becomes positive while the focal cluster is large. The birth probability converts the estimate back to the original law. Its coefficient is fixed before the mesh. Counting the births produces a uniform positive separation probability, which survives convergence of the two aggregate paths. [Fixed-mesh laws](mathfin/ExplicitLebesguePulseLaw.lean) · [Stopped change of measure](han/RawBirthTracePulseStoppedLaw.lean) · [Separation at one birth](han/PhysicalSingleBirthTraceSeparation.lean) · [Counting](mathfin/UniformExplicitMeshSeparation.lean) · [Limit and common Brownian motion](han/ExplicitLebesgueMeshLimit.lean)

The declaration `RoughHeston.theorem1_1_full : RoughHeston.FullRoughHestonTheorem` checks the price–variance system for every ρ in [−1,1] and every positive common initial price. One correlated Brownian pair drives both systems. A version of the predictable Itô convolution satisfies each variance equation simultaneously on the whole horizon almost surely. For each price, the stopped predictable integrals of S√V against the named price Brownian agree with S−S₀. The increasing stopping times eventually reach the horizon on each path. The full declaration has the same three standard axioms. [Full theorem](han/RoughHestonFullTheorem.lean) · [Dyadic and Itô variance equations](mathfin/HestonBrownianItoEquivalence.lean) · [Correlation and joint filtration](mathfin/CorrelatedRegularVariancePair.lean) · [Price SDE](han/HestonPriceSDE.lean)

## Stopped Girsanov on the joint filtration

Let \(Q\) be the birth-conditioned, size-biased law and let \(R\) denote the
law obtained by the stopped reversal of the competitor drift. On a supplied
usual filtration with the Brownian driver under \(Q\), the theorem
`stopped_competitor_change_at_envelope` constructs the envelope stop,
the cumulative-energy stop, the measure \(R\), and the Brownian driver
under \(R\). It takes the predictable variance and focal mass processes
in the coupling as inputs. The focal mass must be positive and the focal
variance must lie between zero and the total variance.

Lean identifies the density with the negative exponential of the project's
joint Itô integral and its half energy. It proves equality of both laws on
the full birth sigma-algebra, transports the joint square-integrable
integrals, and bounds the change in every event probability by
\(\sqrt{\delta}/2\). This is the direction and constant used in
the draft. The transported stopped transform has the same mean as its
birth value once its stochastic representation and integrability are
supplied. The stopped occupation estimate then bounds the expectation
of the physical energy. Lean transfers the probability of the two bad
events, hitting the energy budget and seeing positive variance at the
horizon while still observing the process, using one total variation
estimate. To apply this estimate to the fractional coupling one must obtain its block moments and the predictable stochastic representation of the stopped tests under the changes of measure.
[Physical cost](mathfin/StoppedPhysicalOccupation.lean) · [Separation under the stopped law](han/StoppedCompetitorSeparation.lean) [Stopped competitor change](han/StoppedCompetitorGirsanov.lean) · [Stopped transform](han/StoppedTransformOccupation.lean) · [Entropy estimate](mathfin/StoppedEntropyBound.lean)

Conditioning on a positive-probability event in the birth sigma-algebra
preserves the Brownian increments after birth on the age filtration
\(\mathcal F_{b+s}\). Restriction to the event with its trace sigma-algebra
preserves the usual conditions. For the subsequent focal size bias, the compensated square and mixed
products of the focal mass identify the drift of the Brownian driver.
Localization of the entropy identity gives square integrability of
\(\sigma U/(Z\sqrt X)\) under that tilt. The driver with this drift
removed is Brownian on the original joint filtration. The proof uses
strict positivity of the focal mass. For a rectangular pulse, optional
stopping at the first positive variance and the inverse variance equation give
that positivity simultaneously at all ages.
[Focal Brownian shift](han/FocalSizeBiasBrownian.lean) · [Pulse activation](mathfin/PulseActivation.lean) · [First change of Itô integral](mathfin/FirstTiltItoTransport.lean)
[Brownian increments after conditioning](mathfin/BrownianAfterBirthConditioning.lean) · [Trace filtration](mathfin/BirthEventTrace.lean)

Han's public library supplies the bounded-energy Gaussian shift and the
Itô transport on a given filtration. Its mathlib revision differs from
the project's. The private build applies a compatibility patch and
compiles the relevant public modules against the project pins.
[Build and axiom checks](han/README.md) · [Public Brownian shift](https://github.com/hanyi162013-Yihan/scalar-she-lean/blob/60a63972f07986442801838fa78e758e2ccc6303/SHEStochastic/ScalarGirsanovCoordinateShift.lean) · [Public Itô transport](https://github.com/hanyi162013-Yihan/scalar-she-lean/blob/60a63972f07986442801838fa78e758e2ccc6303/SHEStochastic/ScalarGirsanovCappedTransport.lean)

## Reproducing the checks

For pinned dependencies, build commands and the kernel replay, see [Reproducing the Lean proof](REPRODUCE.md).

The axiom audits in `lean-check.txt` and `mathfin/lean-check.txt`
record the checked declarations. The upstream BrownianMotion build
reports admissions in modules including `LocalMartingale`,
`UniformIntegrable` and `OptionalSampling`. The audited declarations
have no dependency on `sorryAx`. [Upstream source](https://github.com/RemyDegenne/brownian-motion/tree/497e5e2a60450796f75ab920e6c33addae4d644d/BrownianMotion/StochasticIntegral)
