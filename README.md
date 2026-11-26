# Pathwise nonuniqueness for the rough Heston model

This repository contains the Lean 4 proof of Theorem 1.1. For each $T>0$, $1/2<\alpha<1$, and $v_0,\kappa,\theta,\sigma>0$, the theorem constructs two continuous, nonnegative variance processes $X$ and $Y$ on one filtered probability space. Both start from $v_0$ and solve the same equation with the same Brownian motion $B$.

$$
V_t=v_0+\kappa\int_0^t K_\alpha(t-s)(\theta-V_s)\,ds
      +\sigma\int_0^t K_\alpha(t-s)\sqrt{V_s}\,dB_s,
\qquad K_\alpha(u)=\frac{u^{\alpha-1}}{\Gamma(\alpha)}\quad(u>0).
$$

The paths differ with strictly positive probability on $[0,T]$. For any correlation $\rho\in[-1,1]$ and initial price $S_0>0$, the full theorem also constructs the prices associated with $X$ and $Y$. Both prices use the same Brownian motion $W$ with quadratic covariation $\langle B,W\rangle_t=\rho t$ on $[0,T]$. [Variance statement](TheoremStatement.lean#L240) · [Variance proof](han/RoughHestonVarianceTheorem.lean#L98) · [Full theorem and proof](han/RoughHestonFullTheorem.lean#L50)

## Reading the proof

The [proof roadmap](ROADMAP.md) follows the argument in six steps. The [verification notes](VERIFICATION.md) give a more detailed index of intermediate results.

| Where to look | What it contains |
| --- | --- |
| [TheoremStatement.lean](TheoremStatement.lean) and the root Lean files | The variance equation, fractional kernel, stochastic integration, and common-driver construction |
| [mathfin/](mathfin/) | Fixed-mesh laws, fractional estimates, martingale identities, and the connection to Brownian Itô integration |
| [han/](han/) | The stopped changes of measure, separation, passage to the limit, and assembly of both main theorems |

## Reproducing the verification

Follow the [build instructions](REPRODUCE.md) to compile both parts from source with Lean 4.35.0 and replay the final declarations in the kernel. The [verification record](han/theorem-kernel-check.txt) gives the successful replay and the axiom reports for both theorems.

The recorded build covers 535 project modules. The repository also supplies the 15 compatibility modules used to build against the pinned libraries. To compare all 550 Lean sources with the verified snapshot, run the following from the repository root.

~~~sh
shasum -a 256 -c verification/lean-sources.sha256
~~~
