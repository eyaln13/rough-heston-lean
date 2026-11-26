# Reproducing the Lean proof

Start in the root of this proof repository. The commands use a POSIX shell on macOS or Linux, Git, Python 3, `patch`, and Lean's `elan` toolchain manager. Use the same shell for all three steps to retain the paths. The scratch directory holds the dependency checkouts, compiled modules and verification logs.

## 1. Set up the pinned libraries

```sh
sources=$(pwd -P)
work=$(mktemp -d)
mathfin="$work/formal-mathfin"
han="$work/scalar-she-lean"
core_build="$work/core"
han_build="$work/han"

git clone https://github.com/formal-applied-math/formal-mathfin.git "$mathfin"
git -C "$mathfin" checkout --detach cbe842dda1e71fd7173f3325971796686dbf7feb
git clone https://github.com/hanyi162013-Yihan/scalar-she-lean.git "$han"
git -C "$han" checkout --detach 60a63972f07986442801838fa78e758e2ccc6303

cd "$mathfin"
elan toolchain install leanprover/lean4:v4.35.0
lake env lean --version
lake exe cache get
```

The MathFin manifest supplies mathlib at `e91b128082cc221d6432a6a5aadcd3243af8e76c` and BrownianMotion at `497e5e2a60450796f75ab920e6c33addae4d644d`. Han's sources are compiled under the same Lean 4.35.0 environment. The project includes the required compatibility modules and patch in [han/](han/).

## 2. Compile the project from source

```sh
lake env python3 "$sources/verify_core.py" \
  --mathfin "$mathfin" --build "$core_build" --jobs 4

lake env python3 "$sources/han/verify.py" \
  --han "$han" --mathfin "$mathfin" --project-build "$core_build" \
  --build "$han_build" --jobs 2
```

The first command builds the 432 modules in the repository root and `mathfin/`. It asks Lake to build missing public imports. The second compiles the required modules from Han's library and the 103 project modules in `han/`, including both theorem declarations. Each driver starts from an empty output directory. Lower `--jobs` if memory is limited. The source hashes and axiom reports are written to `$core_build/lean-check.txt` and `$han_build/lean-check.txt`. [Core driver](verify_core.py) · [Han driver](han/verify.py)

## 3. Check both theorem declarations

```sh
lake env sh -c '
  export LEAN_PATH="$1/lib:$2:$LEAN_PATH"
  leanchecker --verbose RoughHestonVarianceTheorem RoughHestonFullTheorem
' sh "$han_build" "$core_build"

cat "$han_build/logs/RoughHestonVarianceTheorem.txt"
cat "$han_build/logs/RoughHestonFullTheorem.txt"
```

The kernel checker should replay both modules and exit with status zero. The compiler logs should list exactly `propext`, `Classical.choice`, and `Quot.sound` for each final declaration. Compare these with the [recorded verification](han/theorem-kernel-check.txt).
