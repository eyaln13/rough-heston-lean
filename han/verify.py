"""Replay the private Girsanov bridge from the pinned public Lean sources."""
import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import hashlib
import os
from pathlib import Path
import re
import shutil
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--han", required=True, type=Path)
parser.add_argument("--mathfin", required=True, type=Path)
parser.add_argument("--project-build", required=True, type=Path)
parser.add_argument("--build", required=True, type=Path, help="fresh output directory")
parser.add_argument("--jobs", default=2, type=int)
parser.add_argument("--lean", default="lean")
args = parser.parse_args()
here = Path(__file__).resolve().parent
han, mathfin, project, build = (p.resolve() for p in
    (args.han, args.mathfin, args.project_build, args.build))
if args.jobs < 1:
    parser.error("--jobs must be positive")
if build.exists() and any(build.iterdir()):
    parser.error("--build must be empty for a source replay")
if not os.environ.get("LEAN_PATH"):
    parser.error("run in the pinned MathFin lake environment, with LEAN_PATH set")
lean = shutil.which(args.lean)
version = subprocess.check_output([lean, "--version"], text=True).strip()
if "version 4.35.0," not in version:
    parser.error(f"expected Lean 4.35.0, found {version}")
pins = {han: "60a63972f07986442801838fa78e758e2ccc6303",
        mathfin: "cbe842dda1e71fd7173f3325971796686dbf7feb",
        mathfin/".lake/packages/mathlib": "e91b128082cc221d6432a6a5aadcd3243af8e76c",
        mathfin/".lake/packages/BrownianMotion": "497e5e2a60450796f75ab920e6c33addae4d644d"}
for repo, rev in pins.items():
    if subprocess.check_output(["git", "-C", repo, "rev-parse", "HEAD"], text=True).strip() != rev:
        parser.error(f"unexpected pin for {repo}")
    subprocess.run(["git", "-C", repo, "diff", "--quiet", "HEAD", "--"], check=True)

build.mkdir(parents=True, exist_ok=True)
overlay, lib, logs = (build/d for d in ("overlay", "lib", "logs"))
shutil.copytree(here/"compat", overlay)
lib.mkdir()
logs.mkdir()
patch = here/"scalar-she-pinned-lean.patch"
for rel in re.findall(r"^--- a/(\S+)$", patch.read_text(), re.M):
    target = overlay/rel
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(han/rel, target)
with patch.open("rb") as f:
    subprocess.run(["patch", "-s", "-p1", "-d", overlay], stdin=f, check=True)

paths = [Path(p).resolve() for p in os.environ["LEAN_PATH"].split(os.pathsep) if p]
env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [lib, project, *paths])))
# Lean resolves a top-level package as one tree. Include the standard MathFin
# and BrownianMotion artifacts beside any legacy names or newly built leaves.
for package, upstream in (("MathFin", mathfin), ("BrownianMotion", mathfin/".lake/packages/BrownianMotion")):
    origin = upstream/".lake/build/lib/lean"
    for artifact in (origin/package).rglob("*"):
        if artifact.is_file() and (".olean" in artifact.suffixes or ".ir" in artifact.suffixes):
            dest = lib/artifact.relative_to(origin)
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.symlink_to(artifact.resolve())

local = {p.stem: p for p in here.glob("*.lean")}
nodes = {}
def visit(name):
    if name in nodes:
        return
    rel = Path(*name.split(".")).with_suffix(".lean")
    if name in local:
        root, source = here, local[name]
    elif (overlay/rel).is_file():
        root, source = overlay, overlay/rel
    elif name.startswith(("SHE.", "SHEStochastic.")):
        root, source = han, han/rel
    elif any((p/rel.with_suffix(".olean")).is_file() for p in [lib, project, *paths]):
        return
    elif name.startswith("MathFin."):
        root, source = mathfin, mathfin/rel
    elif name.startswith("BrownianMotion."):
        root = mathfin/".lake/packages/BrownianMotion"
        source = root/rel
    elif name.split(".")[0] in {"Lean","Init","Std","Lake"}:
        return
    else:
        raise RuntimeError(f"build the missing dependency {name} with the pinned MathFin lake")
    if not source.is_file():
        raise FileNotFoundError(source)
    deps = set()
    for match in re.finditer(r"^(?:(?:public|private|meta)\s+)*import[ \t]+([^\n]+)", source.read_text(), re.M):
        for dep in match[1].partition("--")[0].split():
            visit(dep)
            if dep in nodes:
                deps.add(dep)
    nodes[name] = root, source, deps

for target in sorted(local):
    visit(target)
allowed = {"propext","Classical.choice","Quot.sound"}
def compile_module(name):
    root, src, _ = nodes[name]
    dest = lib/Path(*name.split(".")).with_suffix(".olean")
    if dest.is_symlink():
        raise RuntimeError(f"output shadows a pinned dependency: {name}")
    dest.parent.mkdir(parents=True, exist_ok=True)
    completed = subprocess.run([lean, f"--root={root}", "-o", dest, src],
                               env=env, capture_output=True, text=True)
    result = completed.stdout + completed.stderr
    (logs/(name+".txt")).write_text(result)
    if completed.returncode:
        raise RuntimeError(name + "\n" + result)
    if name in local:
        reports = re.findall(r"depends on axioms: \[([^\]]*)\]", result, re.S)
        if "sorryAx" in result or not all(set(x.strip() for x in r.split(",")) <= allowed for r in reports):
            raise RuntimeError("axiom audit failed: " + name)
        checks = src.read_text().count("#print axioms ")
        if len(reports) + result.count("does not depend on any axioms") != checks:
            raise RuntimeError("incomplete axiom report: " + name)
    return name

pending, done, active = set(nodes), set(), {}
print(f"Compiling {len(nodes)} modules", flush=True)
with ThreadPoolExecutor(max_workers=args.jobs) as pool:
    while pending or active:
        for name in nodes:
            if len(active) == args.jobs:
                break
            if name in pending and nodes[name][2] <= done:
                pending.remove(name)
                active[pool.submit(compile_module, name)] = name
        if not active:
            raise RuntimeError(f"unresolved dependencies: {sorted(pending)}")
        for future in wait(active, return_when=FIRST_COMPLETED)[0]:
            name = active.pop(future)
            done.add(future.result())
            print(f"{len(done)}/{len(nodes)} {name}", flush=True)

out = [version, *(f"{p.name} {rev}" for p, rev in pins.items())]
for name, src in sorted(local.items()):
    out.extend(["", f"{hashlib.sha256(src.read_bytes()).hexdigest()}  {src.name}",
                (logs/(name+".txt")).read_text().strip()])
(build/"lean-check.txt").write_text("\n".join(out)+"\n")
