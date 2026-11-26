"""Compile the rough Heston Lean sources against the pinned MathFin environment."""
import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import hashlib
import os
from pathlib import Path
import re
import shutil
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--mathfin", required=True, type=Path)
parser.add_argument("--build", required=True, type=Path, help="empty output directory")
parser.add_argument("--jobs", type=int, default=4)
parser.add_argument("--lean", default="lean")
args = parser.parse_args()
project = Path(__file__).resolve().parent
repo = args.mathfin.resolve()
build = args.build.resolve()
lean = shutil.which(args.lean)
if not lean or args.jobs < 1 or not os.environ.get("LEAN_PATH"):
    parser.error("Use the pinned lake environment with a positive number of jobs.")
if build.exists() and any(build.iterdir()):
    parser.error("The build directory must be empty.")
version = subprocess.check_output([lean, "--version"], text=True).strip()
if "version 4.35.0," not in version:
    parser.error(f"Expected Lean 4.35.0, found {version}.")
for path, pin in [(repo, "cbe842dda1e71fd7173f3325971796686dbf7feb"),
                  (repo/".lake/packages/mathlib", "e91b128082cc221d6432a6a5aadcd3243af8e76c"),
                  (repo/".lake/packages/BrownianMotion", "497e5e2a60450796f75ab920e6c33addae4d644d")]:
    if subprocess.check_output(["git", "-C", path, "rev-parse", "HEAD"], text=True).strip() != pin:
        parser.error(f"Unexpected dependency version at {path}.")
    subprocess.run(["git", "-C", path, "diff", "--quiet", "HEAD", "--"], check=True)

sources = [*project.glob("*.lean"), *(project/"mathfin").glob("*.lean")]
files = {p.stem: p for p in sources}
if len(files) != len(sources):
    parser.error("Two sources have the same module name.")
imports = {n: set(re.findall(r"^import\s+([\w.]+)\s*$", p.read_text(), re.M)) for n, p in files.items()}
requires = {n: deps & files.keys() for n, deps in imports.items()}
paths = [Path(d).resolve() for d in os.environ["LEAN_PATH"].split(os.pathsep) if d]
external = set().union(*imports.values()) - files.keys()
missing = sorted(n for n in external if not any((d/(n.replace(".", "/") + ".olean")).is_file() for d in paths))
if missing:
    subprocess.run(["lake", "build", *("+" + n for n in missing)], cwd=repo, check=True)

build.mkdir(parents=True, exist_ok=True)
env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [build, *paths])))
standard = {"propext", "Classical.choice", "Quot.sound"}
def compile_module(n):
    p = files[n]
    digest = hashlib.sha256(p.read_bytes()).hexdigest()
    proc = subprocess.run([lean, "--root="+str(p.parent), "-o", str(build/(n+".olean")), str(p)],
                          env=env, capture_output=True, text=True)
    log = proc.stdout + proc.stderr
    (build/(n+".txt")).write_text(log)
    reports = re.findall(r"depends on axioms: \[(.*?)\]", log, re.S)
    count = len(reports) + log.count("does not depend on any axioms")
    if (proc.returncode or "sorryAx" in log or re.search(r"declaration uses .sorry.", log)
            or count != len(re.findall(r"^#print axioms ", p.read_text(), re.M))
            or any(set(x.strip() for x in report.split(",")) - standard for report in reports)):
        raise RuntimeError(f"{p.name} failed compilation or axiom checks. See {build/(n+'.txt')}.")
    if digest != hashlib.sha256(p.read_bytes()).hexdigest():
        raise RuntimeError(f"{p.name} changed during compilation.")
    return count, digest

done = {}
pending = set(files)
running = {}
with ThreadPoolExecutor(args.jobs) as pool:
    while pending or running:
        for n in sorted(n for n in pending if requires[n] <= done.keys())[:args.jobs-len(running)]:
            running[pool.submit(compile_module,n)] = n
            pending.remove(n)
        if not running:
            raise RuntimeError(f"Cyclic local imports: {sorted(pending)}")
        for future in wait(running,return_when=FIRST_COMPLETED).done:
            n = running.pop(future)
            done[n] = future.result()
            print(f"{len(done)}/{len(files)} {n}", flush=True)
summary = f"{len(done)} modules, {sum(c for c, _ in done.values())} axiom reports"
(build/"lean-check.txt").write_text(version+"\n"+summary+"\n"+''.join(
    f"\n{done[n][1]}  {files[n].relative_to(project)}\n"+(build/(n+".txt")).read_text() for n in sorted(files)))
print(summary)
