#!/usr/bin/env python3
"""Run the pinned Lean compiler without rebuilding the existing dependency cache.

With file arguments, check those sources. Without arguments, compile all local
modules and run the axiom audit. This does not download or modify dependencies.
For a fresh checkout, install Lean and run `lake update` and `lake exe cache get`
before using this script, or use the normal `lake build` workflow.
"""

from pathlib import Path
import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import os
import re
import shutil
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--build", action="store_true", help="rebuild changed local dependencies")
parser.add_argument("-j", "--jobs", type=int, default=1, help="parallel compiler processes")
parser.add_argument("sources", nargs="*", help="local Lean source files")
args = parser.parse_args()
if args.jobs < 1:
    parser.error("--jobs must be positive")

root = Path(__file__).resolve().parent
os.chdir(root)
toolchain = (root / "lean-toolchain").read_text().strip()
elan = Path(os.environ.get("ELAN_HOME", Path.home() / ".elan"))
compiler = elan / "toolchains" / toolchain.replace("/", "--").replace(":", "---") / "bin" / "lean"
if not compiler.is_file():
    found = shutil.which("lean")
    if not found:
        raise SystemExit("Lean not found. Install the toolchain in lean-toolchain first.")
    compiler = Path(found)

version = subprocess.check_output([str(compiler), "--version"], text=True).strip()
expected_version = toolchain.rsplit(":", 1)[-1].removeprefix("v")
actual_version = re.search(r"\bversion ([^,\s]+)", version)
if actual_version is None or actual_version.group(1) != expected_version:
    raise SystemExit(
        f"Expected Lean {expected_version} from lean-toolchain, got {version}"
    )

deps = root / ".lake" / "packages"
paths = [root / ".lake" / "build" / "lib" / "lean"]
paths.extend(sorted(deps.glob("*/.lake/build/lib/lean")))
env = os.environ.copy()
env["LEAN_PATH"] = os.pathsep.join(map(str, paths))
lean_options = ["-DautoImplicit=false", "-DrelaxedAutoImplicit=false", "-DwarningAsError=true"]

arguments = args.sources
build = not arguments or args.build

if not build:
    for source in arguments:
        subprocess.run([str(compiler), *lean_options, source], env=env, check=True)
else:
    sources = []
    dependencies = {}
    visiting = set()
    visited = set()

    def visit(source):
        source = Path(source)
        if source in visited:
            return
        if source in visiting:
            raise SystemExit(f"Circular local import in {source}")
        visiting.add(source)
        dependencies[str(source)] = set()
        for imported in re.findall(r"^import\s+(\S+)", source.read_text(), re.M):
            dependency = Path(imported.replace(".", "/") + ".lean")
            if dependency.is_file():
                dependencies[str(source)].add(str(dependency))
                visit(dependency)
        visiting.remove(source)
        visited.add(source)
        sources.append(str(source))

    for source in arguments or [*sorted(Path("Jellium").glob("*.lean")), "Jellium.lean", "Audit.lean"]:
        visit(source)
    print(version, flush=True)
    def compile_source(source):
        destination = paths[0] / Path(source).with_suffix(".olean")
        destination.parent.mkdir(parents=True, exist_ok=True)
        # Always execute the audit so an incremental run records fresh output.
        if arguments and source != "Audit.lean" and destination.exists():
            inputs = [Path(source), root / "lean-toolchain"]
            for imported in re.findall(r"^import\s+(\S+)", Path(source).read_text(), re.M):
                dependency = paths[0] / Path(imported.replace(".", "/") + ".olean")
                if dependency.is_file():
                    inputs.append(dependency)
            if all(destination.stat().st_mtime >= item.stat().st_mtime for item in inputs):
                print(f"Current {source}", flush=True)
                return
        print(f"Checking {source}", flush=True)
        subprocess.run(
            [str(compiler), *lean_options, "-o", str(destination), source],
            env=env,
            check=True,
        )
        print(f"Passed {source}", flush=True)

    # A module is submitted only after every local import has completed.
    # This also ensures that the aggregate and audit run after their imports.
    remaining = list(sources)
    completed = set()
    running = {}
    with ThreadPoolExecutor(max_workers=args.jobs) as workers:
        while remaining or running:
            for source in remaining[:]:
                if len(running) == args.jobs:
                    break
                if dependencies[source] <= completed:
                    remaining.remove(source)
                    running[workers.submit(compile_source, source)] = source
            if not running:
                raise SystemExit("No buildable module remains in the local import graph")
            finished, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in finished:
                source = running.pop(future)
                future.result()
                completed.add(source)
    print(f"Verified {len(sources)} local modules", flush=True)
