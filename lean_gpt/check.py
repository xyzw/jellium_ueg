#!/usr/bin/env python3
"""Run the pinned Lean compiler without rebuilding the existing dependency cache.

With file arguments, check those sources. Without arguments, compile all local
modules and run the axiom audit. Add --record to replace verification.log and
verification.json with evidence from a full run, including a failed run. This
does not download or modify dependencies. For a fresh checkout, install Lean
and run `lake update` and `lake exe cache get` before using this script, or use
the normal `lake build` workflow.
"""

from pathlib import Path
import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from datetime import datetime, timezone
import hashlib
import json
import os
import platform
import re
import shlex
import shutil
import subprocess
import sys
from threading import Lock


ROOT = Path(__file__).resolve().parent
LEAN_OPTIONS = ["-DautoImplicit=false", "-DrelaxedAutoImplicit=false", "-DwarningAsError=true"]
AUDIT_MARKERS = {
    "axioms": "No sorryAx or additional axioms. This audit does not discharge theorem hypotheses.",
    "retired_proof_steps_absent": "The equality proof does not depend on the retired sector-assignment or contraction arguments.",
    "required_proof_steps_present": "The equality proof uses every required main, lower, shell, upper, localization and scaling step.",
}


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def snapshot():
    sources = [*ROOT.glob("*.lean"), *ROOT.joinpath("Jellium").rglob("*.lean")]
    sources.extend(ROOT / name for name in ("check.py", "lean-toolchain", "lakefile.toml", "lakefile.lean", "lake-manifest.json"))
    sources.extend(ROOT.parent / name for name in ("jellium_ueg.tex", "dft.bib"))
    documents = [*ROOT.glob("*.txt"), *ROOT.glob("*.md")]
    return tuple(
        {path.relative_to(ROOT.parent).as_posix(): sha256(path)
         for path in sorted(set(paths)) if path.is_file()}
        for paths in (sources, documents)
    )


class Run:
    def __init__(self, args):
        self.args = args
        self.lock = Lock()
        self.log = None
        self.audit_output = []
        self.completed = []
        self.data = {
            "status": "running",
            "started_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
            "command": shlex.join(["python3", "check.py", *sys.argv[1:]]),
            "working_directory": ROOT.name,
            "exit_code": None,
            "compiler": None,
            "python_version": platform.python_version(),
            "compiler_options": [option.removeprefix("-D") for option in LEAN_OPTIONS],
            "requested_modules": [],
            "checked_modules": [],
        }
        if args.record:
            self.log = (ROOT / "verification.log").open("w", encoding="utf-8")
            # Invalidate an earlier successful record before any compiler work.
            self.write_record()

    def write_record(self):
        temporary = ROOT / ".verification.json.tmp"
        temporary.write_text(json.dumps(self.data, indent=2) + "\n", encoding="utf-8")
        temporary.replace(ROOT / "verification.json")

    def emit(self, message, source=None):
        with self.lock:
            print(message, end="" if message.endswith("\n") else "\n", flush=True)
            if self.log is not None:
                self.log.write(message)
                if not message.endswith("\n"):
                    self.log.write("\n")
                self.log.flush()
            if source == "Audit.lean":
                self.audit_output.append(message)

    def compile(self, compiler, env, source, destination=None):
        self.emit(f"Checking {source}")
        command = [str(compiler), *LEAN_OPTIONS]
        if destination is not None:
            destination.parent.mkdir(parents=True, exist_ok=True)
            command.extend(["-o", str(destination)])
        command.append(source)
        with subprocess.Popen(command, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                              text=True, encoding="utf-8", errors="replace") as process:
            for line in process.stdout:
                self.emit(line, source)
            returncode = process.wait()
        if returncode:
            raise subprocess.CalledProcessError(returncode, command)
        with self.lock:
            self.completed.append(source)
        self.emit(f"Passed {source}")

    def audit_result(self):
        output = "".join(self.audit_output)
        counts = re.search(r"Checked (\d+) theorem declarations and (\d+) definitions", output)
        audit_source = (ROOT / "Audit.lean").read_text()
        allowed = re.search(r"let allowed\s*:\s*List Name\s*:=\s*\[([^]]*)\]", audit_source)
        axioms_ok = AUDIT_MARKERS["axioms"] in output
        return {
            "non_internal_theorem_declarations": int(counts[1]) if counts else None,
            "non_internal_definitions": int(counts[2]) if counts else None,
            "allowed_axioms": re.findall(r"``([\w.]+)", allowed[1]) if allowed else None,
            "unexpected_axioms": [] if axioms_ok else None,
            "required_proof_steps_present": AUDIT_MARKERS["required_proof_steps_present"] in output,
            "retired_proof_steps_absent": AUDIT_MARKERS["retired_proof_steps_absent"] in output,
            "scope": "Relative formal verification from explicit analytic, operator and literature hypotheses",
        }

    def finish(self, exit_code):
        if not self.args.record:
            return exit_code
        self.data["checked_modules"] = sorted(self.completed)
        if (ROOT / "Audit.lean").is_file():
            self.data["audit"] = self.audit_result()
        source_hashes, documentation_hashes = snapshot()
        unchanged = (source_hashes == self.data.get("source_sha256") and
                     documentation_hashes == self.data.get("documentation_sha256"))
        self.data["source_hashes_match_recorded_snapshot"] = unchanged
        if not unchanged:
            self.emit("Inputs changed during verification. Run --record again with stable sources.")
            self.data["error"] = "Inputs changed during verification"
            exit_code = exit_code or 1
        self.data["exit_code"] = exit_code
        self.data["status"] = "passed" if exit_code == 0 else "failed"
        self.data["verified_at"] = datetime.now(timezone.utc).isoformat(timespec="seconds")
        self.log.close()
        self.data["log_sha256"] = sha256(ROOT / "verification.log")
        self.write_record()
        return exit_code


def local_imports(source):
    for line in re.findall(r"^import\s+([^\n]+)", Path(source).read_text(), re.M):
        for imported in line.split("--", 1)[0].split():
            yield Path(imported.replace(".", "/") + ".lean")


def check(run):
    args = run.args
    if args.record:
        run.data["source_sha256"], run.data["documentation_sha256"] = snapshot()
        manifest = ROOT / "lake-manifest.json"
        if manifest.is_file():
            packages = json.loads(manifest.read_text()).get("packages", [])
            run.data["mathlib_revision"] = next((p.get("rev") for p in packages if p.get("name") == "mathlib"), None)
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    run.data["toolchain"] = toolchain
    elan = Path(os.environ.get("ELAN_HOME", Path.home() / ".elan"))
    compiler = elan / "toolchains" / toolchain.replace("/", "--").replace(":", "---") / "bin" / "lean"
    if not compiler.is_file():
        found = shutil.which("lean")
        if not found:
            raise RuntimeError("Lean not found. Install the toolchain in lean-toolchain first.")
        compiler = Path(found)
    version_result = subprocess.run([str(compiler), "--version"], text=True, capture_output=True, check=True)
    version = version_result.stdout.strip()
    run.data["compiler"] = version
    expected_version = toolchain.rsplit(":", 1)[-1].removeprefix("v")
    actual_version = re.search(r"\bversion ([^,\s]+)", version)
    if actual_version is None or actual_version.group(1) != expected_version:
        raise RuntimeError(f"Expected Lean {expected_version} from lean-toolchain, got {version}")

    paths = [ROOT / ".lake" / "build" / "lib" / "lean"]
    paths.extend(sorted((ROOT / ".lake" / "packages").glob("*/.lake/build/lib/lean")))
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(map(str, paths))
    arguments = args.sources
    if arguments and not args.build:
        for source in arguments:
            run.compile(compiler, env, source)
        return

    sources = []
    dependencies = {}
    visiting = set()
    visited = set()

    def visit(source):
        source = Path(source).resolve().relative_to(ROOT).as_posix()
        if source in visited:
            return
        if source in visiting:
            raise RuntimeError(f"Circular local import in {source}")
        visiting.add(source)
        dependencies[source] = set()
        for dependency in local_imports(source):
            if dependency.is_file():
                dependencies[source].add(dependency.as_posix())
                visit(dependency)
        visiting.remove(source)
        visited.add(source)
        sources.append(source)

    for source in arguments or [*sorted(Path("Jellium").rglob("*.lean")), "Jellium.lean", "Audit.lean"]:
        visit(source)
    run.data["requested_modules"] = sorted(sources)
    run.emit(version)

    def compile_source(source):
        destination = paths[0] / Path(source).with_suffix(".olean")
        # Full runs rebuild every module. Partial builds always execute the audit.
        if arguments and source != "Audit.lean" and destination.exists():
            inputs = [Path(source), ROOT / "lean-toolchain"]
            for imported in local_imports(source):
                dependency = paths[0] / imported.with_suffix(".olean")
                if dependency.is_file():
                    inputs.append(dependency)
            if all(destination.stat().st_mtime >= item.stat().st_mtime for item in inputs):
                run.emit(f"Current {source}")
                return
        run.compile(compiler, env, source, destination)

    # Submit a module only after every local import has completed.
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
                raise RuntimeError("No buildable module remains in the local import graph")
            finished, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in finished:
                source = running.pop(future)
                future.result()
                completed.add(source)
    if args.record:
        run.data["audit"] = run.audit_result()
        audit = run.data["audit"]
        if (audit["non_internal_theorem_declarations"] is None or
                audit["unexpected_axioms"] != [] or
                not audit["required_proof_steps_present"] or
                not audit["retired_proof_steps_absent"]):
            raise RuntimeError("Audit completed without every expected success message")
    run.emit(f"Verified {len(sources)} local modules")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", action="store_true", help="rebuild changed local dependencies")
    parser.add_argument("--record", action="store_true", help="save a full forced run to verification.log and verification.json")
    parser.add_argument("-j", "--jobs", type=int, default=1, help="parallel compiler processes")
    parser.add_argument("sources", nargs="*", help="local Lean source files")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    if args.record and args.sources:
        parser.error("--record requires a full run without source arguments")
    os.chdir(ROOT)
    run = Run(args)
    exit_code = 0
    try:
        check(run)
    except KeyboardInterrupt:
        run.emit("Verification interrupted")
        run.data["error"] = "Verification interrupted"
        exit_code = 130
    except (OSError, RuntimeError, ValueError, subprocess.CalledProcessError) as error:
        run.emit(str(error))
        run.data["error"] = str(error)
        if isinstance(error, subprocess.CalledProcessError):
            if error.stdout:
                run.emit(error.stdout)
            if error.stderr:
                run.emit(error.stderr)
            exit_code = error.returncode if error.returncode > 0 else 1
        else:
            exit_code = 1
    return run.finish(exit_code)


if __name__ == "__main__":
    sys.exit(main())
