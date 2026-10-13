Lean verification of the Jellium–UEG equality

The main theorem is Jellium.Main.equality in Jellium/Main.lean.
It connects the unit-parameter proof to the density scaling laws and proves
equality at every positive hbar and density. Main.coupling_equality gives the
equivalent positive-coupling formulation. Both use Conjecture51.equality,
which connects the lower and upper constructions on the same abstract state
and charge model from explicitly listed literature, operator and analytic
laws. The lower proof uses inner smoothing, selection of one
sector and canonical completion in an annulus. The former assignment and
contraction arguments, and the older scalar Reduction module, are not used by
the final theorem.

Read VERIFICATION.txt for the current manuscript proof map and build result,
and LITERATURE.txt
for the exact scope of the permitted assumptions and their primary sources.
This update covers the current main proof and shell-completion appendix.
The Basic facts section is outside the requested formalization scope. Its
analytic and operator results remain explicit inputs, alongside the cited
thermodynamic results reviewed in Appendix A. Existing helper identities
are retained.
The physical trace-class and Sobolev operator models are abstract interfaces.
Their usual laws and the cited thermodynamic/localization theorems are inputs,
not claims that those bodies of literature were rebuilt from Lean foundations.

Run from this directory

    python3 check.py

Use python3 check.py --jobs 4 for the same forced check with four compiler
processes. Each module waits for all of its local imports to finish.

This rebuilds every local module with warnings treated as errors, then runs
Audit.lean. The audit checks transitive axiom dependencies of non-internal local
declarations and prints the final theorem's full type and its principal input laws.
It also rejects proof dependencies on the retired assignment and contraction
arguments, and requires the revised shell-completion and principal lower,
upper, localization and scaling steps to occur in the main theorem's proof
dependencies.
It rejects sorryAx and all axioms other than propext, Classical.choice
and Quot.sound. An axiom audit does not discharge theorem hypotheses, which is
why the literature interfaces are documented separately. The saved verification
output is in verification.log. verification.json records source hashes for the
checked manuscript and local Lean files.

To check a source without rebuilding dependencies

    python3 check.py Jellium/Conjecture51.lean

To rebuild a source and its changed local dependencies

    python3 check.py --build Jellium/Conjecture51.lean

Including Audit.lean always reruns its checks even in incremental mode. The
script rejects a compiler whose version differs from lean-toolchain.

The project pins Lean 4.34.0-rc2 and mathlib commit
85e3a25e006c35636f0e53b0e9296caca2685bc0.
The current workstation reuses an existing dependency cache through the
untracked .lake/packages symlink. No dependency files were edited. In a fresh
environment with Lean installed, populate dependencies with lake update and
lake exe cache get. The ordinary lake build command is also supported.
