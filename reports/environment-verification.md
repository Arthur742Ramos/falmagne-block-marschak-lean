# Local environment and verification gates

Checked 2026-10-03; sources frozen for these checks after module-system conversion.

## Exact active versions

- Lean4.35.0-rc2 compiler11acb17ec6b07a8f9e9173e6845197929540936b
- Mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55
- Elan4.2.4 build227caca13
- PalomarSubmission policy/workflow65f0154ed776cd26c224254aa57b379137f28b0d
- PalomarPolicy96b034cc31a72a63d4f4041911dce337a85c9a04

Exact manifests/compiler pins are source-controlled inputs; local setup/cache
paths are excluded and are not part of the candidate package.

## Completed local gates

All commands below ran with the project's isolated elan/cache environment.

1. `lake build EconomicsNextProof.Falmagne EconomicsNextProof.Examples Challenge Solution`
   - Exit0 on active rc2; modular aggregate, examples, and standalone surfaces
   - Log: `local-rc2-targeted-build.log`
2. `lake build`
   - Exit0; defaultTargets are EconomicsNextProof, Challenge, Solution
   - Log: `local-rc2-build-all.log`
3. `lake env lean /workspace/shared/economics-next-proof/Solution.lean` and
   `lake env lean /workspace/shared/economics-next-proof/Challenge.lean`
   from the separately prepared rc2 project before root migration
   - Both exit0; Solution had unused-variable linter warnings; Challenge only
     its single deliberate theorem hole
4. `lake env lean .toolchain/audits/AuditSolution.lean`
   - Exit0; the audit imports Solution and prints axioms for
     Falmagne.falmagne_blockMarschak, Falmagne.randomUtility_necessary, and
     Falmagne.randomUtility_sufficient
   - Each uses only propext, Classical.choice, Quot.sound
   - Log: `local-rc2-axioms.log`
5. Official pinned Python contracts, with installed PyYAML6.0.3
   - load_formalization_metadata: pass
   - load_comparator_config: pass for theorem plus11 substantive definitions
   - inspect_lean_sources: pass for explicit candidate snapshot of all13 Lean
     source files, requiring module headers and≤10000 lines per file
   - Challenge84 lines/3029bytes fits≤1000 lines and100KiB
   - unique root LICENSE filename: pass
   - LICENSE bytes exactly match canonical pinned Mathlib LICENSE (cmp exit0)
   - Ruby/Licensee unavailable; automatic SPDX recognition not run
   - Workflow uses revision/pipeline_commit pairing matches the official pin
   - Log: `local-package-contract.log`

Challenge's deliberate `sorry` is intentional statement-only Comparator input.
The proof library and Solution contain no admissions; the compared proof's
standard-only axiom result is separately recorded above.

## Comparator limitation

`lake comparator --config comparator.json` initially exited2 because the elan
proxy PATH did not include the bundled nanoda_bin. This discovery issue was
corrected by adding the installed rc2 toolchain's bin directory to process PATH.
The subsequent identical comparator invocation exited1 at sandbox dependency
resolution:

```
bwrap: Can't create file /root: Read-only file system
error: Child exited with 1
```

Log: `local-rc2-comparator.log`. Official installed Lake source
`Lake/CLI/Check.lean:buildSandboxArgs` hardcodes the masked home mount targets and
forces HOME=/tmp/home; no supported HOME/XDG/project-root override fixes that
mount target. The sandbox was never disabled, patched, or replaced by a weaker
wrapper. A Comparator statement/definition match remains unestablished in this
environment. Subsequent direct independent kernel replays passed as recorded
below; they do not supply Comparator matching.

## Fresh bundled Lean-kernel gate

`lake env leanchecker --fresh Solution` started15:27:54 UTC. It independently
replays all constants imported by and defined in Solution into a fresh
Lean-kernel environment. Terminal status was verified at15:37:35 UTC: exit0. Log and exact invocation
are recorded in `local-rc2-leanchecker.log`. This is a
separate Lean-kernel gate, not Comparator matching or independent NanoDa replay.

## Official-profile distinction

No official workflow, public publication, submission, or registration was run.
The reusable workflow is advisory verification and not itself registration.
Its base report profile is palomar-standard-v1; the pinned current execution
catalogue default is palomar-namespace-16x32-v1, requiring at least30064771072
bytes host memory, with a base free-workspace floor21474836480bytes. This local
cloud machine has about9.7GiB host memory, so local results cannot claim official
standard-profile equivalence. Full official mechanical verification remains a
future separately authorized gate.


## Additional independent local kernels: passed

The frozen standalone Solution was exported using the officially supported
`lake env leanexport Solution -- <exact declaration target list>` interface.
`local-export-targets.json` records the exact targets: the main theorem, all11
compared definitions, the three permitted standard axioms, quotient primitives,
and additional kernel primitive definitions. The exporter traverses every
requested target's dependency closure. Exit0; export size77,413,293bytes;
SHA256 in `local-export-sha256.txt`. The77MiB export remains local setup output,
not a submitted source file. Recreate it from the frozen source and exact targets.

Sequential direct checker invocations on this export:

- `nanoda_bin <local-nanoda-config.json>`: exit0,16,752 declarations checked,
  no typechecker errors. Its config permits only propext/Quot.sound/Classical.choice,
  unpermitted_axiom_hard_error=true, unsafe_permit_all_axioms=false,
  nat_extension=true, string_extension=true, num_threads4. The reusable config
  in this report uses a relative export path; the run used the same config with
  the actual absolute local export path. NanoDa0.4.17 printed one pretty-printer
  notice, `Unable to print axioms`; this was not a typechecker error or rejection.
  Full log: `local-rc2-nanoda.log`.
- `con-ron --verified --jobs=4 --progress=1000 <export.ndjson>`: exit0,
  accepted15,679 declarations in verified mode. Full log:
  `local-rc2-conron.log`.

The tools were bundled with the pinned official Lean4.35.0-rc2 distribution;
exact checker/exporter binary SHA256 values are in
`bundled-kernel-binary-sha256.txt`. Direct local replays are separate kernel
validation gates. They do not supply a Comparator Challenge/Solution equality
verdict and are not an official Palomar-profile run. The comparator sandbox
limitation above still applies. All frozen Lean source hashes were rechecked
unchanged after these replays.
