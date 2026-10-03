# Reproducible local verification environment

## Active pinned environment

The active project uses:

- Lean `leanprover/lean4:v4.35.0-rc2`
- Compiler commit `11acb17ec6b07a8f9e9173e6845197929540936b`
- Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`
- Elan `4.2.4`, build `227caca13`
- Exact dependency revisions in `lake-manifest.json`

This compiler/mathlib pairing matches Mathlib's own pinned `lean-toolchain` and
meets the current Palomar minimum. Official sources:

- https://github.com/leanprover/lean4/releases/tag/v4.35.0-rc2
- https://github.com/leanprover-community/mathlib4/tree/065356127b1dc0016f66b7283ce0ce2c4055aa55
- https://github.com/leanprover/elan/releases/tag/v4.2.4
- https://github.com/PalomarRegistry/PalomarSubmission/blob/65f0154ed776cd26c224254aa57b379137f28b0d/toolchains.json

The project owns its elan/cache directories; user home and global shell
configuration are not modified. In this local workspace:

```bash
cd /workspace/shared/economics-next-proof
source ./env.sh
lake env lean --version
lake build
```

Ordinary `lake build` checks the modular proof library and standalone Challenge
and Solution. Challenge has exactly one deliberate theorem hole. The proof
library and Solution contain no admitted proofs.

## Fresh reproduction

Install official elan without changing the global PATH and source this project's
`env.sh`, or use an already installed elan with the exact project toolchain:

```bash
mkdir -p .toolchain/downloads .toolchain/elan
curl -fsSL https://github.com/leanprover/elan/releases/download/v4.2.4/elan-x86_64-unknown-linux-gnu.tar.gz \
  -o .toolchain/downloads/elan-v4.2.4.tar.gz
echo '42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63  .toolchain/downloads/elan-v4.2.4.tar.gz' | sha256sum -c -
tar -xzf .toolchain/downloads/elan-v4.2.4.tar.gz -C .toolchain/downloads
ELAN_HOME="$PWD/.toolchain/elan" .toolchain/downloads/elan-init \
  -y --no-modify-path --default-toolchain none
source ./env.sh
elan toolchain install leanprover/lean4:v4.35.0-rc2
lake exe cache get
lake build
```

The checksum records downloaded bytes; it is not a detached publisher signature.
Do not casually regenerate the exact dependency manifest. The matched Mathlib
cache downloaded/decompressed all8915 expected artifacts in this environment.

## Verification and boundaries

The rc2 targeted aggregate/examples/Challenge/Solution build and ordinary whole
project build passed. Main theorem, necessity, and sufficiency axiom audits
report only `propext`, `Classical.choice`, and `Quot.sound`.

Local logs and their exact commands/results are under `reports/`. A separate
fresh whole-Solution Lean kernel replay completed with exit0 and is recorded
there. The local bundled
Comparator could not start its build sandbox: bubblewrap reported
`Can't create file /root: Read-only file system`. Its sandbox was not disabled,
patched, or bypassed; no Comparator Challenge/Solution comparison verdict is
claimed. Direct bundled NanoDa and con-ron replays subsequently passed as
separate local kernel gates; their provenance and restrictions are recorded
in reports.

Current official policy snapshot:
https://github.com/PalomarRegistry/PalomarPolicy/blob/96b034cc31a72a63d4f4041911dce337a85c9a04/CONTRIBUTING.md

The future advisory workflow pairs `.github/workflows/submission.yml` and
`pipeline_commit` at PalomarSubmission
`65f0154ed776cd26c224254aa57b379137f28b0d`. It has not been triggered here. The
base report profile is `palomar-standard-v1`; the current execution catalogue
selects `palomar-namespace-16x32-v1`, requiring at least30064771072 bytes host
memory. This cloud machine has about9.7GiB, so local checks are not equivalent
to an official-profile run. No publication, submission, or registration occurred.

## Preserved historical stable environment

Before the Palomar minimum was checked, the proofs also compiled with stable
Lean4.34.1 (compiler5045d0056413266e57c625dcd7c365b10e377c52) and matching Mathlib
d13f23b723b8a846827a245b89c10fc7d3f11612. Its successful `.lake` state,
`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` remain preserved under
`.toolchain/stable-v4.34.1`. It is historical validation, below the current
Palomar minimum, and is not the active project configuration.

All `.toolchain/` material and generated `.lake/` contents must be excluded from
any future source commit/archive. They contain setup binaries, caches, and local
verification scratch files; they are not the deliverable theorem sources.

Additional independent local gates: target-closure export exit0; bundled
NanoDa0.4.17 exit0 with no typechecker errors; bundled con-ron --verified exit0.
Only the three standard axioms were permitted. See reports for exact targets,
configuration, binary digests and the harmless NanoDa pretty-printer notice.
These gates do not establish Comparator matching or official-profile acceptance.
