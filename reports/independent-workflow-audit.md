# Independent advisory workflow audit

Review date: 2026-10-03 UTC

## Verdict and exact reviewed bytes

Static review approves these workflow-only supplemental drafts:

- palomar-render-advisory.yml SHA-256: f293d5d631336c1dbc7aa56d7367b6a9ccb12eb4a2e4b0f47e8d658b9cd2380e
- palomar-verifier-advisory.yml SHA-256: 1e1e27fca34b56094343794a7cbab5bbcb4a445e84bee4e9b2ef921a00037c41

This review is AI-assisted, separate from drafting these workflows, and applies only to the listed bytes. It is not authorization to dispatch workflows, change runner security, expand account access, incur provider costs, or register the project. It does not assert a passing hosted verification or rendering result.

## Theorem and source identity

The reviewed mathematical candidate remains commit 0049ad934c29fd53c06ba79a70ae5d633991aea2. Independent git comparison found no change to Challenge.lean, Solution.lean, or the EconomicsNextProof proof sources. Challenge.lean at that commit has SHA-256 4ac34e136d44d285147139fd657faa4758620bc3f9a9300f884a6cf57066b0cd, matching the wrapper's hard guard.

The render wrapper requires its source_commit dispatch input to equal github.sha, binding the rendering source to the immutable dispatched workflow commit. It also requires the reviewed Challenge hash. A workflow-only supplement necessarily has its own commit; its proof-source diff must remain empty against the reviewed candidate. The original proof candidate is not replaced by an unreviewed theorem.

## Official pipeline provenance

Both workflows use PalomarSubmission commit 65f0154ed776cd26c224254aa57b379137f28b0d. Nine local official files were independently compared byte-for-byte with that pinned GitHub revision: the official render workflow, render_challenge.py, verification_profile.py, install_bwrap.sh, trusted_download.py, core_notation_audit.lean, render_report.py, and the two profile JSON files. All matched.

The render wrapper calls the unmodified official prepare and execute stages, including the official audit and sanitizer. The official compatible Verso release v4.35.0-rc2 independently resolved to 9f8096e40b31715b1d8d5997f15a0bd832f7e37d. The wrapper explicitly checks prepare's resolved Verso commit against this reviewed SHA before proceeding. Release-tag movement therefore fails that guard rather than silently substituting a different reviewed dependency.

## Profile and security checks

The official resolver explicitly supports palomar-standard-v1 as its hosted base profile, even though the profile catalogue's default is a Namespace profile. Independent pure resolver checks confirmed standard uses github-hosted ubuntu-24.04 and the published standard capacity/time limits. The verifier caller explicitly requests this standard profile; the render workflow defaults to it. The offered Namespace alternative is genuinely supported by the official catalogue, but availability is not permission to select or pay for that provider.

Workflow permissions are contents: read. Trusted pipeline checkouts are SHA-pinned and disable credential persistence. Dependencies use the official hash-locked installation commands. Untrusted candidate build/render execution remains within the official bubblewrap pipeline; no official sandbox was weakened or replaced.

The render wrapper's default-off approval input is checked before the pinned installer can run its conditional AppArmor branch. The guard requires a successfully readable known sysctl value of 0 or 1, and fails closed on missing or unknown values. If restriction is 1, the input must be explicitly true. The verifier caller has a separate prerequisite job requiring explicit true before invoking the unmodified official reusable workflow, whose installer can perform that conditional action.

The official installer conditionally writes /etc/apparmor.d/palomar-bwrap and loads a profile for the exact installed bwrap path, with its published flags and userns permission. This is security-sensitive. A separate specific user approval remains necessary before any dispatch that authorizes the branch. Static code review does not supply that approval.

## Mechanical and advisory distinctions

The verifier wrapper's request_id is falmagne0049 and passed the official twelve-lowercase-alphanumeric regex. Both YAML documents parsed, and every shell run body passed bash -n. The wrappers retain failure checks requiring an actual successful report rather than treating artifact upload as success.

The render workflow is explicitly advisory. Neither wrapper calls registration or claims registry acceptance. Premature mechanical-complete wording was removed. This audit establishes source/statement binding and safe static workflow structure, not execution success. Provider authentication, publication, invitation actions, workflow dispatch, and any security approval are handled separately under their own authorization.
