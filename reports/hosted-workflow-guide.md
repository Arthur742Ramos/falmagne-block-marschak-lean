# Advisory hosted verification and trusted rendering

These manual workflows use the official PalomarSubmission pipeline at
65f0154ed776cd26c224254aa57b379137f28b0d. They do not perform intake or registration.
The source proof is unchanged from independently reviewed commit
0049ad934c29fd53c06ba79a70ae5d633991aea2.

The verifier explicitly selects the official supported GitHub-hosted
palomar-standard-v1 profile. The renderer uses the same profile by default.
Primary implementation evidence is in standard-profile-evidence.log; selecting
this supported profile changes no official verification limits or sandbox.

Both workflows have a default-off conditional AppArmor approval input. Before
setting it true, obtain specific permission for the official installer, when
Ubuntu's restriction is1, to create/load /etc/apparmor.d/palomar-bwrap for the
exact pinned sandbox executable on the disposable runner. This is separate from
permission to publish source or grant OAuth workflow access. The narrow rule
is described in independent-workflow-audit.md; all official confinement probes
remain in place.

After that specific permission and source publication, an authorized responsible
maintainer may use the following. Set SOURCE_COMMIT to the exact published
workflow commit; the renderer rejects any input different from its dispatched
GitHub SHA. Avoid concurrent source changes while these checks are running.

```bash
gh workflow run palomar.yml --repo Arthur742Ramos/falmagne-block-marschak-lean \
  --ref main -f authorization_relationship='I am a responsible author or maintainer' \
  -f approve_binary_scoped_apparmor=true

gh workflow run palomar-render.yml --repo Arthur742Ramos/falmagne-block-marschak-lean \
  --ref main -f source_commit=SOURCE_COMMIT \
  -f challenge_sha256=4ac34e136d44d285147139fd657faa4758620bc3f9a9300f884a6cf57066b0cd \
  -f execution_profile=palomar-standard-v1 \
  -f approve_binary_scoped_apparmor=true
```

The renderer additionally requires toolchain-compatible Verso commit
9f8096e40b31715b1d8d5997f15a0bd832f7e37d. It invokes the unmodified official
trusted notation audit and runtime/static sanitizers. Seven official fixture
tests passed locally; execution success must still come from actual hosted
reports. Download and inspect reports, not merely the workflow's badge.
