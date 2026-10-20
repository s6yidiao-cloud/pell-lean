# Hosted manuscript-primary compiler receipt

Outcome: **passed**, all **857** local modules (773 Pell modules, 82 vendored
TauCeti modules, the importing root and central audit). All nine literal type
challenges and 27 transitive-axiom reports passed. The verifier requires
17 named endpoints and permits only `propext`, `Classical.choice` and
`Quot.sound`. The ten main proof/type closures passed the six-required-leaf
and seven-forbidden-leaf audit.

Source commit: `52ace63b6294009c1a7633d7466302a1efc3e4be`.

- [Successful run #9](https://github.com/s6yidiao-cloud/pell-lean/actions/runs/39291683619)
- [Compiler job](https://github.com/s6yidiao-cloud/pell-lean/actions/runs/39291683619/job/118193648308)
- [Original verification artifact](https://github.com/s6yidiao-cloud/pell-lean/actions/runs/39291683619/artifacts/12209052300)

The original `lean-verification.zip` has SHA-256
`2ebaecc8d045f94e72e9486809adfc87742a9bac2ac43f71cd9efcf4a9c2cfa1`,
matching the artifact digest displayed by GitHub. The artifact was downloaded
through the owner's signed-in Chrome session. Its summary, per-module receipts,
frozen input hashes and raw central-audit output are preserved here.

Compiler:

```text
Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)
```

Command:

```sh
python3 scripts/test_verify.py
python3 scripts/verify.py --mode direct --jobs 1
```

All nine guardrail tests passed. The verifier took **2233.681 seconds** with
one compiler process and two Lean threads; the whole workflow took 40m 29s.
It compiled every local and vendored module into a new temporary directory,
including modules unused by the public entry point. No earlier project or
vendored proof object was reused. All nine external dependency source trees
matched their pinned revisions and had no tracked changes. Available external
compiled caches were reused. Those external caches remain the documented trust boundary.

The input manifest SHA-256 is
`af22bfef63093774593ec7f16291452f6088bc641d22e79d7fbc2099fc94f467`.
The manifest was checked unchanged before and after compilation. The exact
manifest preserved here was reconstructed from the artifact's input hashes
and verified against that SHA-256. `source-hashes.json` covers 890 input files.

Every one of the 857 current Lean sources was compared with the per-module
CI source hash and matched. Follow-up changes fix README math rendering and
record the successful test in documentation and receipts; the Lean proofs,
verifier, toolchain, dependency pins and central audit are unchanged. The
repository-root manifest now covers those follow-up files, while this frozen
manifest continues to describe the tested snapshot.

The prior 851-module publication and 854-module standalone-extension receipts
remain unchanged. The independent primary-route review is
`../PRIMARY_MANUSCRIPT_REVIEW.md`. No human certification or replay by a
separately implemented proof kernel is claimed.
