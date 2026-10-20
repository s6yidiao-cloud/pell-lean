# Compiler receipt

Observed compiler:

```text
Lean (version 4.33.1, arm64-apple-darwin24.6.0, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)
```

Command from the repository root:

```sh
python3 scripts/verify.py --mode direct --dependencies ../.lake/packages --jobs 3 --lean-threads 2 --logs build/verification/publication
```

All Pell and vendored TauCeti outputs were compiled into a newly created
temporary directory. Old local proof objects were absent from its `LEAN_PATH`.
Pinned external Mathlib/dependency caches were reused; their source revisions
and tracked-source cleanliness were checked against the lockfile. The actual
per-dependency receipts are in `summary.json`.

The local system Git requires an unaccepted Xcode license; the verifier used
an already-installed portable Git. No system license or configuration changed.
This is Lean source elaboration with kernel checking. No independently
implemented proof-kernel replay or independent human certification is claimed.
