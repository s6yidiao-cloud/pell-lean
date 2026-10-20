# Full verification after repository reorganization

Source commit: `ea6bac672a9b9c6b937eacc98fe54ab576a04f90`.

Both hosted runs passed on 20 October 2026:

| Repository | Run | Workflow time | Verifier time |
| --- | --- | --- | --- |
| pell-lean | [#14](https://github.com/s6yidiao-cloud/pell-lean/actions/runs/39362153247) | 53m 46s | 3066.743 s |
| pell-lean-release | [#3](https://github.com/s6yidiao-cloud/pell-lean-release/actions/runs/39362161020) | 49m 21s | 2733.613 s |

Each run freshly compiled all 857 authored modules with Lean 4.33.1 on Linux,
one compiler process and two Lean threads. The nine literal type challenges,
ten proof-route checks, and all 27 axiom reports passed; all reports contain
only `propext`, `Classical.choice`, and `Quot.sound`. The 19 guardrail tests
passed. Nine external dependency source revisions and tracked-source
cleanliness were checked; external compiled caches were reused.

The workflow ran:

```sh
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/verify.py --mode direct --jobs 1
```

Both runs recorded exactly the same 912-file input snapshot, SHA-256:
`d4ce46eb30bc7da9e956fa3460cf55c5fb08712d631bdf180d26ac08268a3737`.
`SOURCE_SHA256SUMS` and `source-hashes.json` describe that checked snapshot;
`modules.json` records all source and freshly compiled object hashes.
`summary.json` is the unmodified main-run receipt; `AXIOM_AUDIT.md`
includes the unmodified compiler output. `release-summary.json` is the
unmodified release-run summary.

Downloaded artifact SHA-256:

- Main: `2ba1565386a03caab2a92a72d1a24e0ba9342e92aeb16eaecdb16f694544798b`.
- Release: `b07cab17c0ea92766ddc2eb633e806962823612f1e2d8159e62240cb36c1086c`.

These records and the accompanying status/documentation updates were added
after the runs. All Lean sources, verifier scripts, dependency configuration,
and the CI workflow still match the checked inputs.
