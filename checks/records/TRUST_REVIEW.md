# Trust and reproducibility review

This is an AI-assisted review of the source dependencies and verification
boundary. Statement correspondence is separately reviewed in
[`SEMANTIC_REVIEW.md`](SEMANTIC_REVIEW.md) by an AI agent independent of the
author of the public entry point. No independent human certification or
independently implemented proof-kernel replay is claimed.

## Mathematical trust boundary

The public entry point is `Pell/MainResults.lean`. Its six explicit declarations
are `PellPaper.proper_form_classes_finite`, `field_class_average`,
`odd_class_average`, `uniform_exceptional`, `pell_unit_growth_density`, and
`fixed_power_density`. None takes a conjecture, numerical certificate,
arithmetic estimate, analytic bound, or classification assertion as a supplied
argument. The finiteness theorem has only its discriminant and intended
membership condition; the fixed-power theorem has only its exponent and
positivity condition.

The endpoints use the included proved implementation. In particular:

- The all-order class-average caller supplies the conditional large-block
  assembly with `main3LargeAnalyticBlockSumEstimateElementaryInput_proved`.
  That theorem unfolds the exact interface and uses the internally proved
  elementary large-block endpoint. Its estimate is supplied, rather than left
  as a public assumption.
- The odd-class caller supplies the Wilson rectangle interface with
  `main4WilsonWeightedRectangleEstimate_proved`, constructed from finite
  Selberg weights and moment bounds. Its required Friedlander–Iwaniec estimate
  is also supplied by its proved endpoint.
- `FinalPaperResults` derives the strict-cutoff exceptional-set theorem and
  both growth conclusions from the elementary assembly. The headline route
  does not require an unproved Weil bound or an external numerical certificate.

Conditional intermediate theorem schemas remain valid APIs. Their presence
does not make a final theorem conditional when its actual caller supplies
the proved inputs. The separate semantic review checks the actual arithmetic
objects, finiteness, cutoffs, scales, and uniform quantifier order.

Only `propext`, `Classical.choice`, and `Quot.sound` are allowed in the final
transitive-axiom reports. Source closure is not a substitute for inspecting
those actual compiler reports; their completed outcome belongs to
`summary.json` and `AXIOM_AUDIT.md` in this evidence directory.

## Included proof dependencies

Lean is pinned to `leanprover/lean4:v4.33.1`; Mathlib is locked at
`0df444a360eaa60ab8c11dca51a86af692955474`. The lockfile also pins all eight
other external Git dependencies. The source-tree check in this review found
all nine Git revisions equal to their lockfile entries and no tracked source
changes.

The additional mathematical proof sources are included in the repository.
The 82-module TauCeti genus-theory closure is rebuilt from source. Adapted
FormalPantheon and PrimeNumberTheoremAnd sources are also compiled locally;
provenance and the upstream licenses are recorded in `THIRD_PARTY.md` and the
vendor directory. These are included Lean proofs above Mathlib, rather than
externally assumed mathematical theorems.

## Verification guardrails inspected

The current source/import scan covers all 851 local Lean modules and passed
this review's preflight. The integrity check also passed for 875 frozen
manifest entries. The verifier:

- removes nested comments and strings before scanning for unfinished proofs,
  authored axioms, native-compiler escapes, and disabled strict warnings;
- checks the complete local import graph, including modules outside the main
  endpoint import closure;
- requires hashes for all local Lean source, the manuscript and pinned
  configuration, plus the verifier, tests, packager and CI workflow;
- rejects missing, duplicate, malformed or unsafe manifest entries and verifies
  both the main and vendored source manifests;
- creates a new output directory for every Pell and vendored TauCeti module in
  direct mode, without old local proof objects on its `LEAN_PATH`;
- compiles with warnings treated as errors, respecting local import order and
  propagating compiler failures;
- compiles the six literal type challenges in `PellAudit.lean`, including
  expanded class-average scales and the strict exceptional cutoff;
- requires all twelve public and implementation/meaning axiom reports,
  rejecting missing or duplicate reports and every axiom outside the allowed
  three names;
- rechecks the local module set and frozen source hashes after compilation and
  records source/object hashes, compiler identity and dependency receipts.

The full fresh compiler run is a separate integration gate. This review did
not start a competing build and does not infer its success from source scans
or from the existence of a status file. The completed run, exact commands and
remaining limits are recorded in `VERIFICATION.md` and its compiler receipts.

## Remaining assurance boundary

The build reuses the pinned external Mathlib/dependency compiled caches. Clean
Git source trees and matching revisions do not independently prove that an
arbitrary cached object was built from those exact sources. Those caches are
the documented external artifact trust boundary. All Pell and vendored
TauCeti objects are freshly generated by the publication check.

This review is not a reconstruction of every transitive proof line, an
independent human sign-off, or a separate proof-kernel implementation. The
strict compiler build, transitive-axiom checks, independent AI statement
review, and source-integrity receipts address distinct failure modes; none
should be substituted for another.
