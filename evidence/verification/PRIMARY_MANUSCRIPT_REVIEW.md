# Review of the main manuscript proof routes

Date: 2026-10-19. Outcome: **accepted** for the source correspondence,
integration, and compiler checks described below. This is a critical review:
the constants, growing parameter range, and actual dependencies of the main
theorems determine whether the requested manuscript arguments were integrated.
The independent `readme_math_review` AI agent reviewed the statements before
integration and inspected the final sources and proof dependencies. It did
not author or edit the twelve mathematical modules listed below. This record
is independent AI review, not human certification.

## Source and frozen mathematical modules

The unchanged private `main_v4.tex` has SHA-256
`4290745fdf5234d3f1ccc6ed24cfdc48efde043241939b726713485b700099af`.
The source targets are `L:anisotropic-square` and its product corollary
`C:anisotropic-square` (lines 504–589), and the squarefree-to-general argument
in `T:uniform-exceptional` (lines 2451–2492).

These hashes were frozen before the independent compiler checks and verified
unchanged after both the focused checks and the broader rebuild:

| File | SHA-256 |
| --- | --- |
| `Pell/AnisotropicSharpSquareSieve.lean` | `65ab2bbd0905bd1304fcc74e49575f5c7f252ade12dde6fde4faffa7710cc9a1` |
| `Pell/IntrinsicOddHomogeneousPolynomialSquareSieveElementary.lean` | `bb535f1d0e7e6a6d7de6d60175f704f83f5248ae0e8458ace22a801d0636767f` |
| `Pell/DyadicResidualFullCellSquareSieveElementary.lean` | `c79c1daf7f1c0124fc24474d2dc806d1118cf2b9301221ecbc8d98e78a7509af` |
| `Pell/Main3LargeAnalyticElementaryIntrinsicSieveAt.lean` | `47141606aa9d55fb00381e7475de04128c9b84a8f28a9638c93b55340b109d19` |
| `Pell/PaperExceptionalDefinitions.lean` | `b16842df6b54ab6ef805e2b29e86cfd14fe9b64287d83ea0c848ccc8c616408f` |
| `Pell/Main3ElementarySquarefreeEstimate.lean` | `322393c186ed8e90feba3fdaca7ab2e5b30235f40fea11a2fce8d26d09d540b6` |
| `Pell/UniformDoubledParameterScale.lean` | `6e0049b7a2bd9f01a40c6fa53ec80b5bae58c56221188dd9be0c7c5da11a7faa` |
| `Pell/UniformDoubledParameterRestoration.lean` | `857e20e33ae57196e6aa9f3bdd4b558ffa60a871f610f377acfa6674cc8ddd4d` |
| `Pell/UniformDoubledParameterEstimate.lean` | `035dfa26168c41622715dfbfb2252a36efe069839a37670833b1353a2d91e90c` |
| `Pell/Main3ElementaryFinalAssembly.lean` | `9528735874fa194e7f2785717071096a9993a1dc90bc9bbf1f77e57be5e7fc96` |
| `Pell/FinalPaperResults.lean` | `a64cac2fa0aee02951a442e1682dd7500a50c13c0b19a3d3e5909a9717e314d7` |
| `Pell/UniformSquarePartRestoration.lean` | `d2848fcc6fa048dd1e96edc0dca7e3691f4519793a0917d56e9575a484140eec` |

## Mathematical and statement review

The general square-sieve theorem has absolute positive constants chosen before
the polynomial, odd degree, interval data, and value height. Repeated factors
are allowed. Its closed-real-interval form uses the actual integer window and
the literal height `2 + max |F|`. The zero polynomial is harmless because zero
values are excluded. The estimate has the manuscript bound
`log²(2 S₂) S₁ sqrt(S₂)` under `C log W ≤ sqrt(S₂)`, with `S₁ ≥ S₂ ≥ 1`.

The product corollaries have the source hypothesis
`C log W ≤ (S₁ S₂)^(1/4)` and bound
`K log²(2 S₁ S₂) S₁^(5/4) S₂^(1/4)`. Applying the rectangle theorem with
the side budget `sqrt(S₁ S₂)` is valid since it lies between `S₂` and `S₁`;
the counted integer window and its value height are unchanged. The literal
height and interval adapters preserve the same quantifier order.

The balanced and unbalanced production estimates both now call the general
odd-homogeneous rectangle theorem on the actual substituted eliminant.
The generic full-cell theorem and its `At` interface no longer have a
square-factor/resultant certificate premise. Source inspection and a separate
proof/type traversal confirmed that both production estimates contain
`eventually_oddHomogeneous_rectangle_squareSieve` and exclude
`exists_homogeneous_square_factor_with_bounded_resultant_certificate`.
The application budget `M ≤ UV` remains valid geometric bookkeeping; it is
not a restriction on the general standalone theorem.

The general-radicand estimate now uses the manuscript split `m = s²w` and
parameter `2 theta`. The actual high-kernel condition `sqrt X ≤ w` gives
`epsilon_w ≤ epsilon_m ≤ m^theta ≤ X^theta ≤ w^(2 theta)`.
The low-kernel cover contributes at most `2 X^(3/4)`. A dyadic block crossing
the split is retained with `sqrt X/2 ≤ W`. The high blocks have weight
`sqrt(X/W)`, and their geometric exponent is at least `1/4`, giving a
uniform denominator. Predicate monotonicity supplies the squarefree estimate
at `2 theta` from the existing squarefree API at `2 theta + 1/4`; the global
restoration itself uses the source parameter `2 theta`.

The inclusive `E` estimate saves `1/(1600 theta²)` in the range
`theta ≤ (1/3200) sqrt(log X/log log X)`. The strict manuscript endpoint
weakens this to the common constant `c = 1/3200`. The generic
`UniformExceptionalEstimate (1/6400)` adapter uses `theta ≤ 2 uniformQ theta`,
so `1/(6400 Q²) ≤ 1/(1600 theta²)`. Constants and the eventual threshold
precede the varying parameter. The strict/inclusive count comparison is
unchanged.

The extracted exceptional-count definitions and `uniformQ_le_theta` retain
their executable sources; the five extracted squarefree theorem types and
the elementary block-input definition are unchanged. The moved elementary
log-comparison helper is unchanged. To remove an import cycle, the finite
restoration module copies the existing elementary reciprocal-square-root
sum proof privately; the proof is unchanged apart from its name and privacy,
including the zero-index and zero-bound cases.

`Main3ElementaryFinalAssembly` retains a public compatibility name, but its
proof is the new doubled-parameter estimate. Its class-average assertion
therefore also uses the new route. `final_uniform_exceptional` directly uses
the strict doubled-parameter endpoint. `UniformSquarePartRestoration.lean`
is now only an import of the new estimate with a short compatibility comment;
the old global restoration proof bodies are removed.

## Actual proof and type dependency audit

The independent audit recursively traversed project constants occurring in
both declaration types and opaque proof values, using `getUsedConstants`,
`value? (allowOpaque := true)`, and an environment with exporting disabled.
The central `PellAudit.lean` now checks the same ten endpoints. Each must
contain all six required leaves below:

```text
PellPaper.smallFundamentalSolution_doubled_of_sqrt_le
PellPaper.exceptionalSet_subset_doubledParameter_cover
PellPaper.E_le_doubledParameter_geometric
PellPaper.eventually_oddHomogeneous_rectangle_squareSieve
PellPaper.eventually_sum_full_dyadicTarget_eliminant_squareFilters_le_elementary
PellPaper.eventually_fullCellElementaryOddHomogeneousPolynomialSieveAt
```

Each must exclude all seven obsolete restoration names:

```text
PellPaper.exists_pos_uniform_squarefreeDyadicCoverSum_le_of_main3BlockEstimates
PellPaper.uniformDyadicAllRadicandEstimate_one_div_6400_of_main3BlockEstimates
PellPaper.uniformExceptionalEstimate_one_div_6400_of_main3BlockEstimates
PellPaper.exists_pos_uniform_squarefreeDyadicCoverSum_le_elementary_of_large
PellPaper.uniformDyadicAllRadicandEstimate_one_div_6400_elementary_of_large
PellPaper.uniformExceptionalEstimate_one_div_6400_elementary_of_large
PellPaper.dyadicSquarePartExceptionalCount_le_sum_transferred_add_rpow
```

The independent run and the broader rebuild's central audit produced the
same actual output:

```text
PellPaper.field_class_average: 4469 project constants; missing required leaves []; old restoration leaves []
PellPaper.odd_class_average: 5013 project constants; missing required leaves []; old restoration leaves []
PellPaper.uniform_exceptional: 3812 project constants; missing required leaves []; old restoration leaves []
PellPaper.pell_unit_growth_density: 3837 project constants; missing required leaves []; old restoration leaves []
PellPaper.fixed_power_density: 3821 project constants; missing required leaves []; old restoration leaves []
PellPaper.final_field_class_average: 4468 project constants; missing required leaves []; old restoration leaves []
PellPaper.final_odd_class_average: 5012 project constants; missing required leaves []; old restoration leaves []
PellPaper.final_uniform_exceptional: 3811 project constants; missing required leaves []; old restoration leaves []
PellPaper.final_pell_unit_growth_density: 3836 project constants; missing required leaves []; old restoration leaves []
PellPaper.final_fixed_power_density: 3820 project constants; missing required leaves []; old restoration leaves []
```

## Compiler evidence and its scope

Lean is pinned to `leanprover/lean4:v4.33.1`. The independent focused command
was `python3 build/work-in-progress/independent-review-run-lean.py FILE`,
which invokes Lean with `-DwarningAsError=true -T0 -j 2`. Strict compilations
of `Pell/FinalClassAverages.lean`, `Pell/MainResults.lean`, `Pell.lean`, and
`PellAudit.lean` all exited zero. A separate independent route-audit source
also compiled successfully.

That focused run used an isolated overlay containing the current twelve
mathematical module artifacts and cached unchanged project intermediates,
to avoid races with the simultaneous broader rebuild. It was not by itself
a fresh rebuild of their entire dependency graph.

The broader rebuild subsequently strictly compiled all 67 affected modules,
including the final class-average modules, `MainResults`, `Pell`, and
`PellAudit`. The reviewer independently matched all 67 distinct zero-exit
entries against `primary-rebuild-plan.json` and inspected the final success
line. Both actual central audit outputs passed `scripts.verify.check_audit`:
27 axiom reports, all 17 mandatory endpoints, nine literal type challenges,
and ten successful dependency traversals. Every axiom report contains exactly
`propext`, `Classical.choice`, and `Quot.sound`.

The broader rebuild reuses unaffected project artifacts and pinned external
caches. This record does not certify a fresh build of all 857 modules or a
GitHub Actions run. No separate kernel replay or human certification was
performed. Full fresh verification is reported separately.

| Compiler receipt | SHA-256 |
| --- | --- |
| `primary-rebuild-plan.json` | `b70841fcdeb9e30848ff8639d9631693e8a5d0251035a753d87a81f17517a5d8` |
| `primary-rebuild-console.log` | `5cec548eaa0d5d1a5b9fdaa5bc67bc57f3de2701ffeab9cacb7e4c57311d9fa0` |
| `primary-PellAudit.log` | `79f86f97dcf9e1ae2a5b2c098204ab95098d7b26a86851d6a85f79da208d1853` |
| `independent-primary-route-review.log` | `dc6f84cd3c47470766538174a5bcc93550c93ce1fe2cc656c4a269bfbf2da15f` |

These receipts were read from `build/work-in-progress/`; generated compiler
files are not part of the source archive. The committed central audit makes
the checks reproducible. Its reviewed source hash is
`4f86f96b881d7737ac7bf4de22558a0460470484badc751227af5b4e438b953f`.

## Documentation review

The README correctly states the fundamental-discriminant bound
`sum L(1, chi_D)^2 ≪ X`, defines `chi_D(n)` by the Kronecker symbol, and
explains that the summand is the square of the Dirichlet L-value at `s = 1`.
It distinguishes fundamental `D₀` from order discriminants `D₀ f²`, with
conductor `f`. The class-average proof still uses this fundamental second
moment followed by a conductor class-number comparison, rather than the
manuscript's second moment over all positive nonsquare order discriminants.
That is the remaining stated substantive proof-route difference. The old
limitations concerning restoration and the standalone square sieve were
removed after the actual routes were replaced. The proof map, verification
notes, and machine-readable status agree with the reviewed statements.
