# Independent review of the manuscript extensions

Date: 2026-10-19. Review tier: **Critical** for both extensions, because
uniform constants, growing parameters, interval endpoints, and the proof route
determine the source correspondence. The reviewer was the separate
`semantic_review` AI agent, which did not author the three reviewed modules.
The source statements were ratified before proof generation.

## Frozen source and reviewed files

The unchanged private `main_v4.tex` has SHA-256
`4290745fdf5234d3f1ccc6ed24cfdc48efde043241939b726713485b700099af`.
The source targets are `L:anisotropic-square`, lines 504–589, and the
squarefree-to-general argument in the proof of `T:uniform-exceptional`,
lines 2451–2492.

| Reviewed module | SHA-256 |
| --- | --- |
| `Pell/AnisotropicSharpSquareSieve.lean` | `ff4fadbeb09065e919dd8ccc4981d7ecd513b34c2a2a340a940cabd93ebd1ed2` |
| `Pell/UniformDoubledParameterRestoration.lean` | `3853bd64e032f196518ad46c9949a171e1a1b74865130033117c24c844bea4a3` |
| `Pell/UniformDoubledParameterEstimate.lean` | `8ba031efb9d2548420a9d1ff5f45ae02a74e80a4f8e2396d19c205a36fc321b6` |

## Sharp square sieve: accepted

`PellPaper.anisotropic_sharp_squareSieve` proves the source bound with
`log²(2 S₂) S₁ sqrt S₂` and the literal value height `2 + max |F(x,y)|`.
Both positive constants precede the polynomial, degree, offsets, interval
endpoints, and value height. The degree is arbitrary and odd; repeated factors
are allowed, and no squarefreeness, resultant, discriminant, or coefficient
condition is hidden in the statement. Including the zero polynomial is a
harmless strengthening because zero values are excluded from the count.

The reviewer checked the semantic closure of `closedRealRectangle` and
`homogeneousRectangleValueHeight`. Integer points are encoded by
`Icc (ceil a) (floor b)`; the empty-set supremum is zero. The explicit interval
adapter proves that each integer cardinality is at most twice the real
interval length when that length is at least one. The endpoint convention is
closed real intervals. The general integer-shifted rectangle theorem also
allows arbitrary real side budgets; separate adapters for open and half-open
real intervals are not claimed here.

The proof instantiates the existing elementary square-factor sieve with
`Delta = c = r = 1` and `J = F`, so no polynomial certificate budget remains.
The sieve scale is `ceil (sqrt S₂)`, lies between `sqrt S₂` and
`2 sqrt S₂`, and is forced beyond the absolute eventual threshold by the
hypothesis `C log W ≤ sqrt S₂`, using `W ≥ 2`. The cubic and perimeter errors
are absorbed into the stated bound using `S₂ ≤ S₁`. This does not assume
the dyadic application restriction `M ≤ UV`.

## Doubled-parameter restoration: accepted

`PellPaper.uniform_exceptional_doubled_parameter` proves the literal strict
paper count with the absolute constant `c = 1/3200` in both the growing range
and the saving exponent. The positive implied constant and the eventual
threshold precede the universal quantifier over `theta`.

The reviewer checked the following fragile steps and their definitions:

- `smallFundamentalSolution_doubled_of_sqrt_le` uses actual fundamental Pell
  solutions and `epsilon_w ≤ epsilon_m ≤ m^theta`. The hypothesis on the
  actual kernel is `sqrt X ≤ w`, giving `X^theta ≤ w^(2 theta)`.
- `doubledParameterLowCover_card_le` counts all low kernels, validly dropping
  the squarefree and small-solution restrictions. Exact root fibres give
  weight `sqrt(X/w)` and total at most `2 X^(3/4)`. Including the equality
  boundary in this cover only overcounts.
- `exceptionalSet_subset_doubledParameter_cover` performs the actual
  high-kernel transfer before dropping the kernel restriction inside a
  dyadic block. Ordinary dyadics can straddle the split; their retained
  scales satisfy `sqrt X/2 ≤ W`, which is sufficient for the separate
  admissibility comparison.
- `E_le_doubledParameter_geometric` multiplies the block bound by
  `sqrt(X/W)` and sums exponent `1/2-d ≥ 1/4` geometrically. The denominator
  is uniformly at least `2^(1/4)-1`; no parameter-dependent implied constant
  is introduced.
- The closed squarefree theorem at parameter `2 theta` has an API count at
  `2 theta + 1/4`; predicate monotonicity bounds the required count at
  `2 theta`. It yields `d = 1/(1600 theta²)`. Weakening the saving to
  `1/(3200 theta²)` retains one constant in the range and conclusion.
- `paperExceptionalCount_le_E` transports the inclusive integer envelope to
  the manuscript's strict real cutoff. No arbitrary-radicand estimate is
  used to supply the new endpoint.

## Actual dependency-route check

An independent Lean metaprogram recursively traversed the types and proof
bodies of project constants, using `Expr.getUsedConstants` and
`ConstantInfo.value? (allowOpaque := true)` in the imported environment.
External foundations cannot depend on later Pell declarations and were
pruned. For `uniform_exceptional_doubled_parameter`, the actual result was:

```text
Project proof/type route contains 3862 project constants.
Old arbitrary-radicand endpoint matches: []
```

The rejected name families were `uniformExceptionalEstimate`,
`uniformDyadicAllRadicandEstimate`, `final_uniform_exceptional`, and
`PellPaper.uniform_exceptional`, excluding the new endpoint and its generated
auxiliary declarations. Source inspection separately confirmed that the
existing squarefree bound composes balanced and unbalanced estimates; it does
not derive its count from an arbitrary-radicand endpoint. The analogous
squarefree dependency traversal visited 3796 project constants and also
returned no old arbitrary-radicand endpoint matches. This check distinguishes
importing a module that contains an old endpoint from actually using that
endpoint in the new proof.

## Compiler and trust boundary

The direct iteration compiler used pinned Lean `v4.33.1` with
`-DwarningAsError=true -T0 -j 2`. All three reviewed modules passed their
strict author compiles. The independent route check passed through
`build/work-in-progress/run-lean.py`; its temporary audit source is not a
public theorem or an additional mathematical assumption.

An independent strict check of
`build/work-in-progress/ManuscriptExtensionTypeAudit.lean` imported both final
modules, printed both final types, and ran all eight `#print axioms` commands.
The resulting actual-type and transitive-axiom reports for the sharp sieve's
parameterized, rectangle, interval, and literal-height declarations and the
doubled route's pointwise transfer, low cover, finite aggregation, and final
endpoint contain exactly `propext`, `Classical.choice`, and `Quot.sound`.
No new mathematical axiom, numerical certificate, `sorryAx`, or
`Lean.trustCompiler` is accepted. These source and semantic checks are
separate from the fresh integration compiler receipts recorded elsewhere.

This is independent AI semantic review, not independent human certification
or replay by a separately implemented proof kernel. It does not independently
re-prove every already checked algebraic identity or certify the provenance
of reused external dependency caches.
