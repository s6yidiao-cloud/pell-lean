import Pell.DirichletCharacterOrderedLValue
import Pell.NonprincipalDirichletPolyaVinogradov

/-!
# Quantitative ordered approximation of nonprincipal L-values at one

These statements concern the actual analytic Dirichlet `LFunction`, not an
unordered `LSeries` at one. The bounded-prefix input in the generic analytic
lemmas is discharged by the proved all-nonprincipal Pólya--Vinogradov theorem.
No primitivity, conductor, or caller-supplied character-sum estimate is assumed.
-/

open Filter
open scoped BigOperators Topology

namespace PellPaper

/-- Every nonprincipal character's ordered reciprocal prefixes converge to
its analytic L-value at one. -/
theorem tendsto_nonprincipalDirichletCharacter_reciprocalPrefix
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N,
      chi (n : ZMod q) / (n : ℂ)) atTop
      (𝓝 (DirichletCharacter.LFunction chi (1 : ℂ))) :=
  tendsto_dirichletCharacter_reciprocalPrefix_of_prefixBound chi hchi
    (2 * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)))
    (nonprincipalDirichletCharacter_prefix_norm_le chi hchi)

/-- Uniform truncation at the exact natural endpoint `N > 0`, valid for
all nonprincipal characters, including imprimitive ones. -/
theorem norm_nonprincipalDirichletCharacter_LFunction_one_sub_prefix_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (N : ℕ) (hN : 0 < N) :
    ‖DirichletCharacter.LFunction chi (1 : ℂ) -
        ∑ n ∈ Finset.Icc 1 N, chi (n : ZMod q) / (n : ℂ)‖ ≤
      4 * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)) / (N : ℝ) := by
  calc
    ‖DirichletCharacter.LFunction chi (1 : ℂ) -
        ∑ n ∈ Finset.Icc 1 N, chi (n : ZMod q) / (n : ℂ)‖ ≤
        2 * (2 * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ))) / (N : ℝ) :=
      norm_LFunction_one_sub_reciprocalPrefix_le_of_prefixBound chi hchi
        (2 * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)))
        (nonprincipalDirichletCharacter_prefix_norm_le chi hchi) N hN
    _ = 4 * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)) / (N : ℝ) := by ring

end PellPaper
