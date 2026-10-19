import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# Rank-two triangular integer submodules

This literal span is the common object for the independent Hermite
classification, index calculation, and finite-parameter count. No
normalization or nonvanishing assumption is needed for its definition.
-/

namespace PellPaper

/-- The integer lattice with column generators `(a,0)` and `(b,d)`. -/
def rankTwoHermiteSubmodule (a b d : ℤ) : Submodule ℤ (Fin 2 → ℤ) :=
  Submodule.span ℤ {![a, 0], ![b, d]}

/-- Membership is the literal two-coordinate integer linear combination. -/
theorem mem_rankTwoHermiteSubmodule_iff (a b d : ℤ) (v : Fin 2 → ℤ) :
    v ∈ rankTwoHermiteSubmodule a b d ↔
      ∃ x y : ℤ, v 0 = a * x + b * y ∧ v 1 = d * y := by
  rw [rankTwoHermiteSubmodule, Submodule.mem_span_pair]
  constructor
  · rintro ⟨x, y, h⟩
    refine ⟨x, y, ?_, ?_⟩
    · simpa [mul_comm] using (congr_fun h 0).symm
    · simpa [mul_comm] using (congr_fun h 1).symm
  · rintro ⟨x, y, h0, h1⟩
    refine ⟨x, y, ?_⟩
    funext i
    fin_cases i
    · simpa [mul_comm] using h0.symm
    · simpa [mul_comm] using h1.symm

theorem first_mem_rankTwoHermiteSubmodule (a b d : ℤ) :
    ![a, 0] ∈ rankTwoHermiteSubmodule a b d :=
  Submodule.subset_span (by simp)

theorem second_mem_rankTwoHermiteSubmodule (a b d : ℤ) :
    ![b, d] ∈ rankTwoHermiteSubmodule a b d :=
  Submodule.subset_span (by simp)

end PellPaper
