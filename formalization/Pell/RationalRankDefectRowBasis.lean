import Pell.RationalRowBasisCertificate
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Rational row bases under a rank defect

This small adapter combines the rational row-basis certificate with the
matrix-rank identity for row spans.  A strict rank defect of an integral
matrix after scalar extension to `ℚ` shows that the selected row basis has
strictly fewer elements than the number of columns.

The conclusion still contains the full selected-span, linear-independence,
and rational row-combination data.  It does not select columns, produce a
cofactor block, or make a determinant or counting assertion.
-/

namespace PellPaper

/-- A strict rank defect of the rationalization of an integral matrix gives
an actual row-basis certificate whose size is strictly smaller than the
number of columns. -/
theorem exists_rationalRowBasisCertificate_of_rationalRank_lt_card
    {ι κ : Type*} [Finite ι] [Fintype κ] (A : Matrix ι κ ℤ)
    (hrank : (A.map (algebraMap ℤ ℚ)).rank < Fintype.card κ) :
    ∃ (r : ℕ) (s : Fin r → ι) (c : ι → Fin r → ℚ),
      r = Module.finrank ℚ
        (Submodule.span ℚ (Set.range (A.map (algebraMap ℤ ℚ)).row)) ∧
      r < Fintype.card κ ∧
      Function.Injective s ∧
      HasRationalRowCombination A s c ∧
      Submodule.span ℚ
          (Set.range ((A.map (algebraMap ℤ ℚ)).row ∘ s)) =
        Submodule.span ℚ (Set.range (A.map (algebraMap ℤ ℚ)).row) ∧
      LinearIndependent ℚ ((A.map (algebraMap ℤ ℚ)).row ∘ s) := by
  have hfinrank : Module.finrank ℚ
      (Submodule.span ℚ (Set.range (A.map (algebraMap ℤ ℚ)).row)) <
      Fintype.card κ := by
    rw [← (A.map (algebraMap ℤ ℚ)).rank_eq_finrank_span_row]
    exact hrank
  obtain ⟨r, s, c, hr, hs, hc, hspan, hli⟩ :=
    exists_rationalRowBasisCertificate A
  refine ⟨r, s, c, hr, ?_, hs, hc, hspan, hli⟩
  rw [hr]
  exact hfinrank

end PellPaper
