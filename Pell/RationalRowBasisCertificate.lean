import Pell.RationalRowSpanKernelTransport
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Rational row-basis certificates

For an integral matrix with finitely many columns, its rationalized row space
has a basis consisting of actual rows.  This file packages that finite
dimensional fact in the coordinatewise certificate expected by
`RationalRowSpanKernelTransport`.

The result selects rows and rational coefficients only.  It makes no claim
about a nonzero minor, an integral denominator clearing, or any determinant
or counting estimate.
-/

namespace PellPaper

open scoped BigOperators

/-- The rational row space of an integral matrix admits a basis made of
actual rows, together with explicit (though noncomputably chosen) rational
coefficients expressing every row in that basis. -/
theorem exists_rationalRowBasisCertificate
    {ι κ : Type*} [Fintype κ] (A : Matrix ι κ ℤ) :
    ∃ (r : ℕ) (s : Fin r → ι) (c : ι → Fin r → ℚ),
      r = Module.finrank ℚ
        (Submodule.span ℚ (Set.range (A.map (algebraMap ℤ ℚ)).row)) ∧
      Function.Injective s ∧
      HasRationalRowCombination A s c ∧
      Submodule.span ℚ
          (Set.range ((A.map (algebraMap ℤ ℚ)).row ∘ s)) =
        Submodule.span ℚ (Set.range (A.map (algebraMap ℤ ℚ)).row) ∧
      LinearIndependent ℚ ((A.map (algebraMap ℤ ℚ)).row ∘ s) := by
  classical
  let B : Matrix ι κ ℚ := A.map (algebraMap ℤ ℚ)
  obtain ⟨f, hfmem, hspan, hfli⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range B.row)
  choose s hs using hfmem
  have hfs : f = B.row ∘ s := by
    funext k
    exact (hs k).symm
  have hs_injective : Function.Injective s := by
    intro i j hij
    apply hfli.injective
    rw [hfs]
    change B.row (s i) = B.row (s j)
    rw [hij]
  have hselectedSpan :
      Submodule.span ℚ (Set.range (B.row ∘ s)) =
        Submodule.span ℚ (Set.range B.row) := by
    rw [← hfs]
    exact hspan
  have hselectedLI : LinearIndependent ℚ (B.row ∘ s) := by
    rw [← hfs]
    exact hfli
  have hrowmem : ∀ i, B.row i ∈ Submodule.span ℚ (Set.range f) := by
    intro i
    rw [hspan]
    exact Submodule.subset_span (Set.mem_range_self i)
  choose c hc using fun i =>
    (Submodule.mem_span_range_iff_exists_fun ℚ).mp (hrowmem i)
  refine ⟨Module.finrank ℚ (Submodule.span ℚ (Set.range B.row)), s, c,
    rfl, hs_injective, ?_, ?_, ?_⟩
  · intro i j
    have hij := congr_fun (hc i) j
    simp only [Finset.sum_apply, Pi.smul_apply] at hij
    change (∑ k, c i k * f k j) = B i j at hij
    change B i j = ∑ k, c i k * B (s k) j
    rw [← hij]
    simp_rw [hfs]
    rfl
  · simpa [B] using hselectedSpan
  · simpa [B] using hselectedLI

end PellPaper
