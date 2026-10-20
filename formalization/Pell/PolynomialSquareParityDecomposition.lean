import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic

/-!
# Square-parity decomposition of an integral polynomial

This is the univariate algebraic step behind the manuscript.
It retains the parity of every irreducible exponent, including integer
prime factors in the content.  No primitivity or factorization hypothesis
is imposed on the input polynomial, and either sign is allowed.
-/

namespace PellPaper

open Polynomial

/-- Every nonzero integral polynomial is a square times a squarefree
integral polynomial. -/
theorem exists_sq_mul_squarefree_intPolynomial
    (p : Polynomial ℤ) (hp : p ≠ 0) :
    ∃ r s : Polynomial ℤ, p = r ^ 2 * s ∧ Squarefree s := by
  induction p using WfDvdMonoid.induction_on_irreducible with
  | zero => exact (hp rfl).elim
  | unit u hu => exact ⟨1, u, by simp, hu.squarefree⟩
  | mul z a hz ha ih =>
      obtain ⟨r, s, hrs, hs⟩ := ih hz
      by_cases has : a ∣ s
      · obtain ⟨t, ht⟩ := has
        refine ⟨a * r, t, ?_, hs.squarefree_of_dvd ?_⟩
        · rw [hrs, ht]
          ring
        · exact ⟨a, by rw [ht, mul_comm a t]⟩
      · refine ⟨r, a * s, ?_, ?_⟩
        · rw [hrs]
          ring
        · exact squarefree_mul_iff.mpr
            ⟨ha.isRelPrime_iff_not_dvd.mpr has, ha.squarefree, hs⟩

end PellPaper
