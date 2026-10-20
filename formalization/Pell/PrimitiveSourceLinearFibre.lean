import Pell.PrimitiveSourceEliminantSquare

/-!
# Primitive source fibres of a nonzero integral linear relation

Two primitive integer source vectors annihilating the same nonzero pair
of evaluated coefficients differ only by sign. Hence any finite family
of such source vectors has cardinality at most two. This supplies the
source-fibre assertion in the manuscript; component nonvanishing
remains an explicit hypothesis, separate from polynomial coprimality.
-/

namespace PellPaper

/-- Primitive integer solutions of one nonzero linear relation differ
only by sign. No coordinate is divided by, so both axis cases are included. -/
theorem primitive_linear_solutions_eq_or_neg
    (A B : ℤ) (hcomponents : A ≠ 0 ∨ B ≠ 0)
    (lambda mu : Fin 2 → ℤ)
    (hlambda : IsCoprime (lambda 0) (lambda 1))
    (hmu : IsCoprime (mu 0) (mu 1))
    (hlinearLambda : lambda 0 * A + lambda 1 * B = 0)
    (hlinearMu : mu 0 * A + mu 1 * B = 0) :
    mu = lambda ∨ mu = -lambda := by
  have hcross : lambda 0 * (-mu 1) + lambda 1 * mu 0 = 0 := by
    rcases hcomponents with hA | hB
    · have hproduct : A * (lambda 0 * (-mu 1) + lambda 1 * mu 0) = 0 := by
        linear_combination -mu 1 * hlinearLambda + lambda 1 * hlinearMu
      exact (mul_eq_zero.mp hproduct).resolve_left hA
    · have hproduct : B * (lambda 0 * (-mu 1) + lambda 1 * mu 0) = 0 := by
        linear_combination mu 0 * hlinearLambda - lambda 0 * hlinearMu
      exact (mul_eq_zero.mp hproduct).resolve_left hB
  obtain ⟨n, hn0, hn1⟩ := exists_int_multiple_of_primitive_linear_relation
    (lambda 0) (lambda 1) (-mu 1) (mu 0) hlambda hcross
  have hn1' : mu 1 = n * lambda 1 := by simpa only [neg_neg] using hn1
  have hnunit : IsUnit n :=
    hmu.isUnit_of_dvd' ⟨lambda 0, hn0⟩ ⟨lambda 1, hn1'⟩
  have hvector : mu = fun i => n * lambda i := by
    funext i
    fin_cases i
    · exact hn0
    · exact hn1'
  rcases Int.isUnit_iff.mp hnunit with hn | hn
  · left
    simpa only [hn, one_mul] using hvector
  · right
    funext i
    simpa only [hn, neg_one_mul, Pi.neg_apply] using congrFun hvector i

/-- A finite family of primitive solutions to a nonzero integral linear
relation has at most two elements. The empty family is allowed. -/
theorem card_primitive_linear_solutions_le_two
    (A B : ℤ) (hcomponents : A ≠ 0 ∨ B ≠ 0)
    (S : Finset (Fin 2 → ℤ))
    (hS : ∀ lambda ∈ S, IsCoprime (lambda 0) (lambda 1) ∧
      lambda 0 * A + lambda 1 * B = 0) :
    S.card ≤ 2 := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨lambda, hlambda⟩
  · simp
  · have hsubset : S ⊆ {lambda, -lambda} := by
      intro mu hmu
      have hl := hS lambda hlambda
      have hm := hS mu hmu
      simpa only [Finset.mem_insert, Finset.mem_singleton] using
        primitive_linear_solutions_eq_or_neg A B hcomponents lambda mu
          hl.1 hm.1 hl.2 hm.2
    exact (Finset.card_le_card hsubset).trans Finset.card_le_two

end PellPaper
