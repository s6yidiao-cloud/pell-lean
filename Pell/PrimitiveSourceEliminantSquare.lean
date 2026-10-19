import Pell.BinaryQuadraticLinearEliminant

/-!
# Actual nonzero square values at primitive source solutions

An integral linear relation on a primitive source vector determines an
integer multiple of its perpendicular vector. The exact quadratic surface
then makes the actual eliminant value a nonzero square. This proves
nonvanishing from an actual solution whenever A(y),B(y) are not both zero;
deriving that last condition from coprime homogeneous components is separate.
-/

namespace PellPaper

noncomputable section

/-- An integral vector perpendicular to a primitive integer pair is an
integer multiple of its perpendicular pair. All signs and axis cases are
retained; the multiplier may be zero. -/
theorem exists_int_multiple_of_primitive_linear_relation
    (l1 l2 A B : ℤ) (hprimitive : IsCoprime l1 l2)
    (hlinear : l1 * A + l2 * B = 0) :
    ∃ n : ℤ, B = n * l1 ∧ -A = n * l2 := by
  obtain ⟨u, v, huv⟩ := hprimitive
  refine ⟨u * B - v * A, ?_, ?_⟩
  · linear_combination -B * huv + v * hlinear
  · linear_combination A * huv - u * hlinear

/-- The literal six-coefficient form is quadratic in its source vector. -/
theorem quadraticLinearFormEval_mul_source
    (g : Fin 3 → Fin 2 → ℤ) (n : ℤ) (lambda y : Fin 2 → ℤ) :
    quadraticLinearFormEval g (fun i => n * lambda i) y =
      n ^ 2 * quadraticLinearFormEval g lambda y := by
  simp [quadraticLinearFormEval, Fin.sum_univ_succ]
  ring

/-- At a primitive source solution of the exact nonzero level, the literal
eliminant is a nonzero square, provided the two evaluated components are not
both zero. It follows in particular that the eliminant polynomial is nonzero.
No generic inference from nonzero input forms is used. -/
theorem quadraticLinearEliminant_nonzero_square_of_primitive_source
    (g : Fin 3 → Fin 2 → ℤ) (c : ℤ) (A B : MvPolynomial (Fin 2) ℤ)
    (lambda y : Fin 2 → ℤ) (hprimitive : IsCoprime (lambda 0) (lambda 1))
    (hc : c ≠ 0)
    (hlinear : lambda 0 * MvPolynomial.eval y A + lambda 1 * MvPolynomial.eval y B = 0)
    (hcomponents : MvPolynomial.eval y A ≠ 0 ∨ MvPolynomial.eval y B ≠ 0)
    (hlevel : quadraticLinearFormEval g lambda y = c) :
    IsSquare (MvPolynomial.eval y (quadraticLinearEliminant g c A B)) ∧
      MvPolynomial.eval y (quadraticLinearEliminant g c A B) ≠ 0 ∧
      quadraticLinearEliminant g c A B ≠ 0 := by
  obtain ⟨n, hB, hA⟩ := exists_int_multiple_of_primitive_linear_relation
    (lambda 0) (lambda 1) (MvPolynomial.eval y A) (MvPolynomial.eval y B)
    hprimitive hlinear
  have hn : n ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hA hB
    rcases hcomponents with h | h
    · exact h (neg_eq_zero.mp hA)
    · exact h hB
  have hvector : ![MvPolynomial.eval y B, -MvPolynomial.eval y A] =
      (fun i => n * lambda i) := by
    funext i
    fin_cases i
    · exact hB
    · exact hA
  have heval : MvPolynomial.eval y (quadraticLinearEliminant g c A B) = (c * n) ^ 2 := by
    rw [eval_quadraticLinearEliminant, hvector, quadraticLinearFormEval_mul_source, hlevel]
    ring
  have hvalue : MvPolynomial.eval y (quadraticLinearEliminant g c A B) ≠ 0 := by
    rw [heval]
    exact pow_ne_zero _ (mul_ne_zero hc hn)
  refine ⟨?_, hvalue, ?_⟩
  · rw [heval]
    exact IsSquare.sq _
  · intro hz
    apply hvalue
    rw [hz, map_zero]

end
end PellPaper
