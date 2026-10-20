import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

/-!
# The literal binary eliminant of a quadratic-linear form

The six integral coefficients of a bidegree-(2,1) form are indexed by
the exponent of its second source variable and its target coordinate.
Substitution of (B,-A) constructs the binary polynomial used in
the manuscript, Lemma `L:quantitative-eliminant-height`. Its nonvanishing is
not inferred from the nonvanishing of either input form.
-/

namespace PellPaper

noncomputable section
open scoped BigOperators

/-- Evaluation of the six-coefficient bidegree-(2,1) form: index i is the
exponent of the second source coordinate, and t selects the target coordinate. -/
def quadraticLinearFormEval (g : Fin 3 → Fin 2 → ℤ)
    (x y : Fin 2 → ℤ) : ℤ :=
  ∑ i : Fin 3, ∑ t : Fin 2, g i t * x 0 ^ (2 - i.val) * x 1 ^ i.val * y t

/-- The actual polynomial c*G(B,-A;y), with exactly the same six coefficients
and variable order as `quadraticLinearFormEval`. -/
def quadraticLinearEliminant (g : Fin 3 → Fin 2 → ℤ) (c : ℤ)
    (A B : MvPolynomial (Fin 2) ℤ) : MvPolynomial (Fin 2) ℤ :=
  MvPolynomial.C c *
    ∑ i : Fin 3, ∑ t : Fin 2,
      MvPolynomial.C (g i t) * B ^ (2 - i.val) * (-A) ^ i.val * MvPolynomial.X t

/-- Substitution commutes with actual integral evaluation; negative signs,
zero coordinates and zero input forms are retained. -/
theorem eval_quadraticLinearEliminant
    (g : Fin 3 → Fin 2 → ℤ) (c : ℤ) (A B : MvPolynomial (Fin 2) ℤ)
    (y : Fin 2 → ℤ) :
    MvPolynomial.eval y (quadraticLinearEliminant g c A B) =
      c * quadraticLinearFormEval g ![MvPolynomial.eval y B, -MvPolynomial.eval y A] y := by
  simp [quadraticLinearEliminant, quadraticLinearFormEval]

/-- Homogeneous input components of degree b give a homogeneous eliminant
of degree 2b+1, even when the resulting polynomial is zero. -/
theorem isHomogeneous_quadraticLinearEliminant
    (g : Fin 3 → Fin 2 → ℤ) (c : ℤ) (A B : MvPolynomial (Fin 2) ℤ)
    (b : ℕ) (hA : A.IsHomogeneous b) (hB : B.IsHomogeneous b) :
    (quadraticLinearEliminant g c A B).IsHomogeneous (2 * b + 1) := by
  apply MvPolynomial.IsHomogeneous.C_mul
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  apply MvPolynomial.IsHomogeneous.sum
  intro t _
  have h := (((hB.pow (2 - i.val)).C_mul (g i t)).mul (hA.neg.pow i.val)).mul
    (MvPolynomial.isHomogeneous_X ℤ t)
  have hi : i.val ≤ 2 := by omega
  have hdeg : b * (2 - i.val) + b * i.val + 1 = 2 * b + 1 := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hi]
    omega
  simpa only [hdeg] using h

end
end PellPaper
