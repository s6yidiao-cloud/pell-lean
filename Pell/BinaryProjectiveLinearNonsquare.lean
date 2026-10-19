import Pell.BinaryProjectiveDerivativeResultant

/-!
# Nonsquare binary-projective linear-frequency products at good primes

This file composes the projective derivative-resultant certificate with the
affine squarefree-times-linear criterion.  It is the algebraic nonsquareness
input for the higher-degree character-sum branch.
-/

namespace PellPaper

noncomputable section

/-- At a prime avoiding the projective derivative resultant, multiplying the
reduced affine dehomogenization by any nonzero linear frequency does not
produce a square polynomial. -/
theorem not_isSquare_binaryDehom_map_mul_linear_of_projectiveResultant_not_dvd
    (p j : ℕ) [Fact p.Prime] (J : MvPolynomial (Fin 2) ℤ)
    (hhom : J.IsHomogeneous j) (hj : 3 ≤ j)
    (hgood : ¬ (p : ℤ) ∣ binaryProjectiveDerivativeResultant J j)
    (a b : ZMod p) (hab : a ≠ 0 ∨ b ≠ 0) :
    ¬ IsSquare
      (binaryDehomogenizeAtOne (J.map (Int.castRingHom (ZMod p))) *
        (Polynomial.C a * Polynomial.X + Polynomial.C b)) := by
  let Jp : MvPolynomial (Fin 2) (ZMod p) :=
    J.map (Int.castRingHom (ZMod p))
  let P : Polynomial (ZMod p) := binaryDehomogenizeAtOne Jp
  have hcertificate : Squarefree P ∧ j - 1 ≤ P.natDegree := by
    simpa only [Jp, P] using
      squarefree_dehom_map_and_degree_of_projectiveResultant_not_dvd
        p j J hhom hj hgood
  apply not_isSquare_binaryDehomogenizeAtOne_mul_linear
      Jp a b hcertificate.1 hab
  exact (by omega : 2 ≤ j - 1).trans hcertificate.2

end
end PellPaper
