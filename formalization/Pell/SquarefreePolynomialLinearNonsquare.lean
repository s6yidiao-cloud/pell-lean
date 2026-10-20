import Pell.SquarefreePolynomialLinearFactor
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# A squarefree polynomial times a nonzero linear frequency is not a square

This is the direct algebraic adapter for the polynomial
`J(X) * (a * X + b)` occurring after dehomogenizing the auxiliary binary
form.  Good reduction and the passage from a projective binary form to the
affine polynomial `J` are deliberately outside this statement.
-/

namespace PellPaper

noncomputable section

/-- Dehomogenize a binary polynomial in the affine chart `(X, 1)`. -/
def binaryDehomogenizeAtOne {F : Type*} [CommSemiring F]
    (J : MvPolynomial (Fin 2) F) : Polynomial F :=
  MvPolynomial.eval₂Hom Polynomial.C
    ![Polynomial.X, (1 : Polynomial F)] J

/-- Evaluating the dehomogenization at `r` is literally evaluating the binary
polynomial at `(r, 1)`. -/
theorem eval_binaryDehomogenizeAtOne {F : Type*} [CommSemiring F]
    (J : MvPolynomial (Fin 2) F) (r : F) :
    Polynomial.eval r (binaryDehomogenizeAtOne J) =
      MvPolynomial.eval ![r, 1] J := by
  change (Polynomial.evalRingHom r)
      (MvPolynomial.eval₂Hom Polynomial.C
        ![Polynomial.X, (1 : Polynomial F)] J) = _
  rw [MvPolynomial.map_eval₂Hom]
  change MvPolynomial.eval₂Hom _ _ J = MvPolynomial.eval₂Hom _ _ J
  apply MvPolynomial.eval₂Hom_congr
  · ext x
    simp
  · funext i
    fin_cases i <;> simp
  · rfl

/-- If the affine dehomogenization of `J` is squarefree and has degree at
least two, multiplying it by a nonzero Fourier frequency `aX + b` cannot
produce a square. -/
theorem not_isSquare_binaryDehomogenizeAtOne_mul_linear
    {F : Type*} [Field F] (J : MvPolynomial (Fin 2) F) (a b : F)
    (hJ : Squarefree (binaryDehomogenizeAtOne J))
    (hab : a ≠ 0 ∨ b ≠ 0)
    (hdeg : 2 ≤ (binaryDehomogenizeAtOne J).natDegree) :
    ¬ IsSquare (binaryDehomogenizeAtOne J *
      (Polynomial.C a * Polynomial.X + Polynomial.C b)) := by
  apply not_isSquare_squarefree_mul_of_natDegree_lt
      (binaryDehomogenizeAtOne J)
      (Polynomial.C a * Polynomial.X + Polynomial.C b) hJ
  · intro hzero
    rw [hzero] at hdeg
    simp at hdeg
  · intro hzero
    have ha0 : a = 0 := by
      have hcoeff := congrArg (fun P : Polynomial F ↦ P.coeff 1) hzero
      simpa using hcoeff
    have hb0 : b = 0 := by
      have hcoeff := congrArg (fun P : Polynomial F ↦ P.coeff 0) hzero
      simpa using hcoeff
    exact hab.elim (fun ha ↦ ha ha0) (fun hb ↦ hb hb0)
  · have hlinear :
        (Polynomial.C a * Polynomial.X + Polynomial.C b).natDegree ≤ 1 :=
      Polynomial.natDegree_linear_le
    omega

end
end PellPaper
