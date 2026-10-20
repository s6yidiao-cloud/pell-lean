import Pell.BinaryHomogeneousSquareLift
import Pell.PrimitiveSquarefreePolynomialRat

/-!
# Actual square decomposition of odd-degree integral binary forms

The univariate square-parity decomposition and the padded homogenization
bridge construct all factors from the original nonzero form. The affine
squarefreeness and degree-gap conclusions are the precise inputs needed
for a nonzero projective derivative resultant. No factorization, primitive
factor, or nonsquareness certificate is assumed.
-/

namespace PellPaper

noncomputable section

/-- Every nonzero odd-degree integral homogeneous binary form has an actual
square-content decomposition with a primitive, positive odd-degree remainder.
Its affine polynomial is squarefree over both the integers and the rationals,
and at most one degree is lost at infinity. This states the affine certificate
explicitly rather than silently identifying it with geometric squarefreeness. -/
theorem exists_homogeneous_content_square_primitive_affine_squarefree
    (K : MvPolynomial (Fin 2) ℤ) (d : ℕ)
    (hK : K.IsHomogeneous d) (hK0 : K ≠ 0) (hd : Odd d) :
    ∃ (c : ℤ) (R J : MvPolynomial (Fin 2) ℤ) (m j : ℕ),
      K = MvPolynomial.C c * R ^ 2 * J ∧
      c ≠ 0 ∧ Squarefree c ∧ R ≠ 0 ∧ J ≠ 0 ∧ J ∣ K ∧
      R.IsHomogeneous m ∧ J.IsHomogeneous j ∧
      d = 2 * m + j ∧ Odd j ∧ 0 < j ∧
      (∀ a : ℤ, (∀ e : Fin 2 →₀ ℕ, a ∣ J.coeff e) → IsUnit a) ∧
      (binaryDehomogenizeAtOne J).IsPrimitive ∧
      Squarefree (binaryDehomogenizeAtOne J) ∧
      Squarefree ((binaryDehomogenizeAtOne J).map (Int.castRingHom ℚ)) ∧
      j ≤ (binaryDehomogenizeAtOne J).natDegree + 1 := by
  have hdehom0 : binaryDehomogenizeAtOne K ≠ 0 := by
    intro hz
    have hrecover : (binaryDehomogenizeAtOne K).homogenize d = K := by
      apply Polynomial.homogenize_eq_of_isHomogeneous hK
      rfl
    rw [hz, Polynomial.homogenize_zero] at hrecover
    exact hK0 hrecover.symm
  obtain ⟨c, r, q, hfactor, hc, hr, _, hcsq, hq, hqsq, hqRat⟩ :=
    exists_content_sq_mul_primitive_squarefree_intPolynomial _ hdehom0
  obtain ⟨R, J, m, j, hbinary, hR, hJ, hR0, hJ0, hledger, hj, hjpos,
    _, hJdehom, hgap, hprimitive⟩ :=
    exists_homogeneous_square_lift_of_dehom_factorization K d hK hd
      c r q hc hr hq hfactor
  refine ⟨c, R, J, m, j, hbinary, hc, hcsq, hR0, hJ0, ?_, hR, hJ,
    hledger, hj, hjpos, hprimitive, ?_, ?_, ?_, ?_⟩
  · exact ⟨MvPolynomial.C c * R ^ 2, by rw [hbinary, mul_comm J]⟩
  · simpa only [hJdehom] using hq
  · simpa only [hJdehom] using hqsq
  · simpa only [hJdehom] using hqRat
  · simpa only [hJdehom] using hgap

end
end PellPaper
