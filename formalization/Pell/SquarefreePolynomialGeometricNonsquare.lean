import Pell.BinaryProjectiveLinearNonsquare
import Mathlib.FieldTheory.Perfect

/-!
# Geometric nonsquareness of squarefree polynomial products

A squarefree polynomial over a perfect field remains squarefree after any
field extension.  Consequently, multiplying it by a nonzero lower-degree
factor cannot become a square after extending scalars.  The final theorems
specialize this observation to the good-prime binary-form certificate used
in the quadratic-character Fourier estimates.
-/

namespace PellPaper

noncomputable section

/-- A nonzero squarefree polynomial over a perfect field, multiplied by a
nonzero lower-degree factor, remains nonsquare after every field extension. -/
theorem not_isSquare_map_squarefree_mul_of_natDegree_lt
    {F K : Type*} [Field F] [PerfectField F] [Field K] [Algebra F K]
    (J L : Polynomial F)
    (hJ : Squarefree J) (hJ0 : J ≠ 0) (hL0 : L ≠ 0)
    (hdeg : L.natDegree < J.natDegree) :
    ¬ IsSquare ((J * L).map (algebraMap F K)) := by
  rw [Polynomial.map_mul]
  apply not_isSquare_squarefree_mul_of_natDegree_lt
      (J.map (algebraMap F K)) (L.map (algebraMap F K))
  · exact (PerfectField.separable_iff_squarefree.mpr hJ).map.squarefree
  · exact Polynomial.map_ne_zero hJ0
  · exact Polynomial.map_ne_zero hL0
  · simpa using hdeg

/-- At a prime avoiding the projective derivative resultant, the product of
the reduced affine dehomogenization and any nonzero linear frequency remains
nonsquare over every extension of `ZMod p`.  No odd-prime hypothesis is
needed for this algebraic statement. -/
theorem not_isSquare_map_binaryDehom_mul_linear_of_projectiveResultant_not_dvd
    (p j : ℕ) [Fact p.Prime] (J : MvPolynomial (Fin 2) ℤ)
    (hhom : J.IsHomogeneous j) (hj : 3 ≤ j)
    (hgood : ¬ (p : ℤ) ∣ binaryProjectiveDerivativeResultant J j)
    (a b : ZMod p) (hab : a ≠ 0 ∨ b ≠ 0)
    {K : Type*} [Field K] [Algebra (ZMod p) K] :
    ¬ IsSquare
      ((binaryDehomogenizeAtOne (J.map (Int.castRingHom (ZMod p))) *
          (Polynomial.C a * Polynomial.X + Polynomial.C b)).map
        (algebraMap (ZMod p) K)) := by
  let Jp : MvPolynomial (Fin 2) (ZMod p) :=
    J.map (Int.castRingHom (ZMod p))
  let P : Polynomial (ZMod p) := binaryDehomogenizeAtOne Jp
  let L : Polynomial (ZMod p) :=
    Polynomial.C a * Polynomial.X + Polynomial.C b
  have hcertificate : Squarefree P ∧ j - 1 ≤ P.natDegree := by
    simpa only [Jp, P] using
      squarefree_dehom_map_and_degree_of_projectiveResultant_not_dvd
        p j J hhom hj hgood
  have hPdeg : 2 ≤ P.natDegree :=
    (by omega : 2 ≤ j - 1).trans hcertificate.2
  have hP0 : P ≠ 0 := by
    intro hzero
    rw [hzero] at hPdeg
    simp at hPdeg
  have hL0 : L ≠ 0 := by
    intro hzero
    have ha0 : a = 0 := by
      have hcoeff := congrArg (fun Q : Polynomial (ZMod p) ↦ Q.coeff 1) hzero
      simpa [L] using hcoeff
    have hb0 : b = 0 := by
      have hcoeff := congrArg (fun Q : Polynomial (ZMod p) ↦ Q.coeff 0) hzero
      simpa [L] using hcoeff
    exact hab.elim (fun ha ↦ ha ha0) (fun hb ↦ hb hb0)
  have hLdeg : L.natDegree < P.natDegree := by
    have hlinear : L.natDegree ≤ 1 := by
      simpa only [L] using
        (Polynomial.natDegree_linear_le :
          (Polynomial.C a * Polynomial.X + Polynomial.C b).natDegree ≤ 1)
    omega
  simpa only [Jp, P, L] using
    not_isSquare_map_squarefree_mul_of_natDegree_lt
      (K := K) P L hcertificate.1 hP0 hL0 hLdeg

/-- The preceding geometric nonsquareness statement in the explicit
`AlgebraicClosure` formulation used by hyperelliptic point-count bounds. -/
theorem not_exists_sq_binaryDehom_mul_linear_over_algebraicClosure_of_projectiveResultant_not_dvd
    (p j : ℕ) [Fact p.Prime] (J : MvPolynomial (Fin 2) ℤ)
    (hhom : J.IsHomogeneous j) (hj : 3 ≤ j)
    (hgood : ¬ (p : ℤ) ∣ binaryProjectiveDerivativeResultant J j)
    (a b : ZMod p) (hab : a ≠ 0 ∨ b ≠ 0) :
    ¬ ∃ g : Polynomial (AlgebraicClosure (ZMod p)),
      g * g =
        (binaryDehomogenizeAtOne (J.map (Int.castRingHom (ZMod p))) *
            (Polynomial.C a * Polynomial.X + Polynomial.C b)).map
          (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) := by
  intro hexists
  apply
    not_isSquare_map_binaryDehom_mul_linear_of_projectiveResultant_not_dvd
      (K := AlgebraicClosure (ZMod p)) p j J hhom hj hgood a b hab
  rcases hexists with ⟨g, hg⟩
  exact ⟨g, hg.symm⟩

end
end PellPaper
