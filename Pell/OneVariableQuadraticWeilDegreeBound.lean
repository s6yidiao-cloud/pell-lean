import Pell.ProjectiveCharacterSumFourierBound
import Pell.SquarefreePolynomialGeometricNonsquare
import Mathlib.Tactic

/-!
# A conditional one-variable Weil input for higher-degree binary forms

This file isolates the classical one-variable quadratic-character estimate as
an explicit `Prop` interface and proves the algebraic glue needed by the binary
Fourier argument.  It does not add an axiom or claim a Lean proof of the Weil
estimate.

The interface is the usual degree-form consequence of the Weil bound for
multiplicative character sums; compare Iwaniec--Kowalski, *Analytic Number
Theory*, Theorem 11.23; W. M. Schmidt, *Equations over Finite Fields: An
Elementary Approach*, Lecture Notes in Mathematics 536, Theorem 2C′, p. 43;
and Lidl--Niederreiter, *Finite Fields*, second edition, Theorem 5.41.
-/

namespace PellPaper

noncomputable section

open scoped BigOperators

/-- The standard degree-form Weil estimate for a quadratic-character sum over
one prime field.

This is a named proposition intended to be supplied as an explicit theorem
hypothesis.  It is not an axiom.  Its geometric nonsquare premise excludes the
exceptional case in which the summand is generically constant after extending
scalars to the algebraic closure.  The numerical constant is `deg f - 1`, as
in the standard square-root cancellation theorem; see Iwaniec--Kowalski,
Theorem 11.23, Schmidt LNM 536, Theorem 2C′, and Lidl--Niederreiter,
Theorem 5.41. -/
def OneVariableQuadraticWeilDegreeBound : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (f : Polynomial (ZMod p)),
    letI : Fact p.Prime := ⟨hp⟩
    p ≠ 2 →
    1 ≤ f.natDegree →
    (¬ ∃ g : Polynomial (AlgebraicClosure (ZMod p)),
      g * g = f.map
        (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))) →
    ‖∑ x : ZMod p,
      (quadraticChar (ZMod p) (f.eval x) : ℂ)‖ ≤
      ((f.natDegree - 1 : ℕ) : ℝ) * Real.sqrt (p : ℝ)

private theorem natDegree_binaryDehomogenizeAtOne_le_of_isHomogeneous
    {F : Type*} [CommRing F] [Nontrivial F]
    (J : MvPolynomial (Fin 2) F) (j : ℕ)
    (hJ : J.IsHomogeneous j) :
    (binaryDehomogenizeAtOne J).natDegree ≤ j := by
  refine le_trans ?_ hJ.totalDegree_le
  rw [binaryDehomogenizeAtOne, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_eq']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.prod_univ_two, one_pow, mul_one]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Polynomial.natDegree_X_pow]
  exact (Finsupp.le_degree 0 e).trans (MvPolynomial.le_totalDegree he)

/-- The classical one-variable Weil input implies the projective character-sum
bound with constant `j` for every good reduction of a homogeneous binary form
of degree at least three.

The same polynomial occurring in the projective Fourier chart is used here.
The accepted projective-resultant theorem supplies its geometric nonsquareness;
the only remaining bookkeeping is the elementary degree bound
`deg (J(t,1) * (a*t+b)) - 1 ≤ j`. -/
theorem primePolynomialProjectiveCharacterSumBound_of_oneVariableQuadraticWeil
    (hWeil : OneVariableQuadraticWeilDegreeBound)
    (p j : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (J : MvPolynomial (Fin 2) ℤ) (hJ : J.IsHomogeneous j)
    (hj3 : 3 ≤ j)
    (hgood : ¬ (p : ℤ) ∣ binaryProjectiveDerivativeResultant J j) :
    PrimePolynomialProjectiveCharacterSumBound p hp J (j : ℝ) := by
  let _ : Fact p.Prime := ⟨hp⟩
  intro a b hab
  let Jp : MvPolynomial (Fin 2) (ZMod p) :=
    J.map (Int.castRingHom (ZMod p))
  let P : Polynomial (ZMod p) := binaryDehomogenizeAtOne Jp
  let L : Polynomial (ZMod p) :=
    Polynomial.C a * Polynomial.X + Polynomial.C b
  let f : Polynomial (ZMod p) := P * L
  have hab' : a ≠ 0 ∨ b ≠ 0 := by
    by_cases ha : a = 0
    · right
      intro hb
      exact hab (by simp [ha, hb])
    · exact Or.inl ha
  have hcertificate : Squarefree P ∧ j - 1 ≤ P.natDegree := by
    simpa only [Jp, P] using
      squarefree_dehom_map_and_degree_of_projectiveResultant_not_dvd
        p j J hJ hj3 hgood
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
    exact hab'.elim (fun ha ↦ ha ha0) (fun hb ↦ hb hb0)
  have hfdeg : f.natDegree = P.natDegree + L.natDegree := by
    simpa only [f] using Polynomial.natDegree_mul hP0 hL0
  have hfpos : 1 ≤ f.natDegree := by
    rw [hfdeg]
    omega
  have hgeom :
      ¬ ∃ g : Polynomial (AlgebraicClosure (ZMod p)),
        g * g = f.map
          (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) := by
    simpa only [Jp, P, L, f] using
      not_exists_sq_binaryDehom_mul_linear_over_algebraicClosure_of_projectiveResultant_not_dvd
        p j J hJ hj3 hgood a b hab'
  have hPupper : P.natDegree ≤ j := by
    exact natDegree_binaryDehomogenizeAtOne_le_of_isHomogeneous Jp j
      (hJ.map (Int.castRingHom (ZMod p)))
  have hLupper : L.natDegree ≤ 1 := by
    simpa only [L] using
      (Polynomial.natDegree_linear_le :
        (Polynomial.C a * Polynomial.X + Polynomial.C b).natDegree ≤ 1)
  have hfupper : f.natDegree ≤ j + 1 := by
    rw [hfdeg]
    omega
  have hdegree : f.natDegree - 1 ≤ j := by omega
  have hcast : ((f.natDegree - 1 : ℕ) : ℝ) ≤ (j : ℝ) := by
    exact_mod_cast hdegree
  have hsum := hWeil p hp f hp2 hfpos hgeom
  have hbound :
      ‖∑ r : ZMod p, (quadraticChar (ZMod p) (f.eval r) : ℂ)‖ ≤
        (j : ℝ) * Real.sqrt (p : ℝ) :=
    hsum.trans (mul_le_mul_of_nonneg_right hcast (Real.sqrt_nonneg _))
  simpa [f, P, L, Jp, eval_binaryDehomogenizeAtOne] using hbound

/-- Conditional higher-degree Fourier cancellation obtained by composing the
degree-form one-variable Weil estimate with the projective Fourier adapter.
The `+1` is the adapter's contribution from the projective point at infinity. -/
theorem primePolynomialFourierBound_of_oneVariableQuadraticWeil
    (hWeil : OneVariableQuadraticWeilDegreeBound)
    (p j : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (J : MvPolynomial (Fin 2) ℤ) (hJ : J.IsHomogeneous j)
    (hj : Odd j) (hj3 : 3 ≤ j)
    (hgood : ¬ (p : ℤ) ∣ binaryProjectiveDerivativeResultant J j) :
    PrimePolynomialFourierBound p hp J ((j : ℝ) + 1) := by
  apply primePolynomialFourierBound_of_projectiveCharacterSumBound
    p j hp hp2 J hJ hj (j : ℝ)
  exact
    primePolynomialProjectiveCharacterSumBound_of_oneVariableQuadraticWeil
      hWeil p j hp hp2 J hJ hj3 hgood

end

end PellPaper
