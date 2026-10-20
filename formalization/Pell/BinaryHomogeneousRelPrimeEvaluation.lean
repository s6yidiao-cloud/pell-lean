import Pell.SquarefreePolynomialLinearNonsquare
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Tactic

/-!
# Relatively prime homogeneous binary components have no common projective zero

The finite chart uses actual affine root divisibility and padded
homogenization. A coordinate swap covers the point at infinity. The
coprimality premise is `IsRelPrime`, not a multivariate Bezout identity.
-/

namespace PellPaper

noncomputable section
open Polynomial

private theorem dehom_degree_le {K : Type*} [Field K]
    (A : MvPolynomial (Fin 2) K) (b : ℕ) (hA : A.IsHomogeneous b) :
    (binaryDehomogenizeAtOne A).natDegree ≤ b := by
  refine le_trans ?_ hA.totalDegree_le
  rw [binaryDehomogenizeAtOne, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.prod_univ_two, one_pow, mul_one]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Polynomial.natDegree_X_pow]
  exact (Finsupp.le_degree 0 e).trans (MvPolynomial.le_totalDegree he)

/-- A zero in the finite projective chart gives a literal homogeneous linear
divisor. Homogenization retains the original degree, including padding. -/
theorem homogenized_linear_dvd_of_eval_eq_zero {K : Type*} [Field K]
    (A : MvPolynomial (Fin 2) K) (b : ℕ) (hA : A.IsHomogeneous b)
    (y : Fin 2 → K) (hy1 : y 1 ≠ 0) (hzero : MvPolynomial.eval y A = 0) :
    (Polynomial.X - Polynomial.C (y 0 / y 1)).homogenize 1 ∣ A := by
  let P := binaryDehomogenizeAtOne A
  have hdeg : P.natDegree ≤ b := dehom_degree_le A b hA
  have hhom : P.homogenize b = A := by
    apply Polynomial.homogenize_eq_of_isHomogeneous hA
    rfl
  have hroot : P.eval (y 0 / y 1) = 0 := by
    have hv := Polynomial.eval_homogenize hdeg y hy1
    rw [hhom, hzero] at hv
    exact (mul_eq_zero.mp hv.symm).resolve_right (pow_ne_zero _ hy1)
  have hdiv : Polynomial.X - Polynomial.C (y 0 / y 1) ∣ P :=
    Polynomial.dvd_iff_isRoot.mpr hroot
  have hdivhom := Polynomial.homogenize_dvd hdiv
  rw [Polynomial.natDegree_X_sub_C] at hdivhom
  have hpad : P.homogenize b =
      P.homogenize P.natDegree * MvPolynomial.X 1 ^ (b - P.natDegree) := by
    calc
      P.homogenize b = (P * 1).homogenize (P.natDegree + (b - P.natDegree)) := by
        rw [mul_one, Nat.add_sub_of_le hdeg]
      _ = P.homogenize P.natDegree * (1 : K[X]).homogenize (b - P.natDegree) :=
        Polynomial.homogenize_mul P 1 le_rfl (by simp)
      _ = _ := by simp
  rw [← hhom, hpad]
  exact dvd_mul_of_dvd_left hdivhom _

private theorem component_nonzero_finite_chart {K : Type*} [Field K]
    (A B : MvPolynomial (Fin 2) K) (b : ℕ)
    (hA : A.IsHomogeneous b) (hB : B.IsHomogeneous b)
    (hAB : IsRelPrime A B) (y : Fin 2 → K) (hy1 : y 1 ≠ 0) :
    MvPolynomial.eval y A ≠ 0 ∨ MvPolynomial.eval y B ≠ 0 := by
  by_contra h
  push Not at h
  have hu := hAB (homogenized_linear_dvd_of_eval_eq_zero A b hA y hy1 h.1)
    (homogenized_linear_dvd_of_eval_eq_zero B b hB y hy1 h.2)
  have hv := hu.map (MvPolynomial.eval ![y 0 / y 1, (1 : K)])
  simp at hv

/-- Relatively prime binary forms of the same homogeneous degree cannot both
vanish at a nonzero target. The zero polynomial and degree zero are allowed. -/
theorem eval_ne_zero_or_ne_zero_of_isRelPrime_homogeneous_binary
    {K : Type*} [Field K] (A B : MvPolynomial (Fin 2) K) (b : ℕ)
    (hA : A.IsHomogeneous b) (hB : B.IsHomogeneous b)
    (hAB : IsRelPrime A B) (y : Fin 2 → K) (hy : y 0 ≠ 0 ∨ y 1 ≠ 0) :
    MvPolynomial.eval y A ≠ 0 ∨ MvPolynomial.eval y B ≠ 0 := by
  by_cases hy1 : y 1 ≠ 0
  · exact component_nonzero_finite_chart A B b hA hB hAB y hy1
  have hy0 : y 0 ≠ 0 := hy.resolve_right hy1
  let e := MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin 2) 1)
  have hrel : IsRelPrime (e A) (e B) := by
    intro d hdA hdB
    have hu : IsUnit (e.symm d) := hAB (by simpa using map_dvd e.symm hdA)
      (by simpa using map_dvd e.symm hdB)
    simpa using hu.map e
  have hswap := component_nonzero_finite_chart (e A) (e B) b
    hA.rename_isHomogeneous hB.rename_isHomogeneous hrel ![y 1, y 0] (by simpa using hy0)
  have heval (P : MvPolynomial (Fin 2) K) :
      MvPolynomial.eval ![y 1, y 0] (e P) = MvPolynomial.eval y P := by
    change MvPolynomial.eval ![y 1, y 0]
      (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) P) = _
    rw [MvPolynomial.eval_rename]
    have hycomp : ![y 1, y 0] ∘ Equiv.swap (0 : Fin 2) 1 = y := by
      funext i
      fin_cases i <;> simp
    rw [hycomp]
  simpa only [heval] using hswap

/-- Rational polynomial relative primeness gives actual nonzero integral
component values at a primitive target. No fraction-field coprimality
transport is assumed implicitly. -/
theorem eval_ne_zero_or_ne_zero_of_rat_isRelPrime_homogeneous_binary
    (A B : MvPolynomial (Fin 2) ℤ) (b : ℕ)
    (hA : A.IsHomogeneous b) (hB : B.IsHomogeneous b)
    (hAB : IsRelPrime (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ)))
    (y : Fin 2 → ℤ) (hy : IsCoprime (y 0) (y 1)) :
    MvPolynomial.eval y A ≠ 0 ∨ MvPolynomial.eval y B ≠ 0 := by
  let f := Int.castRingHom ℚ
  have hyQ : (f ∘ y) 0 ≠ 0 ∨ (f ∘ y) 1 ≠ 0 := by
    simpa [f] using hy.ne_zero_or_ne_zero
  have h := eval_ne_zero_or_ne_zero_of_isRelPrime_homogeneous_binary
    (A.map f) (B.map f) b (hA.map f) (hB.map f) hAB (f ∘ y) hyQ
  rw [MvPolynomial.eval_map, MvPolynomial.eval_map,
    ← MvPolynomial.eval₂_comp, ← MvPolynomial.eval₂_comp] at h
  simpa [f] using h

end
end PellPaper
