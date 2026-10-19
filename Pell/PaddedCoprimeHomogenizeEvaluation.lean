import Pell.IntegralPolynomialRelPrimeRat
import Mathlib.Algebra.Polynomial.Homogenize

/-!
# Nonvanishing of a relatively prime pair at its common padding degree

The padding degree is the maximum of the two affine degrees. This exact
choice retains the point at infinity without introducing a common infinity
zero. The output is pointwise nonvanishing, not multivariate relative primeness.
-/

namespace PellPaper

noncomputable section
open Polynomial

/-- At infinity only the coefficient of the specified padding degree
survives. This identity also holds at degree zero and for the zero form. -/
theorem eval_homogenize_at_infinity {R : Type*} [CommSemiring R]
    (p : Polynomial R) (n : ℕ) (x : R) :
    MvPolynomial.eval ![x, 0] (p.homogenize n) = p.coeff n * x ^ n := by
  simp only [Polynomial.homogenize, MvPolynomial.eval_sum]
  rw [Finset.sum_eq_single (n, 0)]
  · simp [MvPolynomial.eval_monomial, Finsupp.update_eq_add_single,
      Finsupp.prod_single_index]
  · intro kl hkl hne
    have hk : kl.2 ≠ 0 := by
      intro hk
      apply hne
      have hs := Finset.mem_antidiagonal.mp hkl
      ext <;> simp_all
    simp [MvPolynomial.eval_monomial, Finsupp.update_eq_add_single, hk]
  · simp

private theorem max_degree_coeff_ne_zero {R : Type*} [Semiring R]
    (p q : Polynomial R) (hpq : p ≠ 0 ∨ q ≠ 0) :
    p.coeff (max p.natDegree q.natDegree) ≠ 0 ∨
      q.coeff (max p.natDegree q.natDegree) ≠ 0 := by
  by_cases hq : q = 0
  · subst q
    left
    simpa only [natDegree_zero, Nat.max_zero, coeff_natDegree, leadingCoeff_ne_zero]
      using hpq.resolve_right (not_not.mpr rfl)
  · by_cases hdeg : p.natDegree ≤ q.natDegree
    · right
      rw [max_eq_right hdeg, coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hq
    · left
      rw [max_eq_left (le_of_not_ge hdeg), coeff_natDegree]
      apply leadingCoeff_ne_zero.mpr
      intro hp
      simp [hp] at hdeg

/-- A coprime univariate pair over a field, homogenized at the maximum
affine degree, cannot vanish simultaneously at a nonzero vector. -/
theorem eval_max_homogenize_ne_zero_or_ne_zero_of_isCoprime
    {K : Type*} [Field K] (p q : Polynomial K) (hpq : IsCoprime p q)
    (y : Fin 2 → K) (hy : y 0 ≠ 0 ∨ y 1 ≠ 0) :
    MvPolynomial.eval y (p.homogenize (max p.natDegree q.natDegree)) ≠ 0 ∨
      MvPolynomial.eval y (q.homogenize (max p.natDegree q.natDegree)) ≠ 0 := by
  by_cases hy1 : y 1 = 0
  · have hy0 : y 0 ≠ 0 := hy.resolve_right (not_not.mpr hy1)
    have hvec : y = ![y 0, 0] := by
      funext i
      fin_cases i <;> simp [hy1]
    rw [hvec, eval_homogenize_at_infinity, eval_homogenize_at_infinity]
    exact (max_degree_coeff_ne_zero p q hpq.ne_zero_or_ne_zero).imp
      (fun h => mul_ne_zero h (pow_ne_zero _ hy0))
      (fun h => mul_ne_zero h (pow_ne_zero _ hy0))
  · rw [Polynomial.eval_homogenize (le_max_left _ _) y hy1,
      Polynomial.eval_homogenize (le_max_right _ _) y hy1]
    have h := hpq.map (Polynomial.evalRingHom (y 0 / y 1))
    exact h.ne_zero_or_ne_zero.imp
      (fun hh => mul_ne_zero hh (pow_ne_zero _ hy1))
      (fun hh => mul_ne_zero hh (pow_ne_zero _ hy1))

/-- Integral relative primeness yields actual nonzero values of the padded
integer binary components at every primitive integer target. -/
theorem eval_max_homogenize_ne_zero_or_ne_zero_of_int_isRelPrime
    (p q : Polynomial ℤ) (hpq : IsRelPrime p q) (y : Fin 2 → ℤ)
    (hy : IsCoprime (y 0) (y 1)) :
    MvPolynomial.eval y (p.homogenize (max p.natDegree q.natDegree)) ≠ 0 ∨
      MvPolynomial.eval y (q.homogenize (max p.natDegree q.natDegree)) ≠ 0 := by
  let f := Int.castRingHom ℚ
  have hyQ : (f ∘ y) 0 ≠ 0 ∨ (f ∘ y) 1 ≠ 0 := by
    simpa [f] using hy.ne_zero_or_ne_zero
  have h := eval_max_homogenize_ne_zero_or_ne_zero_of_isCoprime
    (p.map f) (q.map f) (isCoprime_map_rat_of_isRelPrime_int p q hpq) (f ∘ y) hyQ
  rw [Polynomial.natDegree_map_eq_of_injective (Int.cast_injective),
    Polynomial.natDegree_map_eq_of_injective (Int.cast_injective),
    Polynomial.homogenize_map, Polynomial.homogenize_map,
    MvPolynomial.eval_map, MvPolynomial.eval_map,
    ← MvPolynomial.eval₂_comp, ← MvPolynomial.eval₂_comp] at h
  simpa [f] using h

end
end PellPaper
