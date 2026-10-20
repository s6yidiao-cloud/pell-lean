import Pell.BinaryHomogeneousSquareLift
import Mathlib.Algebra.GCDMonoid.Basic

/-!
# Exact integral common-target-factor extraction

An affine polynomial gcd, homogenized at the padded complementary degree,
retains every common factor at infinity. The residual pair has relatively
prime integral dehomogenizations and no common degree loss at infinity.
No irreducibility or factor-selection hypothesis is assumed.
-/

namespace PellPaper

noncomputable section
open Polynomial

private theorem recover (A : MvPolynomial (Fin 2) ℤ) (n : ℕ)
    (hA : A.IsHomogeneous n) : (binaryDehomogenizeAtOne A).homogenize n = A := by
  apply Polynomial.homogenize_eq_of_isHomogeneous hA
  rfl

private theorem dehom_degree (A : MvPolynomial (Fin 2) ℤ) (n : ℕ)
    (hA : A.IsHomogeneous n) : (binaryDehomogenizeAtOne A).natDegree ≤ n := by
  refine le_trans ?_ hA.totalDegree_le
  rw [binaryDehomogenizeAtOne, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.prod_univ_two, one_pow, mul_one]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Polynomial.natDegree_X_pow]
  exact (Finsupp.le_degree 0 e).trans (MvPolynomial.le_totalDegree he)

private theorem degree_add_le (g r : Polynomial ℤ) (n : ℕ)
    (hg : g ≠ 0) (hgn : g.natDegree ≤ n) (hgr : (g * r).natDegree ≤ n) :
    g.natDegree + r.natDegree ≤ n := by
  by_cases hr : r = 0
  · simpa [hr] using hgn
  · rwa [Polynomial.natDegree_mul hg hr] at hgr

/-- A nonzero homogeneous binary pair has an exact integral common factor.
The residual affine pair is relatively prime, and its common homogeneous
degree is exactly the maximum of its affine degrees. Thus all shared padding
at infinity is assigned to the common factor, including zero-component and
degree-zero cases. -/
theorem exists_homogeneous_binary_common_factor
    (A₀ B₀ : MvPolynomial (Fin 2) ℤ) (n : ℕ)
    (hA₀ : A₀.IsHomogeneous n) (hB₀ : B₀.IsHomogeneous n)
    (h₀ : A₀ ≠ 0 ∨ B₀ ≠ 0) :
    ∃ (D A B : MvPolynomial (Fin 2) ℤ) (d b : ℕ),
      D ≠ 0 ∧ (A ≠ 0 ∨ B ≠ 0) ∧
      D.IsHomogeneous d ∧ A.IsHomogeneous b ∧ B.IsHomogeneous b ∧
      d + b = n ∧ A₀ = D * A ∧ B₀ = D * B ∧
      IsRelPrime (binaryDehomogenizeAtOne A) (binaryDehomogenizeAtOne B) ∧
      b = max (binaryDehomogenizeAtOne A).natDegree
        (binaryDehomogenizeAtOne B).natDegree := by
  let P := binaryDehomogenizeAtOne A₀
  let Q := binaryDehomogenizeAtOne B₀
  have hP : P.homogenize n = A₀ := recover A₀ n hA₀
  have hQ : Q.homogenize n = B₀ := recover B₀ n hB₀
  have hPQ : P ≠ 0 ∨ Q ≠ 0 := by
    contrapose! h₀
    constructor
    · rw [← hP, h₀.1]; simp
    · rw [← hQ, h₀.2]; simp
  let g := gcd P Q
  have hg : g ≠ 0 := by
    intro hz
    have h := (gcd_eq_zero_iff P Q).mp hz
    exact hPQ.elim (fun hp => hp h.1) (fun hq => hq h.2)
  obtain ⟨p, q, hp, hq, hpq⟩ := extract_gcd P Q
  have hp' : P = g * p := hp
  have hq' : Q = g * q := hq
  have hres : p ≠ 0 ∨ q ≠ 0 := by
    rcases hPQ with hP₀ | hQ₀
    · left; intro hz; apply hP₀; rw [hp', hz, mul_zero]
    · right; intro hz; apply hQ₀; rw [hq', hz, mul_zero]
  have hPn : P.natDegree ≤ n := dehom_degree A₀ n hA₀
  have hQn : Q.natDegree ≤ n := dehom_degree B₀ n hB₀
  have hgn : g.natDegree ≤ n := by
    rcases hres with hp₀ | hq₀
    · rw [hp', Polynomial.natDegree_mul hg hp₀] at hPn
      omega
    · rw [hq', Polynomial.natDegree_mul hg hq₀] at hQn
      omega
  have hgpn : g.natDegree + p.natDegree ≤ n :=
    degree_add_le g p n hg hgn (hp' ▸ hPn)
  have hgqn : g.natDegree + q.natDegree ≤ n :=
    degree_add_le g q n hg hgn (hq' ▸ hQn)
  let b := max p.natDegree q.natDegree
  let d := n - b
  have hgb : g.natDegree + b ≤ n := by dsimp [b]; omega
  have hb : b ≤ n := by omega
  have hd : g.natDegree ≤ d := by dsimp [d]; omega
  have hdb : d + b = n := Nat.sub_add_cancel hb
  have hpb : p.natDegree ≤ b := le_max_left _ _
  have hqb : q.natDegree ≤ b := le_max_right _ _
  let D := g.homogenize d
  let A := p.homogenize b
  let B := q.homogenize b
  have hA : binaryDehomogenizeAtOne A = p := by
    exact Polynomial.aeval_homogenize_X_one p hpb
  have hB : binaryDehomogenizeAtOne B = q := by
    exact Polynomial.aeval_homogenize_X_one q hqb
  refine ⟨D, A, B, d, b, ?_, ?_, Polynomial.isHomogeneous_homogenize g,
    Polynomial.isHomogeneous_homogenize p, Polynomial.isHomogeneous_homogenize q,
    hdb, ?_, ?_, ?_, ?_⟩
  · exact (Polynomial.homogenize_eq_zero_iff hd).not.mpr hg
  · exact hres.imp ((Polynomial.homogenize_eq_zero_iff hpb).not.mpr)
      ((Polynomial.homogenize_eq_zero_iff hqb).not.mpr)
  · rw [← hP, hp', ← hdb, Polynomial.homogenize_mul g p hd hpb]
  · rw [← hQ, hq', ← hdb, Polynomial.homogenize_mul g q hd hqb]
  · rw [hA, hB]
    exact gcd_isUnit_iff_isRelPrime.mp hpq
  · rw [hA, hB]

/-- Exact factorization gives the literal source-linear evaluation identity. -/
theorem eval_source_linear_eq_common_factor
    (A₀ B₀ D A B : MvPolynomial (Fin 2) ℤ)
    (hA : A₀ = D * A) (hB : B₀ = D * B) (lambda y : Fin 2 → ℤ) :
    lambda 0 * MvPolynomial.eval y A₀ + lambda 1 * MvPolynomial.eval y B₀ =
      MvPolynomial.eval y D *
        (lambda 0 * MvPolynomial.eval y A + lambda 1 * MvPolynomial.eval y B) := by
  rw [hA, hB, map_mul, map_mul]
  ring

/-- The common-target zero family is retained as a separate branch. -/
theorem source_linear_zero_iff_common_factor_or_residual
    (A₀ B₀ D A B : MvPolynomial (Fin 2) ℤ)
    (hA : A₀ = D * A) (hB : B₀ = D * B) (lambda y : Fin 2 → ℤ) :
    lambda 0 * MvPolynomial.eval y A₀ + lambda 1 * MvPolynomial.eval y B₀ = 0 ↔
      MvPolynomial.eval y D = 0 ∨
        lambda 0 * MvPolynomial.eval y A + lambda 1 * MvPolynomial.eval y B = 0 := by
  rw [eval_source_linear_eq_common_factor A₀ B₀ D A B hA hB lambda y, mul_eq_zero]

end
end PellPaper
