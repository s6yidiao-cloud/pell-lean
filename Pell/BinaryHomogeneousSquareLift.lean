import Pell.SquarefreePolynomialLinearNonsquare
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.Tactic

/-!
# Lifting an actual square factorization from the affine binary chart

Homogenizing at padded degrees retains all powers of the second coordinate.
The padding is divided into a square part and one parity bit. This constructs
literal integral homogeneous factors, with an exact degree ledger and a
primitive odd-degree remainder, from the corresponding univariate factors.
-/

namespace PellPaper

noncomputable section
open Polynomial

private theorem dehom_homogenize (p : Polynomial ℤ) (d : ℕ)
    (hd : p.natDegree ≤ d) :
    binaryDehomogenizeAtOne (p.homogenize d) = p := by
  change MvPolynomial.aeval ![Polynomial.X, (1 : Polynomial ℤ)] (p.homogenize d) = p
  exact Polynomial.aeval_homogenize_X_one p hd

private theorem homogenize_dehom (K : MvPolynomial (Fin 2) ℤ) (d : ℕ)
    (hK : K.IsHomogeneous d) :
    (binaryDehomogenizeAtOne K).homogenize d = K := by
  apply Polynomial.homogenize_eq_of_isHomogeneous hK
  rfl

private theorem dehom_natDegree_le (K : MvPolynomial (Fin 2) ℤ) (d : ℕ)
    (hK : K.IsHomogeneous d) :
    (binaryDehomogenizeAtOne K).natDegree ≤ d := by
  refine le_trans ?_ hK.totalDegree_le
  rw [binaryDehomogenizeAtOne, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.prod_univ_two, one_pow, mul_one]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Polynomial.natDegree_X_pow]
  exact (Finsupp.le_degree 0 e).trans (MvPolynomial.le_totalDegree he)

private theorem primitive_homogenize (q : Polynomial ℤ) (j : ℕ)
    (hq : q.IsPrimitive) (hdeg : q.natDegree ≤ j) :
    ∀ a : ℤ, (∀ e : Fin 2 →₀ ℕ, a ∣ (q.homogenize j).coeff e) → IsUnit a := by
  intro a ha
  apply hq
  apply (Polynomial.C_dvd_iff_dvd_coeff a q).mpr
  intro n
  by_cases hn : n ≤ j
  · have h := ha (Finsupp.single 0 n + Finsupp.single 1 (j - n))
    rw [Polynomial.coeff_homogenize] at h
    simpa [Nat.add_sub_of_le hn] using h
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt (lt_of_not_ge hn))]
    exact dvd_zero a

/-- An actual affine-chart factorization with primitive remainder lifts to
literal integral binary factors. All projective-infinity multiplicity is
retained, the final degree is positive and odd, and its affine degree drops
by at most one. The univariate factorization is an algebraic input here,
not an asserted existence theorem. -/
theorem exists_homogeneous_square_lift_of_dehom_factorization
    (K : MvPolynomial (Fin 2) ℤ) (d : ℕ) (hK : K.IsHomogeneous d) (hd : Odd d)
    (c : ℤ) (r q : Polynomial ℤ) (hc : c ≠ 0) (hr : r ≠ 0) (hq : q.IsPrimitive)
    (hfactor : binaryDehomogenizeAtOne K = Polynomial.C c * r ^ 2 * q) :
    ∃ (R J : MvPolynomial (Fin 2) ℤ) (m j : ℕ),
      K = MvPolynomial.C c * R ^ 2 * J ∧
      R.IsHomogeneous m ∧ J.IsHomogeneous j ∧
      R ≠ 0 ∧ J ≠ 0 ∧ d = 2 * m + j ∧ Odd j ∧ 0 < j ∧
      binaryDehomogenizeAtOne R = r ∧ binaryDehomogenizeAtOne J = q ∧
      j ≤ q.natDegree + 1 ∧
      (∀ a : ℤ, (∀ e : Fin 2 →₀ ℕ, a ∣ J.coeff e) → IsUnit a) := by
  let n : ℕ := (binaryDehomogenizeAtOne K).natDegree
  let k : ℕ := d - n
  let m : ℕ := r.natDegree + k / 2
  let j : ℕ := q.natDegree + k % 2
  let R : MvPolynomial (Fin 2) ℤ := r.homogenize m
  let J : MvPolynomial (Fin 2) ℤ := q.homogenize j
  have hn : n ≤ d := dehom_natDegree_le K d hK
  have hndeg : n = 2 * r.natDegree + q.natDegree := by
    dsimp only [n]
    rw [hfactor, Polynomial.natDegree_mul
      (mul_ne_zero (Polynomial.C_ne_zero.mpr hc) (pow_ne_zero _ hr)) hq.ne_zero,
      Polynomial.natDegree_C_mul hc, Polynomial.natDegree_pow]
  have hledger : d = 2 * m + j := by
    dsimp [m, j, k]
    omega
  have hrdeg : r.natDegree ≤ m := Nat.le_add_right _ _
  have hqdeg : q.natDegree ≤ j := Nat.le_add_right _ _
  have hR : R.IsHomogeneous m := Polynomial.isHomogeneous_homogenize r
  have hJ : J.IsHomogeneous j := Polynomial.isHomogeneous_homogenize q
  have hRdehom : binaryDehomogenizeAtOne R = r := dehom_homogenize r m hrdeg
  have hJdehom : binaryDehomogenizeAtOne J = q := dehom_homogenize q j hqdeg
  have hR0 : R ≠ 0 := by
    intro hz
    have h := hRdehom
    rw [hz] at h
    simp only [binaryDehomogenizeAtOne, map_zero] at h
    exact hr h.symm
  have hJ0 : J ≠ 0 := by
    intro hz
    have h := hJdehom
    rw [hz] at h
    simp only [binaryDehomogenizeAtOne, map_zero] at h
    exact hq.ne_zero h.symm
  have hproductHom : (MvPolynomial.C c * R ^ 2 * J).IsHomogeneous d := by
    rw [hledger]
    have h := ((hR.pow 2).C_mul c).mul hJ
    simpa only [Nat.mul_comm] using h
  have hproductDehom : binaryDehomogenizeAtOne (MvPolynomial.C c * R ^ 2 * J) =
      binaryDehomogenizeAtOne K := by
    rw [hfactor]
    change (MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, (1 : Polynomial ℤ)])
      (MvPolynomial.C c * R ^ 2 * J) = _
    rw [map_mul, map_mul, map_pow, MvPolynomial.eval₂Hom_C]
    change Polynomial.C c * binaryDehomogenizeAtOne R ^ 2 *
      binaryDehomogenizeAtOne J = _
    rw [hRdehom, hJdehom]
  have hbinary : K = MvPolynomial.C c * R ^ 2 * J := by
    rw [← homogenize_dehom K d hK, ← homogenize_dehom _ d hproductHom]
    exact congrArg (fun p : Polynomial ℤ => p.homogenize d) hproductDehom.symm
  have hj : Odd j := by
    rw [Nat.odd_iff] at hd ⊢
    omega
  refine ⟨R, J, m, j, hbinary, hR, hJ, hR0, hJ0, hledger, hj,
    hj.pos, hRdehom, hJdehom, ?_, ?_⟩
  · dsimp [j]
    omega
  · exact primitive_homogenize q j hq hqdeg

end
end PellPaper
