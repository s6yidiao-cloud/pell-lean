import Pell.PrimitiveSlopeFibre
import Pell.ProjectiveBinaryZeroKeys
import Pell.PaddedCoprimeHomogenizeEvaluation
import Pell.SquarefreePolynomialLinearNonsquare

/-!
# Counting primitive integer zeros of a homogeneous binary form

A nonzero degree-d homogeneous binary form has at most d rational projective
zeros, including infinity, and at most two primitive integral representatives
per projective zero. This counts target vectors only. A source-target count
still needs a separate bound for each source fibre.
-/

namespace PellPaper
noncomputable section
open Polynomial

private theorem dehom_degree (D : MvPolynomial (Fin 2) ℤ) (d : ℕ)
    (hD : D.IsHomogeneous d) : (binaryDehomogenizeAtOne D).natDegree ≤ d := by
  refine le_trans ?_ hD.totalDegree_le
  rw [binaryDehomogenizeAtOne, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.prod_univ_two, one_pow, mul_one]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Polynomial.natDegree_X_pow]
  exact (Finsupp.le_degree 0 e).trans (MvPolynomial.le_totalDegree he)

private theorem homogenize_zero_key (p : Polynomial ℤ) (d : ℕ)
    (hdeg : p.natDegree ≤ d) (y : Fin 2 → ℤ) (hy : IsCoprime (y 0) (y 1))
    (heval : MvPolynomial.eval y (p.homogenize d) = 0) :
    match integralBinarySlope y with
    | none => (p.map (Int.castRingHom ℚ)).coeff d = 0
    | some r => (p.map (Int.castRingHom ℚ)).eval r = 0 := by
  let f := Int.castRingHom ℚ
  have hevalQ : MvPolynomial.eval (f ∘ y) ((p.map f).homogenize d) = 0 := by
    rw [Polynomial.homogenize_map, MvPolynomial.eval_map, ← MvPolynomial.eval₂_comp]
    simp [heval]
  by_cases hy1 : y 1 = 0
  · simp only [integralBinarySlope, hy1, if_pos]
    have hy0 : (y 0 : ℚ) ≠ 0 := by
      exact_mod_cast hy.ne_zero_or_ne_zero.resolve_right (not_not.mpr hy1)
    have hvec : f ∘ y = ![(y 0 : ℚ), 0] := by
      funext i
      fin_cases i <;> simp [f, hy1]
    rw [hvec, eval_homogenize_at_infinity] at hevalQ
    exact (mul_eq_zero.mp hevalQ).resolve_right (pow_ne_zero _ hy0)
  · simp only [integralBinarySlope, hy1, if_false]
    have hy1Q : (f ∘ y) 1 ≠ 0 := by simpa [f] using hy1
    have hdegQ : (p.map f).natDegree ≤ d := by
      rw [Polynomial.natDegree_map_eq_of_injective (Int.cast_injective)]
      exact hdeg
    rw [Polynomial.eval_homogenize hdegQ (f ∘ y) hy1Q] at hevalQ
    exact (mul_eq_zero.mp hevalQ).resolve_right (pow_ne_zero _ hy1Q)

/-- The rational projective zero keys of a finite primitive integer zero
family number at most the original homogeneous degree. Infinity is included
without an extra additive one; degree-zero forms have no such zeros. -/
theorem card_slopes_of_homogeneous_binary_zeros_le
    (D : MvPolynomial (Fin 2) ℤ) (d : ℕ) (hD : D.IsHomogeneous d) (hD0 : D ≠ 0)
    (S : Finset (Fin 2 → ℤ))
    (hS : ∀ y ∈ S, IsCoprime (y 0) (y 1) ∧ MvPolynomial.eval y D = 0) :
    (S.image integralBinarySlope).card ≤ d := by
  classical
  let p := binaryDehomogenizeAtOne D
  have hrecover : p.homogenize d = D := by
    apply Polynomial.homogenize_eq_of_isHomogeneous hD
    rfl
  have hp : p ≠ 0 := by
    intro hz
    apply hD0
    rw [← hrecover, hz, Polynomial.homogenize_zero]
  have hdeg : p.natDegree ≤ d := dehom_degree D d hD
  let f := Int.castRingHom ℚ
  have hpQ : p.map f ≠ 0 := by
    intro hz
    apply hp
    exact Polynomial.map_injective f Int.cast_injective (by simpa using hz)
  have hdegQ : (p.map f).natDegree ≤ d := by
    rw [Polynomial.natDegree_map_eq_of_injective (Int.cast_injective)]
    exact hdeg
  apply card_projective_polynomial_zero_keys_le (p.map f) d hpQ hdegQ
  intro r hr
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hr
  exact homogenize_zero_key p d hdeg y (hS y hy).1
    (by rw [hrecover]; exact (hS y hy).2)

/-- A nonzero degree-d homogeneous binary form has at most 2d primitive
integer zero vectors in any finite family. No irreducibility, squarefreeness,
height bound, positive degree, or nonzero-coordinate assumption is needed. -/
theorem card_primitive_homogeneous_binary_zeros_le
    (D : MvPolynomial (Fin 2) ℤ) (d : ℕ) (hD : D.IsHomogeneous d) (hD0 : D ≠ 0)
    (S : Finset (Fin 2 → ℤ))
    (hS : ∀ y ∈ S, IsCoprime (y 0) (y 1) ∧ MvPolynomial.eval y D = 0) :
    S.card ≤ 2 * d :=
  (card_primitive_vectors_le_two_mul_card_slopes S (fun y hy => (hS y hy).1)).trans
    (Nat.mul_le_mul_left 2 (card_slopes_of_homogeneous_binary_zeros_le D d hD hD0 S hS))

/-- The same bound for the literal zero subfamily of an ambient finite set.
The ambient set need not consist of primitive vectors. -/
theorem card_filter_primitive_homogeneous_binary_zeros_le
    (D : MvPolynomial (Fin 2) ℤ) (d : ℕ) (hD : D.IsHomogeneous d) (hD0 : D ≠ 0)
    (T : Finset (Fin 2 → ℤ)) :
    (T.filter fun y => IsCoprime (y 0) (y 1) ∧ MvPolynomial.eval y D = 0).card ≤
      2 * d := by
  classical
  apply card_primitive_homogeneous_binary_zeros_le D d hD hD0
  intro y hy
  exact (Finset.mem_filter.mp hy).2

end
end PellPaper
