import Mathlib.Data.Nat.Squarefree
import Pell.Elementary

/-!
# Square-part decomposition of a positive natural number

This file formalizes the decomposition used in the subsection "Square parts" of
the manuscript.  Every positive natural number has a unique expression

`m = s ^ 2 * w`

with `s` and `w` positive and `w` squarefree.  If `m` is not a square, then the
squarefree part `w` is itself a nonsquare (and hence is greater than one).

The final theorem puts such a decomposition into the exact integer-radicand
form required by `PellPaper.square_part_transfer`.
-/

namespace PellPaper

/-- Every positive natural number is a square times a positive squarefree
natural number, in the orientation used in the manuscript. -/
theorem exists_square_part_decomposition {m : ℕ} (hm : 0 < m) :
    ∃ s w : ℕ, 0 < s ∧ 0 < w ∧ m = s ^ 2 * w ∧ Squarefree w := by
  obtain ⟨w, s, hw, hs, hmul, hsf⟩ := Nat.sq_mul_squarefree_of_pos hm
  exact ⟨s, w, hs, hw, hmul.symm, hsf⟩

/-- The positive square/squarefree decomposition is unique. -/
theorem square_part_decomposition_unique {m s w s' w' : ℕ}
    (hs : 0 < s) (hw : 0 < w) (hs' : 0 < s') (hw' : 0 < w')
    (hm : m = s ^ 2 * w) (hm' : m = s' ^ 2 * w')
    (hsf : Squarefree w) (hsf' : Squarefree w') :
    s = s' ∧ w = w' := by
  have hs0 : s ≠ 0 := hs.ne'
  have hw0 : w ≠ 0 := hw.ne'
  have hs0' : s' ≠ 0 := hs'.ne'
  have hw0' : w' ≠ 0 := hw'.ne'
  have hfac : ∀ p : ℕ,
      s.factorization p = s'.factorization p ∧
        w.factorization p = w'.factorization p := by
    intro p
    have heq := congrArg (fun n : ℕ => n.factorization p) (hm.symm.trans hm')
    have hsf_le : w.factorization p ≤ 1 := hsf.natFactorization_le_one p
    have hsf_le' : w'.factorization p ≤ 1 := hsf'.natFactorization_le_one p
    simp only [Nat.factorization_mul (pow_ne_zero 2 hs0) hw0,
      Nat.factorization_mul (pow_ne_zero 2 hs0') hw0', Nat.factorization_pow,
      Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul] at heq
    omega
  exact
    ⟨Nat.eq_of_factorization_eq hs0 hs0' fun p => (hfac p).1,
      Nat.eq_of_factorization_eq hw0 hw0' fun p => (hfac p).2⟩

/-- In a decomposition of a nonsquare, the squarefree part cannot be a square. -/
theorem squarefree_part_not_isSquare {m s w : ℕ} (hm : m = s ^ 2 * w)
    (hm_nonsquare : ¬ IsSquare m) : ¬ IsSquare w := by
  intro hw
  apply hm_nonsquare
  rw [hm]
  exact (IsSquare.sq s).mul hw

/-- The form of the decomposition used for nonsquare Pell radicands: the
squarefree part is positive, greater than one, and itself nonsquare. -/
theorem exists_square_part_decomposition_of_not_isSquare {m : ℕ} (hm : 0 < m)
    (hm_nonsquare : ¬ IsSquare m) :
    ∃ s w : ℕ,
      0 < s ∧ 1 < w ∧ m = s ^ 2 * w ∧ Squarefree w ∧ ¬ IsSquare w := by
  obtain ⟨s, w, hs, hw, hmul, hsf⟩ := exists_square_part_decomposition hm
  have hwns : ¬ IsSquare w := squarefree_part_not_isSquare hmul hm_nonsquare
  have hw1 : w ≠ 1 := fun hw1 => hwns (hw1.symm ▸ IsSquare.one)
  exact ⟨s, w, hs, by omega, hmul, hsf, hwns⟩

private theorem cast_fundamental {d e : ℤ} (hde : d = e)
    {a : Pell.Solution₁ d} (ha : Pell.IsFundamental a) :
    ∃ b : Pell.Solution₁ e, Pell.IsFundamental b ∧ epsilon b = epsilon a := by
  subst e
  exact ⟨a, ha, rfl⟩

/-- Apply `square_part_transfer` after rewriting a natural-number square-part
decomposition as an equality of integer Pell radicands.  The hypotheses that
`w` is squarefree and nonsquare are useful in applications, but the elementary
transfer itself needs only the displayed decomposition and `s > 0`. -/
theorem square_part_transfer_of_decomposition {m s w : ℕ}
    (hs : 0 < s) (hm : m = s ^ 2 * w)
    {a : Pell.Solution₁ (w : ℤ)} {b : Pell.Solution₁ (m : ℤ)}
    (ha : Pell.IsFundamental a) (hb : Pell.IsFundamental b) :
    epsilon a ≤ epsilon b := by
  have hm_int : (m : ℤ) = (s : ℤ) ^ 2 * (w : ℤ) := by
    exact_mod_cast hm
  obtain ⟨b', hb', hb'_epsilon⟩ := cast_fundamental hm_int hb
  rw [← hb'_epsilon]
  exact square_part_transfer hs ha hb'

end PellPaper
