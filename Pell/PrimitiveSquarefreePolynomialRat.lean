import Pell.PolynomialSquareParityDecomposition

/-!
# Primitive integral squarefree factors over the rationals

The Gauss-lemma bridge needed for the factorization in the manuscript.  The final decomposition is derived for every nonzero
integral polynomial, including constants and nonprimitive inputs.
-/

namespace PellPaper

open Polynomial

/-- A primitive squarefree integral polynomial remains squarefree over `ℚ`.
The proof transports irreducible factors and their nondivisibility by
Gauss's lemma; rational squarefreeness is not an input. -/
theorem squarefree_intPolynomial_map_rat
    (q : Polynomial ℤ) (hq : q.IsPrimitive) (hsq : Squarefree q) :
    Squarefree (q.map (Int.castRingHom ℚ)) := by
  induction q using WfDvdMonoid.induction_on_irreducible with
  | zero => exact (hsq.ne_zero rfl).elim
  | unit u hu => exact (hu.map (Polynomial.mapRingHom (Int.castRingHom ℚ))).squarefree
  | mul z a hz ha ih =>
      have haPrim : a.IsPrimitive :=
        Polynomial.isPrimitive_of_dvd hq (dvd_mul_right a z)
      have hzPrim : z.IsPrimitive :=
        Polynomial.isPrimitive_of_dvd hq (dvd_mul_left z a)
      have hparts := squarefree_mul_iff.mp hsq
      have haRat : Irreducible (a.map (Int.castRingHom ℚ)) :=
        (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast haPrim).mp ha
      rw [Polynomial.map_mul]
      refine squarefree_mul_iff.mpr
        ⟨haRat.isRelPrime_iff_not_dvd.mpr ?_, haRat.squarefree, ih hzPrim hparts.2.2⟩
      intro hadvd
      have haz : a ∣ z :=
        (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast a z haPrim).mpr hadvd
      exact (ha.isRelPrime_iff_not_dvd.mp hparts.1) haz

private theorem squarefree_content_of_squarefree
    (s : Polynomial ℤ) (hs : Squarefree s) : Squarefree s.content := by
  intro a ha
  have hC : Polynomial.C a * Polynomial.C a ∣ Polynomial.C s.content := by
    simpa only [map_mul] using
      (map_dvd (Polynomial.C : ℤ →+* Polynomial ℤ) ha)
  exact Polynomial.isUnit_C.mp (hs _ (hC.trans s.C_content_dvd))

/-- Separate the squarefree integer content and the primitive squarefree
polynomial part, with all factors nonzero and rational squarefreeness proved.
No sign restriction is placed on the input polynomial. -/
theorem exists_content_sq_mul_primitive_squarefree_intPolynomial
    (p : Polynomial ℤ) (hp : p ≠ 0) :
    ∃ (c : ℤ) (r q : Polynomial ℤ),
      p = Polynomial.C c * r ^ 2 * q ∧
      c ≠ 0 ∧ r ≠ 0 ∧ q ≠ 0 ∧
      Squarefree c ∧ q.IsPrimitive ∧ Squarefree q ∧
      Squarefree (q.map (Int.castRingHom ℚ)) := by
  obtain ⟨r, s, hrs, hs⟩ := exists_sq_mul_squarefree_intPolynomial p hp
  have hr0 : r ≠ 0 := by
    intro hr
    apply hp
    simp [hrs, hr]
  have hc0 : s.content ≠ 0 := fun h => hs.ne_zero (Polynomial.content_eq_zero_iff.mp h)
  have hq : Squarefree s.primPart := hs.squarefree_of_dvd s.primPart_dvd
  refine ⟨s.content, r, s.primPart, ?_, hc0, hr0, s.primPart_ne_zero,
    squarefree_content_of_squarefree s hs, s.isPrimitive_primPart, hq,
    squarefree_intPolynomial_map_rat s.primPart s.isPrimitive_primPart hq⟩
  calc
    p = r ^ 2 * s := hrs
    _ = r ^ 2 * (Polynomial.C s.content * s.primPart) :=
      congrArg (r ^ 2 * ·) s.eq_C_content_mul_primPart
    _ = Polynomial.C s.content * r ^ 2 * s.primPart := by ring

end PellPaper
