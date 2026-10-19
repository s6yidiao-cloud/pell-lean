import Pell.ZModFourierCRTBound
import Pell.HomogeneousOddQuadraticCharacterSum
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Literal polynomial Jacobi rectangles from local Fourier coefficients

Integer evaluation, reduction modulo each prime and the actual CRT product
are identified here. Odd homogeneity supplies both local zero modes; only
the nonzero local coefficient estimates remain hypotheses.
-/

namespace PellPaper

noncomputable section

open scoped BigOperators

private theorem quadraticChar_eval_map_intCast
    (p : ℕ) [Fact p.Prime] (J : MvPolynomial (Fin 2) ℤ) (x y : ℤ) :
    quadraticChar (ZMod p)
        (MvPolynomial.eval ![(x : ZMod p), (y : ZMod p)]
          (J.map (Int.castRingHom (ZMod p)))) =
      jacobiSym (MvPolynomial.eval ![x, y] J) p := by
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  unfold legendreSym
  congr 1
  rw [MvPolynomial.eval_map]
  change _ = (Int.castRingHom (ZMod p)) (MvPolynomial.eval ![x, y] J)
  rw [MvPolynomial.eval₂_comp]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- The actual CRT product of the two reduced polynomial characters equals
the integer Jacobi symbol at the product modulus, with arbitrary integer
coordinates. No homogeneity or odd-prime assumption is needed for this identity. -/
theorem zmodCRTProduct_quadraticChar_eval_intCast
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : p.Coprime q)
    (J : MvPolynomial (Fin 2) ℤ) (x y : ℤ) :
    zmodCRTProduct hpq
        (fun u v => (quadraticChar (ZMod p)
          (MvPolynomial.eval ![u, v] (J.map (Int.castRingHom (ZMod p)))) : ℂ))
        (fun u v => (quadraticChar (ZMod q)
          (MvPolynomial.eval ![u, v] (J.map (Int.castRingHom (ZMod q)))) : ℂ))
        (x : ZMod (p * q)) (y : ZMod (p * q)) =
      (jacobiSym (MvPolynomial.eval ![x, y] J) (p * q) : ℂ) := by
  simp only [zmodCRTProduct, map_intCast, Prod.fst_intCast, Prod.snd_intCast]
  rw [quadraticChar_eval_map_intCast, quadraticChar_eval_map_intCast,
    jacobiSym.mul_right, Int.cast_mul]

/-- The literal negative unnormalised double transform of an odd-degree
homogeneous binary polynomial character has zero constant coefficient. -/
theorem zmodFourier2_quadraticChar_eval_binary_zero
    (p j : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (J : MvPolynomial (Fin 2) (ZMod p))
    (hJ : J.IsHomogeneous j) (hj : Odd j) :
    zmodFourier2 (fun x y =>
      (quadraticChar (ZMod p) (MvPolynomial.eval ![x, y] J) : ℂ)) 0 0 = 0 := by
  simp only [zmodFourier2, neg_zero, zero_mul, sub_zero, AddChar.map_zero_eq_one,
    mul_one]
  have h := sum_quadraticChar_eval_binary_eq_zero_of_homogeneous_odd p j hp J hJ hj
  exact_mod_cast h

/-- Local nonzero Fourier estimates for two distinct odd primes give the
actual integer polynomial Jacobi rectangle bound. The offsets may be
negative and both windows may be empty or longer than the product modulus.
No CRT compatibility or zero-frequency hypothesis is supplied by the caller. -/
theorem abs_sum_jacobiSym_polynomial_shifted_rectangle_le_of_local_fourier2_bounds
    (p q j : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q)
    (J : MvPolynomial (Fin 2) ℤ) (hJ : J.IsHomogeneous j) (hj : Odd j)
    (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hbp : ∀ a b : ZMod p, (a, b) ≠ (0, 0) →
      ‖zmodFourier2 (fun u v => (quadraticChar (ZMod p)
        (MvPolynomial.eval ![u, v] (J.map (Int.castRingHom (ZMod p)))) : ℂ)) a b‖ ≤
        C₁ * (p : ℝ))
    (hbq : ∀ a b : ZMod q, (a, b) ≠ (0, 0) →
      ‖zmodFourier2 (fun u v => (quadraticChar (ZMod q)
        (MvPolynomial.eval ![u, v] (J.map (Int.castRingHom (ZMod q)))) : ℂ)) a b‖ ≤
        C₂ * (q : ℝ))
    (x0 y0 : ℤ) (L₁ L₂ : ℕ) :
    |∑ x ∈ Finset.range L₁, ∑ y ∈ Finset.range L₂,
      (jacobiSym (MvPolynomial.eval ![x0 + (x : ℤ), y0 + (y : ℤ)] J)
        (p * q) : ℝ)| ≤
      (C₁ * C₂) *
        (((p * q : ℕ) : ℝ) * (1 + Real.log ((p * q : ℕ) : ℝ)) ^ 2 +
          ((L₁ : ℝ) + (L₂ : ℝ)) * (1 + Real.log ((p * q : ℕ) : ℝ))) := by
  have hc : p.Coprime q := (Nat.coprime_primes Fact.out Fact.out).mpr hpq
  let fp : ZMod p → ZMod p → ℂ := fun u v =>
    (quadraticChar (ZMod p)
      (MvPolynomial.eval ![u, v] (J.map (Int.castRingHom (ZMod p)))) : ℂ)
  let fq : ZMod q → ZMod q → ℂ := fun u v =>
    (quadraticChar (ZMod q)
      (MvPolynomial.eval ![u, v] (J.map (Int.castRingHom (ZMod q)))) : ℂ)
  have hpzero : zmodFourier2 fp 0 0 = 0 :=
    zmodFourier2_quadraticChar_eval_binary_zero p j hp _
      (hJ.map (Int.castRingHom (ZMod p))) hj
  have hqzero : zmodFourier2 fq 0 0 = 0 :=
    zmodFourier2_quadraticChar_eval_binary_zero q j hq _
      (hJ.map (Int.castRingHom (ZMod q))) hj
  have hb := norm_sum_box_zmodCRTProduct_le_of_local_fourier2_bounds
    hc fp fq C₁ C₂ hC₁ hC₂ hpzero hqzero hbp hbq
      (x0 : ZMod (p * q)) (y0 : ZMod (p * q)) L₁ L₂
  have hterm (x y : ℕ) :
      zmodCRTProduct hc fp fq
        ((x0 : ZMod (p * q)) + (x : ZMod (p * q)))
        ((y0 : ZMod (p * q)) + (y : ZMod (p * q))) =
      (jacobiSym (MvPolynomial.eval ![x0 + (x : ℤ), y0 + (y : ℤ)] J)
        (p * q) : ℂ) := by
    simpa only [Int.cast_add, Int.cast_natCast] using
      zmodCRTProduct_quadraticChar_eval_intCast p q hc J (x0 + (x : ℤ)) (y0 + (y : ℤ))
  have hsum :
      (∑ x ∈ Finset.range L₁, ∑ y ∈ Finset.range L₂,
        zmodCRTProduct hc fp fq
          ((x0 : ZMod (p * q)) + (x : ZMod (p * q)))
          ((y0 : ZMod (p * q)) + (y : ZMod (p * q)))) =
      ((∑ x ∈ Finset.range L₁, ∑ y ∈ Finset.range L₂,
        (jacobiSym (MvPolynomial.eval ![x0 + (x : ℤ), y0 + (y : ℤ)] J)
          (p * q) : ℝ) : ℝ) : ℂ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    exact hterm x y
  rw [hsum, Complex.norm_real] at hb
  simpa only [Real.norm_eq_abs] using hb

end
end PellPaper
