import Pell.HomogeneousQuadraticCharFourier

/-!
# Norm bounds for homogeneous quadratic-character Fourier coefficients

The exact Fourier factorization for an odd-degree homogeneous binary form
contains a quadratic Gauss sum and a one-variable character sum together
with one projective-axis value.  This file evaluates the Gauss-sum norm
exactly and bounds the axis value by one.  No estimate for the remaining
one-variable sum is used.
-/

namespace PellPaper

noncomputable section

open scoped BigOperators

/-- Over an odd prime field, the quadratic Gauss sum against the inverse
standard additive character has norm exactly the square root of the prime. -/
theorem quadraticGaussSum_inv_stdAddChar_norm
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    ‖gaussSum
        ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))
        ((ZMod.stdAddChar : AddChar (ZMod p) ℂ)⁻¹)‖ =
      Real.sqrt (p : ℝ) := by
  let χ : MulChar (ZMod p) ℂ :=
    (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)
  let ψ : AddChar (ZMod p) ℂ := ZMod.stdAddChar
  have hpchar : ringChar (ZMod p) ≠ 2 := by
    simpa only [ZMod.ringChar_zmod_n] using hp
  have hχne : χ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff Int.cast_injective).mpr
      (quadraticChar_ne_one hpchar)
  have hχquad : χ.IsQuadratic :=
    (quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)
  have hψprim : ψ.IsPrimitive := ZMod.isPrimitive_stdAddChar p
  have hprod := gaussSum_mul_gaussSum_eq_card (R' := ℂ)
    (R := ZMod p) (χ := χ) hχne hψprim
  have hstar := star_gaussSum_eq χ ψ
  rw [hχquad.inv] at hstar
  rw [hχquad.inv] at hprod
  have hprod' :
      gaussSum χ ψ * star (gaussSum χ ψ) = (p : ℂ) := by
    rw [hstar]
    simpa using hprod
  have hnormSq : Complex.normSq (gaussSum χ ψ) = (p : ℝ) := by
    have hcoerce : (Complex.normSq (gaussSum χ ψ) : ℂ) = (p : ℂ) := by
      calc
        (Complex.normSq (gaussSum χ ψ) : ℂ) =
            (starRingEnd ℂ) (gaussSum χ ψ) * gaussSum χ ψ :=
          Complex.normSq_eq_conj_mul_self
        _ = (p : ℂ) := by
          rw [← hprod']
          exact mul_comm _ _
    exact_mod_cast hcoerce
  have hnorm : ‖gaussSum χ ψ‖ = Real.sqrt (p : ℝ) := by
    rw [Complex.norm_def, hnormSq]
  change ‖gaussSum χ ψ⁻¹‖ = Real.sqrt (p : ℝ)
  calc
    ‖gaussSum χ ψ⁻¹‖ = ‖star (gaussSum χ ψ)‖ :=
      congrArg norm hstar |>.symm
    _ = ‖gaussSum χ ψ‖ := RCLike.norm_conj _
    _ = Real.sqrt (p : ℝ) := hnorm

private theorem norm_complex_quadraticChar_le_one
    (p : ℕ) [Fact p.Prime] (x : ZMod p) :
    ‖(quadraticChar (ZMod p) x : ℂ)‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · rcases quadraticChar_dichotomy hx with h | h
    · rw [h]
      norm_num
    · rw [h]
      norm_num

/-- The double Fourier coefficient is bounded by `sqrt p` times the norm
of its one-variable projective-chart sum plus one.  The added one is the
complete bound for the remaining projective-axis character value. -/
theorem zmodFourier2_quadraticChar_eval_binary_norm_le
    (p j : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (J : MvPolynomial (Fin 2) (ZMod p))
    (hJ : J.IsHomogeneous j) (hj : Odd j) (a b : ZMod p) :
    ‖zmodFourier2 (fun x y =>
        (quadraticChar (ZMod p) (MvPolynomial.eval ![x, y] J) : ℂ)) a b‖ ≤
      Real.sqrt (p : ℝ) *
        (‖∑ r : ZMod p,
            (quadraticChar (ZMod p)
              (MvPolynomial.eval ![r, 1] J * (a * r + b)) : ℂ)‖ + 1) := by
  rw [zmodFourier2_quadraticChar_eval_binary_eq_gaussSum
    p j hp J hJ hj a b]
  rw [norm_mul, quadraticGaussSum_inv_stdAddChar_norm p hp]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  calc
    ‖(∑ r : ZMod p,
          (quadraticChar (ZMod p)
            (MvPolynomial.eval ![r, 1] J * (a * r + b)) : ℂ)) +
        (quadraticChar (ZMod p)
          (MvPolynomial.eval ![1, 0] J * a) : ℂ)‖ ≤
      ‖∑ r : ZMod p,
          (quadraticChar (ZMod p)
            (MvPolynomial.eval ![r, 1] J * (a * r + b)) : ℂ)‖ +
        ‖(quadraticChar (ZMod p)
          (MvPolynomial.eval ![1, 0] J * a) : ℂ)‖ := norm_add_le _ _
    _ ≤ ‖∑ r : ZMod p,
          (quadraticChar (ZMod p)
            (MvPolynomial.eval ![r, 1] J * (a * r + b)) : ℂ)‖ + 1 := by
      gcongr
      exact norm_complex_quadraticChar_le_one p _

end
end PellPaper
