import Pell.TwoLayerBinaryPolynomial
import Pell.BinaryQuadraticLinearEliminantHeight
import Pell.BinaryHomogeneousSquarefreeCertificate

/-!
# The actual eliminant of the original two-layer auxiliary form

The original coefficient vector gives the two binary components A and B.
The literal substitution K=c*G(B,-A;y) is homogeneous of degree 2b+1 and
has an explicit height bound from the original coefficients. Its nonzero
branch constructs the squarefree-factor resultant certificate, without
assuming a factorization or a height for any resulting factor.

Source: the manuscript. Nonvanishing of K remains explicit;
the construction and height estimates do not imply it. At factor degree
one the resultant certificate does not include the separate coefficient-
prime factor required for good reduction in the manuscript.
-/

namespace PellPaper

noncomputable section

/-- The actual c*G(B,-A;y) polynomial, using the original source-coordinate
slices A=f₀ and B=f₁ of the two-layer auxiliary form. -/
def twoLayerEliminant (b : ℕ) (f : twoLayerFormIndex b → ℤ)
    (g : Fin 3 → Fin 2 → ℤ) (c : ℤ) : MvPolynomial (Fin 2) ℤ :=
  quadraticLinearEliminant g c
    (twoLayerBinaryPolynomial b f 0) (twoLayerBinaryPolynomial b f 1)

/-- Literal evaluation retains the source order (B,-A) and the original
six coefficients of G. -/
theorem eval_twoLayerEliminant (b : ℕ) (f : twoLayerFormIndex b → ℤ)
    (g : Fin 3 → Fin 2 → ℤ) (c : ℤ) (y : Fin 2 → ℤ) :
    MvPolynomial.eval y (twoLayerEliminant b f g c) =
      c * quadraticLinearFormEval g
        ![MvPolynomial.eval y (twoLayerBinaryPolynomial b f 1),
          -MvPolynomial.eval y (twoLayerBinaryPolynomial b f 0)] y :=
  eval_quadraticLinearEliminant g c _ _ y

/-- The same substitution annihilates the original two-layer form, even
when both source components vanish at the target point. -/
theorem twoLayerFormEval_at_binary_kernel_eq_zero
    (b : ℕ) (f : twoLayerFormIndex b → ℤ) (y : ℤ × ℤ) :
    twoLayerFormEval b f
      ((MvPolynomial.eval ![y.1, y.2] (twoLayerBinaryPolynomial b f 1),
        -MvPolynomial.eval ![y.1, y.2] (twoLayerBinaryPolynomial b f 0)), y) = 0 := by
  rw [twoLayerFormEval_eq_binaryPolynomial]
  dsimp
  ring

/-- The original auxiliary degree gives the eliminant degree 2b+1.
Homogeneity is also valid when the resulting eliminant is zero. -/
theorem twoLayerEliminant_isHomogeneous (b : ℕ) (f : twoLayerFormIndex b → ℤ)
    (g : Fin 3 → Fin 2 → ℤ) (c : ℤ) :
    (twoLayerEliminant b f g c).IsHomogeneous (2 * b + 1) :=
  isHomogeneous_quadraticLinearEliminant g c _ _ b
    (twoLayerBinaryPolynomial_isHomogeneous b f 0)
    (twoLayerBinaryPolynomial_isHomogeneous b f 1)

/-- Original integer coefficient bounds imply the explicit six-term
eliminant height, with only b+1 coefficient products per term. -/
theorem abs_coeff_twoLayerEliminant_le
    (b : ℕ) (f : twoLayerFormIndex b → ℤ) (g : Fin 3 → Fin 2 → ℤ)
    (c HF HG : ℤ) (hHF : 0 ≤ HF) (hHG : 0 ≤ HG)
    (hf : ∀ ab, |f ab| ≤ HF) (hg : ∀ i t, |g i t| ≤ HG)
    (e : Fin 2 →₀ ℕ) :
    |(twoLayerEliminant b f g c).coeff e| ≤
      6 * ((b : ℤ) + 1) * |c| * HF ^ 2 * HG :=
  abs_coeff_quadraticLinearEliminant_le g c _ _ b HF HG
    (twoLayerBinaryPolynomial_isHomogeneous b f 0)
    (twoLayerBinaryPolynomial_isHomogeneous b f 1) hHF hHG
    (abs_coeff_twoLayerBinaryPolynomial_le b f 0 HF hHF hf)
    (abs_coeff_twoLayerBinaryPolynomial_le b f 1 HF hHF hf) hg e

/-- In the actual nonzero-eliminant branch, construct all square-content
factors and the nonzero resultant certificate from the original f/g heights.
The original scalar c is distinct from the constructed squarefree content a. -/
theorem exists_twoLayerEliminant_bounded_resultant_certificate
    (b : ℕ) (f : twoLayerFormIndex b → ℤ) (g : Fin 3 → Fin 2 → ℤ)
    (c : ℤ) (HF HG : ℕ) (hc : c ≠ 0) (hHF : 0 < HF) (hHG : 0 < HG)
    (hf : ∀ ab, |f ab| ≤ (HF : ℤ)) (hg : ∀ i t, |g i t| ≤ (HG : ℤ))
    (hK : twoLayerEliminant b f g c ≠ 0) :
    let H0 : ℕ := 6 * (b + 1) * c.natAbs * HF ^ 2 * HG
    ∃ (a : ℤ) (R J : MvPolynomial (Fin 2) ℤ) (m j : ℕ),
      twoLayerEliminant b f g c = MvPolynomial.C a * R ^ 2 * J ∧
      a ≠ 0 ∧ Squarefree a ∧ |a| ≤ (H0 : ℤ) ∧ R ≠ 0 ∧ J ≠ 0 ∧
      R.IsHomogeneous m ∧ J.IsHomogeneous j ∧
      2 * b + 1 = 2 * m + j ∧ Odd j ∧ 0 < j ∧
      (∀ z : ℤ, (∀ e : Fin 2 →₀ ℕ, z ∣ J.coeff e) → IsUnit z) ∧
      (∀ e, |J.coeff e| ≤ ((2 ^ (2 * b + 1) * (2 * b + 1 + 1) * H0 : ℕ) : ℤ)) ∧
      2 * a * binaryProjectiveDerivativeResultant J j ≠ 0 ∧
      Real.log ((2 * a * binaryProjectiveDerivativeResultant J j).natAbs : ℝ) ≤
        Real.log 2 + Real.log (H0 : ℝ) +
          Real.log ((2 * (j - 1)).factorial : ℝ) +
            (2 * (j - 1) : ℕ) *
              (2 * Real.log (j : ℝ) + ((2 * b + 1 : ℕ) : ℝ) * Real.log 2 +
                Real.log (((2 * b + 1 : ℕ) : ℝ) + 1) + Real.log (H0 : ℝ)) := by
  let H0 : ℕ := 6 * (b + 1) * c.natAbs * HF ^ 2 * HG
  have hcabs : 0 < c.natAbs := Int.natAbs_pos.mpr hc
  have hH0 : 0 < H0 := by dsimp [H0]; positivity
  have hcoeff : ∀ e, |(twoLayerEliminant b f g c).coeff e| ≤ (H0 : ℤ) := by
    intro e
    have h := abs_coeff_twoLayerEliminant_le b f g c HF HG
      (by positivity) (by positivity) hf hg e
    simpa only [H0, Nat.cast_mul, Nat.cast_add, Nat.cast_pow,
      Nat.cast_ofNat, Nat.cast_one, Int.natCast_natAbs] using h
  exact exists_homogeneous_square_factor_with_bounded_resultant_certificate
    (twoLayerEliminant b f g c) (2 * b + 1) H0
    (twoLayerEliminant_isHomogeneous b f g c) hK ⟨b, rfl⟩ hH0 hcoeff

end
end PellPaper
