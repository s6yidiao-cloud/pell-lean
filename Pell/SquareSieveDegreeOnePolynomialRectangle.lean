import Pell.BinaryLinearCertificateAugmentation
import Pell.GoodPrimeLinearCoefficientUnit
import Pell.SquareSieveLinearRectangle

/-!
# Square sieving degree-one homogeneous polynomials on rectangles

The projective derivative resultant alone need not exclude primes dividing a
linear coefficient.  This wrapper augments a supplied nonzero certificate by
the two nonzero-replaced coefficients, proves the resulting good-prime unit
condition, and invokes the separate Pólya--Vinogradov square-sieve branch.
-/

namespace PellPaper

open Filter

noncomputable section

private theorem eval_binaryLinearCoefficients_of_isHomogeneous_one
    (J : MvPolynomial (Fin 2) ℤ) (hJ : J.IsHomogeneous 1)
    (z : Fin 2 → ℤ) :
    MvPolynomial.eval z J =
      binaryLinearCoefficient J 0 * z 0 +
        binaryLinearCoefficient J 1 * z 1 := by
  calc
    MvPolynomial.eval z J =
        MvPolynomial.eval z
          (sourceLinearPolynomial (binaryLinearCoefficient J 0)
            (binaryLinearCoefficient J 1)) :=
      congrArg (MvPolynomial.eval z)
        (eq_sourceLinearPolynomial_binaryLinearCoefficients J hJ)
    _ = _ := by simp [sourceLinearPolynomial]

/-- A nonzero homogeneous linear factor satisfies the square-sieve estimate
after charging two coefficient-height logarithms to its bad-prime
certificate.  The eventual threshold is uniform in every later datum, and
no polynomial Fourier hypothesis occurs in this degree-one branch. -/
theorem eventually_squareSieve_degreeOne_polynomial_rectangle_le :
    ∀ᶠ N : ℕ in atTop, ∀ Delta0 c : ℤ, ∀ H : ℕ, ∀ W : ℝ,
      ∀ J : MvPolynomial (Fin 2) ℤ,
      ∀ x0 y0 : ℤ, ∀ L₁ L₂ : ℕ, ∀ f r : ℕ × ℕ → ℤ,
      Delta0 ≠ 0 → c ∣ Delta0 →
      J.IsHomogeneous 1 → J ≠ 0 →
      0 < H →
      (∀ e, |J.coeff e| ≤ (H : ℤ)) →
      Real.log (Delta0.natAbs : ℝ) + 2 * Real.log (H : ℝ) ≤
        (Real.log 2 / 8) * (N : ℝ) →
      Real.log W ≤ (Real.log 2 / 16) * (N : ℝ) →
      (∀ xy ∈ (Finset.range L₁).product (Finset.range L₂),
        f xy = c * (r xy) ^ 2 *
          MvPolynomial.eval
            ![x0 + (xy.1 : ℤ), y0 + (xy.2 : ℤ)] J) →
      (∀ xy ∈ (Finset.range L₁).product (Finset.range L₂),
        ((f xy).natAbs : ℝ) ≤ W) →
      ((((Finset.range L₁).product (Finset.range L₂)).filter
        (fun xy => f xy ≠ 0 ∧ IsSquare (f xy))).card : ℝ) ≤
        (32 / Real.log 2) * (L₁ : ℝ) * (L₂ : ℝ) *
            Real.log (N : ℝ) / (N : ℝ) +
          64 * ((max L₁ L₂ : ℕ) : ℝ) * (N : ℝ) *
            (1 + Real.log (16 * (N : ℝ) ^ 2)) := by
  filter_upwards [eventually_squareSieve_linear_rectangle_le] with N hlinear
  intro Delta0 c H W J x0 y0 L₁ L₂ f r hDelta0 hcDelta0 hJ hJ0 hH
    hcoeff hDeltaBudget hW hfactor hsize
  let DeltaLin := binaryLinearAugmentedCertificate Delta0 J
  let a := binaryLinearCoefficient J 0
  let b := binaryLinearCoefficient J 1
  have hDeltaLin : DeltaLin ≠ 0 :=
    binaryLinearAugmentedCertificate_ne_zero Delta0 J hDelta0
  have hcDeltaLin : c ∣ DeltaLin :=
    hcDelta0.trans (dvd_binaryLinearAugmentedCertificate Delta0 J)
  have hDeltaLinBudget :
      Real.log (DeltaLin.natAbs : ℝ) ≤
        (Real.log 2 / 8) * (N : ℝ) :=
    (log_natAbs_binaryLinearAugmentedCertificate_le
      Delta0 J H hDelta0 hH hcoeff).trans hDeltaBudget
  have hab : a ≠ 0 ∨ b ≠ 0 :=
    binaryLinearCoefficients_ne_zero_of_isHomogeneous_one J hJ hJ0
  have hunit : ∀ p ∈ goodPrimeAnnulus N DeltaLin,
      ∀ q ∈ goodPrimeAnnulus N DeltaLin, p ≠ q →
        IsUnit (a : ZMod (p * q)) ∨ IsUnit (b : ZMod (p * q)) := by
    intro p hp q hq _hpq
    exact linearCoefficient_isUnit_or_isUnit_of_goodPrimeAnnulus
      N DeltaLin a b p q hp hq hab
        (fun ha => binaryLinearCoefficient_dvd_binaryLinearAugmentedCertificate
          Delta0 J 0 ha)
        (fun hb => binaryLinearCoefficient_dvd_binaryLinearAugmentedCertificate
          Delta0 J 1 hb)
  have hfactorLinear : ∀ xy ∈ (Finset.range L₁).product (Finset.range L₂),
      f xy = c * (r xy) ^ 2 *
        (a * ((xy.1 : ℤ) + x0) + b * ((xy.2 : ℤ) + y0)) := by
    intro xy hxy
    rw [hfactor xy hxy]
    congr 1
    rw [eval_binaryLinearCoefficients_of_isHomogeneous_one J hJ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [a, b]
    ring
  exact hlinear DeltaLin c a b W x0 y0 L₁ L₂ f r
    hDeltaLin hcDeltaLin hDeltaLinBudget hW hunit hfactorLinear hsize

end

end PellPaper
