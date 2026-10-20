import Pell.BinaryHomogeneousSquarefreeCertificate
import Pell.SourceLinearPolynomialRelPrime

/-!
# Augmenting a degree-one bad-prime certificate

For a homogeneous binary linear form, the projective derivative resultant is
not by itself enough to force either nonzero coefficient to be a unit modulo
the product of two good primes.  This file multiplies an existing nonzero
integer certificate by nonzero replacements of the two linear coefficients.
The original certificate and every nonzero coefficient then divide the
augmentation in the orientation needed to exclude their prime divisors.

The construction does not need primitivity; that stronger property belongs
to the upstream squarefree-factor decomposition.  Its height cost is at most
two additional coefficient-height logarithms.
-/

namespace PellPaper

noncomputable section

/-- Replace a zero coefficient by one and leave every nonzero coefficient
unchanged. -/
def nonzeroCoefficientReplacement (a : ℤ) : ℤ :=
  if a = 0 then 1 else a

theorem nonzeroCoefficientReplacement_ne_zero (a : ℤ) :
    nonzeroCoefficientReplacement a ≠ 0 := by
  by_cases ha : a = 0
  · simp [nonzeroCoefficientReplacement, ha]
  · simp [nonzeroCoefficientReplacement, ha]

/-- The replacement has no larger natural absolute value than the positive
closure of any supplied coefficient-height bound, including height zero. -/
theorem natAbs_nonzeroCoefficientReplacement_le_max
    (a : ℤ) (H : ℕ) (ha : |a| ≤ (H : ℤ)) :
    (nonzeroCoefficientReplacement a).natAbs ≤ max 1 H := by
  by_cases hzero : a = 0
  · simp [nonzeroCoefficientReplacement, hzero]
  · rw [nonzeroCoefficientReplacement, if_neg hzero]
    have hcast : (a.natAbs : ℤ) ≤ (H : ℤ) := by
      simpa only [Int.natCast_natAbs] using ha
    have hnat : a.natAbs ≤ H := by exact_mod_cast hcast
    exact hnat.trans (le_max_right _ _)

/-- The coefficient of the degree-one monomial in variable `i`. -/
def binaryLinearCoefficient (J : MvPolynomial (Fin 2) ℤ) (i : Fin 2) : ℤ :=
  J.coeff (Finsupp.single i 1)

/-- A homogeneous degree-one binary polynomial is exactly the source-linear
form given by its two degree-one coefficients. -/
theorem eq_sourceLinearPolynomial_binaryLinearCoefficients
    (J : MvPolynomial (Fin 2) ℤ) (hJ : J.IsHomogeneous 1) :
    J = sourceLinearPolynomial (binaryLinearCoefficient J 0)
      (binaryLinearCoefficient J 1) := by
  have hsingle : (Finsupp.single 0 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
    intro h
    have hzero := congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
    simp at hzero
  ext e
  by_cases hdegree : e.degree = 1
  · have hsum : e 0 + e 1 = 1 := by
      simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hdegree
    have hcases : (e 0 = 1 ∧ e 1 = 0) ∨ (e 0 = 0 ∧ e 1 = 1) := by omega
    rcases hcases with hzero | hone
    · have he : e = Finsupp.single 0 1 := by
        apply Finsupp.ext
        intro i
        fin_cases i <;> simp [hzero.1, hzero.2]
      subst e
      rw [sourceLinearPolynomial, MvPolynomial.coeff_add,
        MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul,
        MvPolynomial.coeff_X, MvPolynomial.coeff_X]
      simp [binaryLinearCoefficient, Ne.symm hsingle]
    · have he : e = Finsupp.single 1 1 := by
        apply Finsupp.ext
        intro i
        fin_cases i <;> simp [hone.1, hone.2]
      subst e
      rw [sourceLinearPolynomial, MvPolynomial.coeff_add,
        MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul,
        MvPolynomial.coeff_X, MvPolynomial.coeff_X]
      simp [binaryLinearCoefficient]
      intro hcontra
      exact (hsingle hcontra).elim
  · have hlinear :
        (sourceLinearPolynomial (binaryLinearCoefficient J 0)
          (binaryLinearCoefficient J 1)).IsHomogeneous 1 :=
      (MvPolynomial.isHomogeneous_C_mul_X (binaryLinearCoefficient J 0) 0).add
        (MvPolynomial.isHomogeneous_C_mul_X (binaryLinearCoefficient J 1) 1)
    rw [hJ.coeff_eq_zero hdegree, hlinear.coeff_eq_zero hdegree]

/-- A nonzero homogeneous degree-one form has at least one nonzero selected
linear coefficient. -/
theorem binaryLinearCoefficients_ne_zero_of_isHomogeneous_one
    (J : MvPolynomial (Fin 2) ℤ) (hJ : J.IsHomogeneous 1) (hJ0 : J ≠ 0) :
    binaryLinearCoefficient J 0 ≠ 0 ∨ binaryLinearCoefficient J 1 ≠ 0 := by
  by_cases hzero : binaryLinearCoefficient J 0 = 0
  · right
    intro hone
    apply hJ0
    rw [eq_sourceLinearPolynomial_binaryLinearCoefficients J hJ]
    simp [sourceLinearPolynomial, hzero, hone]
  · exact Or.inl hzero

/-- Multiply an existing certificate by the two nonzero-replaced linear
coefficients. -/
def binaryLinearAugmentedCertificate
    (Delta : ℤ) (J : MvPolynomial (Fin 2) ℤ) : ℤ :=
  Delta * nonzeroCoefficientReplacement (binaryLinearCoefficient J 0) *
    nonzeroCoefficientReplacement (binaryLinearCoefficient J 1)

theorem binaryLinearAugmentedCertificate_ne_zero
    (Delta : ℤ) (J : MvPolynomial (Fin 2) ℤ) (hDelta : Delta ≠ 0) :
    binaryLinearAugmentedCertificate Delta J ≠ 0 := by
  exact mul_ne_zero
    (mul_ne_zero hDelta
      (nonzeroCoefficientReplacement_ne_zero (binaryLinearCoefficient J 0)))
    (nonzeroCoefficientReplacement_ne_zero (binaryLinearCoefficient J 1))

/-- The original certificate divides its augmentation. -/
theorem dvd_binaryLinearAugmentedCertificate
    (Delta : ℤ) (J : MvPolynomial (Fin 2) ℤ) :
    Delta ∣ binaryLinearAugmentedCertificate Delta J := by
  refine ⟨nonzeroCoefficientReplacement (binaryLinearCoefficient J 0) *
    nonzeroCoefficientReplacement (binaryLinearCoefficient J 1), ?_⟩
  simp only [binaryLinearAugmentedCertificate]
  ring

/-- Each selected nonzero linear coefficient divides the augmentation. -/
theorem binaryLinearCoefficient_dvd_binaryLinearAugmentedCertificate
    (Delta : ℤ) (J : MvPolynomial (Fin 2) ℤ) (i : Fin 2)
    (hi : binaryLinearCoefficient J i ≠ 0) :
    binaryLinearCoefficient J i ∣ binaryLinearAugmentedCertificate Delta J := by
  fin_cases i
  · change binaryLinearCoefficient J 0 ∣ binaryLinearAugmentedCertificate Delta J
    have hi0 : binaryLinearCoefficient J 0 ≠ 0 := by simpa using hi
    refine ⟨Delta * nonzeroCoefficientReplacement (binaryLinearCoefficient J 1), ?_⟩
    simp only [binaryLinearAugmentedCertificate, nonzeroCoefficientReplacement, if_neg hi0]
    ring
  · change binaryLinearCoefficient J 1 ∣ binaryLinearAugmentedCertificate Delta J
    have hi1 : binaryLinearCoefficient J 1 ≠ 0 := by simpa using hi
    refine ⟨Delta * nonzeroCoefficientReplacement (binaryLinearCoefficient J 0), ?_⟩
    simp only [binaryLinearAugmentedCertificate, nonzeroCoefficientReplacement, if_neg hi1]
    ring

/-- Every nonzero coefficient of a homogeneous degree-one binary polynomial
divides the augmented certificate.  This is the all-coefficients form used
when the particular nonzero linear coefficient has not yet been selected. -/
theorem coeff_dvd_binaryLinearAugmentedCertificate_of_isHomogeneous_one
    (Delta : ℤ) (J : MvPolynomial (Fin 2) ℤ) (hJ : J.IsHomogeneous 1)
    (e : Fin 2 →₀ ℕ) (he : J.coeff e ≠ 0) :
    J.coeff e ∣ binaryLinearAugmentedCertificate Delta J := by
  have hdegree : e.degree = 1 := by
    by_contra hne
    exact he (hJ.coeff_eq_zero hne)
  have hsum : e 0 + e 1 = 1 := by
    simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hdegree
  have hcases : (e 0 = 1 ∧ e 1 = 0) ∨ (e 0 = 0 ∧ e 1 = 1) := by omega
  rcases hcases with hzero | hone
  · have heq : e = Finsupp.single 0 1 := by
      apply Finsupp.ext
      intro i
      fin_cases i <;> simp [hzero.1, hzero.2]
    subst e
    exact binaryLinearCoefficient_dvd_binaryLinearAugmentedCertificate
      Delta J 0 (by simpa only [binaryLinearCoefficient] using he)
  · have heq : e = Finsupp.single 1 1 := by
      apply Finsupp.ext
      intro i
      fin_cases i <;> simp [hone.1, hone.2]
    subst e
    exact binaryLinearCoefficient_dvd_binaryLinearAugmentedCertificate
      Delta J 1 (by simpa only [binaryLinearCoefficient] using he)

/-- Natural absolute-value height of the augmented certificate.  The `max`
convention makes this valid at coefficient height zero. -/
theorem natAbs_binaryLinearAugmentedCertificate_le
    (Delta : ℤ) (J : MvPolynomial (Fin 2) ℤ) (H : ℕ)
    (hcoeff : ∀ e, |J.coeff e| ≤ (H : ℤ)) :
    (binaryLinearAugmentedCertificate Delta J).natAbs ≤
      Delta.natAbs * (max 1 H) ^ 2 := by
  have hzero := natAbs_nonzeroCoefficientReplacement_le_max
    (binaryLinearCoefficient J 0) H (hcoeff (Finsupp.single 0 1))
  have hone := natAbs_nonzeroCoefficientReplacement_le_max
    (binaryLinearCoefficient J 1) H (hcoeff (Finsupp.single 1 1))
  rw [binaryLinearAugmentedCertificate, Int.natAbs_mul, Int.natAbs_mul]
  calc
    Delta.natAbs *
          (nonzeroCoefficientReplacement (binaryLinearCoefficient J 0)).natAbs *
        (nonzeroCoefficientReplacement (binaryLinearCoefficient J 1)).natAbs ≤
      Delta.natAbs * (max 1 H) *
        (nonzeroCoefficientReplacement (binaryLinearCoefficient J 1)).natAbs :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hzero)
    _ ≤ Delta.natAbs * (max 1 H) * (max 1 H) :=
      Nat.mul_le_mul_left _ hone
    _ = Delta.natAbs * (max 1 H) ^ 2 := by ring

/-- Logarithmic augmentation cost, valid even when the supplied coefficient
height is zero.  Nonvanishing of the original certificate is the only
positivity input needed on the left. -/
theorem log_natAbs_binaryLinearAugmentedCertificate_le_max
    (Delta : ℤ) (J : MvPolynomial (Fin 2) ℤ) (H : ℕ)
    (hDelta : Delta ≠ 0) (hcoeff : ∀ e, |J.coeff e| ≤ (H : ℤ)) :
    Real.log ((binaryLinearAugmentedCertificate Delta J).natAbs : ℝ) ≤
      Real.log (Delta.natAbs : ℝ) + 2 * Real.log (max 1 H : ℕ) := by
  let a := nonzeroCoefficientReplacement (binaryLinearCoefficient J 0)
  let b := nonzeroCoefficientReplacement (binaryLinearCoefficient J 1)
  have ha : a ≠ 0 := nonzeroCoefficientReplacement_ne_zero _
  have hb : b ≠ 0 := nonzeroCoefficientReplacement_ne_zero _
  have hapos : 0 < (a.natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.mpr ha
  have hbpos : 0 < (b.natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.mpr hb
  have hdpos : 0 < (Delta.natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.mpr hDelta
  have haBound : (a.natAbs : ℝ) ≤ (max 1 H : ℕ) := by
    exact_mod_cast natAbs_nonzeroCoefficientReplacement_le_max
      (binaryLinearCoefficient J 0) H (hcoeff (Finsupp.single 0 1))
  have hbBound : (b.natAbs : ℝ) ≤ (max 1 H : ℕ) := by
    exact_mod_cast natAbs_nonzeroCoefficientReplacement_le_max
      (binaryLinearCoefficient J 1) H (hcoeff (Finsupp.single 1 1))
  have hloga := Real.log_le_log hapos haBound
  have hlogb := Real.log_le_log hbpos hbBound
  have hsplit :
      Real.log ((binaryLinearAugmentedCertificate Delta J).natAbs : ℝ) =
        Real.log (Delta.natAbs : ℝ) + Real.log (a.natAbs : ℝ) +
          Real.log (b.natAbs : ℝ) := by
    dsimp only [binaryLinearAugmentedCertificate, a, b]
    rw [Int.natAbs_mul, Int.natAbs_mul, Nat.cast_mul, Nat.cast_mul,
      Real.log_mul (mul_pos hdpos hapos).ne' hbpos.ne', Real.log_mul hdpos.ne' hapos.ne']
  rw [hsplit]
  linarith

/-- For a positive natural coefficient height, the `max` disappears and the
augmentation costs exactly at most two copies of `log H`. -/
theorem log_natAbs_binaryLinearAugmentedCertificate_le
    (Delta : ℤ) (J : MvPolynomial (Fin 2) ℤ) (H : ℕ)
    (hDelta : Delta ≠ 0) (hH : 0 < H)
    (hcoeff : ∀ e, |J.coeff e| ≤ (H : ℤ)) :
    Real.log ((binaryLinearAugmentedCertificate Delta J).natAbs : ℝ) ≤
      Real.log (Delta.natAbs : ℝ) + 2 * Real.log (H : ℝ) := by
  have hHone : 1 ≤ H := hH
  simpa only [max_eq_right hHone] using
    log_natAbs_binaryLinearAugmentedCertificate_le_max Delta J H hDelta hcoeff

end

end PellPaper
