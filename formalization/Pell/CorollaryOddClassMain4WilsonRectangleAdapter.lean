import Pell.CorollaryOddClassMain4WilsonPartialSummation

/-!
# Ordinary rectangle adapters for the four Wilson twists

This module puts the ordinary (non-harmonic) prefixes produced by Abel
summation into the exact rectangular Jacobi-sum shape used by Wilson and by
the Friedlander--Iwaniec estimate.  The radicand coefficient is extended by
zero from each of the four discriminant branches.  Its factorization into a
bounded branch mask and the common reciprocal-divisor weight is kept
explicit.

Everything here is a finite identity or an elementary coefficient bound.
No analytic estimate is introduced.
-/

namespace PellPaper

open NumberTheorySymbols
open scoped BigOperators

noncomputable section

/-! ## A source-shaped ordinary rectangle -/

/-- An ordinary Jacobi rectangle, with the radicand variable `m` outermost
and the polynomial variable `n` innermost.  Unlike the original polynomial,
there is no reciprocal factor `1 / n` in this sum. -/
def main4OrdinaryJacobiRectangle
    (nCoefficient mCoefficient : ℕ → ℝ) (M N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M, mCoefficient m *
    ∑ n ∈ Finset.Icc 1 N,
      nCoefficient n * (J((n : ℤ) | m) : ℝ)

/-- The `n`-coefficient obtained from a fixed character modulo eight. -/
def main4WilsonTwistSequence
    (rho : DirichletCharacter ℤ 8) (n : ℕ) : ℝ :=
  (rho (n : ZMod 8) : ℝ)

theorem main4WilsonTwistCoefficient_eq_sequence_mul_jacobi
    (rho : DirichletCharacter ℤ 8) (m n : ℕ) :
    main4WilsonTwistCoefficient rho m n =
      main4WilsonTwistSequence rho n * (J((n : ℤ) | m) : ℝ) := by
  rfl

/-- Every fixed modulus-eight twist is supported on odd indices. -/
theorem main4WilsonTwistSequence_eq_zero_of_even
    (rho : DirichletCharacter ℤ 8) (n : ℕ) (hn : Even n) :
    main4WilsonTwistSequence rho n = 0 := by
  unfold main4WilsonTwistSequence
  rw [dirichletCharacter_mod_eight_apply_eq_zero_of_even rho n hn]
  norm_num

/-- An integral Dirichlet character has real absolute value at most one. -/
theorem abs_main4WilsonTwistSequence_le_one
    (rho : DirichletCharacter ℤ 8) (n : ℕ) :
    |main4WilsonTwistSequence rho n| ≤ 1 := by
  unfold main4WilsonTwistSequence
  by_cases hunit : IsUnit (n : ZMod 8)
  · have himage : IsUnit (rho (n : ZMod 8)) := hunit.map rho
    rcases Int.isUnit_iff.mp himage with h | h
    · rw [h]
      norm_num
    · rw [h]
      norm_num
  · rw [rho.map_nonunit hunit]
    norm_num

/-! ## Exact masks and reciprocal-divisor coefficients -/

/-- The real indicator of a finite radicand family, with a fixed amplitude. -/
def main4WilsonFiniteMask (s : Finset ℕ) (c : ℝ) (m : ℕ) : ℝ :=
  if m ∈ s then c else 0

@[simp]
theorem main4WilsonFiniteMask_of_mem
    {s : Finset ℕ} {c : ℝ} {m : ℕ} (hm : m ∈ s) :
    main4WilsonFiniteMask s c m = c := by
  simp [main4WilsonFiniteMask, hm]

@[simp]
theorem main4WilsonFiniteMask_of_not_mem
    {s : Finset ℕ} {c : ℝ} {m : ℕ} (hm : m ∉ s) :
    main4WilsonFiniteMask s c m = 0 := by
  simp [main4WilsonFiniteMask, hm]

theorem abs_main4WilsonFiniteMask_le_one
    (s : Finset ℕ) (c : ℝ) (m : ℕ) (hc : |c| ≤ 1) :
    |main4WilsonFiniteMask s c m| ≤ 1 := by
  by_cases hm : m ∈ s
  · simpa [main4WilsonFiniteMask, hm] using hc
  · simp [main4WilsonFiniteMask, hm]

/-- A finite mask supported on odd radicands vanishes at every even
radicand. -/
theorem main4WilsonFiniteMask_eq_zero_of_even
    {s : Finset ℕ} {c : ℝ} {m : ℕ}
    (hs : ∀ k ∈ s, Odd k) (hm : Even m) :
    main4WilsonFiniteMask s c m = 0 := by
  apply main4WilsonFiniteMask_of_not_mem
  intro hmem
  exact (Nat.not_odd_iff_even.mpr hm) (hs m hmem)

/-- The arithmetic weight `f(m) = 1 / tau(m)` in Wilson's theorem. -/
def main4WilsonReciprocalDivisorWeight (m : ℕ) : ℝ :=
  1 / (m.divisors.card : ℝ)

theorem main4WilsonReciprocalDivisorWeight_nonneg (m : ℕ) :
    0 ≤ main4WilsonReciprocalDivisorWeight m := by
  unfold main4WilsonReciprocalDivisorWeight
  positivity

theorem abs_main4WilsonReciprocalDivisorWeight_le_one (m : ℕ) :
    |main4WilsonReciprocalDivisorWeight m| ≤ 1 := by
  by_cases hcard : m.divisors.card = 0
  · simp [main4WilsonReciprocalDivisorWeight, hcard]
  · have hnat : 1 ≤ m.divisors.card := Nat.one_le_iff_ne_zero.mpr hcard
    have hreal : (1 : ℝ) ≤ (m.divisors.card : ℝ) := by
      exact_mod_cast hnat
    rw [abs_of_nonneg (main4WilsonReciprocalDivisorWeight_nonneg m)]
    unfold main4WilsonReciprocalDivisorWeight
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hreal

/-- The bounded `b_m` coefficient for the `D = m` branch. -/
def main4WilsonOddBranchMask (X : ℝ) (m : ℕ) : ℝ :=
  main4WilsonFiniteMask (main4OddBranchRadicandsBelow X) 1 m

/-- The bounded `b_m` coefficient for the `D = 4m` branch, including its
exact genus factor `1/2`. -/
def main4WilsonFourBranchMask (X : ℝ) (m : ℕ) : ℝ :=
  main4WilsonFiniteMask (main4FourBranchRadicandsBelow X) (1 / 2) m

/-- The bounded `b_m` coefficient for the `D = 8m`, `m = 1 (mod 4)`
branch after removing `m = 1`. -/
def main4WilsonEightOneBranchMaskAwayFromEight
    (X : ℝ) (m : ℕ) : ℝ :=
  main4WilsonFiniteMask
    (main4EightOneBranchRadicandsBelowAwayFromEight X) (1 / 2) m

/-- The bounded `b_m` coefficient for the `D = 8m`, `m = 3 (mod 4)`
branch. -/
def main4WilsonEightThreeBranchMask (X : ℝ) (m : ℕ) : ℝ :=
  main4WilsonFiniteMask (main4EightThreeBranchRadicandsBelow X) (1 / 2) m

@[simp]
theorem main4WilsonOddBranchMask_ne_zero_iff {X : ℝ} {m : ℕ} :
    main4WilsonOddBranchMask X m ≠ 0 ↔
      1 < m ∧ Squarefree m ∧ m % 4 = 1 ∧ (m : ℝ) < X := by
  simp [main4WilsonOddBranchMask, main4WilsonFiniteMask]

@[simp]
theorem main4WilsonFourBranchMask_ne_zero_iff {X : ℝ} {m : ℕ} :
    main4WilsonFourBranchMask X m ≠ 0 ↔
      Odd m ∧ Squarefree m ∧ m % 4 = 3 ∧
        ((4 * m : ℕ) : ℝ) < X := by
  simp [main4WilsonFourBranchMask, main4WilsonFiniteMask]

@[simp]
theorem main4WilsonEightOneBranchMaskAwayFromEight_ne_zero_iff
    {X : ℝ} {m : ℕ} :
    main4WilsonEightOneBranchMaskAwayFromEight X m ≠ 0 ↔
      1 < m ∧ Odd m ∧ Squarefree m ∧ m % 4 = 1 ∧
        ((8 * m : ℕ) : ℝ) < X := by
  simp [main4WilsonEightOneBranchMaskAwayFromEight,
    main4WilsonFiniteMask]

@[simp]
theorem main4WilsonEightThreeBranchMask_ne_zero_iff {X : ℝ} {m : ℕ} :
    main4WilsonEightThreeBranchMask X m ≠ 0 ↔
      Odd m ∧ Squarefree m ∧ m % 4 = 3 ∧
        ((8 * m : ℕ) : ℝ) < X := by
  simp [main4WilsonEightThreeBranchMask, main4WilsonFiniteMask]

theorem abs_main4WilsonOddBranchMask_le_one (X : ℝ) (m : ℕ) :
    |main4WilsonOddBranchMask X m| ≤ 1 := by
  exact abs_main4WilsonFiniteMask_le_one _ _ _ (by norm_num)

theorem abs_main4WilsonFourBranchMask_le_one (X : ℝ) (m : ℕ) :
    |main4WilsonFourBranchMask X m| ≤ 1 := by
  exact abs_main4WilsonFiniteMask_le_one _ _ _ (by norm_num)

theorem abs_main4WilsonEightOneBranchMaskAwayFromEight_le_one
    (X : ℝ) (m : ℕ) :
    |main4WilsonEightOneBranchMaskAwayFromEight X m| ≤ 1 := by
  exact abs_main4WilsonFiniteMask_le_one _ _ _ (by norm_num)

theorem abs_main4WilsonEightThreeBranchMask_le_one (X : ℝ) (m : ℕ) :
    |main4WilsonEightThreeBranchMask X m| ≤ 1 := by
  exact abs_main4WilsonFiniteMask_le_one _ _ _ (by norm_num)

/-- The odd-branch `b_m` coefficient has Wilson's required odd support. -/
theorem main4WilsonOddBranchMask_eq_zero_of_even
    (X : ℝ) (m : ℕ) (hm : Even m) :
    main4WilsonOddBranchMask X m = 0 := by
  apply main4WilsonFiniteMask_eq_zero_of_even (m := m) _ hm
  intro k hk
  have hmod := (mem_main4OddBranchRadicandsBelow.mp hk).2.2.1
  exact (Nat.odd_iff).2 (by omega)

/-- The `4m`-branch `b_m` coefficient has Wilson's required odd support. -/
theorem main4WilsonFourBranchMask_eq_zero_of_even
    (X : ℝ) (m : ℕ) (hm : Even m) :
    main4WilsonFourBranchMask X m = 0 := by
  apply main4WilsonFiniteMask_eq_zero_of_even (m := m) _ hm
  intro k hk
  exact (mem_main4FourBranchRadicandsBelow.mp hk).1

/-- The nonexceptional congruence-one `8m`-branch `b_m` coefficient has
Wilson's required odd support. -/
theorem main4WilsonEightOneBranchMaskAwayFromEight_eq_zero_of_even
    (X : ℝ) (m : ℕ) (hm : Even m) :
    main4WilsonEightOneBranchMaskAwayFromEight X m = 0 := by
  apply main4WilsonFiniteMask_eq_zero_of_even (m := m) _ hm
  intro k hk
  exact (mem_main4EightOneBranchRadicandsBelowAwayFromEight.mp hk).2.1

/-- The congruence-three `8m`-branch `b_m` coefficient has Wilson's
required odd support. -/
theorem main4WilsonEightThreeBranchMask_eq_zero_of_even
    (X : ℝ) (m : ℕ) (hm : Even m) :
    main4WilsonEightThreeBranchMask X m = 0 := by
  apply main4WilsonFiniteMask_eq_zero_of_even (m := m) _ hm
  intro k hk
  exact (mem_main4EightThreeBranchRadicandsBelow.mp hk).1

/-- The full `m`-coefficient in the odd branch.  Its displayed
factorization is the one used by Wilson: bounded mask times `1 / tau(m)`. -/
def main4WilsonOddBranchCoefficient (X : ℝ) (m : ℕ) : ℝ :=
  main4WilsonOddBranchMask X m * main4WilsonReciprocalDivisorWeight m

/-- The full `m`-coefficient in the `4m` branch. -/
def main4WilsonFourBranchCoefficient (X : ℝ) (m : ℕ) : ℝ :=
  main4WilsonFourBranchMask X m * main4WilsonReciprocalDivisorWeight m

/-- The full `m`-coefficient in the nonexceptional congruence-one `8m`
branch. -/
def main4WilsonEightOneBranchCoefficientAwayFromEight
    (X : ℝ) (m : ℕ) : ℝ :=
  main4WilsonEightOneBranchMaskAwayFromEight X m *
    main4WilsonReciprocalDivisorWeight m

/-- The full `m`-coefficient in the congruence-three `8m` branch. -/
def main4WilsonEightThreeBranchCoefficient (X : ℝ) (m : ℕ) : ℝ :=
  main4WilsonEightThreeBranchMask X m *
    main4WilsonReciprocalDivisorWeight m

/-- The full odd-branch coefficient is supported on odd radicands, as
required when the reciprocal-divisor factor is absorbed into the bounded
coefficient in the Friedlander--Iwaniec estimate. -/
theorem main4WilsonOddBranchCoefficient_eq_zero_of_even
    (X : ℝ) (m : ℕ) (hm : Even m) :
    main4WilsonOddBranchCoefficient X m = 0 := by
  rw [main4WilsonOddBranchCoefficient,
    main4WilsonOddBranchMask_eq_zero_of_even X m hm, zero_mul]

theorem main4WilsonFourBranchCoefficient_eq_zero_of_even
    (X : ℝ) (m : ℕ) (hm : Even m) :
    main4WilsonFourBranchCoefficient X m = 0 := by
  rw [main4WilsonFourBranchCoefficient,
    main4WilsonFourBranchMask_eq_zero_of_even X m hm, zero_mul]

theorem main4WilsonEightOneBranchCoefficientAwayFromEight_eq_zero_of_even
    (X : ℝ) (m : ℕ) (hm : Even m) :
    main4WilsonEightOneBranchCoefficientAwayFromEight X m = 0 := by
  rw [main4WilsonEightOneBranchCoefficientAwayFromEight,
    main4WilsonEightOneBranchMaskAwayFromEight_eq_zero_of_even X m hm,
    zero_mul]

theorem main4WilsonEightThreeBranchCoefficient_eq_zero_of_even
    (X : ℝ) (m : ℕ) (hm : Even m) :
    main4WilsonEightThreeBranchCoefficient X m = 0 := by
  rw [main4WilsonEightThreeBranchCoefficient,
    main4WilsonEightThreeBranchMask_eq_zero_of_even X m hm, zero_mul]

theorem abs_main4WilsonOddBranchCoefficient_le_one (X : ℝ) (m : ℕ) :
    |main4WilsonOddBranchCoefficient X m| ≤ 1 := by
  rw [main4WilsonOddBranchCoefficient, abs_mul]
  calc
    |main4WilsonOddBranchMask X m| *
          |main4WilsonReciprocalDivisorWeight m| ≤ 1 * 1 :=
      mul_le_mul (abs_main4WilsonOddBranchMask_le_one X m)
        (abs_main4WilsonReciprocalDivisorWeight_le_one m)
        (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem abs_main4WilsonFourBranchCoefficient_le_one (X : ℝ) (m : ℕ) :
    |main4WilsonFourBranchCoefficient X m| ≤ 1 := by
  rw [main4WilsonFourBranchCoefficient, abs_mul]
  calc
    |main4WilsonFourBranchMask X m| *
          |main4WilsonReciprocalDivisorWeight m| ≤ 1 * 1 :=
      mul_le_mul (abs_main4WilsonFourBranchMask_le_one X m)
        (abs_main4WilsonReciprocalDivisorWeight_le_one m)
        (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem abs_main4WilsonEightOneBranchCoefficientAwayFromEight_le_one
    (X : ℝ) (m : ℕ) :
    |main4WilsonEightOneBranchCoefficientAwayFromEight X m| ≤ 1 := by
  rw [main4WilsonEightOneBranchCoefficientAwayFromEight, abs_mul]
  calc
    |main4WilsonEightOneBranchMaskAwayFromEight X m| *
          |main4WilsonReciprocalDivisorWeight m| ≤ 1 * 1 :=
      mul_le_mul
        (abs_main4WilsonEightOneBranchMaskAwayFromEight_le_one X m)
        (abs_main4WilsonReciprocalDivisorWeight_le_one m)
        (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem abs_main4WilsonEightThreeBranchCoefficient_le_one
    (X : ℝ) (m : ℕ) :
    |main4WilsonEightThreeBranchCoefficient X m| ≤ 1 := by
  rw [main4WilsonEightThreeBranchCoefficient, abs_mul]
  calc
    |main4WilsonEightThreeBranchMask X m| *
          |main4WilsonReciprocalDivisorWeight m| ≤ 1 * 1 :=
      mul_le_mul (abs_main4WilsonEightThreeBranchMask_le_one X m)
        (abs_main4WilsonReciprocalDivisorWeight_le_one m)
        (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-! ## Exact branch-to-rectangle identities -/

theorem main4OddBranchRadicandsBelow_subset_rectangle (X : ℝ) :
    main4OddBranchRadicandsBelow X ⊆ Finset.Icc 1 ⌈X⌉₊ := by
  intro m hm
  rcases Finset.mem_filter.mp hm with ⟨hmRange, hmgt, _⟩
  exact Finset.mem_Icc.mpr
    ⟨by omega, Nat.le_of_lt (Finset.mem_range.mp hmRange)⟩

theorem main4FourBranchRadicandsBelow_subset_rectangle (X : ℝ) :
    main4FourBranchRadicandsBelow X ⊆ Finset.Icc 1 ⌈X / 4⌉₊ := by
  intro m hm
  rcases Finset.mem_filter.mp hm with ⟨hmRange, hmOdd, _⟩
  rcases hmOdd with ⟨k, hk⟩
  exact Finset.mem_Icc.mpr
    ⟨by omega, Nat.le_of_lt (Finset.mem_range.mp hmRange)⟩

theorem main4EightOneBranchRadicandsBelowAwayFromEight_subset_rectangle
    (X : ℝ) :
    main4EightOneBranchRadicandsBelowAwayFromEight X ⊆
      Finset.Icc 1 ⌈X / 8⌉₊ := by
  intro m hm
  rcases Finset.mem_filter.mp hm with ⟨hmOneBranch, hmgt⟩
  rcases Finset.mem_filter.mp hmOneBranch with ⟨hmEightBranch, _⟩
  rcases Finset.mem_filter.mp hmEightBranch with ⟨hmRange, _⟩
  exact Finset.mem_Icc.mpr
    ⟨by omega, Nat.le_of_lt (Finset.mem_range.mp hmRange)⟩

theorem main4EightThreeBranchRadicandsBelow_subset_rectangle (X : ℝ) :
    main4EightThreeBranchRadicandsBelow X ⊆
      Finset.Icc 1 ⌈X / 8⌉₊ := by
  intro m hm
  rcases Finset.mem_filter.mp hm with ⟨hmEightBranch, _⟩
  rcases Finset.mem_filter.mp hmEightBranch with ⟨hmRange, hmOdd, _⟩
  rcases hmOdd with ⟨k, hk⟩
  exact Finset.mem_Icc.mpr
    ⟨by omega, Nat.le_of_lt (Finset.mem_range.mp hmRange)⟩

/-- Zero-extension by a finite mask turns a family prefix into an ordinary
rectangle, provided the family lies inside the chosen outer interval. -/
theorem main4WilsonWeightedTwistPrefix_eq_ordinaryRectangle_finiteMask
    (rho : DirichletCharacter ℤ 8) (f : ℕ → ℝ) (s : Finset ℕ)
    (c : ℝ) (M N : ℕ) (hs : s ⊆ Finset.Icc 1 M) :
    main4WilsonWeightedTwistPrefix rho (fun m ↦ c * f m) s N =
      main4OrdinaryJacobiRectangle (main4WilsonTwistSequence rho)
        (fun m ↦ main4WilsonFiniteMask s c m * f m) M N := by
  unfold main4OrdinaryJacobiRectangle
  symm
  calc
    (∑ m ∈ Finset.Icc 1 M,
        (main4WilsonFiniteMask s c m * f m) *
          ∑ n ∈ Finset.Icc 1 N,
            main4WilsonTwistSequence rho n * (J((n : ℤ) | m) : ℝ)) =
        ∑ m ∈ s,
          (main4WilsonFiniteMask s c m * f m) *
            ∑ n ∈ Finset.Icc 1 N,
              main4WilsonTwistSequence rho n *
                (J((n : ℤ) | m) : ℝ) := by
      symm
      apply Finset.sum_subset hs
      intro m _ hm
      simp [main4WilsonFiniteMask, hm]
    _ = main4WilsonWeightedTwistPrefix rho (fun m ↦ c * f m) s N := by
      unfold main4WilsonWeightedTwistPrefix
      apply Finset.sum_congr rfl
      intro m hm
      rw [main4WilsonFiniteMask_of_mem hm]
      rfl

/-- The odd discriminant branch is exactly one ordinary Jacobi rectangle. -/
theorem main4WilsonOddBranchPrefix_eq_ordinaryRectangle (X : ℝ) (N : ℕ) :
    main4WilsonWeightedTwistPrefix 1
        (fun m ↦ 1 / (m.divisors.card : ℝ))
        (main4OddBranchRadicandsBelow X) N =
      main4OrdinaryJacobiRectangle (main4WilsonTwistSequence 1)
        (main4WilsonOddBranchCoefficient X) ⌈X⌉₊ N := by
  unfold main4WilsonOddBranchCoefficient main4WilsonOddBranchMask
  change
    main4WilsonWeightedTwistPrefix 1 main4WilsonReciprocalDivisorWeight
        (main4OddBranchRadicandsBelow X) N = _
  simpa only [one_mul] using
    main4WilsonWeightedTwistPrefix_eq_ordinaryRectangle_finiteMask
      (1 : DirichletCharacter ℤ 8) main4WilsonReciprocalDivisorWeight
      (main4OddBranchRadicandsBelow X) 1 ⌈X⌉₊ N
      (main4OddBranchRadicandsBelow_subset_rectangle X)

/-- The `4m` discriminant branch is exactly one ordinary Jacobi rectangle. -/
theorem main4WilsonFourBranchPrefix_eq_ordinaryRectangle (X : ℝ) (N : ℕ) :
    main4WilsonWeightedTwistPrefix main4ChiFourModuloEight
        (fun m ↦ 1 / (2 * (m.divisors.card : ℝ)))
        (main4FourBranchRadicandsBelow X) N =
      main4OrdinaryJacobiRectangle
        (main4WilsonTwistSequence main4ChiFourModuloEight)
        (main4WilsonFourBranchCoefficient X) ⌈X / 4⌉₊ N := by
  unfold main4WilsonFourBranchCoefficient main4WilsonFourBranchMask
  rw [show (fun m : ℕ ↦ 1 / (2 * (m.divisors.card : ℝ))) =
      (fun m ↦ (1 / 2 : ℝ) * main4WilsonReciprocalDivisorWeight m) by
    funext m
    simp only [main4WilsonReciprocalDivisorWeight, one_div_mul_one_div]]
  exact main4WilsonWeightedTwistPrefix_eq_ordinaryRectangle_finiteMask
    main4ChiFourModuloEight main4WilsonReciprocalDivisorWeight
    (main4FourBranchRadicandsBelow X) (1 / 2) ⌈X / 4⌉₊ N
    (main4FourBranchRadicandsBelow_subset_rectangle X)

/-- The nonexceptional congruence-one `8m` branch is exactly one ordinary
Jacobi rectangle. -/
theorem main4WilsonEightOneBranchPrefixAwayFromEight_eq_ordinaryRectangle
    (X : ℝ) (N : ℕ) :
    main4WilsonWeightedTwistPrefix ZMod.χ₈
        (fun m ↦ 1 / (2 * (m.divisors.card : ℝ)))
        (main4EightOneBranchRadicandsBelowAwayFromEight X) N =
      main4OrdinaryJacobiRectangle (main4WilsonTwistSequence ZMod.χ₈)
        (main4WilsonEightOneBranchCoefficientAwayFromEight X)
        ⌈X / 8⌉₊ N := by
  unfold main4WilsonEightOneBranchCoefficientAwayFromEight
    main4WilsonEightOneBranchMaskAwayFromEight
  rw [show (fun m : ℕ ↦ 1 / (2 * (m.divisors.card : ℝ))) =
      (fun m ↦ (1 / 2 : ℝ) * main4WilsonReciprocalDivisorWeight m) by
    funext m
    simp only [main4WilsonReciprocalDivisorWeight, one_div_mul_one_div]]
  exact main4WilsonWeightedTwistPrefix_eq_ordinaryRectangle_finiteMask
    ZMod.χ₈ main4WilsonReciprocalDivisorWeight
    (main4EightOneBranchRadicandsBelowAwayFromEight X)
    (1 / 2) ⌈X / 8⌉₊ N
    (main4EightOneBranchRadicandsBelowAwayFromEight_subset_rectangle X)

/-- The congruence-three `8m` branch is exactly one ordinary Jacobi
rectangle. -/
theorem main4WilsonEightThreeBranchPrefix_eq_ordinaryRectangle
    (X : ℝ) (N : ℕ) :
    main4WilsonWeightedTwistPrefix ZMod.χ₈'
        (fun m ↦ 1 / (2 * (m.divisors.card : ℝ)))
        (main4EightThreeBranchRadicandsBelow X) N =
      main4OrdinaryJacobiRectangle (main4WilsonTwistSequence ZMod.χ₈')
        (main4WilsonEightThreeBranchCoefficient X) ⌈X / 8⌉₊ N := by
  unfold main4WilsonEightThreeBranchCoefficient
    main4WilsonEightThreeBranchMask
  rw [show (fun m : ℕ ↦ 1 / (2 * (m.divisors.card : ℝ))) =
      (fun m ↦ (1 / 2 : ℝ) * main4WilsonReciprocalDivisorWeight m) by
    funext m
    simp only [main4WilsonReciprocalDivisorWeight, one_div_mul_one_div]]
  exact main4WilsonWeightedTwistPrefix_eq_ordinaryRectangle_finiteMask
    ZMod.χ₈' main4WilsonReciprocalDivisorWeight
    (main4EightThreeBranchRadicandsBelow X)
    (1 / 2) ⌈X / 8⌉₊ N
    (main4EightThreeBranchRadicandsBelow_subset_rectangle X)

/-- The complete four-twist ordinary prefix is the sum of the four exact
Jacobi rectangles, with the three natural outer cutoffs retained. -/
theorem main4WilsonFourTwistPrefixSumAwayFromEight_eq_rectangles
    (X : ℝ) (N : ℕ) :
    main4WilsonFourTwistPrefixSumAwayFromEight X N =
      main4OrdinaryJacobiRectangle (main4WilsonTwistSequence 1)
          (main4WilsonOddBranchCoefficient X) ⌈X⌉₊ N +
        main4OrdinaryJacobiRectangle
          (main4WilsonTwistSequence main4ChiFourModuloEight)
          (main4WilsonFourBranchCoefficient X) ⌈X / 4⌉₊ N +
        main4OrdinaryJacobiRectangle (main4WilsonTwistSequence ZMod.χ₈)
          (main4WilsonEightOneBranchCoefficientAwayFromEight X)
          ⌈X / 8⌉₊ N +
        main4OrdinaryJacobiRectangle (main4WilsonTwistSequence ZMod.χ₈')
          (main4WilsonEightThreeBranchCoefficient X) ⌈X / 8⌉₊ N := by
  unfold main4WilsonFourTwistPrefixSumAwayFromEight
  rw [main4WilsonOddBranchPrefix_eq_ordinaryRectangle,
    main4WilsonFourBranchPrefix_eq_ordinaryRectangle,
    main4WilsonEightOneBranchPrefixAwayFromEight_eq_ordinaryRectangle,
    main4WilsonEightThreeBranchPrefix_eq_ordinaryRectangle]

end

end PellPaper
