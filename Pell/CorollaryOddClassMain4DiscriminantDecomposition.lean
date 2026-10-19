import Pell.CorollaryOddPartGenusAlgebra
import Mathlib.Tactic

/-!
# Fundamental-discriminant decomposition for the manuscript moment

The weighted-moment argument in the proof of Corollary 1.2 writes every
positive fundamental discriminant uniquely in one of the forms

* `D = m`, with `m > 1`, squarefree, and `m = 1 (mod 4)`;
* `D = 4m`, with `m` squarefree and `m = 3 (mod 4)`;
* `D = 8m`, with `m` odd and squarefree.

This module proves that decomposition for the project's literal predicate
`PositiveFundamentalDiscriminant`, realizes it as a disjoint decomposition
of the finite strict-cutoff set, and rewrites arbitrary finite sums through
the three radicand families.  It also proves the exact identities between
the genus weight `2^(-omega D)` and the divisor weight `1 / tau(m)` used in
the manuscript.

No character identity or analytic moment estimate is assumed here.
-/

namespace PellPaper

open scoped ArithmeticFunction.omega BigOperators

noncomputable section

/-- A squarefree number has exactly `2 ^ omega(m)` positive divisors. -/
theorem card_divisors_eq_two_pow_cardDistinctFactors {m : ℕ}
    (hm : Squarefree m) :
    m.divisors.card = 2 ^ (ω m) := by
  rw [Nat.card_divisors hm.ne_zero]
  calc
    (∏ p ∈ m.primeFactors, (m.factorization p + 1)) =
        ∏ _p ∈ m.primeFactors, 2 := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.factorization_eq_one_of_squarefree hm
        (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp)]
    _ = 2 ^ m.primeFactors.card := by simp
    _ = 2 ^ (ω m) := by congr 1

/-- The elementary `d = 2m` extraction in the `d = 2 (mod 4)` branch.
Squarefreeness descends from `d` to its odd factor `m`. -/
theorem exists_odd_squarefree_half_of_squarefree_mod_four_eq_two
    {d : ℕ} (hsf : Squarefree d) (hmod : d % 4 = 2) :
    ∃ m : ℕ, Odd m ∧ Squarefree m ∧ d = 2 * m := by
  let m := 2 * (d / 4) + 1
  have hd : d = 4 * (d / 4) + 2 := by omega
  refine ⟨m, ?_, ?_, ?_⟩
  · exact ⟨d / 4, by simp [m]⟩
  · apply hsf.squarefree_of_dvd
    exact ⟨2, by omega⟩
  · omega

/-- Multiplication by two preserves squarefreeness precisely because the
other factor is odd. -/
theorem squarefree_two_mul_of_odd_squarefree {m : ℕ}
    (hodd : Odd m) (hsf : Squarefree m) :
    Squarefree (2 * m) := by
  exact (Nat.squarefree_mul ((Nat.coprime_two_left).2 hodd)).2
    ⟨Nat.squarefree_two, hsf⟩

/-- Adding the prime `2` increases `omega` by exactly one. -/
theorem cardDistinctFactors_two_mul_of_odd {m : ℕ} (hodd : Odd m) :
    ω (2 * m) = ω m + 1 := by
  rw [ArithmeticFunction.cardDistinctFactors_mul
    ((Nat.coprime_two_left).2 hodd)]
  rw [ArithmeticFunction.cardDistinctFactors_apply_prime Nat.prime_two]
  omega

/-- Multiplying an odd number by `4` adds only the one distinct prime `2`. -/
theorem cardDistinctFactors_four_mul_of_odd {m : ℕ} (hodd : Odd m) :
    ω (4 * m) = ω m + 1 := by
  rw [show 4 * m = 2 ^ 2 * m by ring]
  rw [ArithmeticFunction.cardDistinctFactors_mul]
  · rw [ArithmeticFunction.cardDistinctFactors_apply_prime_pow
      Nat.prime_two (by norm_num)]
    omega
  · exact Nat.Coprime.pow_left 2 ((Nat.coprime_two_left).2 hodd)

/-- Multiplying an odd number by `8` likewise adds only the prime `2`. -/
theorem cardDistinctFactors_eight_mul_of_odd {m : ℕ} (hodd : Odd m) :
    ω (8 * m) = ω m + 1 := by
  rw [show 8 * m = 2 ^ 3 * m by ring]
  rw [ArithmeticFunction.cardDistinctFactors_mul]
  · rw [ArithmeticFunction.cardDistinctFactors_apply_prime_pow
      Nat.prime_two (by norm_num)]
    omega
  · exact Nat.Coprime.pow_left 3 ((Nat.coprime_two_left).2 hodd)

/-- Exact three-branch characterization behind the sentence "Every
positive fundamental discriminant is `m`, `4m`, or `8m`" in the manuscript.
The congruence conditions make the three alternatives mutually exclusive. -/
theorem positiveFundamentalDiscriminant_iff_main4_decomposition {D : ℕ} :
    PositiveFundamentalDiscriminant D ↔
      (1 < D ∧ Squarefree D ∧ D % 4 = 1) ∨
      (∃ m : ℕ, Odd m ∧ Squarefree m ∧ m % 4 = 3 ∧ D = 4 * m) ∨
      (∃ m : ℕ, Odd m ∧ Squarefree m ∧ D = 8 * m) := by
  constructor
  · rintro ⟨hD, (⟨hsf, hmod⟩ | ⟨d, rfl, hsf, hmod | hmod⟩)⟩
    · exact Or.inl ⟨hD, hsf, hmod⟩
    · right
      right
      obtain ⟨m, hmOdd, hmSf, hdm⟩ :=
        exists_odd_squarefree_half_of_squarefree_mod_four_eq_two hsf hmod
      refine ⟨m, hmOdd, hmSf, ?_⟩
      omega
    · right
      left
      refine ⟨d, (Nat.odd_iff).2 (by omega), hsf, hmod, rfl⟩
  · rintro (⟨hD, hsf, hmod⟩ | ⟨m, hmOdd, hmSf, hmod, rfl⟩ |
      ⟨m, hmOdd, hmSf, rfl⟩)
    · exact ⟨hD, Or.inl ⟨hsf, hmod⟩⟩
    · exact ⟨by omega, Or.inr ⟨m, rfl, hmSf, Or.inr hmod⟩⟩
    · refine ⟨by rcases hmOdd with ⟨k, rfl⟩; omega,
        Or.inr ⟨2 * m, by ring, squarefree_two_mul_of_odd_squarefree hmOdd hmSf,
          Or.inl ?_⟩⟩
      rcases hmOdd with ⟨k, rfl⟩
      omega

/-- Radicands in the odd (`D = m`) branch below the strict real cutoff. -/
def main4OddBranchRadicandsBelow (X : ℝ) : Finset ℕ :=
  (Finset.range ⌈X⌉₊).filter fun m ↦
    1 < m ∧ Squarefree m ∧ m % 4 = 1

/-- Radicands in the `D = 4m` branch below the strict real cutoff. -/
def main4FourBranchRadicandsBelow (X : ℝ) : Finset ℕ :=
  (Finset.range ⌈X / 4⌉₊).filter fun m ↦
    Odd m ∧ Squarefree m ∧ m % 4 = 3

/-- Radicands in the `D = 8m` branch below the strict real cutoff.  This
family includes `m = 1`, corresponding to the exceptional small case
`D = 8` mentioned explicitly in the manuscript. -/
def main4EightBranchRadicandsBelow (X : ℝ) : Finset ℕ :=
  (Finset.range ⌈X / 8⌉₊).filter fun m ↦
    Odd m ∧ Squarefree m

/-- The common nontrivial odd-squarefree family to which the congruence
conditions are dropped before Wilson's estimate is applied. -/
def main4NontrivialOddSquarefreeRadicandsBelow (Y : ℝ) : Finset ℕ :=
  (Finset.range ⌈Y⌉₊).filter fun m ↦
    1 < m ∧ Odd m ∧ Squarefree m

@[simp]
theorem mem_main4OddBranchRadicandsBelow {m : ℕ} {X : ℝ} :
    m ∈ main4OddBranchRadicandsBelow X ↔
      1 < m ∧ Squarefree m ∧ m % 4 = 1 ∧ (m : ℝ) < X := by
  simp [main4OddBranchRadicandsBelow, Nat.lt_ceil, and_left_comm,
    and_comm]

@[simp]
theorem mem_main4FourBranchRadicandsBelow {m : ℕ} {X : ℝ} :
    m ∈ main4FourBranchRadicandsBelow X ↔
      Odd m ∧ Squarefree m ∧ m % 4 = 3 ∧ ((4 * m : ℕ) : ℝ) < X := by
  simp only [main4FourBranchRadicandsBelow, Finset.mem_filter,
    Finset.mem_range, Nat.lt_ceil, Nat.cast_mul, Nat.cast_ofNat]
  constructor
  · rintro ⟨hmX, hodd, hsf, hmod⟩
    exact ⟨hodd, hsf, hmod, by linarith⟩
  · rintro ⟨hodd, hsf, hmod, hmX⟩
    exact ⟨by linarith, hodd, hsf, hmod⟩

@[simp]
theorem mem_main4EightBranchRadicandsBelow {m : ℕ} {X : ℝ} :
    m ∈ main4EightBranchRadicandsBelow X ↔
      Odd m ∧ Squarefree m ∧ ((8 * m : ℕ) : ℝ) < X := by
  simp only [main4EightBranchRadicandsBelow, Finset.mem_filter,
    Finset.mem_range, Nat.lt_ceil, Nat.cast_mul, Nat.cast_ofNat]
  constructor
  · rintro ⟨hmX, hodd, hsf⟩
    exact ⟨hodd, hsf, by linarith⟩
  · rintro ⟨hodd, hsf, hmX⟩
    exact ⟨by linarith, hodd, hsf⟩

@[simp]
theorem mem_main4NontrivialOddSquarefreeRadicandsBelow
    {m : ℕ} {Y : ℝ} :
    m ∈ main4NontrivialOddSquarefreeRadicandsBelow Y ↔
      1 < m ∧ Odd m ∧ Squarefree m ∧ (m : ℝ) < Y := by
  simp [main4NontrivialOddSquarefreeRadicandsBelow, Nat.lt_ceil,
    and_assoc, and_left_comm, and_comm]

/-- The odd branch is the congruence-one filter of the common Wilson
radicand family. -/
theorem main4OddBranchRadicandsBelow_eq_nontrivial_filter_mod_four_one
    (X : ℝ) :
    main4OddBranchRadicandsBelow X =
      (main4NontrivialOddSquarefreeRadicandsBelow X).filter
        fun m ↦ m % 4 = 1 := by
  ext m
  simp only [mem_main4OddBranchRadicandsBelow, Finset.mem_filter,
    mem_main4NontrivialOddSquarefreeRadicandsBelow]
  constructor
  · rintro ⟨hm, hsf, hmod, hmX⟩
    exact ⟨⟨hm, (Nat.odd_iff).2 (by omega), hsf, hmX⟩, hmod⟩
  · rintro ⟨⟨hm, _, hsf, hmX⟩, hmod⟩
    exact ⟨hm, hsf, hmod, hmX⟩

/-- The `4m` radicands are the congruence-three filter of the common
Wilson family at the naturally rescaled cutoff `X / 4`. -/
theorem main4FourBranchRadicandsBelow_eq_nontrivial_filter_mod_four_three
    (X : ℝ) :
    main4FourBranchRadicandsBelow X =
      (main4NontrivialOddSquarefreeRadicandsBelow (X / 4)).filter
        fun m ↦ m % 4 = 3 := by
  ext m
  simp only [mem_main4FourBranchRadicandsBelow, Finset.mem_filter,
    mem_main4NontrivialOddSquarefreeRadicandsBelow]
  constructor
  · rintro ⟨hodd, hsf, hmod, hmX⟩
    refine ⟨⟨?_, hodd, hsf, by norm_num at hmX ⊢; linarith⟩, hmod⟩
    omega
  · rintro ⟨⟨_, hodd, hsf, hmX⟩, hmod⟩
    exact ⟨hodd, hsf, hmod, by norm_num at hmX ⊢; linarith⟩

/-- Removing the sole possible radicand `m = 1` from the `8m` branch gives
exactly the common Wilson family at cutoff `X / 8`. -/
theorem main4EightBranchRadicandsBelow_filter_one_lt_eq_nontrivial
    (X : ℝ) :
    (main4EightBranchRadicandsBelow X).filter (1 < ·) =
      main4NontrivialOddSquarefreeRadicandsBelow (X / 8) := by
  ext m
  simp only [Finset.mem_filter, mem_main4EightBranchRadicandsBelow,
    mem_main4NontrivialOddSquarefreeRadicandsBelow]
  constructor
  · rintro ⟨⟨hodd, hsf, hmX⟩, hm⟩
    exact ⟨hm, hodd, hsf, by norm_num at hmX ⊢; linarith⟩
  · rintro ⟨hm, hodd, hsf, hmX⟩
    exact ⟨⟨hodd, hsf, by norm_num at hmX ⊢; linarith⟩, hm⟩

/-- The source's exceptional radicand `m = 1` occurs precisely when the
strict discriminant cutoff contains `D = 8`. -/
@[simp]
theorem one_mem_main4EightBranchRadicandsBelow_iff {X : ℝ} :
    1 ∈ main4EightBranchRadicandsBelow X ↔ (8 : ℝ) < X := by
  rw [mem_main4EightBranchRadicandsBelow]
  norm_num

/-- Exact isolation of the `D = 8` case: apart from the conditional
singleton `m = 1`, the `8m` branch is the common nontrivial odd-squarefree
family at cutoff `X / 8`. -/
theorem main4EightBranchRadicandsBelow_eq_singleton_union_nontrivial
    (X : ℝ) :
    main4EightBranchRadicandsBelow X =
      (if (8 : ℝ) < X then {1} else ∅) ∪
        main4NontrivialOddSquarefreeRadicandsBelow (X / 8) := by
  by_cases hX : (8 : ℝ) < X
  · ext m
    simp only [hX, ↓reduceIte, Finset.mem_union, Finset.mem_singleton,
      mem_main4EightBranchRadicandsBelow,
      mem_main4NontrivialOddSquarefreeRadicandsBelow]
    constructor
    · rintro ⟨hodd, hsf, hmX⟩
      by_cases hm : m = 1
      · exact Or.inl hm
      · right
        refine ⟨?_, hodd, hsf, by norm_num at hmX ⊢; linarith⟩
        rcases hodd with ⟨k, hk⟩
        omega
    · rintro (rfl | ⟨hm, hodd, hsf, hmX⟩)
      · exact ⟨by norm_num, by norm_num, by simpa using hX⟩
      · exact ⟨hodd, hsf, by norm_num at hmX ⊢; linarith⟩
  · ext m
    simp only [hX, ↓reduceIte, Finset.empty_union,
      mem_main4EightBranchRadicandsBelow,
      mem_main4NontrivialOddSquarefreeRadicandsBelow]
    constructor
    · rintro ⟨hodd, hsf, hmX⟩
      refine ⟨?_, hodd, hsf, by norm_num at hmX ⊢; linarith⟩
      have hmne : m ≠ 1 := by
        intro hm
        subst m
        exact hX (by norm_num at hmX ⊢; exact hmX)
      rcases hodd with ⟨k, hk⟩
      omega
    · rintro ⟨_, hodd, hsf, hmX⟩
      exact ⟨hodd, hsf, by norm_num at hmX ⊢; linarith⟩

/-- Corresponding exact sum split for the `D = 8` exception. -/
theorem sum_main4EightBranchRadicandsBelow_eq_exception_add_nontrivial
    {A : Type*} [AddCommMonoid A] (F : ℕ → A) (X : ℝ) :
    (∑ m ∈ main4EightBranchRadicandsBelow X, F m) =
      (if (8 : ℝ) < X then F 1 else 0) +
        ∑ m ∈ main4NontrivialOddSquarefreeRadicandsBelow (X / 8), F m := by
  rw [main4EightBranchRadicandsBelow_eq_singleton_union_nontrivial]
  by_cases hX : (8 : ℝ) < X
  · rw [if_pos hX, if_pos hX]
    have hdis : Disjoint ({1} : Finset ℕ)
        (main4NontrivialOddSquarefreeRadicandsBelow (X / 8)) := by
      rw [Finset.disjoint_left]
      intro m hmOne hmNontrivial
      simp only [Finset.mem_singleton] at hmOne
      subst m
      exact (Nat.lt_irrefl 1)
        (mem_main4NontrivialOddSquarefreeRadicandsBelow.mp hmNontrivial).1
    rw [Finset.sum_union hdis]
    simp
  · simp [hX]

/-- The `D = 4m` discriminants at cutoff `X`. -/
def main4FourBranchDiscriminantsBelow (X : ℝ) : Finset ℕ :=
  (main4FourBranchRadicandsBelow X).image fun m ↦ 4 * m

/-- The `D = 8m` discriminants at cutoff `X`. -/
def main4EightBranchDiscriminantsBelow (X : ℝ) : Finset ℕ :=
  (main4EightBranchRadicandsBelow X).image fun m ↦ 8 * m

@[simp]
theorem mem_main4FourBranchDiscriminantsBelow {D : ℕ} {X : ℝ} :
    D ∈ main4FourBranchDiscriminantsBelow X ↔
      ∃ m : ℕ, Odd m ∧ Squarefree m ∧ m % 4 = 3 ∧
        D = 4 * m ∧ (D : ℝ) < X := by
  constructor
  · intro hD
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨hodd, hsf, hmod, hmX⟩ :=
      mem_main4FourBranchRadicandsBelow.mp hm
    exact ⟨m, hodd, hsf, hmod, rfl, hmX⟩
  · rintro ⟨m, hodd, hsf, hmod, rfl, hmX⟩
    apply Finset.mem_image.mpr
    exact ⟨m,
      mem_main4FourBranchRadicandsBelow.mpr ⟨hodd, hsf, hmod, hmX⟩,
      rfl⟩

@[simp]
theorem mem_main4EightBranchDiscriminantsBelow {D : ℕ} {X : ℝ} :
    D ∈ main4EightBranchDiscriminantsBelow X ↔
      ∃ m : ℕ, Odd m ∧ Squarefree m ∧
        D = 8 * m ∧ (D : ℝ) < X := by
  constructor
  · intro hD
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨hodd, hsf, hmX⟩ :=
      mem_main4EightBranchRadicandsBelow.mp hm
    exact ⟨m, hodd, hsf, rfl, hmX⟩
  · rintro ⟨m, hodd, hsf, rfl, hmX⟩
    apply Finset.mem_image.mpr
    exact ⟨m,
      mem_main4EightBranchRadicandsBelow.mpr ⟨hodd, hsf, hmX⟩,
      rfl⟩

/-- Exact finite-set version of the three discriminant branches, retaining
the source's strict real cutoff `D < X`. -/
theorem fundamentalDiscriminantsBelow_eq_main4_branch_union (X : ℝ) :
    fundamentalDiscriminantsBelow X =
      (main4OddBranchRadicandsBelow X ∪
        main4FourBranchDiscriminantsBelow X) ∪
          main4EightBranchDiscriminantsBelow X := by
  ext D
  rw [mem_fundamentalDiscriminantsBelow,
    positiveFundamentalDiscriminant_iff_main4_decomposition]
  simp only [Finset.mem_union, mem_main4OddBranchRadicandsBelow,
    mem_main4FourBranchDiscriminantsBelow,
    mem_main4EightBranchDiscriminantsBelow]
  aesop

/-- The odd branch is disjoint from the `4m` branch. -/
theorem main4OddBranch_disjoint_fourBranch (X : ℝ) :
    Disjoint (main4OddBranchRadicandsBelow X)
      (main4FourBranchDiscriminantsBelow X) := by
  rw [Finset.disjoint_left]
  intro D hodd hfour
  obtain ⟨_, _, hmod, _⟩ := mem_main4OddBranchRadicandsBelow.mp hodd
  obtain ⟨m, _, _, _, hDm, _⟩ :=
    mem_main4FourBranchDiscriminantsBelow.mp hfour
  omega

/-- The odd branch is disjoint from the `8m` branch. -/
theorem main4OddBranch_disjoint_eightBranch (X : ℝ) :
    Disjoint (main4OddBranchRadicandsBelow X)
      (main4EightBranchDiscriminantsBelow X) := by
  rw [Finset.disjoint_left]
  intro D hodd height
  obtain ⟨_, _, hmod, _⟩ := mem_main4OddBranchRadicandsBelow.mp hodd
  obtain ⟨m, _, _, hDm, _⟩ :=
    mem_main4EightBranchDiscriminantsBelow.mp height
  omega

/-- The `4m` and `8m` branches are disjoint because both radicands are odd. -/
theorem main4FourBranch_disjoint_eightBranch (X : ℝ) :
    Disjoint (main4FourBranchDiscriminantsBelow X)
      (main4EightBranchDiscriminantsBelow X) := by
  rw [Finset.disjoint_left]
  intro D hfour height
  obtain ⟨m, hmOdd, _, _, hDm, _⟩ :=
    mem_main4FourBranchDiscriminantsBelow.mp hfour
  obtain ⟨n, _, _, hDn, _⟩ :=
    mem_main4EightBranchDiscriminantsBelow.mp height
  rcases hmOdd with ⟨k, hmk⟩
  omega

/-- The union of the first two branches remains disjoint from the third. -/
theorem main4OddUnionFourBranch_disjoint_eightBranch (X : ℝ) :
    Disjoint
      (main4OddBranchRadicandsBelow X ∪
        main4FourBranchDiscriminantsBelow X)
      (main4EightBranchDiscriminantsBelow X) := by
  rw [Finset.disjoint_union_left]
  exact ⟨main4OddBranch_disjoint_eightBranch X,
    main4FourBranch_disjoint_eightBranch X⟩

/-- Arbitrary finite sums over positive fundamental discriminants reindex
exactly into the three `m`, `4m`, and `8m` branches. -/
theorem sum_fundamentalDiscriminantsBelow_eq_main4_radical_sums
    {A : Type*} [AddCommMonoid A] (F : ℕ → A) (X : ℝ) :
    (∑ D ∈ fundamentalDiscriminantsBelow X, F D) =
      (∑ m ∈ main4OddBranchRadicandsBelow X, F m) +
        (∑ m ∈ main4FourBranchRadicandsBelow X, F (4 * m)) +
          ∑ m ∈ main4EightBranchRadicandsBelow X, F (8 * m) := by
  have hfourInj : Set.InjOn (fun m : ℕ ↦ 4 * m)
      (main4FourBranchRadicandsBelow X : Set ℕ) := by
    intro a _ b _ hab
    exact Nat.mul_left_cancel (by norm_num) hab
  have heightInj : Set.InjOn (fun m : ℕ ↦ 8 * m)
      (main4EightBranchRadicandsBelow X : Set ℕ) := by
    intro a _ b _ hab
    exact Nat.mul_left_cancel (by norm_num) hab
  rw [fundamentalDiscriminantsBelow_eq_main4_branch_union,
    Finset.sum_union (main4OddUnionFourBranch_disjoint_eightBranch X),
    Finset.sum_union (main4OddBranch_disjoint_fourBranch X)]
  unfold main4FourBranchDiscriminantsBelow
    main4EightBranchDiscriminantsBelow
  rw [Finset.sum_image hfourInj, Finset.sum_image heightInj]

/-- On a squarefree radicand, the genus weight is exactly the reciprocal of
the divisor count `tau(m)`. -/
theorem genusWeight_eq_one_div_card_divisors_of_squarefree
    {m : ℕ} (hsf : Squarefree m) :
    genusWeight m = 1 / (m.divisors.card : ℝ) := by
  rw [card_divisors_eq_two_pow_cardDistinctFactors hsf]
  simp [genusWeight]

/-- In the `D = 4m` branch, `w(D) = 1 / (2 * tau(m))`. -/
theorem genusWeight_four_mul_eq_one_div_two_mul_card_divisors
    {m : ℕ} (hodd : Odd m) (hsf : Squarefree m) :
    genusWeight (4 * m) = 1 / (2 * (m.divisors.card : ℝ)) := by
  unfold genusWeight
  rw [card_divisors_eq_two_pow_cardDistinctFactors hsf,
    cardDistinctFactors_four_mul_of_odd hodd]
  simp [pow_succ, mul_comm]

/-- In the `D = 8m` branch, `w(D) = 1 / (2 * tau(m))`. -/
theorem genusWeight_eight_mul_eq_one_div_two_mul_card_divisors
    {m : ℕ} (hodd : Odd m) (hsf : Squarefree m) :
    genusWeight (8 * m) = 1 / (2 * (m.divisors.card : ℝ)) := by
  unfold genusWeight
  rw [card_divisors_eq_two_pow_cardDistinctFactors hsf,
    cardDistinctFactors_eight_mul_of_odd hodd]
  simp [pow_succ, mul_comm]

/-- The literal genus-weighted finite discriminant sum in the manuscript,
rewritten with the exact `tau(m)^{-1}` and `(2 tau(m))^{-1}` weights.  This
is the finite reindexing interface needed before the four mod-eight twists
or Wilson's analytic estimate enter. -/
theorem sum_genusWeight_mul_fundamentalDiscriminantsBelow_eq_main4_radical_sums
    (L : ℕ → ℝ) (X : ℝ) :
    (∑ D ∈ fundamentalDiscriminantsBelow X, genusWeight D * L D) =
      (∑ m ∈ main4OddBranchRadicandsBelow X,
        (1 / (m.divisors.card : ℝ)) * L m) +
      (∑ m ∈ main4FourBranchRadicandsBelow X,
        (1 / (2 * (m.divisors.card : ℝ))) * L (4 * m)) +
      ∑ m ∈ main4EightBranchRadicandsBelow X,
        (1 / (2 * (m.divisors.card : ℝ))) * L (8 * m) := by
  rw [sum_fundamentalDiscriminantsBelow_eq_main4_radical_sums
    (fun D ↦ genusWeight D * L D) X]
  have hoddSum :
      (∑ m ∈ main4OddBranchRadicandsBelow X, genusWeight m * L m) =
        ∑ m ∈ main4OddBranchRadicandsBelow X,
          (1 / (m.divisors.card : ℝ)) * L m := by
    apply Finset.sum_congr rfl
    intro m hm
    obtain ⟨_, hsf, _, _⟩ := mem_main4OddBranchRadicandsBelow.mp hm
    rw [genusWeight_eq_one_div_card_divisors_of_squarefree hsf]
  have hfourSum :
      (∑ m ∈ main4FourBranchRadicandsBelow X,
          genusWeight (4 * m) * L (4 * m)) =
        ∑ m ∈ main4FourBranchRadicandsBelow X,
          (1 / (2 * (m.divisors.card : ℝ))) * L (4 * m) := by
    apply Finset.sum_congr rfl
    intro m hm
    obtain ⟨hodd, hsf, _, _⟩ := mem_main4FourBranchRadicandsBelow.mp hm
    rw [genusWeight_four_mul_eq_one_div_two_mul_card_divisors hodd hsf]
  have heightSum :
      (∑ m ∈ main4EightBranchRadicandsBelow X,
          genusWeight (8 * m) * L (8 * m)) =
        ∑ m ∈ main4EightBranchRadicandsBelow X,
          (1 / (2 * (m.divisors.card : ℝ))) * L (8 * m) := by
    apply Finset.sum_congr rfl
    intro m hm
    obtain ⟨hodd, hsf, _⟩ := mem_main4EightBranchRadicandsBelow.mp hm
    rw [genusWeight_eight_mul_eq_one_div_two_mul_card_divisors hodd hsf]
  rw [hoddSum, hfourSum, heightSum]

end

end PellPaper
